> {-# LANGUAGE TupleSections, DeriveFunctor, LambdaCase #-}
> module Simulate.CleanEval (runProcS, initStateS, buildCodeMemS, heapS) where

> import Simulate.ProcDefs

> import Control.Monad.State.Strict hiding (forM)
> import Data.Array.IO
> import Data.Foldable (toList)
> import Control.Arrow (first, second)
> import Data.Maybe
> import Data.Either
> import Data.IntMap (IntMap, (!), insert, alter, delete, empty, lookup, fromList, updateLookupWithKey, size)
> import Data.List (elemIndex, isSuffixOf)
> import Data.Array.IArray (listArray)
> import Data.Word (Word64, Word32)
> import Data.Bits (shiftL, (.&.), testBit, setBit, clearBit)
> import System.IO (stdout, hFlush)
> import System.IO.Unsafe (unsafePerformIO)
> import Debug.Trace

> data ProcState = ProcState {heap :: !HeapState, stack :: !(Stack StackNode), topTagIndex :: !Word32, topNodeCond :: !(CondValue ()),
>   refQueue :: ![RefValue], primQueue :: ![PrimValue], condQueue :: ![CondValue ()], prefetchRef :: Maybe RefValue,
>   savedCond :: Maybe (CondValue ()), retStack :: !(Stack ((CallFrame, Maybe (CondValue ())), Int)), contStack :: !(Stack ContData), extraCont :: !Int,
>   code :: CodeMem, ip :: CodeAddr, ni :: NextInstr, stats :: !Stats}

> heapS :: ProcState -> HeapState
> heapS = heap

> instance Show ProcState where
>  -- show (ProcState h _ _ _ _ _ _ _ _ _ i n s) = "step: " ++ show s ++ " " ++ show h ++ " ip: " ++ show i ++ " next: " ++ show n
>   show (ProcState h (Stack xs) _ _ sq pq cq _ _ (Stack rs) (Stack cs) ec _ i n s) =
>     "step: " ++ show s ++ " " ++ show h ++ " ip: " ++ show i ++ " next: " ++ show n ++ " ec: " ++ show ec ++
>     "\nrs: " ++ show (length rs) ++ "  " ++ show (take 2 rs) ++ "\nrq: " ++ show (take 5 sq) ++
>     "\npq: " ++ show pq ++ " cs: " ++ show (take 2 cs) ++ "  cq: " ++ show (take 1 cq) ++ "\n" ++ concatMap ((++ "\n") . show) (take 4 xs) ++ "...   "

> showStackResult :: Proc String
> showStackResult = gets (show . peek . stack)

> allocHeapSize :: Int
> allocHeapSize = 512 -- 512
> compactAllocRange :: Int
> compactAllocRange = 64  -- 32
> compactAllocMask :: Word64
> compactAllocMask = 0-1  -- (1 `shiftL` compactAllocRange) - 1 

> cacheIxSize,nWays :: Int
> cacheIxSize = 128
> nWays       = 4
> initCTag :: CacheTag
> initCTag = FourWay Nothing Nothing Nothing Nothing (LRU4 0 1 2)

> data HeapState = HeapState {heapTop :: HeapAddr, nursery :: IOArray HeapAddr (Maybe Node), refCounters :: IOArray Int (RefCounter,ReadState), freeLines :: !Word64,
>   cTags :: IOArray Int CacheTag, cData :: IOArray Int (Maybe Node),
>   heapMem :: !(IntMap Node), inputFifo :: [Node], outputFifo :: [Node]}

> instance Show HeapState where
>   show (HeapState t _ _ _ _ _ m _ _)  = "heap: " ++ show t ++ " mem: " ++ show (size m)

> data CacheTag = FourWay (Maybe HeapAddr) (Maybe HeapAddr) (Maybe HeapAddr) (Maybe HeapAddr) LRU4
> data LRU4 = LRU4 !Int !Int !Int

> oldLRU4 :: LRU4 -> Int
> oldLRU4 (LRU4 a b c)
>   | a /= 0 && b /= 0 && c /= 0 = 0
>   | a /= 1 && b /= 1 && c /= 1 = 1
>   | a /= 2 && b /= 2 && c /= 2 = 2
>   | otherwise                  = 3

> setLRU4 :: Int -> LRU4 -> LRU4
> setLRU4 x (LRU4 a b c)
>  | x == a    = LRU4 a b c
>  | x == b    = LRU4 b a c
>  | x == c    = LRU4 c a b
>  | otherwise = LRU4 x a b

> dropLRU4 :: Int -> LRU4 -> LRU4
> dropLRU4 x r@(LRU4 a b c)
>  | x == a    = LRU4 b c (oldLRU4 r)
>  | x == b    = LRU4 a c (oldLRU4 r)
>  | x == c    = LRU4 a b (oldLRU4 r)
>  | otherwise = LRU4 a b c

> data ReadState = UnTouched | SharedRead deriving (Show, Eq)

> data RefCounter = Zero | One | Two | Three | Four | Five | Six | Many deriving (Show, Eq, Enum)

> incRefCount :: RefCounter -> RefCounter
> incRefCount Zero  = error "resurrecting dead"
> incRefCount Many  = Many
> incRefCount x     = succ x

> decRefCount :: RefCounter -> RefCounter
> decRefCount Zero  = error "already dead"
> decRefCount Many  = Many
> decRefCount x     = pred x

> type CodeMem = IntMap Instruction

> newtype Stack a = Stack [a] deriving (Functor)

> data StackNode = StNode !(Maybe RefValue) !NodeTag !NodeBody PrimVals deriving (Show)
> type PrimVals  = Quad (Maybe PrimValue)
> emptyPrimVals  = Q Nothing Nothing Nothing Nothing

> initStateS :: CodeMem -> [Node] -> IO ProcState
> initStateS c is = do
>   n  <- liftIO $ newArray (0, allocHeapSize - 1) Nothing
>   rc <- liftIO $ newArray (0, allocHeapSize - 1) (Zero, UnTouched)
>   ct <- liftIO $ newArray (0, cacheIxSize - 1) initCTag
>   cd <- liftIO $ newArray (0, cacheIxSize*nWays - 1) Nothing
>   return (ProcState {heap = HeapState {heapTop = 0, nursery = n, refCounters = rc, freeLines = 0, cTags = ct, cData = cd, heapMem = empty, inputFifo = is, outputFifo = []},
>     stack = Stack [], topTagIndex = 0, topNodeCond = (Nothing, False), refQueue = [], primQueue = [], condQueue = [(Nothing,False)], prefetchRef = Nothing,
>     savedCond = Nothing, retStack = Stack [((CallFrame Nothing 0 ThreadFinish,Nothing),0)], contStack = Stack [], extraCont = 0,
>     code = c, ip = CodeAddr (-1), ni = NextIP, stats = Stats 0 0 0 0 0 0 0 0 0 0})

The frame that's pushed on the return stack.

> data CallFrame = CallFrame  (Maybe (PtrTag, HeapRef)) Int Continuation deriving Show   -- update node, extra applications, return address

> type ContData = EvalCont RefValue PrimValue

Where to continue after return from a call.

> data Continuation
>   = ReturnNext
>   | ReturnTo     StackResult (Maybe NodeElem) CodeAddr
>   | IntoCase     StackResult CaseTable        CodeAddr
>   | IntoBigCase  StackResult AltOffset        CodeAddr
>   | IntoWhen     RelCodeAddr                  CodeAddr
>   | ThreadFinish
>   deriving Show

The state of the sequencer.

> data NextInstr
>   = NextIP
>   | BranchTo CodeAddr
>   | DecideBranch CondRead CodeAddr CodeAddr
>   | NextInstr Instruction
>   | FinishLoad (Maybe RefValue) Continuation   -- Nothing is reading from input fifo
>   | EvalTop Bool Continuation                  -- Bool expecting evaluated value
>   | Continue Continuation
>   | Returning PopMask
>   | Unwind RefValue
>   deriving (Show)

> type Proc     a = StateT ProcState IO a
> type HeapProc a = StateT HeapState IO a

> data Stats = Stats {nSteps :: !Int, nInstrs :: !Int,
>   nStores :: !Int, bigStores :: !Int,
>   nLoads :: !Int,  bigLoads :: !Int,
>   nCalls :: !Int,  bigCalls :: !Int,
>   nReturns :: !Int, bigReturns :: !Int
>   }

> instance Show Stats where
>   show s = "total steps: " ++ show (nSteps s) ++ "   executed instructions: " ++ show (nInstrs s) ++
>      "\nstores: " ++ show (nStores s) ++ "   of which big: " ++ show (bigStores s) ++
>      "\nloads : " ++ show (nLoads s)  ++ "   of which big: " ++ show (bigLoads s) ++
>      "\nfun calls: " ++ show (nCalls s)  ++ "   of which big: " ++ show (bigCalls s) ++
>      "\nreturns: " ++ show (nReturns s)  ++ "   of which big: " ++ show (bigReturns s)

> updateStats :: (Stats -> Stats) -> Proc ()
> updateStats f = modify (\gs -> gs {stats = f (stats gs)})

Run a program step by step until the return stack is empty and the top of the stack has been evaluated.

> runProcS :: ProcState -> IO (String, ProcState)
> runProcS s = runStateT (runProgram >> showStackResult) s

> runProgram :: Proc ()
> runProgram = do
>   updateStats (\gs -> gs {nSteps = 1 + nSteps gs})
>   gs <- get
> --  liftIO $ print gs
>   case (ni gs, isLast $ retStack gs) of
>     (Unwind _   , True) -> error "unhandled exception"
>     (Returning _, True) -> trace ("\n" ++ show (stats gs)) (return ())
>     (instr      , _   ) -> runStep instr >> runProgram

Run a single step based on the sequencer state.

> traceDebugI :: String -> a -> a
> traceDebugI m x = {- trace m -} x

> runStep :: NextInstr -> Proc ()
> runStep (NextIP)             = get_next_ip >>= runInstrAt
> runStep (BranchTo t)         = runInstrAt t
> runStep (DecideBranch c t e) = traceDebugI ("\n-===-> finish branch")            (fmap (asBool "need bool value") (peekAtC c) >>= \cond -> set_next_instr $ BranchTo (if cond then t else e))
> runStep (NextInstr x)        = traceDebugI ("\n-----> " ++ show x)               (runInstr x)
> runStep (FinishLoad x c)     = traceDebugI ("\n-===-> fetching @" ++ show x)     (finishLoad x >> set_next_instr (EvalTop False c))
> runStep (EvalTop e c)        = {-  getTag >>= (\t -> trace ("\n-===-> evaluating " ++ show t ++ " with " ++ show c) (return ())) >> -} (runEval e c >>= set_next_instr)
> runStep (Continue c)         = traceDebugI ("\n-===-> continue with " ++ show c) (runContinue c >>= set_next_instr)
> runStep (Returning pm)       = traceDebugI ("\n-===-> returning")                (cleanRefs pm >> runReturn)   -- same as TopReturn instruction
> runStep (Unwind e)           = traceDebugI ("\n-===-> unwinding exception")      (runUnwind e >>= set_next_instr)

Read and run an instruction from code memory.

> runInstrAt :: CodeAddr -> Proc ()
> runInstrAt (CodeAddr i) = do
>   updateStats (\gs -> gs {nInstrs = 1 + nInstrs gs})
>   modify (\gs -> gs {ip = (CodeAddr i), ni = NextIP})
>   gets code >>= runInstr . (\x -> traceDebugI ("\n-----> " ++ show x) x) . (! fromIntegral i)

Run the first step of a normal instruction.

> runInstr :: Instruction -> Proc ()
> runInstr (Nop pm)               = cleanRefs pm
> runInstr (Call    sc r a nl pm) = runRoutine r a pm =<< liftM (ReturnTo sc nl)    get_next_ip
> runInstr (Case    sc r a xs pm) = runRoutine r a pm =<< liftM (IntoCase sc xs)    get_next_ip
> runInstr (BigCase sc r a om pm) = runRoutine r a pm =<< liftM (IntoBigCase sc om) get_next_ip
> runInstr (When       r a ep pm) = runRoutine r a pm =<< liftM (IntoWhen ep)       get_next_ip
> runInstr (Jump       r a    pm) = runRoutine r a pm           (ReturnNext)
> runInstr (Return t as pm) = do
>   updateStats (\gs -> gs {nReturns = 1 + nReturns gs})
>   when (bodyArity as > 3) $ updateStats (\gs -> gs {bigReturns = 1 + bigReturns gs})
>   nb <- readNode as
>   cleanRefs pm
>   newTopNode t nb
>   runReturn
> runInstr (ReturnTag t pm) = do
>   updateStats (\gs -> gs {nReturns = 1 + nReturns gs})
>   cleanRefs pm
>   newTopNode t []
>   runReturn
> runInstr (ReturnTop pm) = updateStats (\gs -> gs {nReturns = 1 + nReturns gs}) >> cleanRefs pm >> runReturn
> runInstr (ReturnConst c x pm) = do
>   updateStats (\gs -> gs {nReturns = 1 + nReturns gs})
>   cleanRefs pm
>   newTopNode (NodeTag Dynamic 1 singlePrimK (Box c)) [PVal $ fromIntegral x]
>   runReturn
> runInstr (ReturnPrim c p pm) = do
>   updateStats (\gs -> gs {nReturns = 1 + nReturns gs})
>   x <- peekAtP p
>   cleanRefs pm
>   pushStack (StNode Nothing (NodeTag Dynamic 1 singlePrimK (Box c)) [] (Q (Just x) Nothing Nothing Nothing))
>   runReturn
> runInstr (ReturnBool a c pm) = do
>   updateStats (\gs -> gs {nReturns = 1 + nReturns gs})
>   x <- peekAtC c
>   cleanRefs pm
>   pushStackWithBool x a
>   runReturn
> runInstr (ReturnRaw abs pm) = do
>   updateStats (\gs -> gs {nReturns = 1 + nReturns gs})
>   when (bodyArity abs > 3) $ updateStats (\gs -> gs {bigReturns = 1 + bigReturns gs})
>   xs <- readNode $ fmap (maybe Nothing (either (Just . Left) (const Nothing))) abs
>   ys <- readValues (rights $ catMaybes $ toList abs)
>   cleanRefs pm
>   newTopNodeRaw xs ys
>   runReturn
> runInstr (IfElse px c ep pm) = do
>   runPrimInstr px
>   cleanRefs pm
>   nip <- get_next_ip
>   set_next_instr $ DecideBranch c nip (relJump nip ep)
> runInstr (Store t rn pm) = do
>   updateStats (\gs -> gs {nStores = 1 + nStores gs})
>   when (bodyArity rn > 3) $ updateStats (\gs -> gs {bigStores = 1 + bigStores gs})
>   nb <- readNode rn
>   cleanRefs pm
>   pushRef =<< storeNode (Node t nb)
> runInstr (StoreFE nf uf x as pm) = do
>   updateStats (\gs -> gs {nStores = 1 + nStores gs})
>   let ef = evalFunFromApply as
>   rx <- peekAtR x
>   av <- readAppValues as
>   let nb = map RVal $ case av of {Select _ -> [rx]; Apply1 y -> [rx,y]; Apply2 y z -> [rx,y,z]} 
>   cleanRefs pm
>   pushRef =<< storeNodeFE nf (FE ef uf) nb
> runInstr (StoreBox c a pm) = do
>   updateStats (\gs -> gs {nStores = 1 + nStores gs})
>   x <- peekAtP a
>   cleanRefs pm
>   pushRef =<< storeNode (Node (NodeTag Dynamic 1 singlePrimK (Box c)) [PVal x])
> runInstr (StoreBool a c pm) = do
>   updateStats (\gs -> gs {nStores = 1 + nStores gs})
>   x <- fmap (asBool "cond Store") $ peekAtC c
>   cleanRefs pm
>   pushRef =<< storeNode (Node (NodeTag Dynamic 0 emptyKinds (Con $ if x then fmap succ a else a)) [])
> runInstr (StoreCVal cv pm) = do
>   cleanRefs pm
>   pushRef (CVRef cv)
> runInstr (PushCAFRef (t,a) pm) = do
>   cleanRefs pm
>   pushRef (Ref t a)
> runInstr (StoreSelect c a b pm) = do
>   cond <- fmap (asBool "need bool value") $ peekAtC c
>   x <- peekAtR a
>   y <- peekAtR b
>   cleanRefs pm
>   pushRef (if cond then x else y)
> runInstr (Push xys pm) = do
>   nb <- readNode $ fmap (maybe Nothing (either (Just . Left) (const Nothing))) xys
>   ps <- readValues $ rights $ catMaybes $ toList xys
>   cleanRefs pm
>   newTopNodeRaw nb ps
> runInstr (PushCont a pm) = do
>   av <- readAppValues a
>   cleanRefs pm
>   pushContStack av
> runInstr (ClearRefs xs pm) = do
>   nb <- readNode (fmap (maybe Nothing (either (Just . Left) (const Nothing))) xs)
>   cleanRefs pm
>   withHeap $ decRefCounters $ bodyRefAddrs nb
> runInstr (PrimInstr a b pm) = do
>   runPrimInstr a
>   runPrimInstr b
>   cleanRefs pm
> runInstr (Send i t rn pm) = do
>   nb <- readNode rn
>   cleanRefs pm
>   withHeap $ modify (\hs -> hs {outputFifo = (Node t nb):outputFifo hs})
>   unsafePerformIO (case (plainTag t,nb) of {(Con (cn,0), [PVal c]) | "Czh" `isSuffixOf` cn -> putChar (toEnum $ fromIntegral c); _ -> putStrLn $ show $ Node t nb} >> hFlush stdout) `seq` return ()
> runInstr (Throw x pm) = do
>   e <- peekAtR x
>   cleanRefs pm
>   runUnwind e >>= set_next_instr
> runInstr (GoTo x pm) = cleanRefs pm >> set_next_instr (BranchTo x)

> runPrimInstr :: PrimInstr -> Proc ()
> runPrimInstr (PrimNop           ) = return ()
> runPrimInstr (PrimOp     p a b c) = pushPrim =<< liftM3 (execPrimOp p) (fmap (asBool "need bool value") $ peekAtC c) (peekAtP a) (peekAtP b) 
> runPrimInstr (PrimConst x       ) = pushPrim x
> runPrimInstr (CmpOp  (p,q) a b c) = pushCond =<< liftM2 (execLogicOp q) (liftM2 (execCmpOp p) (peekAtP a) (peekAtP b)) (peekAtC c)

> runRoutine :: Callable -> ExtraCont -> PopMask -> Continuation -> Proc ()
> runRoutine (Run f xs)      a pm c = runFunCall f (Just False) xs [] a pm c
> runRoutine (Fix f xs)      a pm c = runFunCall f (Just True)  xs [] a pm c
> runRoutine (Proc f xys)    a pm c = runFunCall f Nothing      xs ys a pm c where {xs = fmap (maybe Nothing (either (Just . Left) (const Nothing))) xys; ys = rights $ catMaybes $ toList xys}
> runRoutine (Eval x)        a pm c = peekAtR x >>= runEvalFetchRec False a pm c . Just
> runRoutine (Fetch x)       a pm c = peekAtR x >>= runEvalFetchRec True  a pm c . Just
> runRoutine (EvalCAF (t,r)) a pm c =               runEvalFetchRec False a pm c (Just $ Ref t r)
> runRoutine (EvalFetched)   a pm c =               runEvalFetchRec False a pm c Nothing
> runRoutine (PushFetched)   a pm c =               runEvalFetchRec True  a pm c Nothing
> runRoutine (Receive i)     a pm c =               runEvalFetchRec False a pm c Nothing

> runEvalFetchRec :: Bool -> ExtraCont -> PopMask -> Continuation -> Maybe RefValue -> Proc ()
> runEvalFetchRec e a pm c mvx = do
>   av <- readAppValues a
>   cleanRefs pm
>   pushContStack av
> --  set_next_instr (FinishLoad mvx c)
>   (finishLoad mvx >> set_next_instr (EvalTop e c))  -- TEMP shortcut to reduce differences with DetailEval

> runFunCall :: FunAddr -> Maybe Bool -> NodeRead -> [PrimRead] -> ExtraCont -> PopMask -> Continuation -> Proc ()
> runFunCall f mff xs ys a pm c = do
>   updateStats (\gs -> gs {nCalls = 1 + nCalls gs})
>   nb <- readNode xs
>   ps <- readValues ys
>   when ((length nb + length ys) > 3) $ updateStats (\gs -> gs {bigCalls = 1 + bigCalls gs})
>   av <- readAppValues a
>   cleanRefs pm
>   mur <- case mff of
>     Nothing    -> newTopNodeRaw nb ps                                                                                                         >> return Nothing
>     Just False -> pushStack (node2stnode Nothing $ Node (NodeTag Dynamic (bodyArity xs) (bodyKinds xs) $ Fun f Nothing SkipUpd) nb) >> return Nothing
>     Just True  -> do  -- Fix function
>       r@(Ref pt u) <- useClonedRef =<< storeNode (Node (NodeTag Dynamic (bodyArity xs) emptyKinds $ Blackhole) (map (const $ RVal $ CVRef VoidRef) nb))
>       pushStack (node2stnode (Just r) $ Node (NodeTag Dynamic (bodyArity xs) (bodyKinds xs) $ Fun f Nothing WithUpd) nb)
>       return (Just (pt,u))
>   pushContStack av
>   sc <- gets (Just . head . condQueue)
>   pushCallFrame c sc mur
>   set_next_instr (BranchTo $ snd f)

> readAppValues :: ExtraCont -> Proc ContData
> readAppValues (NoEvalCont  ) = return NoEvalCont
> readAppValues (Apply1 a    ) = liftM  Apply1 (peekAtR a)
> readAppValues (Apply2 a b  ) = liftM2 Apply2 (peekAtR a) (peekAtR b)
> readAppValues (Select i    ) = return (Select i)
> readAppValues (ThenFetch r ) = fmap ThenFetch (peekAtR r)
> readAppValues (WithCatch r ) = fmap WithCatch (peekAtR r)
> readAppValues (WithPrim p x) = fmap (WithPrim p) (peekAtP x)

> storeNodeFE :: NodeFormat -> Tag -> NodeBody -> Proc RefValue
> storeNodeFE _ (FE (E_ap1) uf) ((RVal (CVRef (EmptyPap f ni b vs))) : ns') | b == 1 = storeNode $ Node (NodeTag Dynamic 1 vs $ Fun f ni uf) ns'
> storeNodeFE _ (FE (E_ap2) uf) ((RVal (CVRef (EmptyPap f ni b vs))) : ns') | b == 2 = storeNode $ Node (NodeTag Dynamic 2 vs $ Fun f ni uf) ns'
> storeNodeFE _ (FE (E_ap1) _ ) ((RVal (CVRef (EmptyDCon c   b vs))) : ns') | b == 1 = storeNode $ Node (NodeTag Dynamic 1 vs $ Con c) ns'
> storeNodeFE _ (FE (E_ap2) _ ) ((RVal (CVRef (EmptyDCon c   b vs))) : ns') | b == 2 = storeNode $ Node (NodeTag Dynamic 2 vs $ Con c) ns'
> storeNodeFE _ (FE (E_ap1) uf) ((RVal (CVRef (EmptyPEF fe   b vs))) : [n]) | b == 1 = storeNode $ Node (NodeTag Dynamic 1 vs $ FE fe uf) [n]
> -- storeNodeFE _  (FE (E_sel i)) ([Left ((Ref (TC _) p))]) = do  -- FIXME ref counting updating -- should be only in case of p in the local heap
> --      (_, Node _ xs) <- withHeap $ retrieveNode p   -- maybe check the tag
> --      return (False, either id (error "select of primValue") (xs !! fromEnum i))
> storeNodeFE nf t nb = storeNode $ Node (NodeTag Dynamic (fst nf) (snd nf) t) nb

> storeNode :: Node -> Proc RefValue
> storeNode x@(Node t ns) = case compactNode t ns of
>   _ | nodeKind t == Static -> withHeap (allocNode x)
>   Just v                   -> return v
>   Nothing                  -> withHeap (allocNode x)

Trying to compact a Node in a single Value.

> compactNode :: NodeTag -> NodeBody -> Maybe RefValue
> compactNode t xs
>   | nodeKind t == Static = Nothing
>   | otherwise = case (plainTag t, xs) of
>     (Con c     , []) -> Just (CVRef $ EnumTag c                   )
>     (DCon c n  , []) -> Just (CVRef $ EmptyDCon c   n $ kindMask t)
>     (Pap f ni n, []) -> Just (CVRef $ EmptyPap f ni n $ kindMask t)
>     (PE ef n   , []) -> Just (CVRef $ EmptyPEF ef   n $ kindMask t)
>     (Box c     , [PVal n]) | n < 2147483648 || n >= -2147483648 -> Just (CVRef $ PrimBox c (fromIntegral n))
>     _                   -> Nothing

> expandValue :: CompactValue -> Node
> expandValue (PrimBox t n       ) = Node (NodeTag Dynamic 1 singlePrimK $ Box t     ) [PVal $ fromIntegral n]
> expandValue (EnumTag t         ) = Node (NodeTag Dynamic 0 emptyKinds  $ Con t     ) []
> expandValue (EmptyDCon c   n vs) = Node (NodeTag Dynamic 0 vs          $ DCon c n  ) []
> expandValue (EmptyPap f ni a vs) = Node (NodeTag Dynamic 0 vs          $ Pap f ni a) []
> expandValue (EmptyPEF ef   a vs) = Node (NodeTag Dynamic 0 vs          $ PE ef    a) []

Fetch from the heap or if it's a compact value push it on the stack directly.

> finishLoad :: Maybe RefValue -> Proc ()
> finishLoad (Nothing) = do
>   updateStats (\gs -> gs {nLoads = 1 + nLoads gs})
>   mpf <- gets prefetchRef
>   case mpf of
>     Nothing -> do
>       rn <- withHeap $ gets (head . inputFifo)
>       withHeap $ modify (\hs -> hs {inputFifo = tail (inputFifo hs)})
>       pushStack $ node2stnode Nothing rn
>     Just vx -> do
>       modify (\gs -> gs {prefetchRef = Nothing})
>       finishLoad (Just vx)
> finishLoad (Just (CVRef vx  )) =  do
>   updateStats (\gs -> gs {nLoads = 1 + nLoads gs})
>   let nb = expandValue vx 
>   pushStack (node2stnode (Just $ CVRef vx) nb)
> finishLoad (Just (Ref _ r)) = do
>   updateStats (\gs -> gs {nLoads = 1 + nLoads gs})
>   lx <- withHeap (retrieveNode r)
>   pushStack (uncurry node2stnode lx)
>   StNode _ _ xs _ <- peekStackTop
>   when (length xs > 3) $ updateStats (\gs -> gs {bigLoads = 1 + bigLoads gs})

> runEval :: Bool -> Continuation -> Proc NextInstr
> runEval e c = do
>   StNode tr ct xs _ <- peekStackTop
>   case (plainTag ct, e) of
>     (Fun f _ _, True ) -> error ("expected eval " ++ show ct)
>     (Fun f _ _, False) -> do
>       takeUpdateRef tr ct >>= pushCallFrame c Nothing
>       return (BranchTo $ snd f)
>     (FE ef _, True )  -> error ("expected eval " ++ show ct)
>     (FE ef _, False)  -> do
>       takeUpdateRef tr ct >>= pushCallFrame c Nothing
>       return (NextInstr $ Jump (Eval (R 0 A)) (decodeEvalFunCont ef) (DropRQ,popSTop))
>     (Ind, True ) -> error ("expected eval " ++ show ct)
>     (Ind, False) -> do
>       _ <- popStackTop
>       decRefCounterM tr
>       let [RVal x] = xs
>       return (FinishLoad (Just x) c)
>     _           -> runContinue c

> decodeEvalFunCont :: EvalFun -> ExtraCont
> decodeEvalFuncont (E_id   ) = NoEvalCont
> decodeEvalFunCont (E_ap1  ) = Apply1 (R 0 B)
> decodeEvalFunCont (E_ap2  ) = Apply2 (R 0 B) (R 0 C)
> decodeEvalFunCont (E_sel i) = Select i

> runReturn :: Proc ()
> runReturn = do
>   ec   <- gets extraCont
>   done <- gets (isLast . retStack)
>   case (ec, done) of
>     (0, False) -> do
>       ((CallFrame tmu tec tc, sc), 1) <- popRetStack
>       runUpdate tmu
>       modify (\gs -> gs {extraCont = tec, savedCond = sc}) >> adjustNodeCount 1
>       runContinue tc >>= set_next_instr
>     _ -> runContinue ReturnNext >>= set_next_instr

> runContinue :: Continuation -> Proc NextInstr
> runContinue c = do
>   ec <- gets extraCont
>   av <- case ec of {0 -> return Nothing; _ -> gets (Just . peek . contStack)}
>   StNode tr ct nb _ <- peekStackTop
>   case (plainTag ct, av) of
>     (_, Nothing) -> nextTo False c
>     (_, Just (WithCatch h)) -> do   -- drop catch 'frame'
>       decRefCounterM (Just h)
>       replaceTopCont NoEvalCont
>       nextTo False c
>     (_, Just (ThenFetch x)) -> do
>       modify (\gs -> gs {prefetchRef = Just x})
>       replaceTopCont NoEvalCont
>       nextTo False c
>     (t, Just (WithPrim f x)) | Just b <- primBoxConAlt t -> do
>       replaceTopCont NoEvalCont
>       _ <- modifyStack_ (withTop (\(StNode _ _ _ (Q (Just y) _ _ _)) -> StNode Nothing (NodeTag Dynamic 1 singlePrimK (Box b)) [] (Q (Just $ execPrimOp f True x y) Nothing Nothing Nothing)))
>       decRefCounterM tr
>       nextTo True c
>     (Con _, Just (Select n)) -> do
>       replaceTopCont NoEvalCont
>       pushCallFrame c Nothing Nothing
>       return (NextInstr $ Jump (Eval (R 0 n)) NoEvalCont (DropRQ,popSTop))
>     (Unboxed, Just (Select n)) -> do
>       replaceTopCont NoEvalCont
>       pushCallFrame c Nothing Nothing
>       return (NextInstr $ Jump (Eval (R 0 n)) NoEvalCont (DropRQ,popSTop))
>     (DCon d toAp, Just (Apply1 a)) -> do
>       let nt = case (compare 1 toAp) of {LT -> DCon d (toAp-1); EQ -> Con d; GT -> error ("overapplying " ++ show av ++ " on " ++ show ct)}
>       applyToStackTop nt [a]
>       replaceTopCont NoEvalCont
>       nextTo True c
>     (DCon d toAp, Just (Apply2 a b)) -> do
>       let nt = case (compare 2 toAp) of {LT -> DCon d (toAp-2); EQ -> Con d; GT -> error ("overapplying " ++ show av ++ " on " ++ show ct)}
>       applyToStackTop nt [a,b]
>       replaceTopCont NoEvalCont
>       nextTo True c
>     (HCon d ie     , Just (Apply1 a)) -> do
>       insertToStackTop (Con d) ie a
>       replaceTopCont NoEvalCont
>       nextTo True c
>     (Pap f ni toAp, Just (Apply1 a)) -> do
>       case (compare 1 toAp) of
>         LT -> do
>           applyToStackTop (Pap f ni (toAp-1)) [a]
>           replaceTopCont NoEvalCont
>           nextTo True c
>         _ -> do
>           applyToStackTop (Fun f ni SkipUpd) [a]
>           replaceTopCont NoEvalCont
>           pushCallFrame c Nothing Nothing
>           return (BranchTo $ snd f)
>     (Pap f ni toAp, Just (Apply2 a b)) -> do
>       case (compare 2 toAp) of
>         LT -> do
>           applyToStackTop (Pap f ni (toAp-2)) [a,b]
>           replaceTopCont NoEvalCont
>           nextTo True c
>         EQ -> do
>           applyToStackTop (Fun f ni SkipUpd) [a,b]
>           replaceTopCont NoEvalCont
>           pushCallFrame c Nothing Nothing
>           return (BranchTo $ snd f)
>         GT -> do
>           applyToStackTop (Fun f ni SkipUpd) [a]
>           replaceTopCont (Apply1 b)
>           pushCallFrame c Nothing Nothing
>           return (BranchTo $ snd f)
>     (HFun f ni ie, Just (Apply1 a)) -> do
>       insertToStackTop (Fun f ni SkipUpd) ie a
>       replaceTopCont NoEvalCont
>       pushCallFrame c Nothing Nothing
>       return (BranchTo $ snd f)
>     (HFun f ni ie, Just (Apply2 a b)) -> do
>       insertToStackTop (Fun f ni SkipUpd) ie a
>       replaceTopCont (Apply1 b)
>       pushCallFrame c Nothing Nothing
>       return (BranchTo $ snd f)
>     (PE (E_sel n) 1, Just (Apply1 a)) -> do
>       applyToStackTop (FE (E_sel n) SkipUpd) [a]
>       replaceTopCont NoEvalCont
>       pushCallFrame c Nothing Nothing
>       return (NextInstr $ Jump (Eval (R 0 A)) (Select n) (DropRQ,popSTop))
>     (PE (E_sel n) 1, Just (Apply2 a b)) -> do
>       applyToStackTop (FE (E_sel n) SkipUpd) [a]
>       replaceTopCont (Apply1 b)
>       pushCallFrame c Nothing Nothing
>       return (NextInstr $ Jump (Eval (R 0 A)) (Select n) (DropRQ,popSTop))
>     (PE (E_id) 1, Just (Apply1 a)) -> do
>       applyToStackTop (FE (E_id) SkipUpd) [a]
>       replaceTopCont NoEvalCont
>       pushCallFrame c Nothing Nothing
>       return (NextInstr $ Jump (Eval (R 0 A)) NoEvalCont (DropRQ,popSTop))
>     (PE (E_id) 1, Just (Apply2 a b)) -> do
>       applyToStackTop (FE (E_id) SkipUpd) [a]
>       replaceTopCont (Apply1 b)
>       pushCallFrame c Nothing Nothing
>       return (NextInstr $ Jump (Eval (R 0 A)) NoEvalCont (DropRQ,popSTop))
>     _ -> error ("runContinue with " ++ show av ++ " on " ++ show (tr,ct,nb))

> nextTo :: Bool -> Continuation -> Proc NextInstr
> nextTo withApply c = do
>   ec <- gets extraCont
>   case c of
>     _ | ec > 0         -> return (Continue c)
>     (ReturnNext      ) -> return (Returning (KeepRQ, popNone))
>     (ReturnTo sp mi r) -> adjustPushedResult withApply mi sp r
>     (IntoCase sp xs r) -> do
>        ca <- fmap (caseAltTarget xs . plainTag) getTag
>        case ca of
>          Left (mi, o) -> adjustPushedResult withApply Nothing sp (relJump r o)
>          Right pm     -> return (Returning (DropRQ, pm))
>     (IntoBigCase sp om r) -> getTag >>= adjustPushedResult withApply Nothing sp . relJump r . RelCodeAddr . (`shiftL` fst om) . (.&. ((1 `shiftL` snd om) - 1)) . fromIntegral . getAltIndex . plainTag
>     (IntoWhen eo r)       -> gets (asBool "when condition" . topNodeCond) >>= \c -> return $ BranchTo $ if c then r else relJump r eo

> adjustPushedResult :: Bool -> Maybe NodeElem -> StackResult -> CodeAddr -> Proc NextInstr
> adjustPushedResult withApply mi sp r = do
>   StNode mtr t xs _ <- peekStackTop
>   case (sp, mtr) of
>     (OnlyNode, Nothing) -> return (BranchTo r)
>     (OnlyNode, Just _ ) -> dropTopNodeRef >> return (BranchTo r)
>     (NodeWSC , Just _ ) -> return (BranchTo r)
>     (NodeWSC , Nothing) -> fixupStackTopRef sp withApply mi r
>     (OnlyTag , _     ) -> do
>       _ <- modifyStack_ (withTop (\(StNode _ _ _ _) -> StNode Nothing t [] emptyPrimVals))
>       withHeap $ decRefCounters (bodyRefAddrs $ maybe id ((:) . RVal) mtr xs)
>       return (BranchTo r)
>     (OnlySC  , Just _ ) -> do
>       _ <- modifyStack_ (withTop (\(StNode _ _ _ _) -> StNode mtr t [] emptyPrimVals))
>       withHeap (decRefCounters $ bodyRefAddrs xs)
>       return (BranchTo r)
>     (OnlySC  , Nothing) -> fixupStackTopRef sp withApply mi r

> fixupStackTopRef :: StackResult -> Bool -> Maybe NodeElem -> CodeAddr -> Proc NextInstr
> fixupStackTopRef sp True  mi r = return (Continue $ ReturnTo sp mi r)
> fixupStackTopRef sp False _  r = do
>   StNode _ t xs ys <- peekStackTop
>   case sp of
>     NodeWSC -> case (plainTag t, ys) of
>       (Box _, Q (Just y) _ _ _) -> do
>         tr <- storeNode (Node (asBoxTag t) [PVal y])
>         _ <- modifyStack_ (withTop (\(StNode _ _ _ _) -> StNode (Just tr) t xs ys))
>         return (BranchTo r)
>       _ -> do
>         tr <- storeNode (Node t (map (withRef shareRef) xs))
>         _ <- modifyStack_ (withTop (\(StNode _ nt xs' ys') -> StNode (Just tr) nt (map (withRef shareRef) xs') ys'))
>         withHeap (incRefCounters $ bodyRefAddrs xs)
>         return (BranchTo r)
>     OnlySC -> do
>       tr <- storeNode (Node t xs)
>       _ <- modifyStack_ (withTop (\(StNode _ _ _ _) -> StNode (Just tr) t [] emptyPrimVals))
>       return (BranchTo r)

> dropTopNodeRef :: Proc ()
> dropTopNodeRef = do
>   StNode mtr _ _ _ <- peekStackTop
>   _ <- modifyStack_ (withTop (\(StNode _ t xs ys) -> StNode Nothing t xs ys))
>   decRefCounterM mtr

> asBoxTag :: NodeTag -> NodeTag
> asBoxTag t = NodeTag Dynamic 1 singlePrimK (Box c) where
>   Just c = primBoxConAlt (plainTag t)

> runUpdate :: Maybe (PtrTag, HeapRef) -> Proc ()
> runUpdate (Just (pt, ur@(u, _, _))) = do
>   StNode mtr nt xs ys <- peekStackTop
>   case mtr of
>     Just tr | u /= GlobalRef -> do
>       tr' <- useClonedRef tr
>       withHeap (updateNodeWithInd ur tr')
>       decRefCounterM (Just $ Ref pt ur)
>     _ -> do
>     case plainTag nt of
>       Box   c -> withHeap $ updateNode ur (Node (fixupStaticTag u $ NodeTag Dynamic 1 singlePrimK (Box c)) [PVal y]) where Q (Just y) _ _ _ = ys
>       _       -> do
>         StNode _ t' xs' _ <- modifyStack_ (withTop (\(StNode _ t xs' ys') -> let t' = fixupStaticTag u t in
>                 StNode (Just (Ref (node2PtrTag t') ur)) t' (map (withRef shareRef) xs') ys'))
>         withHeap (incRefCounters (bodyRefAddrs xs') >> updateNode ur (Node t' xs'))
>         decRefCounterM mtr
> runUpdate _ = return ()

> fixupStaticTag :: Uniqueness -> NodeTag -> NodeTag
> fixupStaticTag (GlobalRef) t = t {nodeKind = Static}
> fixupStaticTag _           t = t {nodeKind = Dynamic}

> takeUpdateRef :: Maybe RefValue -> NodeTag -> Proc (Maybe (PtrTag, HeapRef))
> takeUpdateRef r t = do
>   _ <- modifyStack_ (withTop (\(StNode _ nt xs ys) -> StNode Nothing nt xs ys))
>   case r of
>     Just (Ref pt i@(Shared, _, _)) | isUpdFTag (plainTag t) -> return (Just (pt,i))
>     _                                                       -> decRefCounterM r >> return Nothing   -- the reference to nonupdatable function node is also dropped here

> pushCallFrame :: Continuation -> Maybe (CondValue ()) -> Maybe (PtrTag, HeapRef) -> Proc ()
> pushCallFrame c msc mu = do
>   ec <- gets extraCont
>   mtr <- gets (listToMaybe . (\(Stack rs) -> rs) . retStack)
>   case (mu, ec, c, mtr) of
>     (Nothing, 0, ReturnNext, _) -> return ()                                                    -- pushing trivial stack frame
>     (_      , _, _, Just ((CallFrame _ _ ThreadFinish, _), _)) -> do   -- do not merge with last stack frame
>       adjustNodeCount (negate 1)   -- fixup, topmost stack node belongs to new callframe
>       modify (\gs -> gs {retStack = fst (push ((CallFrame mu ec c, msc), 1) (retStack gs)), extraCont = 0})
>     (_      , _, ReturnNext, Just ((CallFrame Nothing tec tc, tsc), tnc)) -> do   -- stack frame merging
>       modify (\gs -> gs {retStack = fst (withTop (const ((CallFrame mu (tec+ec) tc, tsc), tnc)) (retStack gs)), extraCont = 0})
>     _ -> do
>       adjustNodeCount (negate 1)   -- fixup, topmost stack node belongs to new callframe
>       modify (\gs -> gs {retStack = fst (push ((CallFrame mu ec c, msc), 1) (retStack gs)), extraCont = 0})

> pushContStack :: ContData -> Proc ()
> pushContStack NoEvalCont = return ()
> pushContStack x          = modify (\gs -> gs {contStack = fst $ push x $ contStack gs, extraCont = succ (extraCont gs)})

> replaceTopCont :: ContData -> Proc ()
> replaceTopCont NoEvalCont = modify (\gs -> gs {contStack = fst $ pop $ contStack gs, extraCont = pred (extraCont gs)})
> replaceTopCont ec         = modify (\gs -> gs {contStack = fst $ push ec $ fst $ pop $ contStack gs})

> runUnwind :: RefValue -> Proc NextInstr
> runUnwind e = do
>   nc <- getNodeCount
>   when (nc > 4) $ error "unwinding too much at once"
>   let popAt x = if nc > x then Pop else Keep
>   cleanRefs (KeepRQ, Q (popAt 0) (popAt 1) (popAt 2) (popAt 3))
>   ec <- gets extraCont
>   av <- gets (peek . contStack)
>   case ec of
>     0 -> do
>       ((CallFrame mu tec _, sc), 0) <- popRetStack             -- TODO deal with update refcounts??
>       modify (\gs -> gs {extraCont = tec, savedCond = sc})   -- not sure if savedCond updating is needed here
>       return (Unwind e)
>     _ -> case av of
>       (WithCatch h) -> do
>         replaceTopCont (Apply1 e)          -- replace handler by application of the exception
>         return (FinishLoad (Just h) ReturnNext)
>       _ -> replaceTopCont NoEvalCont >> return (Unwind e)   -- TODO refcounts of dropped continuation

> newTopNodeRaw :: NodeBody -> [PrimValue] -> Proc ()
> newTopNodeRaw nb ps = pushStack (StNode Nothing (NodeTag Dynamic (toEnum $ length nb) (bodyKinds_ $ map ate nb) Unboxed) nb ps') where
>   ps' = extractPrimVals (map (const $ RVal undefined) nb ++ map PVal ps)
>   ate x = case x of {RVal r -> Left r; PVal p-> Right p} 

> newTopNode :: NodeTag -> NodeBody -> Proc ()
> newTopNode t nb = pushStack (node2stnode (compactNode t nb) $ Node t nb) where

> get_next_ip :: Proc CodeAddr
> get_next_ip = gets ip >>= (\(CodeAddr i) -> return (CodeAddr (i+1)))

> set_next_instr :: NextInstr -> Proc ()
> set_next_instr x = modify (\gs -> gs {ni = x})

> relJump :: CodeAddr -> RelCodeAddr -> CodeAddr
> relJump (CodeAddr i) (RelCodeAddr x) = CodeAddr (i + fromIntegral x)

> modifyStack_ :: (Stack StackNode -> (Stack StackNode, x)) -> Proc x
> modifyStack_ f = do
>   gs <- get
>   let (s', x) = f (stack gs)
>   put (gs {stack = s'})
>   return x

> peekStackTop :: Proc StackNode
> peekStackTop = gets (peek . stack)

> popStackTop :: Proc StackNode
> popStackTop = adjustNodeCount (negate 1) >> modifyStack_ pop

> cleanRefs :: PopMask -> Proc ()
> cleanRefs (prq, pm) = do
>   when (prq == DropRQ) $ do
>     gets refQueue >>= withHeap . decRefCounters . bodyRefAddrs . map RVal
>     modify (\gs -> gs {refQueue = []})
>   modifyStack_ (popN pm) >>= withHeap . decRefCounters . bodyRefAddrs . map RVal
>   adjustNodeCount (negate $ length $ filter (==Pop) $ toList pm)

> pushStack :: StackNode -> Proc ()
> pushStack n@(StNode _ t _ _) = adjustNodeCount 1 >> modifyStack_ (push n) >> updateTopTagIndex (plainTag t) (Nothing, odd $ tag2Index $ plainTag t)

> pushStackWithBool :: CondValue () -> ConAlt -> Proc ()
> pushStackWithBool c a = adjustNodeCount 1 >> modifyStack_ (push $ StNode Nothing (NodeTag Dynamic 0 emptyKinds $ Con a) [] (Q Nothing Nothing Nothing Nothing)) >> updateTopTagIndex (Con a) c

> updateTopTagIndex :: Tag -> CondValue () -> Proc ()
> updateTopTagIndex t c = modify (\gs -> gs {topTagIndex = tag2Index t, topNodeCond = c})

> applyToStackTop :: Tag -> [RefValue] -> Proc ()
> applyToStackTop t as = do
>   StNode mtr ont _ _ <- peekStackTop 
>   _ <- modifyStack_ (withTop (\(StNode _ _ xs ys) -> StNode Nothing (NodeTag Dynamic (toEnum (length xs + length as)) (kindMask ont) t) (xs ++ map RVal as) ys))
>   updateTopTagIndex t (Nothing, odd $ tag2Index t)
>   decRefCounterM mtr

> insertToStackTop :: Tag -> NodeElem -> RefValue -> Proc ()
> insertToStackTop t e a = do
>   StNode mtr ont _ _ <- peekStackTop 
>   let i = fromEnum e
>   _ <- modifyStack_ (withTop (\(StNode _ _ xs ys) -> StNode Nothing (NodeTag Dynamic (nodeArity ont) (kindMask ont) t) (take i xs ++ [RVal a] ++ drop (i+1) xs) ys))
>   updateTopTagIndex t (Nothing, odd $ tag2Index t)
>   decRefCounterM mtr

> getTag :: Proc NodeTag
> getTag = gets ((\(StNode _ t _ _) -> t) . peek . stack)

> popRetStack :: Proc ((CallFrame, Maybe (CondValue ())), Int)
> popRetStack = do
>   gs <- get
>   let (s', x) = pop (retStack gs)
>   put (gs {retStack = s'})
>   return x

> adjustNodeCount :: Int -> Proc ()
> adjustNodeCount x = x `seq` modify (\gs -> gs {retStack = fst $ withTop (second (+x)) (retStack gs)})

> getNodeCount :: Proc Int
> getNodeCount = gets (snd . peek . retStack)

> shareRef :: RefValue -> RefValue
> shareRef (Ref t (_, s, a)) = Ref t (Shared, s, a)
> shareRef x                 = x

> invRef :: RefValue -> RefValue
> invRef = const $ CVRef VoidRef

> peekAtR :: RefRead -> Proc RefValue
> peekAtR (SCC c) = return (CVRef $ EnumTag c)
> peekAtR (R i c) = do
>   x <- withNodeFrom i (\(StNode nr t xs ys) -> let (r,xs') = ixMwE ("c of " ++ show (R i c)) (withRef invRef) (fromEnum c) xs in (r, StNode nr t xs' ys))
>   return $ asRef (show (R i c) ++ " on P") x
> peekAtR (CR i c) = do
>   x <- withNodeFrom i (\(StNode nr t xs ys) -> let (r,xs') = ixMwE ("c of " ++ show (R i c)) (withRef shareRef) (fromEnum c) xs in (r, StNode nr t xs' ys))
>   useClonedRef $ asRef (show (CR i c) ++ " on P") x
> peekAtR (RQ i)  =  do
>   rq <- gets refQueue
>   let (x, rq') = ixMwE (show (RQ i)) invRef i rq
>   modify (\gs -> gs {refQueue = rq'})
>   return x
> peekAtR (CRQ i) = do
>   rq <- gets refQueue
>   let (x, rq') = ixMwE (show (CRQ i)) shareRef i rq
>   modify (\gs -> gs {refQueue = rq'})
>   useClonedRef x
> peekAtR (NR i)  = fmap (fromMaybe (error (show (NR i) ++ " is Nothing"))) $ withNodeFrom i (\(StNode r t xs ys) -> (r, StNode Nothing t xs ys))
> peekAtR (CNR i) = do
>   x <- withNodeFrom i (\(StNode r t xs ys) -> let r' = fmap shareRef r in (r', StNode r' t xs ys))
>   let y = fromMaybe (error (show (NR i) ++ " is Nothing")) x
>   useClonedRef y

> peekAtW :: WordRead -> Proc PrimValue
> peekAtW (PA x)  = peekAtP x
> peekAtW (W i c) = fmap (asPrim (show (W i c) ++ " on R") . ixwE ("c of " ++ show (W i c)) (fromEnum c) . (\(StNode _ _ xs _) -> xs)) (readNodeFrom i)

> peekAtP :: PrimRead -> Proc PrimValue
> peekAtP (Im i)  = return (fromIntegral i)
> peekAtP (STTI)  = gets (fromIntegral . topTagIndex)
> peekAtP (PQ i)  = do
>   x <- gets (ixwE (show (PQ i)) i . primQueue)
>   x `seq` return x
> peekAtP (V i c) = do
>   x <- fmap (selPrimVal c . (\(StNode _ _ _ xs) -> xs)) (readNodeFrom i)
>   x `seq` return x

> selPrimVal :: QuadElem -> PrimVals -> PrimValue
> selPrimVal H (Q (Just a) _        _        _       ) = a
> selPrimVal I (Q _        (Just b) _        _       ) = b
> selPrimVal J (Q _        _        (Just c) _       ) = c
> selPrimVal K (Q _        _        _        (Just d)) = d

> peekAtC :: CondRead -> Proc (CondValue ())
> peekAtC (CTrue     ) = return (Nothing, True)
> peekAtC (CFalse    ) = return (Nothing, False)
> peekAtC (CSTI inv  ) = gets (fmap (xor inv) . topNodeCond) where xor = (/=)
> peekAtC (CNext inv ) = return (Just (), inv)
> peekAtC (CSaved inv) = gets (fmap (xor inv) . fromMaybe (error "no saved cond") . savedCond) where xor = (/=)
> peekAtC (CQ inv qi ) = gets (fmap (xor inv) . ixwE (show (CQ inv qi)) qi . condQueue) where xor = (/=)

> readNode :: NodeRead -> Proc NodeBody
> readNode = mapM (either (fmap RVal . peekAtR) (fmap PVal . peekAtW)) . catMaybes . toList

> readValues :: [PrimRead] -> Proc [PrimValue]
> readValues = mapM peekAtP

> readNodeFrom :: StackOffset -> Proc StackNode
> readNodeFrom i = do
>   x <- gets ((\(Stack xs) -> ixwE ("i of " ++ show i) i xs) . stack)
>   x `seq` return x

> withNodeFrom :: StackOffset -> (StackNode -> (a, StackNode)) -> Proc a
> withNodeFrom i f = do
>   Stack xs <- gets stack
>   let (n, ys) = ixMwE ("i of " ++ show i) (snd . f) i xs
>   modify (\gs -> gs {stack = Stack ys})
>   return (fst $ f $ n)

> ixwE :: String -> Int -> [a] -> a
> ixwE e _ []     = error ("index too large " ++ e)
> ixwE _ 0 (x:_ ) = x
> ixwE e n (_:xs) = ixwE e (n-1) xs

> ixMwE :: String -> (a -> a) -> Int -> [a] -> (a, [a])
> ixMwE e _ _ []     = error ("index too large " ++ e)
> ixMwE _ f 0 (x:xs) = (x, f x : xs)
> ixMwE e f n (x:xs) = let (y,ys) = ixMwE e f (n-1) xs in (y, x:ys)

> pushRef :: RefValue -> Proc ()
> pushRef x = do
>   gets (drop 15 . refQueue) >>= withHeap . decRefCounters . concatMap (\case {Ref _ r -> [r]; _ -> []})
>   modify (\gs -> gs {refQueue = take' 16 (x : refQueue gs)})

> pushPrim :: PrimValue -> Proc ()
> pushPrim x = modify (\gs -> gs {primQueue = take' 16 (x : primQueue gs)})

> pushCond :: CondValue () -> Proc ()
> pushCond x = modify (\gs -> gs {condQueue = take' 8 (x : map (combineCond x) (condQueue gs)),
>   savedCond = fmap (combineCond x) (savedCond gs), retStack = fmap (first $ second $ fmap (combineCond x)) (retStack gs), topNodeCond = combineCond x (topNodeCond gs)})

> combineCond :: CondValue () -> CondValue () -> CondValue ()
> combineCond (mf, x) (Just (), y) = (mf, xOr x y) where xOr = (/=)
> combineCond _       (Nothing, y) = (Nothing, y) 

> take' :: Int -> [a] -> [a]
> take' m xs = go m xs [] where
>   go 0 _      bs = reverse bs
>   go _ []     bs = reverse bs
>   go n (a:as) bs = go (n-1) as (a:bs)

> buildCodeMemS :: [Instruction] -> CodeMem
> buildCodeMemS = fromList . zip [0..]

> isLast :: Stack a -> Bool
> isLast (Stack xs) = null xs || null (tail xs)

> pop :: Stack a -> (Stack a, a)
> pop (Stack (x:xs)) = (Stack xs, x)

> peek :: Stack a -> a
> peek (Stack xs) = head xs

> push :: a -> Stack a -> (Stack a, ())
> push x (Stack ys) = (Stack (x:ys), ())

> popN :: StackPops -> Stack StackNode -> (Stack StackNode, [RefValue])
> popN ys (Stack zs) = (Stack zs', concat prs)
>   where (ps, prs)                     = partitionEithers $ zipWith (\p z -> case p of {Pop -> Right (stNodeRefs z); Keep -> Left z;}) (toList ys) zs
>         zs'                           = ps ++ drop 4 zs
>         stNodeRefs (StNode nr _ xs _) = maybe id (:) nr $ catMaybes $ map (\x -> case x of {RVal r -> Just r; _ -> Nothing}) xs

> withTop :: (a -> a) -> Stack a -> (Stack a, a)
> withTop f (Stack ~(x:xs)) = (Stack (f x : xs), f x)

> node2stnode :: Maybe RefValue -> Node -> StackNode
> node2stnode mr (Node t xs) = StNode mr t xs (extractPrimVals xs)

> extractPrimVals :: [NodeArg r PrimValue] -> PrimVals
> extractPrimVals xs = Q (leftPrim a e) (leftPrim b f) (leftPrim c g) (leftPrim d Nothing) where
>   (a:b:c:d:e:f:g:_) = map Just xs ++ repeat Nothing

> leftPrim :: Maybe (NodeArg r PrimValue) -> Maybe (NodeArg r PrimValue) -> Maybe PrimValue
> leftPrim (Just (PVal x)) _               = Just x
> leftPrim (Just _       ) (Just (PVal y)) = Just y
> leftPrim _               _               = Nothing

> withHeap :: HeapProc a -> Proc a
> withHeap m = do
>   hs <- gets heap
>   (x, hs') <- liftIO $ runStateT m hs
>   modify (\ps -> ps {heap = hs'})
>   return x

> retrieveNode :: HeapRef -> HeapProc (Maybe RefValue, Node)
> retrieveNode r@(_,_,i) = do
>   hs <- get
>   if (i >= (heapTop hs - allocHeapSize))
>     then do
>       mn <- liftIO $ readArray (nursery hs) (i `mod` allocHeapSize)
>       rc <- liftIO $ readArray (refCounters hs) (i `mod` allocHeapSize)
>       case mn of
>         Nothing -> error ("reading invalid heap ref: " ++ show r)
>         Just (Node t xs)  -> case rc of
>           (One, s) -> do
>             _ <- deAllocNode True i
>             return (Nothing, Node t (if (s /= SharedRead || isUpdFTag (plainTag t)) then xs else (map (withRef shareRef) xs)))
>           _ | isUpdFTag $ plainTag t -> return (Just (Ref (node2PtrTag t) r), Node t xs)  -- overwrite with blackhole here ??  
>           _ -> updateRefCount (second (const SharedRead)) i >> sharedReadResult r t xs
>     else do
>       mx <- liftIO $ tryUseTag (cTags hs) i
>       case mx of
>         Just x -> do
>           mn <- liftIO $ readArray (cData hs) x
>           case mn of
>             Nothing -> error ("reading invalid heap ref: " ++ show r)
>             Just (Node t xs)  -> case r of
>               (Unique,_,i) -> do
>                 _ <- deAllocNode True i
>                 return (Nothing, Node t xs)
>               (_     ,_,_) | isUpdFTag $ plainTag t -> return (Just (Ref (node2PtrTag t) r), Node t xs)  -- overwrite with blackhole here ??
>               (_     ,_,_) -> sharedReadResult r t xs
>         Nothing  -> case Data.IntMap.lookup i (heapMem hs) of
>           Nothing          -> error ("reading invalid heap ref: " ++ show r)
>           Just (Node t xs) -> case r of
>             (Unique,_,i) -> do
>               _ <- deAllocNode True i
>               return (Nothing, Node t xs)
>             (_     ,_,_) | isUpdFTag $ plainTag t -> return (Just (Ref (node2PtrTag t) r), Node t xs)  -- overwrite with blackhole here ??
>             (_     ,_,i) -> do
>               moveIntoCache i (Node t xs)
>               modify (\hs -> hs {heapMem = Data.IntMap.delete i (heapMem hs)})
>               sharedReadResult r t xs

> sharedReadResult :: HeapRef -> NodeTag -> NodeBody -> HeapProc (Maybe RefValue, Node)
> sharedReadResult r t xs = do
>   let ys = map (withRef shareRef) xs
>   incRefCounters (bodyRefAddrs ys)
>   return (Just (Ref (node2PtrTag t) r), Node t ys)

> reserveHeapAddr :: HeapProc HeapAddr
> reserveHeapAddr = do
>   hs <- get
>   let fls = freeLines hs
>   case (fls .&. compactAllocMask) of
>     0 -> do
>       let x = heapTop hs
>       freeAllocHeap (x - allocHeapSize)
>       modify (\hs -> hs {heapTop = heapTop hs + 1, freeLines = fls `shiftL` 1})
>       return x
>     mfls -> do
>       let oi = foldr1 (\i y -> if testBit mfls i then i else y) [compactAllocRange-1, compactAllocRange-2..]
>       let x = heapTop hs - (oi + 1)
>       pn <- liftIO $ readArray (nursery hs) (x `mod` allocHeapSize)
>       when (isJust pn) $ error ("incorrect reuse of @" ++ show x ++ " with " ++ show fls)
>       modify (\hs -> hs {freeLines = clearBit fls oi})
>       return x
 
> allocNode :: Node -> HeapProc RefValue
> allocNode n@(Node t xs) = seq (forceNB xs) $ do
>   ahx <- reserveHeapAddr
>   hs <- get
>   liftIO $ writeArray (nursery hs    ) (ahx `mod` allocHeapSize) (Just n)
>   liftIO $ writeArray (refCounters hs) (ahx `mod` allocHeapSize) (case nodeKind t of {Dynamic -> One; Static -> Many}, UnTouched)
>   let ns = nodeSize__ xs
>   ns `seq` return (Ref (node2PtrTag t) (case nodeKind t of {Dynamic -> Unique; Static -> GlobalRef}, ns, ahx))

> allocNodeAt :: HeapAddr -> Node -> HeapProc ()
> allocNodeAt ahx n@(Node t xs) = seq (forceNB xs) $ do
>   hs <- get
>   liftIO $ writeArray (nursery hs    ) (ahx `mod` allocHeapSize) (Just n)
>   liftIO $ writeArray (refCounters hs) (ahx `mod` allocHeapSize) (case nodeKind t of {Dynamic -> One; Static -> Many}, UnTouched)

> freeAllocHeap :: HeapAddr -> HeapProc ()
> freeAllocHeap i = do
>   hs <- get
>   pn <- liftIO $ readArray (nursery hs) (i `mod` allocHeapSize)
>   liftIO $ writeArray (nursery hs) (i `mod` allocHeapSize) Nothing
>   (rc, _) <- liftIO $ readArray (refCounters hs) (i `mod` allocHeapSize)
>   case pn of
>     Just n -> do
>        when (rc == Zero) $ error ("should have been deallocated"  ++ show n)
>        moveIntoCache i n
>     _      -> return ()

> updateNode :: HeapRef -> Node -> HeapProc ()
> updateNode (Unique,_,i) _  = error ("updating unique ref @" ++ show i)
> updateNode (_     ,_,i) un = do
>   hs <- get
>   if (i >= (heapTop hs - allocHeapSize))
>     then do
>        mn <- liftIO $ readArray (nursery hs) (i `mod` allocHeapSize)
>        case mn of
>          Nothing -> error "updating invalid ref"
>          Just _  -> do  -- maybe check for blackhole
>            liftIO $ writeArray (nursery hs) (i `mod` allocHeapSize) (Just un)
>            updateRefCount (second (const UnTouched)) i
>     else do
>       mx <- liftIO $ tryUseTag (cTags hs) i
>       case mx of
>         Just x -> do
>           mn <- liftIO $ readArray (cData hs) x
>           case mn of
>             Nothing -> error "updating invalid ref"
>             Just _  -> liftIO $ writeArray (cData hs) x (Just un)   -- maybe check for blackhole
>         Nothing -> do
>           let h' = alter (updateNH un) i (heapMem hs)
>           put (hs {heapMem = h'})

> updateNH :: Node -> Maybe Node -> Maybe Node
> updateNH _ Nothing  = error "updating invalid ref"
> updateNH n (Just _) = Just n   -- maybe check for blackhole

> updateNodeWithInd :: HeapRef -> RefValue -> HeapProc ()
> updateNodeWithInd (Unique,_,i) _ = error ("updating unique ref @" ++ show i)
> updateNodeWithInd (_     ,_,i) v = do
>   let indN = Node (NodeTag Dynamic 1 singleRefK Ind) [RVal v]
>   hs <- get
>   if (i >= (heapTop hs - allocHeapSize))
>     then do
>        mn <- liftIO $ readArray (nursery hs) (i `mod` allocHeapSize)
>        case mn of
>          Nothing -> error "updating invalid ref"
>          Just _  -> do  -- maybe check for blackhole
>            liftIO $ writeArray (nursery hs) (i `mod` allocHeapSize) (Just indN)
>            updateRefCount (second (const UnTouched)) i
>     else do
>       mx <- liftIO $ tryUseTag (cTags hs) i
>       case mx of
>         Just x -> do
>           mn <- liftIO $ readArray (cData hs) x
>           case mn of
>             Nothing -> error "updating invalid ref"
>             Just _  -> liftIO $ writeArray (cData hs) x (Just indN)   -- maybe check for blackhole
>         Nothing -> do
>           let h' = alter (updateNH indN) i (heapMem hs)
>           put (hs {heapMem = h'})

> useClonedRef :: RefValue -> Proc RefValue
> useClonedRef x = withHeap (incRefCounters $ case x of {Ref _ r -> [r]; _ -> []}) >> return (shareRef x)

> incRefCounters :: [HeapRef] -> HeapProc ()
> incRefCounters = mapM_ iRC where
>   iRC (_, _, i) = get >>= \hs -> when (i >= (heapTop hs - allocHeapSize)) $ updateRefCount (first incRefCount) i

> decRefCounterM :: Maybe RefValue -> Proc ()
> decRefCounterM = maybe (return ()) (\case {Ref _ r -> withHeap $ decRefCounters [r]; _ -> return()}) 

> decRefCounters :: [HeapRef] -> HeapProc ()
> decRefCounters []                  = return ()
> decRefCounters ((Unique, _, i):xs) = deAllocNode False i >>= decRefCounters . (++ xs)
> decRefCounters ((_     , _, i):xs) = decRefCounter i >> decRefCounters xs

> decRefCsNoUniques :: [HeapRef] -> HeapProc ()
> decRefCsNoUniques = mapM_ dRCNU where
>   dRCNU (_, _, i) = decRefCounter i

> decRefCounter :: HeapAddr -> HeapProc ()
> decRefCounter x | x < 0 = return ()
> decRefCounter x  = do
>   hs <- get
>   if (x >= (heapTop hs - allocHeapSize))
>     then do
>        let i = (x `mod` allocHeapSize)
>        (rc,s) <- liftIO $ readArray (refCounters hs) i
>        case rc of
>          One  -> do
>            xs <- deAllocNode False x
>            case s of
>              SharedRead -> decRefCsNoUniques xs
>              _          -> decRefCounters  xs
>          Zero -> liftIO (readArray (nursery hs) i) >>= error . ("gcing dead :" ++) . (++ show x) . show
>          _    -> do
>            liftIO $ writeArray (refCounters hs) i (decRefCount rc, s)
>     else (return ())

> updateRefCount :: ((RefCounter,ReadState) -> (RefCounter,ReadState)) -> HeapAddr -> HeapProc ()
> updateRefCount f x = do
>   rca <- gets refCounters
>   liftIO (readArray rca i >>= writeArray rca i . f)
>   where i = x `mod` allocHeapSize

> deAllocNode :: Bool -> HeapAddr -> HeapProc [HeapRef]
> deAllocNode direct x = do
>  hs <- get
>  if (x >= (heapTop hs - allocHeapSize))
>    then do
>      let i = x `mod` allocHeapSize
>      Just (Node _ ys) <- liftIO $ readArray (nursery hs) i
>      liftIO $ writeArray (nursery hs) i Nothing
>      let age = heapTop hs - x
>      put (hs {freeLines = (if (age <= compactAllocRange) then (flip setBit (age-1)) else id) (freeLines hs)})   -- TODO dead double size node, after updating with too big nodes in alloc heap is fixed
>      liftIO $ writeArray (refCounters hs) i (Zero, UnTouched)
>      return (bodyRefAddrs ys)
>    else do
>      mi <- liftIO $ tryDeAllocTag (cTags hs) x
>      case mi of
>        Just i -> do
>          Just (Node _ ys) <- liftIO $ readArray (cData hs) i
>          liftIO $ writeArray (cData hs) i Nothing
>          return (bodyRefAddrs ys)
>        Nothing | direct -> do
>          let (Just (Node _ ys), h') = updateLookupWithKey (const $ const Nothing) x (heapMem hs)
>          put (hs {heapMem = h'})
>          return (bodyRefAddrs ys)
>        Nothing -> return []

> tryUseTag :: IOArray Int CacheTag -> HeapAddr -> IO (Maybe Int)
> tryUseTag tags x = fmap fst $ withCacheTags (Right x) id setLRU4 tags x

> tryDeAllocTag :: IOArray Int CacheTag -> HeapAddr -> IO (Maybe Int)
> tryDeAllocTag tags x = fmap fst $ withCacheTags (Right x) (const $ Nothing) dropLRU4 tags x

> getReplaceEntry :: IOArray Int CacheTag -> HeapAddr -> IO (Int, Maybe HeapAddr) 
> getReplaceEntry tags x = fmap (first fromJust) $ withCacheTags (Left oldLRU4) (const $ Just x) setLRU4 tags x

> withCacheTags :: Either (LRU4 -> Int) HeapAddr -> (Maybe HeapAddr -> Maybe HeapAddr) -> (Int -> LRU4 -> LRU4) -> IOArray Int CacheTag -> HeapAddr -> IO (Maybe Int, Maybe HeapAddr)
> withCacheTags lf fmt flru tags x = do
>   ct <- readArray tags (x `mod` cacheIxSize)
>   case lookupTag lf ct of
>     Nothing -> return (Nothing, Nothing)
>     Just ti -> do
>       let (nt, mtx) = modifyTag fmt flru ct ti
>       writeArray tags (x `mod` cacheIxSize) nt
>       return (Just ((ti*cacheIxSize) + (x `mod` cacheIxSize)), mtx)

> lookupTag :: Either (LRU4 -> Int) HeapAddr -> CacheTag -> Maybe Int
> lookupTag (Left fu) (FourWay ta tb tc td lru) = elemIndex Nothing  [ta,tb,tc,td] `mplus` (Just $ fu lru)
> lookupTag (Right x) (FourWay ta tb tc td lru) = elemIndex (Just x) [ta,tb,tc,td]

> modifyTag :: (Maybe HeapAddr -> Maybe HeapAddr) -> (Int -> LRU4 -> LRU4) -> CacheTag -> Int -> (CacheTag, Maybe HeapAddr)
> modifyTag ft fu (FourWay ta tb tc td lru) 0 = (FourWay (ft ta) tb tc td (fu 0 lru), ta)
> modifyTag ft fu (FourWay ta tb tc td lru) 1 = (FourWay ta (ft tb) tc td (fu 1 lru), tb)
> modifyTag ft fu (FourWay ta tb tc td lru) 2 = (FourWay ta tb (ft tc) td (fu 2 lru), tc)
> modifyTag ft fu (FourWay ta tb tc td lru) 3 = (FourWay ta tb tc (ft td) (fu 3 lru), td)

> moveIntoCache :: HeapAddr -> Node -> HeapProc ()
> moveIntoCache i n = do
>   hs <- get
>   (x, ma) <- liftIO $ getReplaceEntry (cTags hs) i
>   case ma of
>     Nothing -> liftIO $ writeArray (cData hs) x (Just n)
>     Just a  -> do
>       Just on <- liftIO $ readArray (cData hs) x
>       liftIO $ writeArray (cData hs) x (Just n)
>       put (hs {heapMem = insert a on (heapMem hs)})

> forceNB :: NodeBody -> ()
> forceNB [] = ()
> forceNB (RVal r : xs) = seq r (forceNB xs)
> forceNB (PVal w : xs) = seq w (forceNB xs)

> withRef :: (a -> b) -> NodeArg a p -> NodeArg b p
> withRef f (RVal x) = RVal $ f x
> withRef _ (PVal x) = PVal x

> bodyRefAddrs :: NodeBody -> [HeapRef]
> bodyRefAddrs = catMaybes . map (\x -> case x of {RVal (Ref _ r) -> Just r; _ -> Nothing})

> -- bodyKinds_ :: [NodeArg r p] -> KindMask
> -- bodyKinds_ xs = FB (T a b c) (Q d e f g) where
> --  (a:b:c:d:e:f:g:_)  = map (\x -> case x of {RVal _ -> RefK; PVal _ -> PrimK}) xs ++ repeat PrimK

> asRef :: String -> NodeArg r p -> r
> asRef _ (RVal r) = r
> asRef e (PVal _) = error e

> asPrim :: String -> NodeArg r p -> p
> asPrim e (PVal p) = p
> asPrim e (RVal _) = error e
