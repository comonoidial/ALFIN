> {-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections, DeriveFunctor, BangPatterns, LambdaCase, Rank2Types #-}
> module Simulate.DetailEval (runProc, initState, heap) where

> import Simulate.ProcDefs
> import Simulate.DEvalTypes
> import Simulate.PipeLineMonad

> import Control.Monad
> import Control.Monad.State.Class (modify')
> import Data.Array.IArray (Array, (!))
> import Data.Array.IO
> import qualified Data.Array.IArray as IArray
> import Data.Traversable (traverse)
> import Control.Applicative 
> import Control.Arrow (first, second)
> import Data.Monoid
> import Data.Maybe
> import Data.Either
> import qualified Data.IntMap as IM (insert, alter, delete, empty, lookup)
> import qualified Data.Map.Strict as M (empty, alter)
> import Control.Applicative ((<$>), (<*>))
> import qualified Data.Foldable (mapM_, any, maximum)
> import Data.Foldable (foldMap, traverse_)
> import Data.Int (Int64)
> import Data.Word (Word8, Word16, Word32, Word64)
> import Data.Bits (shiftL, (.&.), testBit, setBit, clearBit)
> import Debug.Trace
> import Control.Lens hiding ((%=), (.=), (+=))

> type Proc a = PLST ProcState a

Run a program step by step until the return stack is empty and the top of the stack has been evaluated.

> runProc :: ProcState -> IO (String, ProcState)
> runProc s = do
>   let gs = (stats.steps +~ 1) s
> --  putStr ("step " ++ show (view (stats.steps) s))
> --  showProcState gs >>= putStrLn
>   case (gs^.instrCtrl.nextI, gs^.ctrlStack.callStack.top.ecCount, gs^.ctrlStack.callStack.top.callCont) of
>     (Continue   , 0, ThreadFinish) -> trace (showStatSummary gs) (showStackResult gs)
>     (Unwinding _, 0, ThreadFinish) -> error "unhandled exception"
>     (instr      , _, _           ) -> runFullPipe gs (runBackgroundTasks >> nextCycle >> get_next_ip >>= runStep instr) >>= runProc -- nextCycle required after runBackgroundTasks to commit changes

> showStatSummary :: ProcState -> String
> showStatSummary gs = "\ntotal steps: " ++ show (gs^.stats.steps) ++ " +" ++ show (gs^.stats.multiSteps) ++ "   iRDs: " ++ show (gs^.code.instrRds) ++ "  ccHits: "  ++ show (gs^.code.ccHits) ++ "  ccMiss: "  ++ show (gs^.code.ccMiss) ++ " goodPreds: " ++ show (gs^.code.goodPreds) ++ " good2Preds: " ++ show (gs^.code.good2Preds) ++ "  noPreds: " ++ show ((gs^.code.ccHits) - (gs^.code.good2Preds))
>   --                   ++ "\nrefLoads: "  ++ show (gs^.stats.refLoads) ++ " knownPTloads: " ++ show (gs^.stats.knownPTrefLoads) ++ " funrefLoads: " ++ show (gs^.stats.funrefLoads)

> runFullPipe :: ProcState -> Proc a -> IO ProcState
> runFullPipe s m  = do
>  sr <- evalPipeStage m s
>  case sr of
>    Done x s'        -> return s'
>    NextStage k s'   -> runFullPipe s' k
>    Blocked          -> runFullPipe s (countExtraCycle >> runBackgroundTasks >> nextCycle >> m) -- nextCycle is crucial here to make sure state changes in runBackgroundTasks are committed even if m blocks again!
>    FixupNext f s' k -> runFullPipe s' f >>= \s'' -> runFullPipe s'' (countExtraCycle >> runBackgroundTasks >> k)

Run a single step based on the sequencer state.

> traceDebugI :: String -> a -> a
> traceDebugI m x = {- trace m -} x

> runStep :: NextInstr -> CodeAddr -> Proc ()
> runStep (NextIP        ) nip =                                        runInstrAt nip
> runStep (BranchTo t    ) _   =                                        runInstrAt t
> runStep (NextInstr x   ) _   = traceDebugI ("\n-----> " ++ show x   ) runInstr x
> runStep (DecideBr ti eo) _   = traceDebugI ("\n-===-> decide branch") (preFetchInstrAt t >> preFetchInstrAt e >> gets (instrCtrl.branchCond.to (asBool "need bool to branch")) >>= \cond -> instrCtrl.nextI .= BranchTo (if cond then t else e)) where {t = ti; e = relJump ti eo}
> runStep (EvalLoad e    ) _   = traceDebugI ("\n-===-> eval load"    ) (finishLoad >> evalAndExecStages (Right e    ) XLoadRes SPushLoad Nothing)
> runStep (Continue      ) _   = traceDebugI ("\n-===-> continue"     ) (              evalAndExecStages (Right False) XUseTop  SKeepTop  Nothing)
> runStep (EvalJump ec   ) _   = traceDebugI ("\n-===-> eval jump"    ) (runFunEvalCombinator ec)
> runStep (Returning ps  ) _   = traceDebugI ("\n-===-> returning"    ) (runDecInstr (ApplyNop, (DropRQ, ps), defRI) Nothing)
> runStep (Unwinding ps  ) _   = traceDebugI ("\n-===-> unwinding"    ) (runDecInstr (ApplyNop, (DropRQ, ps), defRI) Nothing)
> runStep (DummyNext     ) _   = error "dummy NextInstr"

> initState :: CodeMem -> [HeapNode] -> IO ProcState
> initState c is = do
>   rc <- newArray (0, allocHeapMax) Zero
>   n  <- newArray (0, (allocHeapSize*2) - 1) Bad
>   rs <- newArray (0, (allocHeapSize*2) - 1) FreeLine
>   ct <- newArray (0, cacheIxSize       - 1) initCTag
>   cd <- newArray (0, cacheIxSize*nWays - 1) Bad
>   ci <- newArray (0, cacheIxSize*nWays - 1) FreeLine
>   lb <- newArray (IxL 0, IxL 3 ) Nothing
>   sr <- newArray (IxS 0, IxS 7 ) Bad
>   ps <- newArray (IxS 0, IxS 7 ) Bad
>   let rm = IArray.listArray (0, 7) (replicate 8 StVoid)
>   mr <- newArray (IxS 0, IxS 7 ) Bad
>   rq <- newArray (IxQ 0, IxQ 31) (CVRef VoidRef)
>   pq <- newArray (IxQ 0, IxQ 31) 0
>   cq <- newArray (IxQ 0, IxQ 15) (Nothing, False)
>   cc <- newArray (0, ccSize - 1) (WayB, Nothing, Nothing)
>   cl <- newArray (H,K) Nothing
>   cp <- newArray (0, (ccSize * ccLineWidth) - 1) ((WeakP, (WayB,0)), (WeakP, (WayB,0)))
>   c2 <- newArray (0, (ccSize * ccLineWidth) - 1) ((WeakP, (WayB,0)), (WeakP, (WayB,0)))
>   return (ProcState {
>     _heap = HeapState {_ahBounds = (0,0), _nursery = n, _ahInfo = rs, _freeLines = 0, _nextFreeAddress = Nothing, _cTags = ct, _cData = cd, _cInfo = ci, _loadDeallocs = 0, {- _dupDeallocs = 0, -} _loadDelays = 0, _allocProfile = M.empty},
>     _ext = ExtState {_heapMem = IM.empty, _inputFifo = foldr enFifo emptyFifo (reverse is), _outputFifo = emptyFifo},
>     _loader = LoadState {_loadReq = Nothing, _loadBuffer = lb, _lastLoadIx = LB 3, _loadResult = Nothing, _rewriteLoadResult = Nothing, _cacheReq = Nothing},
>     _rcUnit = RCState {_stackForPop = emptyStackMask, _stackDropRef = emptyStackMask, _rqToPop = IxQ 0, _rqLastIx = IxQ 0, _rcUpdates = [], _dropRefs = emptyFifo, _dropAHRefs = emptyFifo, _counters = rc, _dropLoadRes = Nothing},
>     _renamer = RenState {_loadBase = LB 0, _stackMapping = rm, _stackForFree = foldr enFifo emptyFifo [IxS 0 .. IxS 7], _hasSTop = False, _refBase = QB 0, _primBase = QB 0, _condBase = QB 0},
>     _ctrlStack = CtrlStack {_topNodeCond = (Nothing, False), _metaSTop = emptyMetaSTop, _metaSRegs = mr, _savedCond = Bad, _callStack = push (CallFrame 0 ThreadFinish Bad 0) emptyStack, _metaContStack = emptyStack, _extraPushCont = 0},
>     _dataPath = DataPath {_stackTop = Bad, _stackRegs = sr, _stackMem = emptyStack, _refQueue = rq, _contStack = emptyStack, _rewriteBuffer = Nothing},
>     _primSide = PrimSide {_primSTop = emptyPrimVals, _primStack = ps, _primQueue = pq, _condQueue = cq, _primContStack = emptyStack},
>     _code = CodeState {_codeMem = c, _codeCache = cc, _cLineTags = initCTag, _cLineBuf = cl, _instrRds = 0, _ccHits = 0, _ccMiss = 0, _prevLine = ((WayB, 0), 0), _clinePred = cp, _goodPreds = 0, _prev2Line = ((WayB, 0), 0), _cline2Pred = c2, _good2Preds = 0},
>     _instrCtrl = InstrCtrl {_ip = CodeAddr (-1), _nextI = NextIP, _branchCond = (Nothing,False)}, _stats = Stats {_steps = 0, _multiSteps = 0, _refLoads = 0, _knownPTrefLoads = 0, _funrefLoads = 0}})

> countExtraCycle :: Proc ()
> countExtraCycle = stats.multiSteps += 1

Read and run an instruction from code memory.

> runInstrAt :: CodeAddr -> Proc ()
> runInstrAt ci = do
>   instrCtrl.ip .= ci
>   ix <- readInstrAt ci
>   runInstr $ traceDebugI ("\n@" ++ show ci ++ " --> " ++ show ix) ix

> readInstrAt :: CodeAddr -> Proc Instruction
> readInstrAt ci = do
>   code.instrRds += 1
>   mi <- readInstrBuff ci
>   case mi of
>     Just x -> return x
>     Nothing -> do
>       readInstrCache ci
>       fmap fromJust $ readInstrBuff ci

> preFetchInstrAt :: CodeAddr -> Proc ()
> preFetchInstrAt i = do
>   mi <- readInstrBuff i
>   when (isNothing mi) $ readInstrCache i

> matchesTag :: Word32 -> Maybe CodeCacheLine -> Bool
> matchesTag xt (Just (ta, _)) = xt == ta
> matchesTag _  _              = False

> readInstrBuff :: CodeAddr -> Proc (Maybe Instruction)
> readInstrBuff (CodeAddr i) = do
>   lt <- gets (code.cLineTags)
>   case lookupTag (Just (i `div` ccLineWidth)) lt of
>     Nothing -> return Nothing
>     Just wx -> do
>       Just il <- peeking (code.cLineBuf) wx
>       ix <- peekArray (const il) (i `mod` ccLineWidth)
>       code.cLineTags.tagLRU %= setLRU4 wx
>       return $ Just ix

> pushLineBuff :: CodeCacheLine -> Proc ()
> pushLineBuff (ci, cl) = do
>   lt <- gets (code.cLineTags)
>   let Just x = lookupTag Nothing lt
>   code.cLineTags %= fst . modifyTag (const $ Just ci) setLRU4 x
>   poking (code.cLineBuf) x (Just cl)

> readInstrCache :: CodeAddr -> Proc ()
> readInstrCache (CodeAddr i) = do
>   let xl = i `div` ccLineWidth
>   mx <- peeking (code.codeCache) (xl `mod` ccSize)
>   case mx of
>    (_    , ma@(Just (ta, as)), mb                ) | ta == xl -> do
>      poking (code.codeCache) (xl `mod` ccSize) (WayA, ma, mb)
>      pushLineBuff (xl, as)
>      code.ccHits += 1
>      updatePreds ((WayA, xl `mod` ccSize), i `mod` ccLineWidth)
>    (_    , ma                , mb@(Just (tb, bs))) | tb == xl -> do
>      poking (code.codeCache) (xl `mod` ccSize) (WayB, ma, mb)
>      pushLineBuff (xl, bs)
>      code.ccHits += 1
>      updatePreds ((WayB, xl `mod` ccSize), i `mod` ccLineWidth)
>    (WayB, _                 , mb                ) -> do
>      rs <- readCodeMemLine (xl * ccLineWidth)
>      poking (code.codeCache) (xl `mod` ccSize) (WayA, Just (xl, rs), mb)
>      pushLineBuff (xl, rs)
>      code.ccMiss += 1
>      updatePreds ((WayA, xl `mod` ccSize), i `mod` ccLineWidth)
>    (WayA, ma                , _                 ) -> do
>      rs <- readCodeMemLine (xl * ccLineWidth)
>      poking (code.codeCache) (xl `mod` ccSize) (WayB, ma, Just (xl, rs))
>      pushLineBuff (xl, rs)
>      code.ccMiss += 1
>      updatePreds ((WayB, xl `mod` ccSize), i `mod` ccLineWidth)

> readCodeMemLine :: Word32 -> Proc (IOArray Word32 Instruction)
> readCodeMemLine x = do
>   cm <- gets (code.codeMem )
>   listArray (0,ccLineWidth-1) $ map (fromJust . flip IM.lookup cm . fromIntegral) [x..(x+ccLineWidth-1)]

> updatePreds :: ((MRU2, Word32), Word32) -> Proc ()
> updatePreds np = do
>   update2Preds np
>   ((lx, ix), ii) <- gets (code.prevLine)
>   let ax = (ix * ccLineWidth) + ii
>   (ppa, ppb) <- peeking (code.clinePred) ax
>   code.prevLine .= np
>   case lx of
>     WayA -> do
>       poking (code.clinePred) ax (adjustPred (fst np) ppa, ppb)
>       code.goodPreds += (if fst np == snd ppa then 1 else 0)
>     WayB -> do
>       poking (code.clinePred) ax (ppa, adjustPred (fst np) ppb)
>       code.goodPreds += (if fst np == snd ppb then 1 else 0)

> update2Preds :: ((MRU2, Word32), Word32) -> Proc ()
> update2Preds np = do
>   n2p <- gets (code.prevLine)
>   ((lx, ix), ii) <- gets (code.prev2Line)
>   let ax = (ix * ccLineWidth) + ii
>   (ppa, ppb) <- peeking (code.cline2Pred) ax
>   code.prev2Line .= n2p
>   case lx of
>     WayA -> do
>       poking (code.cline2Pred) ax (adjustPred (fst np) ppa, ppb)
>       code.good2Preds += (if fst np == snd ppa then 1 else 0)
>     WayB -> do
>       poking (code.cline2Pred) ax (ppa, adjustPred (fst np) ppb)
>       code.good2Preds += (if fst np == snd ppb then 1 else 0)

> adjustPred :: (MRU2, Word32) -> ICPred -> ICPred
> adjustPred ncp (ps     , ocp) | ncp == ocp = (StrongP, ocp)
> adjustPred _   (StrongP, ocp)              = (WeakP  , ocp)
> adjustPred ncp (WeakP  , _  )              = (WeakP  , ncp)

> data InstrFlowCtrl
>   = INop
>   | INopClrRs         -- distinguishing ClearRefs instruction
>   | IRoutine FunAddr
>   | IEval Bool        -- Bool is already evaluated
>   | IContinue         -- continue with the call stack, mostly return instructions
>   | IBranch CodeAddr
>   | ICBr CodeAddr RelCodeAddr
>   | IThrow

> data CallFrameCtrl
>   = CFNop
>   | CFPushCall Continuation
>   | CFEnterApply
>   | CFContinue
>   | CFPushEval
>   deriving Show

> data FetchCtrl
>   = FNop
>   | FEvalRef
>   | FUsePre
>   | FReceive Channel
>   | FRWLoad EvalFun
>   | FApplyLoad          -- used for prefetch 'applications' and exception handler loads
>   | FNodeArg NodeElem
>   | FNextArg NodeElem   -- as above but for next load argument prefetching

> type DecPrims q p c = (DecPrimInstr q p c, DecPrimInstr q p c)

> data DecPrimInstr q p c 
>   = DecPrimNop
>   | DecPrimOp  q PrimOp          p p c
>   | DecCmpOp   q (CmpOp,LogicOp) p p c
>   | DecPrimC   q PrimValue

> type WriteCtrl = (StoreCtrl, Checked QueueIndex)

> data StoreCtrl
>   = WNop
>   | WStore        NodeTag
>   | WStoreBox     ConAlt
>   | WStoreCond    ConAlt
>   | WStoreFE      NodeTag
>   | WPushRef      RefValue
>   | WSelPush
>   | WSend Channel NodeTag
>   | WFixHole      FunAddr
>   | WSaveNode     NodeTag    -- store without pushing ref on queue
>   | WSaveBox      NodeTag
>   | WUpdCVal      NodeTag
>   | WUpdRef
>   | WUpdBox       NodeTag
>   | WUpdNode      NodeTag    -- update with either a node or indirection to a new node

> data BuildCtrl
>   = BNop
>   | BNode        NodeTag
>   | BTValue      NodeTag
>   | BCall        NodeTag
>   | BCallFix     NodeTag
>   | BRaw   Arity NodeTag         -- Arity is here the number of elements on the primitive side
>   | BPrim        NodeTag
>   | BConst Int64 NodeTag

> data NodeSelCtrl
>   = XNop
>   | XBuild
>   | XUseTop
>   | XLoadRes
>   deriving Eq

> data DemuxUpdateCtrl
>   = NoUpdate
>   | UpdateCNodeVal
>   | UpdateWithRef
>   | UpdateWithN PtrTag
>   | DemuxLoadFun
>   | DemuxLoadGen  -- non updatable functions
>   | DemuxLoadInd

> data ApplyCtrl
>   = ApplyNop
>   | ApplyToStore        -- for store rewrites
>   | PushApply ContMeta
>   | PushUpdate
>   | PushFixRef
>   | MergeApply Word8
>   | MergePrimAp PrimOp
>   | ApplyPrim PrimOp
>   | NodeApplyLast
>   | NodeApplyNext
>   | UseApplyLast
>   | UseApplyNext
>   | UseCatch
>   | StartPreFetch
>   | UseUpdate
>   | DropSelect
>   | DropECont ContMeta
>   | DropNextAp
>   deriving Show

> data TopRefFix = DropNRef | MergeRef | DropBoth
> data TopBodyFix = KeepBody | DropBody

> data NodeStackCtrl
>   = SNop
>   | SPopTop
>   | SWaitLoad
>   | SPushLoad
>   | SKeepTop
>   | SPushNode
>   | SPushCond   -- push raw conditional node
>   | SFixTopRef

> data ReadInstr = ReadInstr {rrd :: Either RefRead RefValue, crd :: Checked CondRead, nrd :: BodyRead, vrd :: Quad (Maybe WordRead), ecrd :: ((RefRead, RefRead), Maybe PrimRead)}
> type BodyRead = FB (Maybe (Either RefRead WordRead))

> data ReadCtrl = ReadCtrl {rri :: Either RefUseIndex RefValue, cri :: Checked CondIndex, nri :: NodeIndex, vri :: Quad (Maybe WordIndex),
>   ecri :: (RefUseIndex, RefUseIndex), expi :: Maybe PrimIndex, nru :: Quad (Maybe (StackResult, StackPos)), nrts :: Quad (Maybe StackPos)}

> type RefUseIndex = (RefUse,RefIndex)
> type NodeIndex = FB (Maybe (Either RefUseIndex WordIndex))
> data RefIndex  = RSI StackIndex NodeElem | RSTI NodeElem | NRI StackIndex | TNR | RQI QueueIndex | ICC ConAlt | IVoid
> data PrimIndex = VSI StackIndex QuadElem | VSTI QuadElem | PQI QueueIndex | IC Int | TTI deriving Show
> data LocPIndex = XI | LQI QueueIndex | SIC Int deriving Show
> data WordIndex = WSI StackIndex NodeElem | WSTI NodeElem | PAI PrimIndex deriving Show
> data CondIndex = CQI Bool QueueIndex | IBC Bool | FCQV Bool QueueIndex | TNC Bool | CSC Bool deriving Show

> readValuesRCs :: (RCMod -> RCMod) -> NodeTag -> ReadBody -> (FB (Maybe RCRef), FixedBody)
> readValuesRCs rmf t xs = (mapBodyWithKind Nothing readValRCs t xs, fmap (fmap snd) xs) where
>   readValRCs RefK (rcm, ~(RVal r)) = Just (rmf rcm, r)
>   readValRCs _    _                = Nothing

> defRI :: ReadInstr
> defRI = ReadInstr (Right (CVRef VoidRef)) Bad emptyBody emptyQuad ((RVoid, RVoid), Nothing)

> defaultRC :: ReadCtrl
> defaultRC = ReadCtrl (Right (CVRef VoidRef)) Bad emptyBody emptyQuad ((TakeRef,IVoid), (TakeRef,IVoid)) Nothing emptyQuad emptyQuad

> noPrims :: DecPrims q p c
> noPrims = (DecPrimNop, DecPrimNop)

> decInstr :: Instruction -> CodeAddr -> (InstrFlowCtrl, CallFrameCtrl, BuildCtrl, NodeSelCtrl, NodeStackCtrl, StoreCtrl, FetchCtrl, DecPrims () PrimRead CondRead)
> decInstr (Call    sc r _ nl _) nip = decRoutine r (ReturnTo    sc nl nip)
> decInstr (Case    sc r _ xs _) nip = decRoutine r (IntoCase    sc xs nip)
> decInstr (BigCase sc r _ om _) nip = decRoutine r (IntoBigCase sc om nip)
> decInstr (When       r _ eo _) nip = decRoutine r (IntoWhen       eo nip)
> decInstr (Jump       r _    _) _   = decRoutine r (ReturnNext)
> decInstr (Nop               _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WNop        , FNop      , noPrims)
> decInstr (IfElse px _ ep    _) nip = (ICBr nip ep, CFNop, BNop      , XNop   , SNop     , WNop        , FNop      , ps     ) where ps = (decPrimInstr px, DecPrimNop)
> decInstr (GoTo x            _) _   = (IBranch x  , CFNop, BNop      , XNop   , SNop     , WNop        , FNop      , noPrims) 
> decInstr (ReturnTop         _) _   = (IContinue  , CFNop, BNop      , XUseTop, SKeepTop , WNop        , FNop      , noPrims)
> decInstr (Return t _        _) _   = (IContinue  , CFNop, BNode    t, XBuild , SPushNode, WNop        , FNop      , noPrims)
> decInstr (ReturnTag t       _) _   = (IContinue  , CFNop, BTValue  t, XBuild , SPushNode, WNop        , FNop      , noPrims)
> decInstr (ReturnRaw abs     _) _   = (IContinue  , CFNop, BRaw pa  t, XBuild , SPushNode, WNop        , FNop      , noPrims) where (t,pa) = rawNodeTag abs
> decInstr (ReturnConst c n   _) _   = (IContinue  , CFNop, BConst n t, XBuild , SPushNode, WNop        , FNop      , noPrims) where t  = boxNodeTag c
> decInstr (ReturnPrim c _    _) _   = (IContinue  , CFNop, BPrim    t, XBuild , SPushNode, WNop        , FNop      , noPrims) where t  = boxNodeTag c
> decInstr (ReturnBool c _    _) _   = (IContinue  , CFNop, BNode    t, XBuild , SPushCond, WNop        , FNop      , noPrims) where t  = NodeTag Dynamic 0 emptyKinds $ Con c
> decInstr (StoreCVal cv      _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WPushRef pr , FNop      , noPrims) where pr = CVRef cv
> decInstr (StoreFE nf uf _ a _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WStoreFE t  , FRWLoad ef, noPrims) where {t = NodeTag Dynamic fnx fks (FE ef uf); ef = evalFunFromApply a; (fnx,fks) = nf}
> decInstr (Store t _         _) _   = (INop       , CFNop, BNode    t, XBuild , SNop     , WStore t    , FNop      , noPrims)
> decInstr (StoreSelect _ _ _ _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WSelPush    , FNop      , noPrims)
> decInstr (PushCAFRef (pt,r) _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WPushRef pr , FNop      , noPrims) where pr = Ref pt r
> decInstr (StoreBox c _      _) _   = (INop       , CFNop, BPrim    t, XBuild , SNop     , WStoreBox c , FNop      , noPrims) where t  = boxNodeTag c
> decInstr (StoreBool c _     _) _   = (INop       , CFNop, BNode    t, XBuild , SNop     , WStoreCond c, FNop      , noPrims) where t  = NodeTag Dynamic 0 emptyKinds $ Con c
> decInstr (Push xys          _) _   = (INop       , CFNop, BRaw pa  t, XBuild , SPushNode, WNop        , FNop      , noPrims) where (t,pa) = rawNodeTag xys
> decInstr (PushCont _        _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WNop        , FNop      , noPrims)
> decInstr (ClearRefs xs      _) _   = (INopClrRs  , CFNop, BRaw 0   t, XBuild , SNop     , WNop        , FNop      , noPrims) where (t,0) = rawNodeTag xs
> decInstr (PrimInstr a b     _) _   = (INop       , CFNop, BNop      , XNop   , SNop     , WNop        , FNop      , ps     ) where ps = (decPrimInstr a, decPrimInstr b)
> decInstr (Send c t _        _) _   = (INop       , CFNop, BNode    t, XBuild , SNop     , WSend c t   , FNop      , noPrims)
> decInstr (Throw _           _) _   = (IThrow     , CFNop, BNode    t, XBuild , SPushNode, WNop        , FNop      , noPrims) where t  = singleRefNodeTag Excep

> decRoutine :: Callable -> Continuation -> (InstrFlowCtrl, CallFrameCtrl, BuildCtrl, NodeSelCtrl, NodeStackCtrl, StoreCtrl, FetchCtrl, DecPrims () PrimRead CondRead)
> decRoutine (Run  f xs     ) c = (IRoutine f , CFPushCall c, BCall    t, XBuild, SPushNode, WNop      , FNop      , noPrims) where t  = NodeTag Dynamic (bodyArity xs) (bodyKinds xs) $ Fun f Nothing SkipUpd
> decRoutine (Fix  f xs     ) c = (IRoutine f , CFPushCall c, BCallFix t, XBuild, SPushNode, WFixHole f, FNop      , noPrims) where t  = NodeTag Dynamic (bodyArity xs) (bodyKinds xs) $ Fun f Nothing WithUpd
> decRoutine (Proc f xys    ) c = (IRoutine f , CFPushCall c, BRaw pa  t, XBuild, SPushNode, WNop      , FNop      , noPrims) where (t,pa) = rawNodeTag xys
> decRoutine (Eval  _       ) c = (IEval False, CFPushCall c, BNop      , XNop  , SWaitLoad, WNop      , FEvalRef  , noPrims)   -- CFPushCall here because Eval and friends behave like function calls
> decRoutine (Fetch _       ) c = (IEval True , CFPushCall c, BNop      , XNop  , SWaitLoad, WNop      , FEvalRef  , noPrims)
> decRoutine (EvalFetched   ) c = (IEval False, CFPushCall c, BNop      , XNop  , SWaitLoad, WNop      , FUsePre   , noPrims)
> decRoutine (PushFetched   ) c = (IEval True , CFPushCall c, BNop      , XNop  , SWaitLoad, WNop      , FUsePre   , noPrims)
> decRoutine (EvalCAF (pt,_)) c = (IEval e    , CFPushCall c, BNop      , XNop  , SWaitLoad, WNop      , FEvalRef  , noPrims) where e = isValuePtrTag pt
> decRoutine (Receive i     ) c = (IEval False, CFPushCall c, BNop      , XNop  , SWaitLoad, WNop      , FReceive i, noPrims)

> decInstrReads :: Instruction -> (ApplyCtrl, PopMask, ReadInstr)
> decInstrReads (Call    _  r a _  pm) = decRoutineReads r a pm
> decInstrReads (Case    _  r a _  pm) = decRoutineReads r a pm
> decInstrReads (BigCase _  r a _  pm) = decRoutineReads r a pm
> decInstrReads (When       r a _  pm) = decRoutineReads r a pm
> decInstrReads (Jump       r a    pm) = decRoutineReads r a pm
> decInstrReads (Nop               pm) = (ApplyNop    , pm, defRI                                         )
> decInstrReads (IfElse px c _     pm) = (ApplyNop    , pm, defRI {crd = OK c, vrd = primStRds px PrimNop})
> decInstrReads (GoTo _            pm) = (ApplyNop    , pm, defRI                                         ) 
> decInstrReads (ReturnTop         pm) = (ApplyNop    , pm, defRI                                         )
> decInstrReads (Return _ as       pm) = (ApplyNop    , pm, defRI `plainNodeReads` as                     )
> decInstrReads (ReturnTag _       pm) = (ApplyNop    , pm, defRI                                         )
> decInstrReads (ReturnRaw abs     pm) = (ApplyNop    , pm, defRI `rawNodeReads` abs                      )
> decInstrReads (ReturnConst _ _   pm) = (ApplyNop    , pm, defRI                                         )
> decInstrReads (ReturnPrim _ x    pm) = (ApplyNop    , pm, defRI {ecrd = ((RVoid, RVoid), Just x)}       )
> decInstrReads (ReturnBool _ c    pm) = (ApplyNop    , pm, defRI {crd = OK c}                            )
> decInstrReads (StoreCVal _       pm) = (ApplyNop    , pm, defRI                                         )
> decInstrReads (StoreFE _ _ x a   pm) = (ApplyToStore, pm, defRI {rrd = Left x, ecrd = extraContReads a} )
> decInstrReads (Store   _ as      pm) = (ApplyNop    , pm, defRI `plainNodeReads` as                     )
> decInstrReads (StoreSelect c a b pm) = (ApplyNop    , pm, defRI {crd = OK c, ecrd = ((a, b),Nothing)}   )
> decInstrReads (PushCAFRef _      pm) = (ApplyNop    , pm, defRI                                         )
> decInstrReads (StoreBox _ x      pm) = (ApplyNop    , pm, defRI {ecrd = ((RVoid, RVoid), Just x)}       )
> decInstrReads (StoreBool _ c     pm) = (ApplyNop    , pm, defRI {crd = OK c}                            )
> decInstrReads (Push xys          pm) = (ApplyNop    , pm, defRI `rawNodeReads` xys                      )
> decInstrReads (PushCont a        pm) = (decApPush a , pm, defRI {ecrd = extraContReads a}               )
> decInstrReads (ClearRefs xs      pm) = (ApplyNop    , pm, defRI `rawNodeReads` xs                       )
> decInstrReads (PrimInstr a b     pm) = (ApplyNop    , pm, defRI {vrd = primStRds a b}                   )
> decInstrReads (Send _ _ xs       pm) = (ApplyNop    , pm, defRI `plainNodeReads` xs                     )
> decInstrReads (Throw x           pm) = (ApplyNop    , pm, defRI `plainNodeReads` nr                     ) where nr = FB (T (Just (Left x)) Nothing Nothing) (pure Nothing)

> decRoutineReads :: Callable -> ExtraCont -> PopMask -> (ApplyCtrl, PopMask, ReadInstr)
> decRoutineReads (Fix  _  xs) ~NoEvalCont pm = (PushFixRef, pm, (defRI {crd = OK $ CQ False 0})`plainNodeReads` xs)
> decRoutineReads c            a           pm = (decApPush a  , pm, decCallReads c (defRI {ecrd = extraContReads a, crd = OK $ CQ False 0})) where
>   decCallReads (Run  _  xs ) xRI = xRI `plainNodeReads` xs
>   decCallReads (Proc _  xys) xRI = xRI `rawNodeReads` xys
>   decCallReads (Eval  x    ) xRI = xRI {rrd = Left x                  }
>   decCallReads (Fetch x    ) xRI = xRI {rrd = Left x                  }  -- FIXME does it make sense to save a condition on a fetch without posteval? but it is more regular ...
>   decCallReads (EvalFetched) xRI = xRI {rrd = Right $ CVRef FetchedRef}
>   decCallReads (PushFetched) xRI = xRI {rrd = Right $ CVRef FetchedRef}  -- idem ^^^
>   decCallReads (EvalCAF r  ) xRI = xRI {rrd = Right $ uncurry Ref r   }
>   decCallReads (Receive _  ) xRI = xRI {rrd = Right $ CVRef VoidRef   }

> extraContReads :: ExtraCont -> ((RefRead, RefRead), Maybe PrimRead)
> extraContReads = first (\(ra,rb) -> (fromMaybe RVoid ra, fromMaybe RVoid rb)) . extraContReads'

> extraContReads' :: EvalCont r p -> ((Maybe r, Maybe r), Maybe p)
> extraContReads' (NoEvalCont   ) = ((Nothing, Nothing), Nothing)
> extraContReads' (Apply1    x  ) = ((Just x , Nothing), Nothing)
> extraContReads' (Apply2    x y) = ((Just x , Just y ), Nothing)
> extraContReads' (Select _     ) = ((Nothing, Nothing), Nothing)
> extraContReads' (ThenFetch   x) = ((Just x , Nothing), Nothing)
> extraContReads' (MaskFetch _ x) = ((Just x , Nothing), Nothing)
> extraContReads' (WithCatch   x) = ((Just x , Nothing), Nothing)
> extraContReads' (WithPrim _ z ) = ((Nothing, Nothing), Just z )

> plainNodeReads :: ReadInstr -> NodeRead -> ReadInstr
> plainNodeReads xri xs = xri {nrd = xs, vrd = extractPrimReads xs}  -- FIXME deal with prim reads better instead of reading them on both sides

> rawNodeReads :: ReadInstr -> SplitRead -> ReadInstr
> rawNodeReads xri xys = xri {nrd = rs, vrd = extractPrimReads (fmap (fmap (fmap PA)) xys)} where
>   rs = fmap (maybe Nothing $ either (Just . Left) $ const Nothing) xys

> extractPrimReads :: FB (Maybe (Either r WordRead)) -> Quad (Maybe WordRead)
> extractPrimReads (FB (T a b c) (Q d e f g)) = zipQuadWith firstPrim (Q a b c d) (Q e f g Nothing) where
>   firstPrim (Just (Right a)) _                = Just a
>   firstPrim _                (Just (Right b)) = Just b
>   firstPrim _                _                = Nothing

> decApPush :: EvalCont r p -> ApplyCtrl
> decApPush (NoEvalCont   ) = ApplyNop   
> decApPush (Apply1    _  ) = PushApply $ ApplyN' 1
> decApPush (Apply2    _ _) = PushApply $ ApplyN' 2
> decApPush (Select i     ) = PushApply $ Select' i
> decApPush (ThenFetch   _) = PushApply $ ThenFetch'
> decApPush (MaskFetch m _) = PushApply $ MaskFetch' m
> decApPush (WithCatch   _) = PushApply $ WithCatch'
> decApPush (WithPrim p _ ) = PushApply $ WithPrim' p

> primStRds :: PrimInstr -> PrimInstr -> Quad (Maybe WordRead)
> primStRds px py = Q xa xb ya yb where
>   (xa,xb) = primStRd px
>   (ya,yb) = primStRd py
>   primStRd (PrimOp _ a b _) = (primSR a, primSR b)
>   primStRd (CmpOp  _ a b _) = (primSR a, primSR b)
>   primStRd _                = (Nothing , Nothing )
>   primSR (Im _) = Nothing
>   primSR (PQ _) = Nothing
>   primSR x      = Just $ PA x

> decPrimInstr :: PrimInstr -> DecPrimInstr () PrimRead CondRead
> decPrimInstr (PrimNop         ) = DecPrimNop
> decPrimInstr (PrimOp   p a b c) = DecPrimOp () p a b c
> decPrimInstr (CmpOp    p a b c) = DecCmpOp  () p a b c
> decPrimInstr (PrimConst   x   ) = DecPrimC  ()  x

> calcNextInstr :: InstrFlowCtrl -> Maybe (Bool, NextInstr)  -- Bool for Clearing Refs
> calcNextInstr (INop      ) = Just (False, NextIP           )
> calcNextInstr (INopClrRs ) = Just (True , NextIP           )
> calcNextInstr (IEval e   ) = Just (False, EvalLoad e       )
> calcNextInstr (IRoutine f) = Just (False, BranchTo $ snd f )
> calcNextInstr (IBranch x ) = Just (False, BranchTo x       )
> calcNextInstr (ICBr ti eo) = Just (False, DecideBr ti eo   )
> calcNextInstr (IThrow    ) = Just (False, Unwinding popNone)
> calcNextInstr (IContinue ) = Nothing

> maxStackReadDepth :: ReadInstr -> StackPops -> StackOffset
> maxStackReadDepth (ReadInstr r _ n ys (ec,mp)) pm = mr `max` mn `max` my `max` me `max` ms where
>   mr = either maxSRDRef (const 0) r
>   mn = Data.Foldable.maximum $ fmap (maybe 0 $ either maxSRDRef maxSRDWord) n
>   my = Data.Foldable.maximum $ fmap (maybe 0 maxSRDWord) ys
>   me = maxSRDRef (fst ec) `max` maxSRDRef (snd ec) `max` maybe 0 maxSRDPrim mp
>   Q pa pb pc pd = pm
>   ms = popsrd 0 pa `max` popsrd 1 pb `max` popsrd 2 pc `max` popsrd 3 pd
>   popsrd i p = case p of {Pop -> i; Keep -> 0}

> maxSRDRef :: RefRead -> StackOffset
> maxSRDRef (R  i _) = i
> maxSRDRef (CR i _) = i
> maxSRDRef (NR   i) = i
> maxSRDRef (CNR  i) = i
> maxSRDRef _        = 0

> maxSRDWord :: WordRead -> StackOffset
> maxSRDWord (W i _) = i
> maxSRDWord (PA px) = maxSRDPrim px

> maxSRDPrim :: PrimRead -> StackOffset
> maxSRDPrim (V i _) = i
> maxSRDPrim _       = 0

> renamePrimReads :: QueueBase -> QueueBase -> DecPrims () PrimRead CondRead -> (QueueBase, QueueBase, DecPrims QueueIndex LocPIndex CondIndex)
> renamePrimReads pb cb (a, b) = let {(pb', cb', a') = renamePrimInstr pb cb a; (pb'', cb'', b') = renamePrimInstr pb' cb' b} in (pb'', cb'', (a', b'))

> renamePrimInstr :: QueueBase -> QueueBase -> DecPrimInstr () PrimRead CondRead -> (QueueBase, QueueBase, DecPrimInstr QueueIndex LocPIndex CondIndex)
> renamePrimInstr pb cb (DecPrimNop           ) = (pb , cb , DecPrimNop                                                                    )
> renamePrimInstr pb cb (DecPrimOp () px a b c) = (npb, cb , DecPrimOp (primIxAt npb 0) px (renamePA pb a) (renamePA pb b) (indexCond cb c)) where npb = nextPrimBase pb
> renamePrimInstr pb cb (DecCmpOp  () px a b c) = (pb , ncb, DecCmpOp  (condIxAt ncb 0) px (renamePA pb a) (renamePA pb b) (indexCond cb c)) where ncb = nextCondBase cb
> renamePrimInstr pb cb (DecPrimC  ()   n     ) = (npb, cb , DecPrimC  (primIxAt npb 0) n                                                  ) where npb = nextPrimBase pb

> nextPrimBase :: QueueBase -> QueueBase
> nextPrimBase (QB pb) = QB (pred pb `mod` 32)

> nextCondBase :: QueueBase -> QueueBase
> nextCondBase (QB cb) = QB (pred cb `mod` 16)

> renamePA :: QueueBase -> PrimRead -> LocPIndex
> renamePA _  (V _ _) = XI
> renamePA _  (Im x ) = SIC x
> renamePA pb (PQ i ) = LQI (primIxAt pb i)

> data StackPos = SPTop | Deep StackIndex | SPVoid deriving (Show, Eq)
> stackPos :: a -> (StackIndex -> a) -> StackPos -> a
> stackPos x _ (SPTop ) = x
> stackPos _ f (Deep i) = f i
> stackPos _ _ (SPVoid) = error "reading from invalid stack index"

> type StackLookup = Array StackOffset StackPos

> stackLookup :: Array StackOffset StMapping -> StackLookup
> stackLookup xs = IArray.listArray (0, 3) [stMap (xs!0), stMap (xs!1), stMap (xs!2), stMap (xs!3)] where
>   stMap (StTop _  ) = SPTop
>   stMap (StIndex i) = Deep i 
>   stMap (StVoid   ) = SPVoid

> renameReads :: StackLookup -> QueueBase -> QueueBase -> QueueBase -> StackPops -> ReadInstr -> ReadCtrl
> renameReads rmlf rb pb cb pm rx@(ReadInstr r c n ys ec) = ReadCtrl r' c' n' ys' ers' exp' rus txs where
>   r'  = either (Left . indexRef rmlf rb) Right r
>   c'  = fmap (indexCond cb) c
>   n'  = indexNode rmlf rb pb n
>   ys' = indexPrimVals rmlf pb ys
>   (ers', exp') = renameEvalCont rmlf rb pb ec
>   ru' = collectNodeRefUse rmlf rx pm
>   rus = fmap (>>= \((_, mu), sp) -> fmap (,sp) mu) ru'
>   txs = fmap (\case {Just ((Just TakeRef, _), sp) -> Just sp; _ -> Nothing}) ru'   -- gathering destructive reads on node refs

> renameEvalCont :: StackLookup -> QueueBase -> QueueBase -> ((RefRead, RefRead), Maybe PrimRead) -> ((RefUseIndex, RefUseIndex), Maybe PrimIndex)
> renameEvalCont rmlf rb pb ((mx, my), mz) = ((indexRef rmlf rb mx, indexRef rmlf rb my), fmap (indexPrim rmlf pb) mz)

> collectNodeRefUse :: StackLookup -> ReadInstr -> StackPops -> Quad (Maybe ((Maybe RefUse, Maybe StackResult), StackPos))
> collectNodeRefUse rmlf (ReadInstr r _ n _ ((ex,ey), _)) pm = nrs where
>   bru = foldMap (foldMap nodeRefUse) n
>   xru = bru `mappend` foldMap nodeRefUse (T r (Left ex) (Left ey))
>   nrs = zipQuadWith (\i p -> case mayNeedNodeRefFix (xru i) p of {(Nothing,Nothing) -> Nothing; rs -> Just (rs, rmlf!i)}) (Q 0 1 2 3) pm

> nodeRefUse :: Either RefRead a -> StackOffset -> (Maybe RefUse, Maybe RefUse)  -- (node ref read usage, body ref read usage)
> nodeRefUse (Left ( R j _)) i | i == j = (Nothing     , Just TakeRef)
> nodeRefUse (Left (CR j _)) i | i == j = (Nothing     , Just CopyRef)
> nodeRefUse (Left (NR j  )) i | i == j = (Just TakeRef, Nothing     )
> nodeRefUse (Left (CNR j )) i | i == j = (Just CopyRef, Nothing     )
> nodeRefUse _               _          = (Nothing     , Nothing     )

> mayNeedNodeRefFix :: (Maybe RefUse, Maybe RefUse) -> PopNode -> (Maybe RefUse, Maybe StackResult)
> mayNeedNodeRefFix (Just ru, Just _      ) _    = (Just ru, Just NodeWSC)
> mayNeedNodeRefFix (Just ru, Nothing     ) Pop  = (Just ru, Just OnlySC )  -- only Node Ref will be used
> mayNeedNodeRefFix (Just ru, Nothing     ) Keep = (Just ru, Just NodeWSC)
> mayNeedNodeRefFix (Nothing, Just TakeRef) Keep = (Nothing, Just NodeWSC)  -- some ref will be taken from body so fixup is needed now
> mayNeedNodeRefFix (Nothing, Just TakeRef) Pop  = (Nothing, Nothing     )  -- only Node will be used
> mayNeedNodeRefFix (Nothing, Just CopyRef) _    = (Nothing, Nothing     )  -- only copying reads from node
> mayNeedNodeRefFix (Nothing, Nothing     ) _    = (Nothing, Nothing     )

> indexRef :: StackLookup -> QueueBase -> RefRead -> RefUseIndex
> indexRef rmlf _  (R  i c) = (TakeRef, stackPos RSTI RSI (rmlf!i) c)
> indexRef rmlf _  (CR i c) = (CopyRef, stackPos RSTI RSI (rmlf!i) c)
> indexRef rmlf _  (NR   i) = (TakeRef, stackPos TNR  NRI (rmlf!i))
> indexRef rmlf _  (CNR  i) = (CopyRef, stackPos TNR  NRI (rmlf!i))
> indexRef _    rb (RQ   i) = (TakeRef, RQI (refIxAt rb i))
> indexRef _    rb (CRQ  i) = (CopyRef, RQI (refIxAt rb i))
> indexRef _    _  (SCC  c) = (TakeRef, ICC c)
> indexRef _    _  (RVoid ) = (TakeRef, IVoid)

> refIxAt :: QueueBase -> Int -> QueueIndex
> refIxAt (QB rb) i = IxQ ((rb + i) `mod` 32)

> indexWord :: StackLookup -> QueueBase -> WordRead -> WordIndex
> indexWord rmlf _  (W i c) = stackPos WSTI WSI (rmlf!i) c
> indexWord rmlf pb (PA pr) = PAI $ indexPrim rmlf pb pr

> indexPrimVals :: StackLookup -> QueueBase -> Quad (Maybe WordRead) -> Quad (Maybe WordIndex)
> indexPrimVals rmlf pb = fmap (fmap $ indexWord rmlf pb)

> indexNode :: StackLookup -> QueueBase -> QueueBase -> BodyRead -> NodeIndex
> indexNode rmlf rb pb xs = fmap (fmap $ either (Left . indexRef rmlf rb) (Right . indexWord rmlf pb)) xs

> indexPrim :: StackLookup -> QueueBase -> PrimRead -> PrimIndex
> indexPrim rmlf _  (V i c) = stackPos VSTI VSI (rmlf!i) c
> indexPrim _    pb (PQ i ) = PQI $ primIxAt pb i
> indexPrim _    _  (Im x ) = IC x
> indexPrim _    _  (STTI ) = TTI

> primIxAt :: QueueBase -> Int -> QueueIndex
> primIxAt (QB pb) i = IxQ ((pb + i) `mod` 32)

> indexCond :: QueueBase -> CondRead -> CondIndex
> indexCond cb (CQ inv x ) = CQI inv $ condIxAt cb x
> indexCond cb (CNext inv) = FCQV inv $ condIxAt cb (negate 2)  -- assuming CNext is used as argument of a logic operator
> indexCond _  (CSTI inv ) = TNC inv
> indexCond _  (CSaved i ) = CSC i
> indexCond _  (CTrue    ) = IBC True
> indexCond _  (CFalse   ) = IBC False

> condIxAt :: QueueBase -> Int -> QueueIndex
> condIxAt (QB pb) i = IxQ ((pb + i) `mod` 16)

> updateRefBase :: StoreCtrl -> QueueBase -> Proc (Checked QueueIndex)
> updateRefBase dwi (QB rb)
>   | pushesRef dwi = (renamer.refBase .= QB rb') >> return (OK $ IxQ rb')
>   | otherwise     = return Bad
>   where rb' = (rb-1) `mod` 32

> data StackPushDown = PushDownNop | PushDownTo StackIndex | FixNodeRef StackIndex

> renameStackMod :: StackPops -> NodeStackCtrl -> Proc (NodeStackCtrl, StackPushDown, Quad (Maybe StackIndex))
> renameStackMod ps dsi = do
>   rm <- gets (renamer.stackMapping)
>   let fsfp = freeStackForPush dsi
>   let Q pa pb pc pd = ps
>   let ips = Q (renamePop pa (rm!0)) (renamePop pb (rm!1)) (renamePop pc (rm!2)) (renamePop pd (rm!3))
>   mpi <- if fsfp
>     then do
>       pdi <- popFifo (renamer.stackForFree)
>       return (StTop pdi)
>     else
>       return StVoid
>   let xs = filter (/=StVoid) (mpi : IArray.elems (invalidatePops fsfp ps rm)) ++ repeat StVoid
>   let rm' = IArray.listArray (0, 7) $ take 8 xs
>   renamer.stackMapping .= rm'
>   let spd = case rm!0 of {StTop i | pa == Pop || fsfp -> PushDownTo i;_ -> PushDownNop}
>   let dsi' = case (pa,dsi) of {(Pop,SNop) -> SPopTop; _ -> dsi}
>   return (dsi', spd, ips)

> renameStackPopTopForEvalLoad :: Proc (StackPushDown, Quad (Maybe StackIndex))
> renameStackPopTopForEvalLoad = do   -- special variant of above only affecting the known present stacktop
>   (StTop i) <- gets (renamer.stackMapping.to (! 0))
>   let ips = Q (Just i) Nothing Nothing Nothing
>   pdi <- popFifo (renamer.stackForFree)
>   renamer.stackMapping.ix 0 .= StTop pdi  
>   return (PushDownTo i, ips)

> renamePop :: PopNode -> StMapping -> Maybe StackIndex
> renamePop Keep _           = Nothing
> renamePop Pop  (StTop   i) = Just i
> renamePop Pop  (StIndex i) = Just i
> renamePop Pop  (StVoid   ) = error "popping unavailable stack node"

> invalidatePops :: Bool -> StackPops -> Array StackOffset StMapping -> Array StackOffset StMapping
> invalidatePops fsfp (Q pa pb pc pd) = over (ix 0) invPTop . invPX 1 pb . invPX 2 pc . invPX 3 pd where
>   invPTop m = case (pa, m) of {(Pop, _) -> StVoid; (_, StVoid) -> StVoid; (_, StTop i) -> if fsfp then StIndex i else StTop i; (_, StIndex i) -> StIndex i}
>   invPX i px = case px of {Pop -> set (ix i) StVoid; Keep -> id}

> checkLazyNodeRefUse :: Quad (Maybe (StackResult, StackPos)) -> Proc (Quad (Maybe (StackResult, StackPos, NodeTag)))
> checkLazyNodeRefUse nrus = do
>   rms <- traverse (tryReadMetaNode . fmap snd) nrus
>   return (clNodeRefUse <$> nrus <*> rms)

> tryReadMetaNode :: Maybe StackPos -> Proc (Checked StackMeta)
> tryReadMetaNode (Just SPTop   ) = fmap (\(rn, htrcv, mt, s) -> case mt of {Nothing -> Bad; Just t -> OK $ StMeta rn (mergeNodeValue htrcv) t s}) $ gets (ctrlStack.metaSTop)
> tryReadMetaNode (Just (Deep i)) = peeking (ctrlStack.metaSRegs) i
> tryReadMetaNode (Nothing      ) = return Bad

> mergeNodeValue :: (RefStatus, ValStatus) -> RefStatus
> mergeNodeValue (NoNR, NoCV) = NoNR
> mergeNodeValue _            = HasNR

> clNodeRefUse :: Maybe (StackResult, StackPos) -> Checked StackMeta -> Maybe (StackResult, StackPos, NodeTag)
> clNodeRefUse (Just (sp, mi)) (OK (StMeta NeedRef NoNR t _)) = Just (sp    , mi, t)
> clNodeRefUse (Just (_ , mi)) (OK (StMeta OnlyRef NoNR t _)) = Just (OnlySC, mi, t)     -- here we known the node body won't be read later
> clNodeRefUse (Just (_ , _ )) (Bad                         ) = error "clNodeRefUse Bad" -- annoyingly using ~ on OK does not work because of required matching on nested parts
> clNodeRefUse _               _                              = Nothing

> runLoadUnit :: Proc ()
> runLoadUnit = do
>   mlv <- replaces (loader.loadReq) $ const Nothing  -- TODO make less ugly by adding a pop operation?
>   case mlv of
>     Nothing -> return ()
>     Just (PopChannel ixl _) -> do
>       HNode t xs <- popFifo (ext.inputFifo)
>       poking (loader.loadBuffer) ixl $ Just (Nothing, HNode t xs, NoSharing)
>     Just (LoadRef _ (CVRef FetchedRef)) -> return ()   -- TODO probably it is better to handle such next fetch preload cases in an earlier stage
>     Just (LoadRef ixl (CVRef vx)) -> do
>       poking (loader.loadBuffer) ixl $ Just (Just (CVRef vx), expandValue vx, NoSharing)   -- TODO check if expanding in this stage is the best place
>     Just (LoadRef ixl (Ref pt r@(u,ns,x))) -> do
>       stats.refLoads += 1
>       case pt of
>         TC _ -> stats.knownPTrefLoads += 1 >> return ()
>         TF _ -> stats.funrefLoads += 1 >> return ()
>         _    -> return ()
>       mhi <- getAHIndex x
>       case mhi of
>         Just i  -> do
>           (kr, HNode t xs, fnvs) <- retrieveNodeAH (u,ns,i)
>           let nr = if kr then Just (Ref (node2PtrTag t) r) else Nothing
>           poking (loader.loadBuffer) ixl $ Just (nr, HNode t xs, fnvs)
>           when (ns < nodeSizeT t) $ trace ("nodeSize mismatch " ++ show t) $ return ()
>         Nothing -> do
>           heap.loadDelays += 1    -- TODO find better place for this counter loadDelays 
>           loader.cacheReq .= (Just $ CLoadRef ixl r)
>     Just (RewriteLoad ef lr@(CVRef cv)) -> case decideRewriteCV ef cv of
>       Nothing -> loader.rewriteLoadResult .= Just (CantRewrite   , Just lr, Nothing                         )
>       Just n  -> loader.rewriteLoadResult .= Just (ApplyRewrite n, Nothing, Just (expandValue cv, NoSharing))
>     Just (RewriteLoad ef lr@(Ref pt (u,ns,x))) -> do
>       mhi <- getAHIndex x
>       case (mhi, decideRewriteRef ef pt) of     -- TODO if the logic for decideRewrite turns out critical, make it in parallel with a speculative local load
>         (Nothing, _          ) -> loader.rewriteLoadResult .= Just (CantRewrite, Just lr, Nothing)
>         (_      , CantRewrite) -> loader.rewriteLoadResult .= Just (CantRewrite, Just lr, Nothing)
>         (Just i , rwx        ) -> do
>           (kr, hn, fnvs) <- retrieveNodeAH (u,ns,i)
>           let mrl = if kr then Just lr else Nothing
>           loader.rewriteLoadResult .= Just (rwx, mrl, Just (hn, fnvs))

> runDataCache :: Proc ()
> runDataCache = do
>   mcr <- replaces (loader.cacheReq) (const Nothing)   -- TODO make it a fifo instead?
>   case mcr of
>     Nothing -> return ()
>     Just (CLoadRef ixl r@(_,ns,_)) -> do
>       (kr, HNode t xs, fnvs) <- retrieveNodeCache r
>       let nr = if kr then Just (Ref (node2PtrTag t) r) else Nothing
>       poking (loader.loadBuffer) ixl $ Just (nr, HNode t xs, fnvs)
>       when (ns < nodeSizeT t) $ trace ("nodeSize mismatch " ++ show t) $ return ()

> finishLoad :: Proc ()
> finishLoad = do
>   LB li <- gets (loader.lastLoadIx)
>   let nx = (li + 1) `mod` 4
>   let ixl = IxL nx
>   lbe <- peeking (loader.loadBuffer) ixl
>   case lbe of
>     Nothing -> block                 -- wait for load result
>     Just (nr, HNode t xs, fnvs) -> {- trace ("loaded: " ++ show (HNode t xs)) $ -} do
>       poking (loader.loadBuffer) ixl Nothing
>       loader.loadResult .= Just (nr, HNode t $ over (mapped.mapped.withRef) (applyRefSharing fnvs) xs)
>       loader.lastLoadIx .= LB nx

> execFixupStackRef :: (StackResult, StackPos, NodeTag) -> Proc ()  -- TODO maybe use a more direct method for fixing the stacktop
> execFixupStackRef (sp, mi, t) = evalAndExecStages (Left (Just (False, DummyNext), CFNop, NoUpdate, ApplyNop, FNop, dwi)) xni dsi (Just (rnrs, bni, (Nothing, stm, emptyQuad), noPrims)) where
>   (dsi, stm)       = case mi of {SPTop -> (SFixTopRef, PushDownNop); Deep xi -> (SNop, FixNodeRef xi)}
>   (rnrs, bni, xni, dwi) = case (primBoxConAlt $ plainTag t, sp) of
>     (Just b , _      ) -> (defaultRC {expi = Just (stackPos VSTI VSI mi H)}, BPrim t, XBuild, (WSaveBox tb, Bad)) where tb = boxNodeTag b  -- special case for boxed prim requiring node ref
>     (Nothing, NodeWSC) -> (defaultRC {nri = indexStackNode t CopyRef mi   }, BNode t, XBuild, (WSaveNode t, Bad))
>     (Nothing, _      ) -> (defaultRC {nri = indexStackNode t TakeRef mi   }, BNode t, XBuild, (WSaveNode t, Bad))

> indexStackNode :: NodeTag -> RefUse -> StackPos -> NodeIndex
> indexStackNode t ru mi = zipBodyWith ixStElem (kindMaskBody t) bodyIndices where
>   ixStElem (Just RefK ) = Just . Left  . (,) ru . stackPos RSTI RSI mi
>   ixStElem (Just PrimK) = Just . Right .          stackPos WSTI WSI mi
>   ixStElem (Nothing   ) = const Nothing

> runInstr :: Instruction -> Proc ()
> runInstr instr = do
> {- * -- * -- * -- * -- * -- * DECODE STAGE * -- * -- * -- * -- * -- * -}
>   nextCycle
>   nip <- get_next_ip                                                -- R   ip
>   let decR = decInstrReads instr                                    -- .
>   let decI = decInstr instr nip                                     -- .
>   runDecInstr decR (Just decI)

> runDecInstr :: (ApplyCtrl, PopMask, ReadInstr) -> Maybe (InstrFlowCtrl, CallFrameCtrl, BuildCtrl, NodeSelCtrl, NodeStackCtrl, StoreCtrl, FetchCtrl, DecPrims () PrimRead CondRead) -> Proc ()
> runDecInstr (ai, (prq, pm), rx) mdi = do
>   let (ci,cfi,bni,xni,smi,whi,fi,dpo) = fromMaybe (IContinue, CFNop, BNop, XUseTop, SKeepTop, WNop, FNop, noPrims) mdi
> {- * -- * -- * -- * -- * -- * RENAME STAGE * -- * -- * -- * -- * -- * -}
>   nextCycle
>   rm <- gets (renamer.stackMapping)                                 -- R   stackMapping
>   rb <- gets (renamer.refBase)                                      -- R   refBase
>   pb <- gets (renamer.primBase)                                     -- R   primBase
>   cb <- gets (renamer.condBase)                                     -- R   condBase
>   esff <- gets (renamer.stackForFree.to nullFifo)                   -- R   stackForFree
>   let stRn = stackLookup rm                                         -- .
>   let mrd = maxStackReadDepth rx pm                                 -- .               -- TODO consider moving (part of) this to decode stage if it is critical
>   when (esff && freeStackForPush smi) block                         -- .               -- blocking on no free stack
>   when (mrd > 0 && (stRn!mrd) == SPVoid) block                      -- .               -- blocking on not enough reachable stack  -- TODO check empty StRn corner case better
>   let (pb', cb', dpo') = renamePrimReads pb cb dpo                  -- .
>   let rnrs = renameReads stRn rb pb' cb' pm rx                      -- .               -- pb' and cb' here because of combined prim/other instructions
>   let sprq = case prq of {DropRQ -> Just rb; KeepRQ -> Nothing}     -- .
>   renamer.primBase .= pb'                                           -- W   primBase 
>   renamer.condBase .= cb'                                           -- W   condBase
>   wqi <- updateRefBase whi rb                                       -- W   refBase
>   (smi', stm, ips) <- renameStackMod pm smi                         -- R/W stackMapping POP stackForFree
>   let rbpp = Just (rnrs, bni, (sprq, stm, ips), dpo')               -- .
>   checkLazyNodeRefUse (nru rnrs) >>=                                -- R  metaSTop metaStack  -- metaStack/STop is writen in next stage so this check needs to use bypassed data instead
>     Data.Foldable.mapM_ (maybe (return ()) (fixupWith . execFixupStackRef))     -- Exec next stages
> {- * -- * -- * -- * -- * -- * ISSUE STAGE * -- * -- * -- * -- * -- * -}
>   case calcNextInstr ci of  -- Nothing implies next instruction depends on call stack
>     Nothing -> evalAndExecStages (Right False                                     ) xni smi' rbpp    -- cfi ai fi dwi must be nops here
>     Just ni -> evalAndExecStages (Left (Just ni, cfi, NoUpdate, ai, fi, (whi,wqi))) xni smi' rbpp

> runFunEvalCombinator :: (EvalCont NodeElem QuadElem) -> Proc ()
> runFunEvalCombinator ec = do
>   let ai = decApPush ec                        -- FIXME these two should be
>   let ((rra, rrb), rrp) = extraContReads' ec   -- moved to the previous stage
> {- * -- * -- * -- * -- * -- * RENAME STAGE * -- * -- * -- * -- * -- * -}
>   nextCycle
>   esff <- gets (renamer.stackForFree.to nullFifo)                   -- R   stackForFree
>   when esff block                                                   -- .               -- blocking on no free stack
>   let (xa, xb) = (maybe IVoid RSTI rra, maybe IVoid RSTI rrb)
>   let rnrs = defaultRC {ecri = ((TakeRef, xa), (TakeRef, xb)), expi = fmap VSTI rrp}
>   (stm, ips) <- renameStackPopTopForEvalLoad                        -- R/W stackMapping POP stackForFree
>   let rbpp = Just (rnrs, BNop, (Nothing, stm, ips), noPrims)        -- .
>   let ni = (False, EvalLoad False)                                  -- .  EvalFetched
>   evalAndExecStages (Left (Just ni, CFPushCall ReturnNext, NoUpdate, ai, FUsePre, (WNop,Bad))) XNop SWaitLoad rbpp

> evalAndExecStages :: Either (Maybe (Bool,NextInstr), CallFrameCtrl, DemuxUpdateCtrl, ApplyCtrl, FetchCtrl, (StoreCtrl, Checked QueueIndex)) Bool -> NodeSelCtrl -> NodeStackCtrl ->
>   Maybe (ReadCtrl, BuildCtrl, (Maybe QueueBase, StackPushDown, Quad (Maybe StackIndex)), DecPrims QueueIndex LocPIndex CondIndex) -> Proc ()
> evalAndExecStages mci xni xsi mrbpp = do
>   let (rnrs, bni, (sprq, stm, ips), dpo) = fromMaybe (defaultRC, BNop, (Nothing, PushDownNop, emptyQuad), noPrims) mrbpp
>   nextCycle
> {- * -- * -- * -- * -- * -- * ISSUE STAGE * -- * -- * -- * -- * -- * -}
>   cf@(CallFrame fec c _ nc) <- gets (ctrlStack.callStack.top)       -- R   callStack nodeCount
>   epc <- gets (ctrlStack.extraPushCont)                             -- R   extraPushCont
>   mav <- peekTopMetaCont                                            -- R   metaContStack
>   mlr <- fmap toChecked $ gets (loader.loadResult)                  -- R   loadResult      -- TODO should block here or in finishLoad on incomplete loadResult
>   let hlr = fmap (isJust . fst) mlr                                 -- .
>   otc <- gets (ctrlStack.topNodeCond)                               -- R   topNodeCond
>   mrc <- traverse (peekAtC otc) (cri rnrs)                          -- R   condQueue savedCond
>   let tnrts = Data.Foldable.any (== Just SPTop) (nrts rnrs)         -- .                   -- TODO need to only check the first one here?
>   mstn@(tnrn,_,_,_) <- readTopMetaNode tnrts                        -- R   metaSTop
>   ixl <- gets (renamer.loadBase.to (\(LB i) -> IxL i))              -- R   loadBase
>   let !nc' = nc - countJusts ips                                    -- .                   -- subtract stack pop count
>   let mmbn = buildMetaNode bni                                      -- .
>   let (rnt, htrv, mnt, tns) = selectMetaNode xni mmbn mlr mstn      -- .
>   let mtc = selectTopCond xsi mrc mnt otc                           -- .
>   let mtx = fmap plainTag mnt                                       -- .
>   let mti = toChecked $ fmap tag2Index mtx                          -- .
>   let dsi = case mtx of {Just Ind -> SNop; _ -> xsi}                -- .                   -- do not push indirections
>   let (mni, cfi, udi, xa, fci, dwi) = case (mci, mnt) of {          -- .
>     (Left dci, _         ) -> dci;                                  -- .
>     (Right e , ~(Just tx)) | checkEvalStatus e (plainTag tx) ->     -- .
>       decideEvalUpdApply fec tx hlr mav htrv nc'                    -- .
>     }                                                               -- .
>   let ai = decideApplyMerge (mayApplyMerge cfi epc fec) xa mav      -- .
>   let fi = (fci, ixl)                                               -- .
>   let xec = addNewApply epc ai                                      -- .                   -- new extra applications
>   let aec = subUsedApply fec ai                                     -- .                   -- updated number of extra applications in current callframe
>   let (rrr, ni) = decideContinue mni aec c mtx                      -- .
>   let (tfrn,tfrf,tfbf) = decideFixup rrr htrv ai                    -- . 
>   let uhtr = runMetaUpdate udi htrv                                 -- .
>   let (mant,aei,atns) = applyToMetaTag ai mnt tns                   -- .
>   let mftn = runMetaTopFix (tfrn,tfrf,tfbf) (rnt,uhtr,mant,atns)    -- .
>   let pnnc = pushNewNodeCount dsi                                   -- .
>   runMetaApplyStack ai                                              -- W   metaContStack
>   modifyCallFrame cfi xec mrc aec pnnc (cf,nc')                     -- W   callStack nodeCount extraPushCont savedCond
>   setBranchCond ni (isLeft mci) mrc mtc                             -- W   branchCond
>   ctrlStack.topNodeCond .= mtc                                      -- W   topNodeCond
>   adjustMetaStack stm mstn (nrts rnrs)                              -- W   metaStack
>   setMetaStackTop dsi tnrts mftn                                    -- W   metaSTop
>   when (advancesLdBuff fci) $ nextLoadBase                          -- W   loadBase
>   startEarlyFetch xni fi (fmap snd mlr)                             -- W   loadReq    -- TODO these chained loads should be initiated in the load unit itself
>   instrCtrl.nextI .= ni                                             -- W   nextI
> {- * -- * -- * -- * -- * -- * REG READ STAGE * -- * -- * -- * -- * -- * -}    -- TODO consider making reg read stage speculative and integrate it with the previous stage
>   nextCycle
>   rvs <- readPrimVals mti (vri rnrs)                                -- R   primQueue primSTop primStack stackTop nodeStack
>   (rlx, lrc) <- readLoadRef (rri rnrs)                              -- R/W stackTop nodeStack refQueue
>   rras <- readExtraCont (ecri rnrs)                                 -- R/W stackTop nodeStack refQueue
>   rrxp <- readExtraPrim mti (expi rnrs)                             -- R   primQueue primSTop primStack
>   rrn <- readBody mti (nri rnrs)                                    -- R/W stackTop nodeStack refQueue  R primQueue primSTop primStack
>   avs <- fmap (toChecked) $ gets (dataPath.contStack.safePeek)      -- R   contStack       -- will be writen in next pipeline stage thus requires bypass
>   let usr = fmap (\ ~(Ref pt r) -> (pt,r)) avs                      -- .
>   pax <- gets (primSide.primContStack.safePeek)                     -- R   primContStack   -- idem ^^
>   sxr <- genStoreAddr (fst dwi)                                     -- POP nextFreeAddress
>   pushEarlyRef dwi sxr                                              -- W   refQueue
>   startFetchRef fi rlx avs                                          -- W   loadReq rewriteLoadRef  R inAH
> {- * -- * -- * -- * -- * -- STACK MODIFY STAGE -- * -- * -- * -- * -- * -} 
>   nextCycle
>   stn <- gets (dataPath.stackTop)                                   -- R   stackTop
>   pst <- gets (primSide.primSTop)                                   -- R   primSTop
>   let mbn = buildNode bni rrn sxr                                   -- .
>   let mpv = buildPrimVals bni rvs rrxp                              -- .
>   let (xtrv, xnb) = selectStackNode xni mbn mlr stn                 -- .
>   let xps = selectPrimVals xni mpv (fmap snd mlr) pst               -- .
>   let ecru = hasUpdateSplit udi
>   let (brcs, cnb) = nodeBodyRCUpdates mnt tns ecru tfbf xnb         -- .
>   let (munrc, fsn, wnb) = demuxUpdNode udi tfrf tfbf usr xtrv cnb   -- .
>   let apvs = applyToPrimVals ai pax xps                             -- .
>   let asn = applyToBody ai aei tfbf avs fsn                         -- .                        -- to simplify control applications are done one argument at a time
>   let esn = dropLoadedArg (fst fi) asn                              -- .
>   startLateFetch xni fi cnb                                         -- W   loadReq  R inAH
>   updatePrimApStack ai rrxp                                         -- W   primContStack
>   arcs <- updateApplyStack ai tfbf avs rras (fmap fst mlr) sxr      -- W   contStack
>   queueRC lrc                                                       -- W   refC*1
>   queueRCs brcs                                                     -- W   refC*N               -- does RC updates for both node reading as update duplication
>   queueRC $ fst munrc                                               -- W   refC*1
>   queueRC $ snd munrc                                               -- W   refC*1
>   queueRC $ fst arcs                                                -- W   refC*1
>   queueRC $ snd arcs                                                -- W   refC*1
>   setRQPopIndex sprq                                                -- W   rqToPop
>   setStackPops ips                                                  -- W   stackForPop
>   pushDownStack stm tnrn stn sxr                                    -- W   nodeStack stackDropRef
>   pushDownPrimStack stm pst                                         -- W   primStack
>   setStackTop dsi sxr esn                                           -- W   stackTop
>   setPrimStackTop dsi apvs                                          -- W   primSTop
> {- * -- * -- * -- * -- * -- * EXECUTE STAGE * -- * -- * -- * -- * -- * -}
>   nextCycle 
>   sc <- readCond mtc (cri rnrs)                                     -- R   condQueue savedCond
>   let xep = selectFirstPrim xps                                     -- .
>   let sr = fmap (\(Ref _ r)  -> r) sxr                              -- .
>   runStoreInstr dwi sr usr sc wnb xep (fst rras)                    -- W   refQueue heap rewriteBuffer
>   runPrims mtc dpo rvs                                              -- R/W primQueue R/W/B condQueue R/B savedCond B callStack\Conds topNodeCond branchCond
> {- * -- * -- * -- * -- * --  WRITEBACK STAGE  -- * -- * -- * -- * -- * -}

> runBackgroundTasks :: Proc ()
> runBackgroundTasks = do
>   findNewStoreAddr                                                  -- R/W heap nextFreeAddress
>   runDataCache                                                      -- R/W cacheReq heap  W loadBuffer
>   runLoadUnit                                                       -- R/W loadReq rewriteLoadRef inputFifo heap  W cacheReq loadBuffer rewriteLoadResult
>   runLoadGCNodes                                                    -- R/W dropRefs dropAHRefs  W dropLoadRes
>   runRCUpdates                                                      -- R/W refCs W dropRefs dropAHRefs
>   clearRQEntries                                                    -- R/W refQueue rqLastIx  R rqToPop                       W refC*1
>   clearStackPops                                                    -- R/W stackForPop stackDropRef stackForFree R nodeStack  W refC*N
>   spillRefillStack                                                  -- R/W metaStack nodeStack primStack stackMem 
>   runDropGCNode                                                     -- POP dropLoadRes                                        W refC*N
>   runStoreRewrite                                                   -- R   rewriteBuffer aheap W refQueue heap                W refC*(N+1) -- FIXME things go bad when findNewStoreAddr evicts the node to be read by the store rewrite

> readTopMetaNode :: Bool -> Proc MetaSTop  -- Bool if taking out top node ref
> readTopMetaNode tnrs = fmap (if tnrs then (\(_, _, t, ns) -> (SkipRef, (NoNR, NoCV), t, ns)) else id) $ gets (ctrlStack.metaSTop)    -- TODO consider keeping the compacted value to reduce stack spilling effort

> peekTopMetaCont :: Proc ContMeta
> peekTopMetaCont = fmap (fromMaybe NoEvalCont') $ gets (ctrlStack.metaContStack.safePeek)

> readLoadRef :: Either RefUseIndex RefValue -> Proc (RefValue, RCRef)
> readLoadRef (Right r) = return (r, rcNopRef)
> readLoadRef (Left ri) = do
>   (rcm, rx) <- peekAtR ri
>   return (rx, (rcm, rx))

> readExtraPrim :: Checked Word32 -> Maybe PrimIndex -> Proc (Checked PrimValue)
> readExtraPrim mti = fmap toChecked . traverse (peekAtP mti)

> readExtraCont :: (RefUseIndex, RefUseIndex) -> Proc ((RefValue,RefValue), (RCRef,RCRef))
> readExtraCont (x, y) = do
>   (rcma, a) <- peekAtR x
>   (rcmb, b) <- peekAtR y
>   return ((a, b), ((rcma,a), (rcmb,b)))

> readCond :: CondValue QueueIndex -> Checked CondIndex -> Proc (Checked Bool)
> readCond tnc = traverse (fmap (asBool "need bool value") . peekAtC tnc)

> freeStackForPush :: NodeStackCtrl -> Bool  -- used in the rename stage to determine if the stack will be pushed eventually
> freeStackForPush (SNop      ) = False
> freeStackForPush (SPopTop   ) = False
> freeStackForPush (SKeepTop  ) = False
> freeStackForPush (SFixTopRef) = False
> freeStackForPush (SWaitLoad ) = True
> freeStackForPush (SPushNode ) = True
> freeStackForPush (SPushCond ) = True
> freeStackForPush (SPushLoad ) = False   -- the stack top for load result is reserved early (in SWaitLoad)

> pushNewNodeCount :: NodeStackCtrl -> NodeCount
> pushNewNodeCount (SNop      ) = 0
> pushNewNodeCount (SPopTop   ) = 0      
> pushNewNodeCount (SKeepTop  ) = 0
> pushNewNodeCount (SFixTopRef) = 0
> pushNewNodeCount (SWaitLoad ) = 0
> pushNewNodeCount (SPushNode ) = 1
> pushNewNodeCount (SPushCond ) = 1
> pushNewNodeCount (SPushLoad)  = 1

> buildMetaNode :: BuildCtrl -> MetaSTop
> buildMetaNode (BNop      ) = emptyMetaSTop
> buildMetaNode (BNode    t) = (WeakRef, (NoNR , NoCV ), Just t, NodeS )
> buildMetaNode (BCall    t) = (SkipRef, (NoNR , NoCV ), Just t, NodeS )
> buildMetaNode (BCallFix t) = (NeedRef, (HasNR, NoCV ), Just t, NodeS )
> buildMetaNode (BTValue  t) = (WeakRef, (NoNR , HasCV), Just t, NodeS )
> buildMetaNode (BRaw a   t) = (SkipRef, (NoNR , NoCV ), Just t, RawS a)
> buildMetaNode (BPrim    t) = (SkipRef, (NoNR , NoCV ), Just t, PrimS )
> buildMetaNode (BConst _ t) = (WeakRef, (NoNR , HasCV), Just t, PrimS )

> extractPrimVals :: NodeTag -> FixedBody -> PrimVals
> extractPrimVals t nb = Q xh xi xj xk where
>   bm = mapBodyWithKind (OK Nothing) (\case {PrimK -> (\ ~(PVal x) -> OK (Just x)); _ -> const (OK Nothing)}) t nb   -- inserted OK just for elemAt...
>   xh = leftPrim (bm^.elemAt A) (bm^.elemAt E)
>   xi = leftPrim (bm^.elemAt B) (bm^.elemAt F)
>   xj = leftPrim (bm^.elemAt C) (bm^.elemAt G)
>   xk = leftPrim (bm^.elemAt D) (Nothing     )
>   leftPrim p q = toChecked (p `mplus` q)

> buildNode :: BuildCtrl -> ReadBody -> Checked RefValue -> StackRead
> buildNode (BNop      ) _  _               = ((Nothing, Nothing            ), emptyRBody)
> buildNode (BNode    _) rb _               = ((Nothing, Nothing            ), rb        ) 
> buildNode (BCall    _) rb _               = ((Nothing, Nothing            ), rb        )
> buildNode (BCallFix _) rb (OK ~(Ref pt r)) = ((Just (pt,r) , Nothing            ), rb        ) 
> buildNode (BTValue  t) _  _               = ((Nothing, emptyNodeTagValue t), emptyRBody)
> buildNode (BRaw _   _) rb _               = ((Nothing, Nothing            ), rb        )
> buildNode (BPrim    _) _  _               = ((Nothing, Nothing            ), emptyRBody) 
> buildNode (BConst n t) _  _               = ((Nothing, smallBoxValue t nx ), emptyRBody) where nx = fromIntegral n

> buildPrimVals :: BuildCtrl -> PrimVals -> Checked PrimValue -> PrimVals
> buildPrimVals (BNop      ) _  _      = emptyPrimVals
> buildPrimVals (BNode    _) ps _      = ps
> buildPrimVals (BTValue  _) _  _      = emptyPrimVals
> buildPrimVals (BCall    _) ps _      = ps
> buildPrimVals (BCallFix _) ps _      = ps
> buildPrimVals (BRaw _   _) ps _      = ps
> buildPrimVals (BPrim    _) _  (OK x) = Q (OK x ) Bad Bad Bad
> buildPrimVals (BConst n _) _  _      = Q (OK nx) Bad Bad Bad where nx = fromIntegral n

> selectMetaNode :: NodeSelCtrl -> MetaSTop -> Checked (Maybe RefValue, HeapNode) -> MetaSTop -> MetaSTop
> selectMetaNode XNop     _  _                       _  = emptyMetaSTop
> selectMetaNode XBuild   bn _                       _  = bn
> selectMetaNode XUseTop  _  _                       tn = tn
> selectMetaNode XLoadRes _  (OK (mtr, HNode nt xs)) _  = (WeakRef, (hnr, hcv), Just nt, NodeS) where
>   hnr = case mtr of {Just (Ref _ _) -> HasNR; _ -> NoNR}
>   hcv = if (isJust $ compactValueNode nt xs) then HasCV else NoCV   -- TODO think about storing compactibility bit in nodetag when this ends up on the critical path

> selectTopCond :: NodeStackCtrl -> Checked (CondValue QueueIndex) -> Maybe NodeTag -> CondValue QueueIndex -> CondValue QueueIndex
> selectTopCond SPushNode _        (Just t) _   = (Nothing, odd $ tag2Index $ plainTag t)
> selectTopCond SPushLoad _        (Just t) _   = (Nothing, odd $ tag2Index $ plainTag t)
> selectTopCond SPushCond (OK mrc) _        _   = mrc
> selectTopCond _         _        _        otc = otc

> selectStackNode :: NodeSelCtrl -> StackRead -> Checked (Maybe RefValue, HeapNode) -> Checked StackNode -> StackRead
> selectStackNode XNop     _  _                      _                    = ((Nothing,Nothing), emptyRBody)
> selectStackNode XBuild   bn _                      _                    = bn
> selectStackNode XUseTop  _  _                      (OK (StNode mtx xs)) = (maybe (Nothing,Nothing) (\case {Ref pt r -> (Just (pt,r), Nothing); CVRef v -> (Nothing, Just v)}) mtx, over (mapped.mapped) (RCNop,) xs)   
> selectStackNode XLoadRes _  (OK (mtx, HNode t xs)) _                    = ((mtr, compactValueNode t xs), ys) where
>   mtr = case mtx of {Just (Ref pt r) -> Just (pt,r); _ -> Nothing}
>   ys  = over (mapped.mapped) ((rcm),) xs
>   rcm = if isJust mtx && not (isUpdFTag $ plainTag t) then RCInc else RCNop

> selectPrimVals :: NodeSelCtrl -> PrimVals -> Checked HeapNode -> PrimVals -> PrimVals
> selectPrimVals XNop     _  _                 _  = emptyPrimVals
> selectPrimVals XBuild   bn _                 _  = bn
> selectPrimVals XUseTop  _  _                 ys = ys
> selectPrimVals XLoadRes _  (OK (HNode t xs)) _  = extractPrimVals t xs

> selectFirstPrim ::  PrimVals -> Checked PrimValue
> selectFirstPrim (Q hy _ _ _) = hy

> checkEvalStatus :: Bool -> Tag -> Bool
> checkEvalStatus ee t 
>   | ee && not (isValueTag t) = error ("expected eval " ++ show t)
>   | otherwise                = True

> decideEvalUpdApply :: EContCount -> NodeTag -> Checked Bool -> ContMeta -> (RefStatus, ValStatus) -> NodeCount -> (Maybe (Bool,NextInstr), CallFrameCtrl, DemuxUpdateCtrl, ApplyCtrl, FetchCtrl, (StoreCtrl, Checked QueueIndex))
> decideEvalUpdApply e tx@(NodeTag _ _ _ t) hlr cm htrv nc = (fmap (False,) amni, cfi, udi     , aa , fi, (uwi, Bad)) where
>   (aa, fi, uwi, udi, cfi, amni) = decEA e t hlr cm nc
>   decEA _ (Fun f nf WithUpd) (OK True ) _     _  = (PushUpdate   , funFetch nf, WNop       , DemuxLoadFun  , CFPushEval  , Just $ BranchTo $ snd f     )
>   decEA _ (Fun f nf WithUpd) (OK False) _     _  = (ApplyNop     , funFetch nf, WNop       , DemuxLoadFun  , CFPushEval  , Just $ BranchTo $ snd f     )
>   decEA _ (Fun f nf SkipUpd) (OK False) _     _  = (ApplyNop     , funFetch nf, WNop       , DemuxLoadGen  , CFPushEval  , Just $ BranchTo $ snd f     )
>   decEA _ (FE ef    WithUpd) (OK True ) _     _  = (PushUpdate   , FNodeArg A , WNop       , DemuxLoadFun  , CFPushEval  , Just $ decodeEvalFunCont ef )
>   decEA _ (FE ef    WithUpd) (OK False) _     _  = (ApplyNop     , FNodeArg A , WNop       , DemuxLoadFun  , CFPushEval  , Just $ decodeEvalFunCont ef ) 
>   decEA _ (FE ef    SkipUpd) (OK False) _     _  = (ApplyNop     , FNodeArg A , WNop       , DemuxLoadGen  , CFPushEval  , Just $ decodeEvalFunCont ef ) 
>   decEA _ (Ind             ) _ _              _  = (ApplyNop     , FNodeArg A , WNop       , DemuxLoadInd  , CFNop       , Just $ EvalLoad False       )   -- FIXME is directly using the load result with FLoadArg the best thing to do ???
>   decEA 0 (Excep           ) _ _              1  = (ApplyNop     , FNop       , WNop       , NoUpdate      , CFContinue  , Just $ unwindNodes 1        )   -- pop cleared call frame before unwinding next
>   decEA 0 (Excep           ) _ _              nc = (ApplyNop     , FNop       , WNop       , NoUpdate      , CFNop       , Just $ unwindNodes nc       )   -- still have some node stack to clear
>   decEA _ (Excep           ) _ (WithCatch'  ) 1  = (UseCatch     , FApplyLoad , WNop       , NoUpdate      , CFEnterApply, Just $ EvalJump (Apply1 A)  )   -- apply the prefetched handler to the exception on the stack
>   decEA _ (Excep           ) _ (WithCatch'  ) nc = (ApplyNop     , FNop       , WNop       , NoUpdate      , CFNop       , Just $ unwindNodes nc       )   -- still have some node stack to clear
>   decEA _ (Excep           ) _ _              nc = (dropExCont cm, FNop       , WNop       , NoUpdate      , CFNop       , Just $ unwindNodes nc       )   -- clearing application stack
>   decEA 0 _                  _ _              _  = (ApplyNop     , FNop       , WNop       , NoUpdate      , CFContinue  , Nothing                     )   -- the default case that just pops the callframe
>   decEA _ _                  _ (WithCatch'  ) _  = (DropECont  cm, FNop       , WNop       , NoUpdate      , CFContinue  , Nothing                     )   -- dropping catch frame
>   decEA _ (Box  c          ) _ (Update'     ) _  = (UseUpdate    , FNop       , wu         , du            , CFContinue  , Nothing                     ) where (du,wu) = decideBoxUpdate tx htrv
>   decEA _ _                  _ (Update'     ) _  = (UseUpdate    , FNop       , wu         , du            , CFContinue  , Nothing                     ) where (du,wu) = decideUpdate tx htrv
>   decEA _ _                  _ (ThenFetch'  ) _  = (StartPreFetch, FApplyLoad , WNop       , NoUpdate      , CFContinue  , Nothing                     )
>   decEA _ (Box  c          ) _ (MaskFetch' m) _  = (ax           , fx         , WNop       , NoUpdate      , CFContinue  , Nothing                     ) where (ax,fx) = maskedFetch c m
>   decEA _ (Con  c          ) _ (MaskFetch' m) _  = (ax           , fx         , WNop       , NoUpdate      , CFContinue  , Nothing                     ) where (ax,fx) = maskedFetch c m 
>   decEA _ (Box  _          ) _ (WithPrim' p ) _  = (ApplyPrim  p , FNop       , WNop       , NoUpdate      , CFContinue  , Nothing                     )
>   decEA _ (Con  _          ) _ (Select' i   ) _  = (DropSelect   , FNodeArg i , WNop       , NoUpdate      , CFEnterApply, Just $ EvalJump NoEvalCont  )
>   decEA _ (Unboxed         ) _ (Select' i   ) _  = (DropSelect   , FNodeArg i , WNop       , NoUpdate      , CFEnterApply, Just $ EvalJump NoEvalCont  )
>   decEA _ (DCon _   _      ) _ (ApplyN' a   ) _  = (applyOneOf a , FNop       , WNop       , NoUpdate      , CFContinue  , Nothing                     )   -- overapplication of DCon cannot happen
>   decEA _ (HCon _   _      ) _ (ApplyN' a   ) _  = (applyOneOf a , FNop       , WNop       , NoUpdate      , CFContinue  , Nothing                     )   -- idem
>   decEA _ (Pap f nf 1      ) _ (ApplyN' a   ) _  = (applyOneOf a , FNop       , WNop       , NoUpdate      , CFEnterApply, Just $ BranchTo $ snd f     )   -- TODO start preloading the next fetch 
>   decEA _ (Pap _ _  _      ) _ (ApplyN' a   ) _  = (applyOneOf a , FNop       , WNop       , NoUpdate      , CFContinue  , Nothing                     ) 
>   decEA _ (HFun f nf _     ) _ (ApplyN' a   ) _  = (applyOneOf a , FNop       , WNop       , NoUpdate      , CFEnterApply, Just $ BranchTo $ snd f     )   -- TODO start preloading the next fetch 
>   decEA _ (PE (E_sel i) 1  ) _ (ApplyN' a   ) _  = (useOneOf a   , FApplyLoad , WNop       , NoUpdate      , CFEnterApply, Just $ EvalJump (Select i)  )   -- FIXME generalize for other eval funs
>   decEA _ (PE (E_id   ) 1  ) _ (ApplyN' a   ) _  = (useOneOf a   , FApplyLoad , WNop       , NoUpdate      , CFEnterApply, Just $ EvalJump NoEvalCont  )   -- idem
>   decEA _ _                  _ _              _  = error (show cm ++ " on " ++ show tx ++ "   ec: " ++ show e)

> funFetch :: NextFetch -> FetchCtrl
> funFetch (Nothing) = FNop
> funFetch (Just fe) = FNextArg fe

> decideUpdate :: NodeTag -> (RefStatus, ValStatus) -> (DemuxUpdateCtrl, StoreCtrl)
> decideUpdate tx (_    , HasCV) = (UpdateCNodeVal, WUpdCVal tx)   -- simple update without indirection for compacted Ref value
> decideUpdate tx (HasNR, NoCV ) = (UpdateWithRef , WUpdRef    )
> decideUpdate tx (NoNR , NoCV ) = (UpdateWithN pt, WUpdNode tx) where pt = node2PtrTag tx -- TODO think about UpdateWithN in case of inderections, is not ideal here because then topref refers to an indirection -- also maybe use indirection for all size mismatches

> decideBoxUpdate :: NodeTag -> (RefStatus, ValStatus) -> (DemuxUpdateCtrl, StoreCtrl)
> decideBoxUpdate tx (NoNR , NoCV ) = (UpdateWithN pt, WUpdBox  tx) where pt = node2PtrTag tx
> decideBoxUpdate tx (HasNR, NoCV ) = (UpdateWithRef , WUpdRef    )
> decideBoxUpdate tx (_    , HasCV) = (UpdateCNodeVal, WUpdBox  tx)

> maskedFetch :: ConAlt -> Word8 -> (ApplyCtrl, FetchCtrl)
> maskedFetch c m
>   | m `testBit` (fromIntegral (snd c) `mod` 8) = (StartPreFetch           , FApplyLoad)
>   | otherwise                                  = (DropECont $ MaskFetch' m, FNop      ) 

> applyOneOf :: Word8 -> ApplyCtrl
> applyOneOf 1 = NodeApplyLast
> applyOneOf _ = NodeApplyNext

> useOneOf :: Word8 -> ApplyCtrl
> useOneOf 1 = NodeApplyLast
> useOneOf _ = NodeApplyNext

> dropExCont :: ContMeta -> ApplyCtrl   -- dealing special case of clearing references in apply chain one by one
> dropExCont (ApplyN' 1) = DropECont $ ApplyN' 1
> dropExCont (ApplyN' _) = DropNextAp
> dropExCont cm          = DropECont cm

> unwindNodes :: NodeCount -> NextInstr
> unwindNodes 1 = Unwinding $ popNone
> unwindNodes _ = Unwinding $ popNext   -- clear the node stack one by one, popping more can not be sustained

> decodeEvalFunCont :: EvalFun -> NextInstr
> decodeEvalFunCont (E_ap1  ) = EvalJump (Apply1 B  )
> decodeEvalFunCont (E_ap2  ) = EvalJump (Apply2 B C)
> decodeEvalFunCont (E_sel i) = EvalJump (Select i  )

> runMetaUpdate :: DemuxUpdateCtrl -> (RefStatus, ValStatus) -> (RefStatus, ValStatus)
> runMetaUpdate (NoUpdate      ) ms             = ms
> runMetaUpdate (UpdateWithN  _) (NoNR , NoCV ) = (HasNR, NoCV )
> runMetaUpdate (UpdateWithRef ) (HasNR, NoCV ) = (HasNR, NoCV )
> runMetaUpdate (UpdateCNodeVal) (hnr  , HasCV) = (hnr  , HasCV)
> runMetaUpdate (DemuxLoadFun  ) (_    , NoCV ) = (NoNR , NoCV )
> runMetaUpdate (DemuxLoadGen  ) (_    , NoCV ) = (NoNR , NoCV )
> runMetaUpdate (DemuxLoadInd  ) (_    , NoCV ) = (NoNR , NoCV )

> data ExtraRCUpdate = NoRCU | ExRCU
> hasUpdateSplit :: DemuxUpdateCtrl -> ExtraRCUpdate
> hasUpdateSplit (UpdateWithN _ ) = ExRCU
> hasUpdateSplit (UpdateCNodeVal) = ExRCU  -- compact values have no refs so ExtraRCUpdate is only token for node going to both stack and store
> hasUpdateSplit _                = NoRCU

> nodeBodyRCUpdates :: Maybe NodeTag -> NodeShape -> ExtraRCUpdate -> TopBodyFix -> ReadBody -> (FB (Maybe RCRef), FixedBody)
> nodeBodyRCUpdates (Nothing) _      _     _        _  = (emptyBody, emptyNBody)                            -- no tag implies xs is an empty body
> nodeBodyRCUpdates (Just  _) EmptyS _     _        _  = (emptyBody, emptyNBody)                            -- FIXME workaround for mismatch between tag arity and body size for bodyless nodes
> nodeBodyRCUpdates (Just  _) PrimS  _     _        _  = (emptyBody, emptyNBody)                            -- idem ^^ for Prim shaped nodes
> nodeBodyRCUpdates (Just  t) _      NoRCU KeepBody xs = readValuesRCs id         t xs
> nodeBodyRCUpdates (Just  t) _      NoRCU DropBody xs = readValuesRCs extraRCDec t xs & _2 .~ emptyNBody   -- dropping unused body
> nodeBodyRCUpdates (Just  t) _      ExRCU KeepBody xs = readValuesRCs extraRCInc t ds where ds = over (mapped.mapped._2.withRef) shareRef xs
> nodeBodyRCUpdates (Just  t) _      ExRCU DropBody xs = readValuesRCs id         t xs                      -- not duplicating unused body but keeping it for update store

> demuxUpdNode :: DemuxUpdateCtrl -> TopRefFix -> TopBodyFix -> Checked (PtrTag, HeapRef) -> TempTopRV -> FixedBody -> ((RCRef, RCRef), StackNode, FixedBody)
> demuxUpdNode (NoUpdate      ) trf      tbf _       mtx          xs = ((rcNopRef  , rctrs     ), demStBody tbf mxr       xs, xs        ) where (rctrs, mxr) = combineDropNRs mtx trf
> demuxUpdNode (UpdateCNodeVal) trf      tbf (OK ur) mtx          xs = ((decURef ur, rctrs     ), demStBody tbf mxr       xs, xs        ) where (rctrs, mxr) = combineDropNRs mtx trf
> demuxUpdNode (UpdateWithRef ) MergeRef tbf (OK ur) (Just tr, _) xs = ((decURef ur, (RCInc,xt)), demStBody tbf (Just xt) xs, ib        ) where {xt = shareRef $ uncurry Ref tr; ib = unaryBody $ RVal xt}
> demuxUpdNode (UpdateWithRef ) _        tbf (OK ur) (Just tr, _) xs = ((decURef ur, rcNopRef  ), demStBody tbf (Nothing) xs, ib        ) where ib = unaryBody $ RVal $ uncurry Ref tr  -- skip duplicating unneeded topref  
> demuxUpdNode (UpdateWithN pt) MergeRef tbf (OK ur) (Nothing, _) xs = ((rcNopRef  , rcNopRef  ), demStBody tbf (Just xu) xs, xs        ) where xu = Ref pt (snd ur)                    -- set top node ref after update
> demuxUpdNode (UpdateWithN _ ) _        tbf (OK ur) (Nothing, _) xs = ((decURef ur, rcNopRef  ), demStBody tbf (Nothing) xs, xs        )                                               -- drop unneeded topref
> demuxUpdNode (DemuxLoadFun  ) _        tbf _       _            xs = ((rcNopRef  , rcNopRef  ), demStBody tbf (Nothing) xs, emptyNBody)
> demuxUpdNode (DemuxLoadGen  ) _        tbf _       mtx          xs = ((rcNopRef  , rctrs     ), demStBody tbf (Nothing) xs, emptyNBody) where (rctrs, mxr) = combineDropNRs mtx DropBoth
> demuxUpdNode (DemuxLoadInd  ) _        _   _       mtx          xs = ((rcNopRef  , rctrs     ), demStBody tbf mxr       xs, emptyNBody) where {(rctrs, mxr) = combineDropNRs mtx DropBoth; tbf = KeepBody}

> decURef :: (PtrTag, HeapRef) -> RCRef
> decURef (_, ur) = (RCDec, Ref TX ur)

> demStBody :: TopBodyFix -> Maybe RefValue -> FixedBody -> StackNode
> demStBody KeepBody mxr xs = StNode mxr xs       
> demStBody DropBody mxr _  = StNode mxr emptyNBody

> combineDropNRs :: TempTopRV -> TopRefFix -> (RCRef, Maybe RefValue) -- dropped heapref, combined node reference
> combineDropNRs (Nothing    , Nothing) _        = (rcNopRef         , Nothing        )
> combineDropNRs (Nothing    , Just _ ) DropBoth = (rcNopRef         , Nothing        )
> combineDropNRs (Nothing    , Just cv) _        = (rcNopRef         , Just $ CVRef cv)     -- preserving mcv just for stack spiller
> combineDropNRs (Just (pt,r), Just _ ) DropBoth = ((RCDec, Ref pt r), Nothing        )
> combineDropNRs (Just (pt,r), Just cv) _        = ((RCDec, Ref pt r), Just $ CVRef cv)
> combineDropNRs (Just (pt,r), Nothing) MergeRef = (rcNopRef         , Just $ Ref pt r)
> combineDropNRs (Just (pt,r), Nothing) _        = ((RCDec, Ref pt r), Nothing        )

> mayApplyMerge :: CallFrameCtrl -> EContCount -> EContCount -> Bool
> mayApplyMerge (CFNop                ) 0 _ = False  -- nothing to merge with
> mayApplyMerge (CFNop                ) _ _ = True   -- merge with extra applications, only happens when codegenerator is stupid
> mayApplyMerge (CFPushCall ReturnNext) 0 0 = False  -- nothing to merge with in next frame
> mayApplyMerge (CFPushCall ReturnNext) 0 _ = True   -- merge with other call frame in tail call
> mayApplyMerge (CFPushCall _         ) _ _ = True   -- merge with extra applications, only happens when codegenerator is stupid
> mayApplyMerge _                       _ _ = False

> decideApplyMerge :: Bool -> ApplyCtrl -> ContMeta -> ApplyCtrl  -- TODO think about reordering continuations, moving ThenFetch towards top over call/effect free ones
> decideApplyMerge True (PushApply (WithPrim' OpAdd)) (WithPrim' OpAdd) = MergePrimAp OpAdd -- TODO add other simple operator combinations
> decideApplyMerge True (PushApply (ApplyN' n      )) (ApplyN' _      ) = MergeApply n
> decideApplyMerge _    ax                              _               = ax

> addNewApply :: EContCount -> ApplyCtrl -> EContCount
> addNewApply xc (PushApply _ ) = xc+1
> addNewApply xc (PushUpdate  ) = xc+1
> addNewApply xc (PushFixRef  ) = xc+1
> addNewApply xc _              = xc

> subUsedApply :: EContCount -> ApplyCtrl -> EContCount
> subUsedApply ec (ApplyNop     ) = ec
> subUsedApply ec (ApplyToStore ) = ec
> subUsedApply ec (PushApply _  ) = ec
> subUsedApply ec (PushUpdate   ) = ec
> subUsedApply ec (PushFixRef   ) = ec
> subUsedApply ec (MergeApply _ ) = ec
> subUsedApply ec (MergePrimAp _) = ec
> subUsedApply ec (DropSelect   ) = ec-1
> subUsedApply ec (DropECont  _ ) = ec-1
> subUsedApply ec (DropNextAp   ) = ec
> subUsedApply ec (UseCatch     ) = ec-1
> subUsedApply ec (StartPreFetch) = ec-1
> subUsedApply ec (UseUpdate    ) = ec-1
> subUsedApply ec (ApplyPrim _  ) = ec-1
> subUsedApply ec (NodeApplyLast) = ec-1
> subUsedApply ec (NodeApplyNext) = ec
> subUsedApply ec (UseApplyLast ) = ec-1
> subUsedApply ec (UseApplyNext ) = ec

> runMetaApplyStack :: ApplyCtrl -> Proc ()
> runMetaApplyStack (ApplyNop     ) = return ()
> runMetaApplyStack (ApplyToStore ) = return ()
> runMetaApplyStack (PushApply cm ) = ctrlStack.metaContStack %= push cm
> runMetaApplyStack (PushUpdate   ) = ctrlStack.metaContStack %= push (Update')
> runMetaApplyStack (PushFixRef   ) = ctrlStack.metaContStack %= push (Update')
> runMetaApplyStack (MergeApply n ) = ctrlStack.metaContStack.top._ApplyN %= (+n)
> runMetaApplyStack (MergePrimAp _) = return ()      -- just keep the existing prim apply -- TODO need changes for more complex cases
> runMetaApplyStack (DropSelect   ) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (DropECont  _ ) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (DropNextAp   ) = ctrlStack.metaContStack.top._ApplyN %= pred
> runMetaApplyStack (UseCatch     ) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (StartPreFetch) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (UseUpdate    ) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (ApplyPrim  _ ) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (NodeApplyLast) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (NodeApplyNext) = ctrlStack.metaContStack.top._ApplyN %= pred
> runMetaApplyStack (UseApplyLast ) = ctrlStack.metaContStack %= pop
> runMetaApplyStack (UseApplyNext ) = ctrlStack.metaContStack.top._ApplyN %= pred

> applyToTag :: NodeTag -> Arity -> UpdateFlag -> (NodeTag, NodeElem)
> applyToTag (NodeTag _ n vs (Pap  f ni b )) ac uf | ac == b = (NodeTag Dynamic (n+ac) vs $ Fun f ni uf      , ae) where ae = toEnum $ fromEnum n
> applyToTag (NodeTag _ n vs (Pap  f ni b )) ac _  | ac <  b = (NodeTag Dynamic (n+ac) vs $ Pap f ni (b - ac), ae) where ae = toEnum $ fromEnum n
> applyToTag (NodeTag _ n vs (HFun f ni ae)) ac uf | ac == 1 = (NodeTag Dynamic n      vs $ Fun f ni uf      , ae)   -- arity doesn't change because of just filling in an undefined argument
> applyToTag (NodeTag _ n vs (DCon c    b )) ac _  | ac == b = (NodeTag Dynamic (n+ac) vs $ Con  c           , ae) where ae = toEnum $ fromEnum n
> applyToTag (NodeTag _ n vs (DCon c    b )) ac _  | ac <  b = (NodeTag Dynamic (n+ac) vs $ DCon c   (b - ac), ae) where ae = toEnum $ fromEnum n
> applyToTag (NodeTag _ n vs (HCon c    ae)) ac _  | ac == 1 = (NodeTag Dynamic n      vs $ Con  c           , ae)   -- arity doesn't change because of just filling in an undefined argument
> applyToTag (NodeTag _ n vs (PE ef     b )) ac uf | ac == b = (NodeTag Dynamic (n+ac) vs $ FE ef    uf      , ae) where ae = toEnum $ fromEnum n
> applyToTag (NodeTag _ n vs (PE ef     b )) ac uf | ac <  b = (NodeTag Dynamic (n+ac) vs $ PE ef    (b - ac), ae) where ae = toEnum $ fromEnum n
> applyToTag t                               ac _            = error ("applying " ++ show ac ++ " to " ++ show t)

> applyToMetaTag :: ApplyCtrl -> Maybe NodeTag -> NodeShape -> (Maybe NodeTag, Checked NodeElem, NodeShape)
> applyToMetaTag (ApplyPrim _  ) (Just t) _  = (Just t , Bad  , PrimS)
> applyToMetaTag (NodeApplyLast) (Just t) _  = (Just t', OK ae, NodeS) where (t', ae) = applyToTag t 1 SkipUpd
> applyToMetaTag (NodeApplyNext) (Just t) _  = (Just t', OK ae, NodeS) where (t', ae) = applyToTag t 1 SkipUpd
> applyToMetaTag _               mt       ns = (mt     , Bad  , ns   )

> updateApplyStack :: ApplyCtrl -> TopBodyFix -> Checked RefValue -> ((RefValue,RefValue), (RCRef, RCRef)) -> Checked (Maybe RefValue) -> Checked RefValue -> Proc (RCRef, RCRef)
> updateApplyStack (ApplyNop     ) _        _      _   _ _            =                                         return (rcNopRef , rcNopRef )
> updateApplyStack (ApplyToStore ) _        _      cvs _ _            =                                         return (snd cvs)  -- only for RC updates
> updateApplyStack (PushApply cm ) _        _      cvs _ _            = pushExtraApply cm          (fst cvs) >> return (snd cvs)
> updateApplyStack (MergeApply 1 ) _        _      cvs _ _            = pushExtraApply (ApplyN' 1) (fst cvs) >> return (snd cvs)
> updateApplyStack (MergeApply 2 ) _        _      cvs _ _            = pushExtraApply (ApplyN' 2) (fst cvs) >> return (snd cvs)
> updateApplyStack (MergePrimAp _) _        _      _   _ _            =                                         return (rcNopRef , rcNopRef )
> updateApplyStack (PushUpdate   ) _        _      _ ~(OK (Just r)) _ = dataPath.contStack %= push r         >> return (rcNopRef , rcNopRef )
> updateApplyStack (PushFixRef   ) _        _      _   _ ~(OK r)      = dataPath.contStack %= push r         >> return (rcNopRef , rcNopRef )
> updateApplyStack (UseCatch     ) _        _      _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )
> updateApplyStack (StartPreFetch) _        _      _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )
> updateApplyStack (UseUpdate    ) _        (OK _) _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )  -- TODO figure out where update ref counter-update is done best
> updateApplyStack (ApplyPrim  _ ) _        _      _   _ _            =                                         return (rcNopRef , rcNopRef )
> updateApplyStack (NodeApplyLast) KeepBody (OK _) _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )
> updateApplyStack (NodeApplyLast) DropBody (OK a) _   _ _            = dataPath.contStack %= pop            >> return ((RCDec,a), rcNopRef )
> updateApplyStack (NodeApplyNext) KeepBody (OK _) _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )
> updateApplyStack (NodeApplyNext) DropBody (OK a) _   _ _            = dataPath.contStack %= pop            >> return ((RCDec,a), rcNopRef )
> updateApplyStack (UseApplyLast ) KeepBody _      _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )
> updateApplyStack (UseApplyNext ) KeepBody _      _   _ _            = dataPath.contStack %= pop            >> return (rcNopRef , rcNopRef )
> updateApplyStack (DropSelect   ) _        _      _   _ _            =                                         return (rcNopRef , rcNopRef )
> updateApplyStack (DropECont  cm) _        avs    _   _ _            = dropTopCont cm avs                                                     -- TODO consider ignoring these rare RC decrements
> updateApplyStack (DropNextAp   ) _        (OK a) _   _ _            = dataPath.contStack %= pop            >> return ((RCDec,a), rcNopRef )

> pushExtraApply :: ContMeta -> (RefValue,RefValue) -> Proc ()
> pushExtraApply (ApplyN' 1   ) (x, _) = dataPath.contStack %= push x
> pushExtraApply (ApplyN' 2   ) (x, y) = dataPath.contStack %= (push x . push y)
> pushExtraApply (Select' _   ) (_, _) = return ()
> pushExtraApply (ThenFetch'  ) (x, _) = dataPath.contStack %= push x
> pushExtraApply (MaskFetch' _) (x, _) = dataPath.contStack %= push x
> pushExtraApply (WithCatch'  ) (x, _) = dataPath.contStack %= push x
> pushExtraApply (WithPrim' _ ) (_, _) = return ()
> pushExtraApply cm             _      = error ("pushExtraApply" ++ show cm)

> dropTopCont :: ContMeta -> Checked RefValue -> Proc (RCRef, RCRef)
> dropTopCont (NoEvalCont' ) (_   ) =                               return (rcNopRef , rcNopRef )
> dropTopCont (Update'     ) (OK x) = dataPath.contStack %= pop  >> return ((RCDec,x), rcNopRef )
> dropTopCont (ApplyN' 1   ) (OK x) = dataPath.contStack %= pop  >> return ((RCDec,x), rcNopRef )
> dropTopCont (Select' _   ) (_   ) =                               return (rcNopRef , rcNopRef )
> dropTopCont (ThenFetch'  ) (OK x) = dataPath.contStack %= pop  >> return ((RCDec,x), rcNopRef )
> dropTopCont (MaskFetch' _) (OK x) = dataPath.contStack %= pop  >> return ((RCDec,x), rcNopRef )
> dropTopCont (WithCatch'  ) (OK x) = dataPath.contStack %= pop  >> return ((RCDec,x), rcNopRef )
> dropTopCont (WithPrim' _ ) (_   ) =                               return (rcNopRef , rcNopRef )

> updatePrimApStack :: ApplyCtrl -> Checked PrimValue -> Proc ()
> updatePrimApStack (PushApply (WithPrim' _)) (OK x) = primSide.primContStack %= push x
> updatePrimApStack (MergePrimAp px         ) (OK x) = primSide.primContStack.top %= execPrimOp px True x
> updatePrimApStack (ApplyPrim  _           ) _      = primSide.primContStack %= pop
> updatePrimApStack (DropECont (WithPrim' _)) _      = primSide.primContStack %= pop
> updatePrimApStack _                         _      = return ()

> applyToBody :: ApplyCtrl -> Checked NodeElem -> TopBodyFix -> Checked RefValue -> StackNode -> StackNode   -- clearing of NodeRefs is done elsewhere
> applyToBody (ApplyPrim _  ) _      _        (_   ) = stNBody .~ emptyNBody                           -- here we assume the node body has no refs
> applyToBody (NodeApplyLast) (OK e) KeepBody (OK a) = stNBody.elemAt e .~ RVal a
> applyToBody (NodeApplyLast) (OK _) DropBody (OK _) = id                                              -- skip applying if body will be dropped  -- TODO are these special cases really needed?
> applyToBody (NodeApplyNext) (OK e) KeepBody (OK a) = stNBody.elemAt e .~ RVal a
> applyToBody (NodeApplyNext) (OK _) DropBody (OK _) = id                                              -- skip applying if body will be dropped
> applyToBody _               _      _        (_   ) = id

> applyToPrimVals :: ApplyCtrl -> Maybe PrimValue -> PrimVals -> PrimVals
> applyToPrimVals (ApplyPrim p) (Just x) = primAt H %~ execPrimOp p True x
> applyToPrimVals _             _        = id

> dropLoadedArg :: FetchCtrl -> StackNode -> StackNode
> dropLoadedArg (FNodeArg e) = stNBody.elemAt e .~ (RVal $ CVRef VoidRef)
> dropLoadedArg (FNextArg e) = stNBody.elemAt e .~ (RVal $ CVRef FetchedRef)
> dropLoadedArg _            = id

> decideContinue ::  Maybe (Bool, NextInstr) -> EContCount -> Continuation -> Maybe Tag -> (Maybe StackResult, NextInstr)
> decideContinue (Nothing         ) 0 c (Just t) = calcContinue c t 
> decideContinue (Nothing         ) _ _ _        = (Nothing     , Continue)  -- more 'applications' to do
> decideContinue (Just (False, ni)) _ _ _        = (Nothing     , ni      )  -- NextInstr determined by the 'application'
> decideContinue (Just (True , ni)) _ _ _        = (Just OnlyTag, ni      )  -- dropping refs for ClearRefs instr, implied by asking for OnlyTag

> calcContinue :: Continuation -> Tag -> (Maybe StackResult, NextInstr)
> calcContinue (ThreadFinish       ) _ = (Nothing, Continue)
> calcContinue (ReturnNext         ) _ = (Nothing, Continue)
> calcContinue (ReturnTo    sp _  r) _ = (Just sp, BranchTo r)
> calcContinue (IntoWhen       eo r) _ = (Nothing, DecideBr r eo)
> calcContinue (IntoBigCase sp om r) t = (Just sp, BranchTo . relJump r . RelCodeAddr . (`shiftL` fst om) . (.&. ((1 `shiftL` snd om) - 1)) . fromIntegral $ getAltIndex t)
> calcContinue (IntoCase    sp xs r) t = case caseAltTarget xs t of
>   Left (_, o)                       -> (Just sp, BranchTo $ relJump r o)
>   Right ps | ps == popNone          -> (Nothing, Continue)      -- nothing to pop from stack thus continue on fast path
>            | otherwise              -> (Nothing, Returning ps)

> appliesToStackTop :: ApplyCtrl -> Bool
> appliesToStackTop (ApplyPrim     _) = True
> appliesToStackTop (NodeApplyLast  ) = True
> appliesToStackTop (NodeApplyNext  ) = True
> appliesToStackTop _                 = False

> decideFixup :: Maybe StackResult -> (RefStatus, ValStatus) -> ApplyCtrl -> (RefNeed, TopRefFix, TopBodyFix)  -- first Bool is has node value, second Bool is with application
> decideFixup sr htrv ai = decFix sr (case ai of {UseUpdate -> True; _ -> fst htrv == HasNR || snd htrv == HasCV}) (appliesToStackTop ai) where
>   decFix (Nothing      ) _   app = (WeakRef, (if app then DropBoth else MergeRef), KeepBody)  -- here we don't know yet what is expected on the top of the stack
>   decFix (Just NodeWSC ) _   app = (NeedRef, (if app then DropBoth else MergeRef), KeepBody)
>   decFix (Just OnlyNode) _   app = (SkipRef, (if app then DropBoth else DropNRef), KeepBody)
>   decFix (Just OnlyTag ) _   app = (SkipRef, (if app then DropBoth else DropNRef), DropBody)
>   decFix (Just OnlySC  ) htr app = (OnlyRef, (if app then DropBoth else MergeRef), tbf     ) where tbf = if htr && not app then DropBody else KeepBody  -- keep body because when no correct ref is avaible

> runMetaTopFix :: (RefNeed, TopRefFix, TopBodyFix) -> MetaSTop -> MetaSTop
> runMetaTopFix (xnr, fr, fb) (nr, hnrcv, mt, ns) = (case xnr of {WeakRef -> nr; _ -> xnr}, combineNRInfo fr hnrcv, mt, case fb of {DropBody -> EmptyS; KeepBody -> ns})

> combineNRInfo :: TopRefFix -> (RefStatus, ValStatus) -> (RefStatus, ValStatus)
> combineNRInfo MergeRef (hnr, hcv) = (hnr', hcv ) where hnr' = if hcv == HasCV then NoNR else hnr
> combineNRInfo DropNRef (_  , hcv) = (NoNR, hcv )   -- preserving compact value just for stack spiller
> combineNRInfo DropBoth _          = (NoNR, NoCV)

> setMetaStackTop :: NodeStackCtrl -> Bool -> MetaSTop -> Proc ()  -- Bool if taking out top node ref
> setMetaStackTop (SNop      ) ttnr _  = ctrlStack.metaSTop %= (if ttnr then (\(_,_,t,ns) -> (SkipRef, (NoNR, NoCV), t, ns)) else id)   -- TODO consider keeping the compacted value to reduce stack spilling effort
> setMetaStackTop (SPopTop   ) _    _  = ctrlStack.metaSTop .= emptyMetaSTop
> setMetaStackTop (SWaitLoad ) _    _  = ctrlStack.metaSTop .= emptyMetaSTop
> setMetaStackTop (SKeepTop  ) _    mn = ctrlStack.metaSTop .= mn
> setMetaStackTop (SPushNode ) _    mn = ctrlStack.metaSTop .= mn
> setMetaStackTop (SPushCond ) _    mn = ctrlStack.metaSTop .= mn
> setMetaStackTop (SPushLoad ) _    mn = ctrlStack.metaSTop .= mn
> setMetaStackTop (SFixTopRef) _    _  = ctrlStack.metaSTop._2._1 .= HasNR

> adjustMetaStack :: StackPushDown -> MetaSTop -> Quad (Maybe StackPos) -> Proc ()
> adjustMetaStack stm mstn nris = do
>   Data.Foldable.mapM_ (\case {Just (Deep si) -> withMetaFrom si (\(StMeta _ HasNR t s) -> StMeta SkipRef NoNR t s); _ -> return ()}) nris
>   pushDownMetaStack stm mstn

> pushDownMetaStack :: StackPushDown -> MetaSTop -> Proc ()
> pushDownMetaStack (PushDownNop  ) _  = return ()
> pushDownMetaStack (FixNodeRef xi) _  = withMetaFrom xi (\(StMeta rn _ t s) -> StMeta rn HasNR t s)
> pushDownMetaStack (PushDownTo xi) mn = do
>   let (ntr, (hnr, hcv), Just t, s) = mn
>   let htr = if hcv == HasCV then HasNR else (if (ntr == NeedRef || ntr == OnlyRef) then hnr else NoNR)   -- nodeRef is dropped only if it is a true reference and not required
>   poking (ctrlStack.metaSRegs) xi (OK (StMeta ntr htr t s))

> setStackTop :: NodeStackCtrl -> Checked RefValue -> StackNode -> Proc ()
> setStackTop (SNop      ) _       _  = return ()
> setStackTop (SPopTop   ) _       _  = dataPath.stackTop .= Bad  -- pushdown from popping stacktop
> setStackTop (SWaitLoad ) _       _  = dataPath.stackTop .= Bad
> setStackTop (SKeepTop  ) _       sn = dataPath.stackTop .= OK sn
> setStackTop (SPushNode ) _       sn = dataPath.stackTop .= OK sn
> setStackTop (SPushCond ) _       sn = dataPath.stackTop .= OK sn
> setStackTop (SPushLoad ) _       sn = dataPath.stackTop .= OK sn
> setStackTop (SFixTopRef) ~(OK r) _  = dataPath.stackTop.checked.stNRef .= Just r

> setPrimStackTop :: NodeStackCtrl -> PrimVals -> Proc ()
> setPrimStackTop (SNop      ) _  = return ()
> setPrimStackTop (SPopTop   ) _  = primSide.primSTop .= emptyPrimVals
> setPrimStackTop (SWaitLoad ) _  = primSide.primSTop .= emptyPrimVals
> setPrimStackTop (SKeepTop  ) ys = primSide.primSTop .= ys
> setPrimStackTop (SPushNode ) ys = primSide.primSTop .= ys
> setPrimStackTop (SPushCond ) _  = primSide.primSTop .= emptyPrimVals
> setPrimStackTop (SPushLoad ) ys = primSide.primSTop .= ys
> setPrimStackTop (SFixTopRef) _  = return ()

> pushDownStack :: StackPushDown -> RefNeed -> Checked StackNode -> Checked RefValue -> Proc ()
> pushDownStack (PushDownNop  ) _   _      _      = return ()
> pushDownStack (FixNodeRef xi) _   _      (OK r) = withNodeFrom xi (\(StNode _ xs) -> ((), StNode (Just r) xs)) >> return ()
> pushDownStack (PushDownTo xi) ntr (OK n) _      = do
>   poking (dataPath.stackRegs) xi (OK n)
>   let hasRefValue = case n^.stNRef of {Just (Ref _ _) -> True; _ -> False }
>   unless (ntr == NeedRef || ntr == OnlyRef || not hasRefValue) $ do  -- nodeRef is dropped only if it is a true reference and not required
>      rcUnit.stackDropRef.stMaskAt xi .= True

> pushDownPrimStack :: StackPushDown -> PrimVals -> Proc ()
> pushDownPrimStack (PushDownNop  ) _  = return ()
> pushDownPrimStack (FixNodeRef _ ) _  = return ()
> pushDownPrimStack (PushDownTo xi) ys = poking (primSide.primStack) xi (OK ys)

> setStackPops :: Quad (Maybe StackIndex) -> Proc ()
> setStackPops = traverse_ setSP where
>   setSP (Nothing) = return ()
>   setSP (Just ip) = rcUnit.stackForPop.stMaskAt ip .= True

> advancesLdBuff :: FetchCtrl -> Bool
> advancesLdBuff (FNop      ) = False
> advancesLdBuff (FEvalRef  ) = True
> advancesLdBuff (FUsePre   ) = False  -- uses already reserved buffer entry
> advancesLdBuff (FReceive _) = True
> advancesLdBuff (FRWLoad  _) = False  -- goes to store unit instead
> advancesLdBuff (FApplyLoad) = True
> advancesLdBuff (FNodeArg _) = True
> advancesLdBuff (FNextArg _) = False  -- avoid double increment on the actual load

> nextLoadBase :: Proc ()
> nextLoadBase = renamer.loadBase %= ((`mod` 4) . succ)

> startEarlyFetch :: NodeSelCtrl -> (FetchCtrl, LoadIndex) -> Checked HeapNode -> Proc ()
> startEarlyFetch XLoadRes (FNodeArg e, ixl) (OK (HNode _ xs)) = loader.loadReq .= Just (LoadRef ixl (xs^.elemAt e.asRef))
> startEarlyFetch XLoadRes (FNextArg e, ixl) (OK (HNode _ xs)) = loader.loadReq .= Just (LoadRef ixl (xs^.elemAt e.asRef))
> startEarlyFetch _        _                 _                 = return ()

> startFetchRef :: (FetchCtrl, LoadIndex) -> RefValue -> Checked RefValue -> Proc ()
> startFetchRef (FNop      , _  ) _ _      = return ()
> startFetchRef (FUsePre   , _  ) _ _      = return () 
> startFetchRef (FEvalRef  , ixl) x _      = loader.loadReq .= Just (LoadRef    ixl x)
> startFetchRef (FReceive c, ixl) _ _      = loader.loadReq .= Just (PopChannel ixl c)
> startFetchRef (FApplyLoad, ixl) _ (OK x) = loader.loadReq .= Just (LoadRef    ixl x)
> startFetchRef (FNodeArg _, _  ) _ _      = return ()   -- loadReq will be at another place
> startFetchRef (FNextArg _, _  ) _ _      = return ()   -- idem ^^
> startFetchRef (FRWLoad ef, _  ) x _      = loader.loadReq .= Just (RewriteLoad ef x)

> startLateFetch :: NodeSelCtrl -> (FetchCtrl, LoadIndex) -> FixedBody -> Proc ()  -- FIXME late fetch should not needed with specializing all the possible cases
> startLateFetch XLoadRes (FNodeArg _, _  ) _  = return ()   -- loadReq has been set earlier
> startLateFetch XLoadRes (FNextArg _, _  ) _  = return ()   -- idem ^^
> startLateFetch _        (FNodeArg e, ixl) xs = loader.loadReq .= Just (LoadRef ixl (xs^.elemAt e.asRef))
> startLateFetch _        (FNextArg e, ixl) xs = loader.loadReq .= Just (LoadRef ixl (xs^.elemAt e.asRef))
> startLateFetch _        _                 _  = return ()

> genStoreAddr :: StoreCtrl -> Proc (Checked RefValue)
> genStoreAddr (WStore    t) = getReservedRef (node2PtrTag t) ux     (nodeSizeT t) where ux = case nodeKind t of {Dynamic -> Unique; Static -> GlobalRef}
> genStoreAddr (WStoreFE  t) = getReservedRef (node2PtrTag t) Unique DoubleNode  -- FIXME nodesize depends on store rewrite
> genStoreAddr (WStoreBox b) = getReservedRef (TC b         ) Unique SingleNode
> genStoreAddr (WFixHole _ ) = getReservedRef (TX           ) Shared SingleNode
> genStoreAddr (WSaveNode t) = getReservedRef (node2PtrTag t) Unique (nodeSizeT t)
> genStoreAddr (WSaveBox  t) = getReservedRef (node2PtrTag t) Unique SingleNode
> genStoreAddr (WUpdNode  t) = getReservedRef (node2PtrTag t) Unique (nodeSizeT t)
> genStoreAddr _             = return Bad

> getReservedRef :: PtrTag -> Uniqueness -> NodeSize -> Proc (Checked RefValue)
> getReservedRef pt ux ns = do  -- TODO take NodeSize in account
>   Just ha <- replaces (heap.nextFreeAddress) (const Nothing)
>   return (OK (Ref pt (ux,ns,ha)))

> pushesRef :: StoreCtrl -> Bool
> pushesRef (WStore   _  ) = True
> pushesRef (WStoreFE   _) = True
> pushesRef (WStoreBox  _) = True
> pushesRef (WStoreCond _) = True
> pushesRef (WPushRef   _) = True
> pushesRef (WSelPush    ) = True
> pushesRef _              = False

> pushEarlyRef :: WriteCtrl -> Checked RefValue -> Proc ()
> pushEarlyRef (WPushRef x, OK qi) _      = writeRef qi x
> pushEarlyRef (WStore _  , OK qi) (OK r) = writeRef qi r
> pushEarlyRef _                   _      = return ()

> runStoreInstr :: WriteCtrl -> Checked HeapRef -> Checked (PtrTag, HeapRef) -> Checked Bool -> FixedBody -> Checked PrimValue -> (RefValue,RefValue) -> Proc ()
> runStoreInstr (WNop        , _    ) _      _      _      _  _      (_, _) =                      return ()
> runStoreInstr (WStore    t , _    ) (OK r) _      _      nb _      (_, _) = {- pushed early -}   storeNode r t nb
> runStoreInstr (WStoreBox b , OK qi) (OK r) _      _      _  (OK y) (_, _) = writeRef qi bvr   >> storeNewBox r b y  where bvr = getBoxValueRef r b y
> runStoreInstr (WStoreCond a, OK qi) _      _      (OK c) _  _      (_, _) = writeRef qi cv    >> return ()          where cv = CVRef $ EnumTag $ if c then fmap succ a else a
> runStoreInstr (WPushRef _  , _    ) _      _      _      _  _      (_, _) = {- pushed early -}   return ()
> runStoreInstr (WSelPush    , OK qi) _      _      (OK c) _  _      (x, y) = writeRef qi r     >> return ()          where r = if c then x else y
> runStoreInstr (WFixHole _  , _    ) (OK r) _      _      nb _      (_, _) =                      storeNode r t nb   where t = NodeTag Dynamic 0 emptyKinds Blackhole  -- FIXME arity in tag and or empty node body ??
> runStoreInstr (WSaveNode t , _    ) (OK r) _      _      nb _      (_, _) =                      storeNode r t nb
> runStoreInstr (WSaveBox  t , _    ) (OK r) _      _      _  (OK y) (_, _) =                      storeNode r t (unaryBody $ PVal y)
> runStoreInstr (WStoreFE  t , OK qi) (OK r) _      _      _  _      (x, y) = {- push ref later -} queueStoreRewrite t qi r (x,y)
> runStoreInstr (WUpdRef     , _    ) _      (OK u) _      nb _      (_, _) =                      updateNode u t nb  where t  = singleRefNodeTag Ind
> runStoreInstr (WUpdBox   t , _    ) _      (OK u) _      _  (OK y) (_, _) =                      updateNode u t (unaryBody $ PVal y)
> runStoreInstr (WUpdCVal  t , _    ) _      (OK u) _      nb _      (_, _) =                      updateNode u t nb
> runStoreInstr (WUpdNode  t,  _    ) (OK r) (OK u) _      nb _      (_, _)   -- TODO think about using indirections when u is not in alloc heap/L1 cache, or maybe just write allocate the update in L1
>   | nsu < nodeSizeT t                                                     = updateNode u i ib >> storeNode r t nb  -- update node with Ind to new node -- TODO think about pipelining
>   | otherwise                                                             = updateNode u t nb >> freeReservedAddress r
>   where {(_, (_, nsu, _)) = u; i = singleRefNodeTag Ind; ib = unaryBody $ RVal $ Ref (node2PtrTag t) r}
> runStoreInstr (WSend  _  t , _    ) _      _      _      nb _      (_, _) = do
>   ext.outputFifo %= enFifo (HNode t nb)
>   putString (\_ -> return $ printHNode (HNode t nb))

> queueStoreRewrite :: NodeTag -> QueueIndex -> HeapRef -> (RefValue,RefValue) -> Proc ()
> queueStoreRewrite t qi r as = do
>   Nothing <- replaces (dataPath.rewriteBuffer) $ const $ Just (t, qi, r, as)
>   return ()

> runStoreRewrite :: Proc ()
> runStoreRewrite = do
>   rwx <- replaces (dataPath.rewriteBuffer) $ const Nothing
>   case rwx of
>     Nothing -> return ()
>     Just (t, qi, r, as) -> finishStoreRewrite t qi r as

> decideRewriteCV :: EvalFun -> CompactValue -> Maybe Arity
> decideRewriteCV E_ap1 (EmptyPap _ _ _ _)         = Just 1
> decideRewriteCV E_ap2 (EmptyPap _ _ b _) | b > 1 = Just 2
> decideRewriteCV E_ap1 (EmptyDCon _  _ _)         = Just 1
> decideRewriteCV E_ap2 (EmptyDCon _  b _) | b > 1 = Just 2
> decideRewriteCV E_ap1 (EmptyPEF _   1 _)         = Just 1    -- could attempt to rewrite the actual select too, but multi step rewrites are too complex for now
> decideRewriteCV _     _                          = Nothing 

> decideRewriteRef ::  EvalFun -> PtrTag -> RewriteAction    -- TODO check impact of rewrites resulting in something partial again
> decideRewriteRef (E_ap1  ) (TP _ _)         = ApplyRewrite 1
> decideRewriteRef (E_ap2  ) (TP _ b) | b > 1 = ApplyRewrite 2
> decideRewriteRef (E_ap1  ) (TD _ _)         = ApplyRewrite 1
> decideRewriteRef (E_ap2  ) (TD _ b) | b > 1 = ApplyRewrite 2
> decideRewriteRef (E_sel i) (TC _  )         = SelRewrite i
> decideRewriteRef  _         _               = CantRewrite 

> finishStoreRewrite :: NodeTag -> QueueIndex -> HeapRef -> (RefValue,RefValue) -> Proc ()
> finishStoreRewrite et@(NodeTag _ _ _ ~(FE ef uf)) qi r as = do
>   Just rlr <- replaces (loader.rewriteLoadResult) $ const Nothing
>   case rlr of
>     (CantRewrite   , Just rl, Nothing   ) -> do
>       writeRef qi (Ref (node2PtrTag et) r)
>       storeNode r et $ insertRewriteApplies ef B as (unaryBody $ RVal rl)
>     (SelRewrite  si, mrl    , Just (HNode t xs, fnvs)) -> do
>       let nb = over (mapped.mapped.withRef) (applyRefSharing fnvs) xs
>       let ir = xs^.elemAt si.asRef
>       writeRef qi ir
>       freeReservedAddress r 
>       queueRCM $ fmap (RCDec,) mrl
>       let rcSelMod ri = if isJust mrl then (if ri == si then RCInc else RCNop) else (if ri == si then RCNop else RCDec)  -- if copied then increment the selected elem else decrement the dropped rest
>       queueRCsBody rcSelMod t nb
>     (ApplyRewrite n, mrl, Just (HNode t xs, fnvs)) -> do
>       let nb = over (mapped.mapped.withRef) (applyRefSharing fnvs) xs
>       let (xt,ae) = applyToTag t n uf
>       writeRef qi (Ref (node2PtrTag xt) r)
>       storeNode r xt $ insertRewriteApplies ef ae as nb
>       queueRCM $ fmap (RCDec,) mrl
>       let rcMod _ = if isJust mrl then RCInc else RCNop
>       queueRCsBody rcMod t nb

> insertRewriteApplies :: EvalFun -> NodeElem -> (RefValue,RefValue) -> FixedBody -> FixedBody
> insertRewriteApplies (E_ap1  ) ae (a, _) = (elemAt ae .~ RVal a)
> insertRewriteApplies (E_ap2  ) ae (a, b) = (elemAt (succ ae) .~ RVal b) . (elemAt ae .~ RVal a)
> insertRewriteApplies (E_sel _) _  (_, _) = id    -- in case of CantRewrite on a select

> runPrims :: CondValue QueueIndex -> DecPrims QueueIndex LocPIndex CondIndex -> PrimVals -> Proc ()
> runPrims tnc (px, py) (Q xa xb ya yb) = runPrimInstr tnc (xa,xb) px >> runPrimInstr tnc (ya,yb) py

> runPrimInstr :: CondValue QueueIndex -> (Checked PrimValue, Checked PrimValue) -> DecPrimInstr QueueIndex LocPIndex CondIndex -> Proc ()
> runPrimInstr _   _       (DecPrimNop             ) = return ()
> runPrimInstr tnc (xa,xb) (DecPrimOp  qi p   a b c) = poking (primSide.primQueue) qi =<< liftM3 (execPrimOp p) (fmap (asBool "need bool value") (peekAtC tnc c)) (readPA a xa) (readPA b xb) 
> runPrimInstr _   _       (DecPrimC   qi   x      ) = poking (primSide.primQueue) qi x
> runPrimInstr tnc (xa,xb) (DecCmpOp qi (p,q) a b c) = broadcastCond qi =<< liftM2 (execLogicOp q) (liftM2 (execCmpOp p) (readPA a xa) (readPA b xb)) (peekAtC tnc c)

> readPA :: LocPIndex -> Checked PrimValue -> Proc PrimValue
> readPA (XI    ) ~(OK x) = return x
> readPA (SIC x ) _       = return $ fromIntegral x
> readPA (LQI qi) _       = peekAtP Bad $ PQI qi

> getBoxValueRef :: HeapRef -> ConAlt -> PrimValue -> RefValue
> getBoxValueRef r c n 
>   | n < 2147483648 || n >= -2147483648 = CVRef $ PrimBox c (fromIntegral n)
>   | otherwise                          = Ref (tag2PtrTag $ Box c) r

> storeNewBox :: HeapRef -> ConAlt -> PrimValue -> Proc ()
> storeNewBox r c n
>   | n < 2147483648 || n >= -2147483648 = freeReservedAddress r
>   | otherwise                          = storeNode r (boxNodeTag c) $ unaryBody $ PVal n

> storeNode :: HeapRef -> NodeTag -> FixedBody -> Proc ()
> storeNode r t xs = storeNewNode r $ HNode t xs

Trying to compact a Node in a single Value.

> compactValueNode :: NodeTag -> FixedBody -> Maybe CompactValue
> compactValueNode nt xs
>   | nodeKind nt == Static = Nothing
>   | nodeArity nt == 0     = emptyNodeTagValue nt
>   | otherwise             = case plainTag nt of
>     (Box c ) | n < 2147483648 || n >= -2147483648 -> Just (PrimBox c (fromIntegral n)) where n = xs^.elemAt A .asPrim
>     _                                             -> Nothing

> smallBoxValue :: NodeTag -> PrimValue -> Maybe CompactValue
> smallBoxValue (NodeTag _ _ _ (Box c)) n | n < 2147483648 || n >= -2147483648 = Just (PrimBox c (fromIntegral n))
> smallBoxValue _                       n                                      = error ("Boxed value not small: " ++ show n)

> emptyNodeTagValue :: NodeTag -> Maybe CompactValue
> emptyNodeTagValue nt
>   | nodeKind nt == Static = Nothing
>   | otherwise             = case plainTag nt of
>     (Con c    ) -> Just (EnumTag c                   )
>     (DCon c  n) -> Just (EmptyDCon c  n $ kindMask nt)
>     (Pap f i n) -> Just (EmptyPap f i n $ kindMask nt)
>     (PE ef   n) -> Just (EmptyPEF ef  n $ kindMask nt)
>     _           -> Nothing

> expandValue :: CompactValue -> HeapNode
> expandValue (VoidRef          ) = error "loading voided reference"
> expandValue (FetchedRef       ) = error "expanding value already being prefetched"
> expandValue (PrimBox   c  n   ) = HNode (NodeTag Dynamic 1 singlePrimK $ Box  c   ) (unaryBody $ PVal $ fromIntegral n)
> expandValue (EnumTag   c      ) = HNode (NodeTag Dynamic 0 emptyKinds  $ Con  c   ) emptyNBody
> expandValue (EmptyDCon c  a vs) = HNode (NodeTag Dynamic 0 vs          $ DCon c  a) emptyNBody
> expandValue (EmptyPap f i a vs) = HNode (NodeTag Dynamic 0 vs          $ Pap f i a) emptyNBody
> expandValue (EmptyPEF ef  a vs) = HNode (NodeTag Dynamic 0 vs          $ PE ef   a) emptyNBody

> setBranchCond :: NextInstr -> Bool -> Checked (CondValue QueueIndex) -> CondValue QueueIndex -> Proc ()
> setBranchCond (DecideBr _ _) True (OK nsc) _   = instrCtrl.branchCond .= nsc
> setBranchCond (DecideBr _ _) False _       tnc = instrCtrl.branchCond .= tnc
> setBranchCond _              _     _       _   = return ()

> modifyCallFrame :: CallFrameCtrl -> EContCount -> Checked (CondValue QueueIndex) -> EContCount -> NodeCount -> (CallFrame, NodeCount) -> Proc ()
> modifyCallFrame (CFNop       ) xc _   _   = updateStackCounts xc
> modifyCallFrame (CFPushCall c) xc nsc _   = pushNewFrame c xc nsc
> modifyCallFrame (CFEnterApply) _  _   ec' = enterApplyCall ec'
> modifyCallFrame (CFContinue  ) _  _   ec' = maybePopCallFrame ec'
> modifyCallFrame (CFPushEval  ) xc _   _   = pushNewFrame ReturnNext xc Bad

> updateStackCounts :: EContCount -> NodeCount -> (CallFrame, NodeCount) -> Proc ()
> updateStackCounts xc' pn (cf, tnc) = do
>   ctrlStack.callStack.top .= set' nodeCount (tnc+pn) cf  -- TODO make this less ugly
>   ctrlStack.extraPushCont .= xc'

> enterApplyCall :: EContCount -> NodeCount -> (CallFrame, NodeCount) -> Proc ()  -- when entering an apply call we need to be careful to preserve the return continuation
> enterApplyCall 0   pn ((CallFrame _ ReturnNext msc _), tnc) = (ctrlStack.savedCond .= msc) >> dropCallFrame (tnc + pn)     -- drop useless callframe / tail call
> enterApplyCall ec' pn ((CallFrame _ tc         msc _), tnc) = ctrlStack.callStack.top .= (CallFrame ec' tc msc (tnc+pn))

> maybePopCallFrame :: EContCount -> NodeCount -> (CallFrame, NodeCount) -> Proc ()
> maybePopCallFrame 0   pn (CallFrame _ ThreadFinish msc _, tnc) = ctrlStack.callStack.top .= CallFrame 0 ThreadFinish msc (tnc+pn)   -- do not drop last call frame
> maybePopCallFrame 0   pn (CallFrame _ tc           msc _, tnc) = (ctrlStack.savedCond .= msc) >> dropCallFrame (tnc + pn)
> maybePopCallFrame ec' pn (CallFrame _ tc           msc _, tnc) = ctrlStack.callStack.top .= CallFrame ec' tc msc (tnc+pn)

> pushNewFrame :: Continuation -> EContCount -> Checked (CondValue QueueIndex) -> NodeCount -> (CallFrame, NodeCount) -> Proc ()
> pushNewFrame ReturnNext xc _   pn (CallFrame tec tc msc _, tnc) = (ctrlStack.extraPushCont .= 0) >> (ctrlStack.callStack.top .=  (CallFrame (tec+xc) tc msc (tnc+pn)))
> pushNewFrame c          xc nsc pn _                             = (ctrlStack.extraPushCont .= 0) >> (ctrlStack.callStack %= push (CallFrame      xc   c nsc (    pn)))

> dropCallFrame :: NodeCount -> Proc ()
> dropCallFrame xnc = ctrlStack.callStack %= ((top.nodeCount %~ (+xnc)) . pop)

> runRCUpdates :: Proc ()
> runRCUpdates = mapM_ modRefCounter_ =<< replaces (rcUnit.rcUpdates) (const [])

> runLoadGCNodes :: Proc ()
> runLoadGCNodes = do   -- TODO instead of prioritizing dropAHRefs, use any of allocHeap and cache if not in use by other processes
>   dahs <- gets (rcUnit.dropAHRefs)
>   durs <- gets (rcUnit.dropRefs)
>   mn <- case (nullFifo dahs, nullFifo durs) of  -- TODO also check for space in the dropLoadRes buffer
>     (True , True ) -> return Nothing
>     (False,  _   ) -> do
>       x <- popFifo (rcUnit.dropAHRefs)
>       fmap Just $ deAllocNodeAH x
>     (_    , False) -> do   -- TODO in principle this could done in parallel with above
>       x <- popFifo (rcUnit.dropRefs)
>       deAllocNodeCache x
>   rcUnit.dropLoadRes .= mn
>
> runDropGCNode :: Proc ()
> runDropGCNode = do
>   mn <- replaces (rcUnit.dropLoadRes) (const Nothing)
>   case mn of
>     Nothing               -> return ()
>     Just (rs, HNode t xs) -> do
>       let nb = over (mapped.mapped.withRef) (applyRefSharing rs) xs  -- make sure previously read refs are marked shared
>       queueRCsBody (const RCDec) t nb  -- these rc updates are shared on low priority with the rewriteload

> get_next_ip :: Proc CodeAddr
> get_next_ip = gets (instrCtrl.ip.to (\(CodeAddr i) -> CodeAddr (i+1)))

> relJump :: CodeAddr -> RelCodeAddr -> CodeAddr
> relJump (CodeAddr i) (RelCodeAddr x) = CodeAddr (i + fromIntegral x)

> setRQPopIndex :: Maybe QueueBase -> Proc ()
> setRQPopIndex Nothing       = return ()
> setRQPopIndex (Just (QB i)) = rcUnit.rqToPop .= IxQ i

> clearRQEntries :: Proc ()
> clearRQEntries = do
>   (IxQ dqi) <- gets (rcUnit.rqLastIx)
>   (IxQ tqi) <- gets (rcUnit.rqToPop)
>   when (dqi /= tqi) $ do   -- TODO to minimize number of ports in RC unit share this RC update with the second apply rc update
>     let pqi = IxQ ((dqi-1) `mod` 32)
>     x <- replacing (dataPath.refQueue) pqi (const $ CVRef VoidRef)   -- overwriting for checking only
>     queueRC (RCDec, x)
>     rcUnit.rqLastIx .= pqi

> clearStackPops :: Proc ()
> clearStackPops = do
>   ips <- gets (rcUnit.stackForPop)
>   drs <- gets (rcUnit.stackDropRef)
>   case (firstStMaskBit ips, firstStMaskBit drs) of
>     (Nothing ,  Nothing) -> return ()
>     (Just ipx,  _       ) -> do
>       OK (StNode tr xs) <- replacing (dataPath.stackRegs ) ipx (const Bad)
>       OK pms            <- replacing (ctrlStack.metaSRegs) ipx (const Bad)
>       OK _              <- replacing (primSide.primStack ) ipx (const Bad)
>       rcUnit.stackForPop.stMaskAt ipx .= False
>       rcUnit.stackDropRef.stMaskAt ipx .= False
>       renamer.stackForFree %= enFifo ipx
>       case pms of
>        (StMeta _ _ _ PrimS ) -> queueRCM (fmap (RCDec,) tr)                                      -- FIXME workaround for mismatch between tag arity and body size for Prim shaped nodes
>        (StMeta _ _ _ EmptyS) -> queueRCM (fmap (RCDec,) tr)                                      -- FIXME workaround for mismatch between tag arity and body size for bodyless nodes
>        (StMeta _ _ t _     ) -> queueRCM (fmap (RCDec,) tr) >> queueRCsBody (const RCDec) t xs
>     (_      , Just irx) -> do
>       OK (StNode tr _) <- replacing (dataPath.stackRegs) irx (checked.stNRef .~ Nothing)
>       queueRCM (fmap (RCDec,) tr)
>       rcUnit.stackDropRef.stMaskAt irx .= False

> spillRefillStack :: Proc ()
> spillRefillStack = do
>   rm  <- gets (renamer.stackMapping)
>   fns <- gets (renamer.stackForFree)
>   case nullFifo fns of
>     True -> do  -- spill 
>       let nsi = maybe 8 fst (rm ^@? (traversed . filtered (== StVoid)))
>       when (nsi > 5) $ do  -- TODO change limit to only spill with an (almost) full stack
>         let xi = case rm ! pred nsi of {StIndex i -> i; _ -> error "bad stack spill index"}
> --    let (xi, rm') = (last rm, init rm)
>         drsxi  <- gets (rcUnit.stackDropRef.stMaskAt xi)
>         unless drsxi $ do   -- block spilling if node ref still has to be removed
>           OK mx  <- replacing (dataPath.stackRegs ) xi (const Bad)
>           OK pvs <- replacing (primSide.primStack ) xi (const Bad)
>           OK mp  <- replacing (ctrlStack.metaSRegs) xi (const Bad)
>           let ssn = toStoredStackNode mp mx pvs
>           seq ssn $ do
>             dataPath.stackMem %= push ssn
>             renamer.stackForFree %= enFifo xi
>             renamer.stackMapping.ix (pred nsi) .= StVoid
>     False  -> do
>          Stack ys <- gets (dataPath.stackMem)
>          let (fns', fi) = deFifo fns
>          if (nullFifo fns' || null ys)   -- try refilling all but one stack entry
>            then return ()
>            else do   -- refilling one at a time
>              (MemStN (nr, mtr) t xs) <- gets (dataPath.stackMem.top)
>              let htr = if isJust mtr then HasNR else NoNR
>              Bad <- replacing (ctrlStack.metaSRegs) fi (const $ OK $ StMeta nr htr t NodeS)
>              Bad <- replacing (dataPath.stackRegs ) fi (const $ OK $ StNode mtr xs        )
>              Bad <- replacing (primSide.primStack ) fi (const $ OK $ extractPrimVals t xs )
>              dataPath.stackMem %= pop 
>              renamer.stackForFree .= fns'
>              let Just nsi = fmap fst (rm ^@? (traversed . filtered (== StVoid)))
>              renamer.stackMapping.ix nsi .= StIndex fi

> toStoredStackNode :: StackMeta -> StackNode -> PrimVals -> StoredSN  -- node shape are normalized to standard nodes  -- TODO do not store body of node with node ref
> toStoredStackNode (StMeta ntr _ t (EmptyS)) (StNode tr _ ) _                 = MemStN (ntr, tr) t emptyNBody            -- FIXME here we lose info that node body is not wanted anymore and causes arity mismatch between body and tag
> toStoredStackNode (StMeta ntr _ t (NodeS )) (StNode tr xs) _                 = MemStN (ntr, tr) t xs                    -- FIXME vv & - & ^^  node reference might linger around while it's invalidated in meta node
> toStoredStackNode (StMeta ntr _ t (PrimS )) (StNode tr _ ) (Q ~(OK y) _ _ _) = MemStN (ntr, tr) t (unaryBody $ PVal y)  -- TODO use compacted value if available
> toStoredStackNode (StMeta ntr _ t (RawS a)) (StNode tr xs) (Q yh yi yj yk  ) = MemStN (ntr, tr) t' xs' where
>   t'  = t {nodeArity = nodeArity t + a} 
>   xs' = zip3BodyWith mergeBody (kindMaskBody t') xs (FB (T yh yi yj) (Q yk yh yi yj))
>   mergeBody (Nothing   ) _              _       = Bad
>   mergeBody (Just RefK ) ~(OK (RVal r)) _       = OK (RVal r)
>   mergeBody (Just PrimK) _              ~(OK p) = OK (PVal p)

> shareRef :: RefValue -> RefValue
> shareRef (CVRef x) = CVRef x
> shareRef (Ref t r) = Ref t $ shMHRef r where
>   shMHRef (GlobalRef, s, a) = (GlobalRef, s, a)
>   shMHRef (_        , s, a) = (Shared   , s, a)

> invRef :: RefValue -> RefValue
> invRef = const $ CVRef VoidRef

> peekAtR :: RefUseIndex -> Proc ReadRef
> peekAtR (_, IVoid) = return (RCNop, CVRef $ VoidRef)
> peekAtR (_, ICC c) = return (RCNop, CVRef $ EnumTag c)
> peekAtR (TakeRef, RSTI c) = do
>   OK (StNode r xs) <- gets (dataPath.stackTop)
>   let (x,xs') = elemAt c.asRef <<%~ invRef $ xs
>   dataPath.stackTop .= OK (StNode r xs')
>   return (RCNop,x)
> peekAtR (CopyRef, RSTI c) = do
>   OK (StNode r xs) <- gets (dataPath.stackTop)
>   let (x,xs') = elemAt c.asRef <<%~ shareRef $ xs
>   dataPath.stackTop .= OK (StNode r xs')
>   return (RCInc, shareRef x)
> peekAtR (TakeRef, RSI i c) = do
>   r <- withNodeFrom i (stNBody.elemAt c.asRef <<%~ invRef)
>   return (RCNop,r)
> peekAtR (CopyRef, RSI i c) = do
>   r <- withNodeFrom i (stNBody.elemAt c.asRef <<%~ shareRef)
>   return (RCInc, shareRef r)
> peekAtR (TakeRef, RQI i)  =  do
>   x <- replacing (dataPath.refQueue) i invRef
>   return (RCNop, x)
> peekAtR (CopyRef, RQI i) = do
>   x <- replacing (dataPath.refQueue) i shareRef
>   return (RCInc, shareRef x)
> peekAtR (TakeRef, TNR) = do
>   nr <- replaces (dataPath.stackTop.checked.stNRef) $ const Nothing
>   return (RCNop, fromMaybe (error "top node ref is Nothing") nr)
> peekAtR (CopyRef, TNR) = do
>   nr <- replaces (dataPath.stackTop.checked.stNRef) $ fmap shareRef
>   return (RCInc, shareRef $ fromMaybe (error "top node ref is Nothing") nr)
> peekAtR (TakeRef, NRI i) = do
>   x <- withNodeFrom i (stNRef <<.~ Nothing)
>   return (RCNop, fromMaybe (error ("stack " ++ show i ++ " is Nothing")) x)
> peekAtR (CopyRef, NRI i) = do
>   x <- withNodeFrom i (stNRef <<%~ fmap shareRef)
>   return (RCInc, shareRef $ fromMaybe (error ("stack " ++ show i ++ " is Nothing")) x)  -- TODO investigate: using a more conservative shareManyRef here sometimes gives better behaviour with deAllocs and node ref fixups

> readPrimVals :: Checked Word32 -> Quad (Maybe WordIndex) -> Proc PrimVals
> readPrimVals mti = fmap (fmap toChecked) . traverse (traverse $ peekAtW mti)

> peekAtW :: Checked Word32 -> WordIndex -> Proc PrimValue
> peekAtW mti (PAI   x) = peekAtP mti x
> peekAtW _   (WSTI  c) = gets (dataPath.stackTop.checked.stNBody.elemAt c.asPrim)
> peekAtW _   (WSI i c) = fmap (view (checked.stNBody.elemAt c.asPrim)) (peeking (dataPath.stackRegs) i)

> peekAtP :: Checked Word32 -> PrimIndex -> Proc PrimValue
> peekAtP _        (IC i ) = return (fromIntegral i)
> peekAtP ~(OK ti) (TTI  ) = return (fromIntegral ti)   -- TODO consider making top tag index an independent register that is preserved when stack top is popped
> peekAtP _        (PQI i) = peeking (primSide.primQueue) i
> peekAtP _       (VSTI c) = gets (primSide.primSTop.primAt c)
> peekAtP _      (VSI i c) = fmap (^.checked.primAt c) $ peeking (primSide.primStack) i

> peekAtC :: CondValue QueueIndex -> CondIndex -> Proc (CondValue QueueIndex)
> peekAtC _   (IBC x     ) = return (Nothing, x)
> peekAtC _   (CQI  inv i) = fmap (flipCV inv) $ peeking (primSide.condQueue) i
> peekAtC tnc (TNC inv   ) = return $ flipCV inv tnc
> peekAtC _   (CSC inv   ) = fmap (flipCV inv) $ gets (ctrlStack.savedCond.checked)
> peekAtC _   (FCQV inv i) = return (Just i, inv)

> flipCV :: Bool -> CondValue QueueIndex -> CondValue QueueIndex
> flipCV inv = fmap (xor inv) where xor = (/=)

> readBody :: Checked Word32 -> NodeIndex -> Proc ReadBody
> readBody mti = traverse (readBodyArg mti)

> readBodyArg :: Checked Word32 -> Maybe (Either RefUseIndex WordIndex) -> Proc (Checked (RCMod, BodyArg))
> readBodyArg _   (Just (Left  x)) = fmap (OK . second RVal    ) $ peekAtR x
> readBodyArg mti (Just (Right y)) = fmap (OK . (RCNop,) . PVal) $ peekAtW mti y
> readBodyArg _   (Nothing       ) = return Bad

> withNodeFrom :: StackIndex -> (StackNode -> (a, StackNode)) -> Proc a
> withNodeFrom i f = do
>   OK x <- peeking (dataPath.stackRegs) i
>   let (n, x') = f x
>   poking (dataPath.stackRegs) i (OK x')
>   return n

> withMetaFrom :: StackIndex -> (StackMeta -> StackMeta) -> Proc ()
> withMetaFrom i f = do
>   OK _ <- replacing (ctrlStack.metaSRegs) i (fmap f)
>   return ()

> writeRef :: QueueIndex -> RefValue -> Proc ()
> writeRef qi x = poking (dataPath.refQueue) qi x

> broadcastCond :: QueueIndex -> CondValue QueueIndex -> Proc ()
> broadcastCond qi x = do
>   mapM_ (\i -> replacing (primSide.condQueue) i $ combineCond x qi) [IxQ 0 .. IxQ 15]
>   poking (primSide.condQueue) qi x
>   ctrlStack.savedCond.mapped                      %= combineCond x qi
>   ctrlStack.topNodeCond                           %= combineCond x qi
>   ctrlStack.callStack.mapped.callSavedCond.mapped %= combineCond x qi   -- FIXME only want to broadcast to the top one or two elements of the callstack, calls should block on more unresolved conds
>   instrCtrl.branchCond                            %= combineCond x qi

> combineCond :: CondValue QueueIndex -> QueueIndex -> CondValue QueueIndex -> CondValue QueueIndex
> combineCond x qix ((Just qiy, inv)) | qix == qiy = fmap (xOr inv) x where xOr = (/=)
> combineCond _ _   y                              = y

> applyRefSharing :: RefSharing -> RefValue -> RefValue
> applyRefSharing NoSharing   = id
> applyRefSharing MoreSharing = shareRef 

> asAH_Addr :: HeapAddr -> AH_Index
> asAH_Addr x = fromIntegral (x `mod` allocHeapSize)

> getAHIndex :: HeapAddr -> Proc (Maybe AH_Index)
> getAHIndex x = do
>   (hTop, ahL) <- gets (heap.ahBounds)
>   if (ahL <= x && x <= hTop)  -- TODO check timing issues, last AH node might be evicted already
>     then return (Just $ asAH_Addr x)
>     else return Nothing

> retrieveNodeAH :: (Uniqueness, NodeSize, AH_Index) -> Proc (Bool, HeapNode, RefSharing)  -- Bool for ref staying valid
> retrieveNodeAH (u,ns,i) = do
>   OK ri <- peeking (heap.nursery) (2*i)
>   rs    <- peeking (heap.ahInfo ) (2*i)
>   rn <- case (ns,ri) of 
>     (_         , HNRest _    ) -> error ("reading HNRest at " ++ show i)
>     (SingleNode, HNInit rt rl) -> return $ HNode rt $ FB rl (Q Bad Bad Bad Bad)
>     (DoubleNode, HNInit rt rl) -> do
>       NodeExt        <- peeking (heap.ahInfo ) ((2*i)+1)
>       OK (HNRest rr) <- peeking (heap.nursery) ((2*i)+1)
>       return $ HNode rt $ FB rl rr
>   c <- gets (stats.steps)
>   case (rs,u) of
>     (FreeLine  , _  ) -> error ("reading deallocated ref: " ++ show i)
>     (BlackHoled, _  ) -> error ("reading blackhole ref: " ++ show i)
>     (s      , Unique) -> do
>       heap.loadDeallocs += 1
>       poking (heap.nursery) (i*2) Bad      -- overwriting for checking purposes only
>       when (ns == DoubleNode) $ poking (heap.nursery) ((i*2)+1) Bad
>       markFreeHeapAddr (ns, i)
>       when (ns == DoubleNode) $ poking (heap.ahInfo) ((i*2)+1) FreeLine
>       return ()       >> poking (heap.ahInfo) (i*2) FreeLine   >> return (False, rn, lastReadSharing s)
>     (FreshFun  , _  ) -> poking (heap.ahInfo) (i*2) BlackHoled >> return (True , rn, NoSharing        )
>     _                 -> poking (heap.ahInfo) (i*2) SharedRead >> return (True , rn, MoreSharing      )

> lastReadSharing :: ReadState -> RefSharing
> lastReadSharing FreshData = NoSharing
> lastReadSharing FreshFun  = NoSharing
> lastReadSharing Updated   = NoSharing
> lastReadSharing _         = MoreSharing

> retrieveNodeCache :: HeapRef -> Proc (Bool, HeapNode, RefSharing)  -- Bool for ref staying valid
> retrieveNodeCache r = do -- TODO if node is not in cache, read and free the to be evicted one early ???
>   mx <- tryRetrieveNodeCache r
>   case mx of
>     Just x  -> return x
>     Nothing -> retrieveNodeMem r

> tryRetrieveNodeCache :: HeapRef -> Proc (Maybe (Bool, HeapNode, RefSharing)) -- TODO take in account NodeSize
> tryRetrieveNodeCache r@(u,_,i) = do
>   mx <- (case u of {Unique -> tryDeAllocTagAt; _ -> tryUseTagAt}) i
>   case mx of
>     Nothing -> return Nothing
>     Just x -> do
>       OK rn <- peeking (heap.cData) x
>       when (u == Unique) $ poking (heap.cData) x Bad   -- overwriting destructive read for checking purposes only
>       rs <- peeking (heap.cInfo) x
>       case (u, rs) of
>         (_     , FreeLine  ) -> error ("reading deallocated ref: " ++ show r)
>         (_     , BlackHoled) -> error ("reading blackhole ref: " ++ show r)
>         (Unique, _         ) -> poking (heap.cInfo) x FreeLine   >> return (Just (False, rn, NoSharing  ))
>         (_     , FreshFun  ) -> poking (heap.cInfo) x BlackHoled >> return (Just (True , rn, NoSharing  ))
>         (_     , _         ) -> poking (heap.cInfo) x SharedRead >> return (Just (True , rn, MoreSharing))

> retrieveNodeMem :: HeapRef -> Proc (Bool, HeapNode, RefSharing)
> retrieveNodeMem r@(u,_,i) = do
>   hm <- gets (ext.heapMem)
>   case IM.lookup i hm of
>     Nothing          -> error ("reading invalid heap ref: " ++ show r)
>     Just rn@(HNode t _) -> case u of
>       Unique -> do
>         _ <- replaces (ext.heapMem) (IM.delete i)  -- only purpose of this is making simulation not run out of memory quickly while having no GC yet
>         return (False, rn, NoSharing)
>       _ | isUpdFTag $ plainTag t -> do
>         ext.heapMem %= IM.insert i (HNode (blackholeTag t) emptyNBody)
>         return (True , rn, NoSharing)
>       _ -> do
>         moveIntoCache i SharedRead rn                                -- default ReadState because we don't have extra bits in external memory
>         ext.heapMem %= IM.delete i
>         return (True , rn, MoreSharing)

> blackholeTag :: NodeTag -> NodeTag
> blackholeTag (NodeTag k _ vs (Fun _ _ _)) = NodeTag k 0 vs Blackhole   -- TODO maybe keep node arity instead of zero ??
> blackholeTag (NodeTag k _ vs (FE _    _)) = NodeTag k 0 vs Blackhole
> blackholeTag _                            = error "expecting function node to blackhole"

> findNewStoreAddr :: Proc ()
> findNewStoreAddr = do
>   na <- gets (heap.nextFreeAddress)
>   when (isNothing na) $ do
>     ha <- reserveNodeAddress DoubleNode  -- FIXME should not default to DoubleNode
>     heap.nextFreeAddress .= Just ha

> reserveNodeAddress :: NodeSize -> Proc HeapAddr
> reserveNodeAddress ns = do   -- TODO take in account NodeSize
>   fls <- gets (heap.freeLines)
>   (hTop, ahL) <- gets (heap.ahBounds)
>   case (fls .&. compactAllocMask) of
>     0 -> do
>       let x = hTop
>       let ey = x - allocHeapSize
>       freeAllocHeap ey
>       heap.ahBounds .= (hTop + 1, if ahL == ey then ahL+1 else ahL)   -- update allocheapLast if it is evicted
>       heap.freeLines .= (fls `shiftL` 1)
>       return x
>     mfls -> do
>       let oi = foldr1 (\i y -> if testBit mfls i then i else y) [compactAllocRange-1, compactAllocRange-2..]
>       let x = hTop - (oi + 1)
>       Bad <- peeking (heap.nursery) (2 * asAH_Addr x)   -- only checking that heap line is empty for debugging
>       heap.freeLines .= clearBit fls oi
>       return x

> storeNewNode :: HeapRef -> HeapNode -> Proc ()
> storeNewNode (u, ns, ahx) (HNode t (FB rl rr)) = do  -- TODO take in account NodeSize
>   let i = asAH_Addr ahx
>   heap.allocProfile %= M.alter (Just . maybe 1 succ) (plainTag t)
>   poking (rcUnit.counters) i $ case u of {Unique -> {- InitRC -} One ; _ -> Two;}
>   poking (heap.nursery   ) (2*i) $ OK $ HNInit t rl
>   poking (heap.ahInfo    ) (2*i) $ if isUpdFTag (plainTag t) then FreshFun else FreshData  -- non updatable functions behave like data as far as the heap is concerned
>   when (ns == DoubleNode) $ do
>     poking (heap.nursery) ((2*i)+1) $ OK $ HNRest rr
>     poking (heap.ahInfo ) ((2*i)+1) NodeExt

> freeAllocHeap :: HeapAddr -> Proc ()
> freeAllocHeap x = do
>   let i = 2 * asAH_Addr x
> --  trace ("evicting " ++ show x ++ " " ++ show i) $ return ()
>   pn <- replacing (heap.nursery) i (const Bad)    -- overwriting for checking purposes only
>   rs <- replacing (heap.ahInfo) i (const FreeLine)
>   case (rs, pn) of
>     (FreeLine, Bad ) -> return ()
>     (FreeLine, OK n) -> error ("should have been deallocated " ++ show n)
>     (_       , Bad ) -> error ("bad reference counter at " ++ show i)
>     (_       , OK n) -> do
>       let HNInit nt nl = n
>       case nodeSizeT nt of
>         SingleNode -> moveIntoCache x rs $ HNode nt (FB nl (Q Bad Bad Bad Bad))
>         DoubleNode -> do
>           OK (HNRest nr) <- replacing (heap.nursery) (i+1) (const Bad)
>           NodeExt        <- replacing (heap.ahInfo ) (i+1) (const FreeLine)
>           moveIntoCache x rs $ HNode nt (FB nl nr)

> updateNode :: (PtrTag, HeapRef) -> NodeTag -> FixedBody -> Proc ()
> updateNode (_, (Unique,_ , a)) _  _  = error ("updating unique ref @" ++ show a)
> updateNode (_, (u     ,ns, a)) tx xs = do
>   let nk = case u of {GlobalRef -> Static; _ -> Dynamic}  -- fixup tag when updating static node
>   let t  = NodeTag nk (nodeArity tx) (kindMask tx) (plainTag tx)
>   let nb = HNode t xs
>   mhi <- getAHIndex a
>   case mhi of
>     Just i  -> updateNodeAH    (ns,i) nb
>     Nothing -> updateNodeCache (ns,a) nb

> updateNodeAH :: (NodeSize, AH_Index) -> HeapNode -> Proc ()
> updateNodeAH (ns,i) nb = do   -- TODO take in account node size
>   case (ns, nb) of
>     (SingleNode, HNode nt _) | nodeSizeT nt == DoubleNode -> error "TODO cannot update with larger node in place"
>     (SingleNode, HNode nt (FB nl _)) -> do
>       BlackHoled <- replacing (heap.ahInfo) (2*i) (const Updated)
>       OK _ <- replacing (heap.nursery) (2*i) (const $ OK $ HNInit nt nl)
>       return ()
>     (DoubleNode, HNode nt (FB nl nr)) -> do
>       BlackHoled <- replacing (heap.ahInfo) (2*i) (const Updated)
>       OK _ <- replacing (heap.nursery) (2*i) (const $ OK $ HNInit nt nl)
>       poking (heap.nursery) ((2*i)+1) (OK $ HNRest nr)

> updateNodeCache :: (NodeSize, HeapAddr) -> HeapNode -> Proc ()
> updateNodeCache (ns,a) nb = do    -- TODO take in account node size
>   mx <- tryUseTagAt a
>   case mx of
>     Just x -> do
>       OK _ <- replacing (heap.cData) x (const $ OK nb)
>       BlackHoled <- replacing (heap.cInfo) x (const Updated)
>       return ()
>     Nothing -> do
>       ext.heapMem %= IM.alter (maybe (error "updating invalid ref") (const $ Just nb)) a  -- maybe check for blackhole

> moveIntoCache :: HeapAddr -> ReadState -> HeapNode -> Proc ()
> moveIntoCache i rs n = do
>   (x, ma) <- getReplaceEntry i
>   case ma of
>     Nothing -> return ()
>     Just a  -> do
>       OK (HNode t xs) <- peeking (heap.cData) x
>       s <- peeking (heap.cInfo) x
>       let mn = case s of {BlackHoled -> HNode (blackholeTag t) emptyNBody; _ -> HNode t xs}
>       ext.heapMem %= IM.insert a mn
>   poking (heap.cData) x (OK n)
>   poking (heap.cInfo) x rs

> freeReservedAddress :: HeapRef -> Proc ()  -- in case nothing will and has been stored
> freeReservedAddress (_, ns, x) = do
>   mhi <- getAHIndex x
>   case mhi of
>     Just i  -> markFreeHeapAddr (ns,i)
>     Nothing -> error ("freeReservedAddress on non local address " ++ show x)

> markFreeHeapAddr :: (NodeSize, AH_Index) -> Proc ()
> markFreeHeapAddr (ns, x) = do    -- TODO dead double size node, after updating with too big nodes in alloc heap is fixed
>   age <- fmap ((.&. allocHeapMax) . (subtract $ fromIntegral x)) $ gets (heap.ahBounds._1)
>   heap.freeLines %= (if (age <= compactAllocRange && age > 0) then (flip setBit (age-1)) else id)  -- TODO fix annoying off by one issues

> deAllocNodeAH :: (NodeSize, AH_Index) -> Proc (RefSharing, HeapNode)
> deAllocNodeAH (ns, i) = do  -- TODO take in account NodeSize
>   markFreeHeapAddr (ns, i)
>   OK (HNInit rt rl) <- replacing (heap.nursery) (2*i) (const Bad)      -- overwriting for checking purposes only
>   s <- replacing (heap.ahInfo) (2*i) (const FreeLine)
>   case ns of
>     SingleNode -> return (lastReadSharing s, HNode rt (FB rl (Q Bad Bad Bad Bad)))
>     DoubleNode -> do
>       OK (HNRest rr) <- replacing (heap.nursery) ((2*i)+1) (const Bad)      -- overwriting for checking purposes only
>       NodeExt        <- replacing (heap.ahInfo ) ((2*i)+1) (const FreeLine)
>       return (lastReadSharing s, HNode rt (FB rl rr))

> deAllocNodeCache :: (NodeSize, HeapAddr) -> Proc (Maybe (RefSharing, HeapNode))
> deAllocNodeCache (ns, x) = do  -- TODO take in account NodeSize
>   mi <- tryDeAllocTagAt x
>   case mi of
>     Just i -> do
>       OK hn <- replacing (heap.cData) i (const Bad)    -- overwriting for checking purposes only
>       s <- replacing (heap.cInfo) i (const FreeLine)
>       return $ Just (lastReadSharing s, hn)
>     Nothing -> do
>       _ <- replaces (ext.heapMem) (IM.delete x)  -- only purpose of this is making simulation not run out of memory quickly while having no GC yet
>       return Nothing  -- keeping track of references in external memory is probably not worth the effort/cost

> queueRCM :: Maybe RCRef -> Proc ()
> queueRCM = Data.Foldable.mapM_ queueRC

> queueRCs :: FB (Maybe RCRef) -> Proc ()
> queueRCs = Data.Foldable.mapM_ queueRCM

> queueRCsBody :: (NodeElem -> RCMod) -> NodeTag -> FixedBody -> Proc ()
> queueRCsBody rcf t xs = queueRCs (zip3BodyWith rcVal bodyIndices (kindMaskBody t) xs) where
>   rcVal e (Just RefK) ~(OK (RVal rx)) = Just (rcf e, rx)
>   rcVal _ _           _               = Nothing

> queueRC :: RCRef -> Proc ()
> queueRC (RCNop, _      ) = return ()
> queueRC (_    , CVRef _) = return ()
> queueRC (rcm  , Ref _ x) = modify ((rcUnit.rcUpdates) %~ ((rcm,x):))

> modRefCounter_ :: RCHRef -> Proc ()
> modRefCounter_ (_  , (GlobalRef, _ , _)) = return ()  -- TODO maybe filter this trivial case out earlier?
> modRefCounter_ (rcm, (Unique   , ns, x)) = do
>   mhi <- getAHIndex x
>   case (mhi, rcm) of
>     (Nothing, RCDec) -> rcUnit.dropRefs %= enFifo (ns,x)
>     (Just i , RCDec) -> rcUnit.dropAHRefs %= enFifo (ns,i)
>     (_      , _    ) -> error (show rcm ++ " Unique")
> modRefCounter_ (rcm, (_        , ns, x)) = do
>   mhi <- getAHIndex x
>   case (mhi, rcm) of
>     (_      , RCNop  ) -> error "RCNop at refCounter update"
>     (Nothing, _      ) -> return ()
>     (Just i , RCInc  ) -> do
>       _ <- replacing (rcUnit.counters) i incRefCount
>       return ()
>     (Just i , RCtwInc) -> do
>       _ <- replacing (rcUnit.counters) i (incRefCount . incRefCount)
>       return ()
>     (Just i , RCDec  ) -> do
>         rc <- replacing (rcUnit.counters) i decRefCount
>         case rc of
>           Zero   -> error ("gcing dead: " ++ show x)
>           One    -> rcUnit.dropAHRefs %= enFifo (ns,i)   -- this assumes no increments are underway
>           _      -> return ()

> tryUseTagAt :: HeapAddr -> Proc (Maybe Int)
> tryUseTagAt x = fmap fst $ withCacheTags (Just x) id setLRU4 x

> tryDeAllocTagAt :: HeapAddr -> Proc (Maybe Int)
> tryDeAllocTagAt x = fmap fst $ withCacheTags (Just x) (const $ Nothing) dropLRU4 x

> getReplaceEntry :: HeapAddr -> Proc (Int, Maybe HeapAddr) 
> getReplaceEntry x = fmap (first fromJust) $ withCacheTags Nothing (const $ Just x) setLRU4 x

> withCacheTags :: Maybe HeapAddr -> (Maybe HeapAddr -> Maybe HeapAddr) -> (QuadElem -> LRU4 -> LRU4) -> HeapAddr -> Proc (Maybe Int, Maybe HeapAddr)
> withCacheTags lf fmt flru x = do
>   ct <- peeking (heap.cTags) (x `mod` cacheIxSize)
>   case lookupTag lf ct of
>     Nothing -> return (Nothing, Nothing)
>     Just ti -> do
>       let (nt, mtx) = modifyTag fmt flru ti ct 
>       poking (heap.cTags) (x `mod` cacheIxSize) nt
>       return (Just ((fromEnum ti * cacheIxSize) + (x `mod` cacheIxSize)), mtx)

> lookupTag :: Eq a => Maybe a -> CacheTag a -> Maybe QuadElem
> lookupTag (Nothing) (FourWay ta tb tc td lru)
>   | ta == Nothing = Just H
>   | tb == Nothing = Just I
>   | tc == Nothing = Just J
>   | td == Nothing = Just K
>   | otherwise     = Just $ oldLRU4 lru
> lookupTag (Just x) (FourWay ta tb tc td _  ) 
>   | ta == Just x = Just H
>   | tb == Just x = Just I
>   | tc == Just x = Just J
>   | td == Just x = Just K
>   | otherwise    = Nothing  

> modifyTag :: (Maybe a -> Maybe a) -> (QuadElem -> LRU4 -> LRU4) -> QuadElem -> (CacheTag a) -> (CacheTag a, Maybe a)
> modifyTag ft fu H (FourWay ta tb tc td lru) = (FourWay (ft ta) tb tc td (fu H lru), ta)
> modifyTag ft fu I (FourWay ta tb tc td lru) = (FourWay ta (ft tb) tc td (fu I lru), tb)
> modifyTag ft fu J (FourWay ta tb tc td lru) = (FourWay ta tb (ft tc) td (fu J lru), tc)
> modifyTag ft fu K (FourWay ta tb tc td lru) = (FourWay ta tb tc (ft td) (fu K lru), td)

> popFifo :: Lens' ProcState (Fifo a) -> Proc a
> popFifo fn = do
>   fs <- gets fn
>   let (fs', x) = deFifo fs
>   fn .= fs'
>   return x