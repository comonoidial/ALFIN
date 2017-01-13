module Alfin.Assemble where

import Data.List (elemIndex, findIndex, dropWhile, mapAccumL, delete, (\\), nub, sortBy)
import Data.Maybe (fromJust, fromMaybe, catMaybes, isJust, isNothing, maybeToList)
import Data.Ord (comparing)
import Data.Either (lefts, rights, partitionEithers)
import Data.Foldable (toList)
import Data.Array.IArray (Array, listArray, elems)
import Data.Int (Int32)
import Data.Word (Word32)
import Control.Monad.State
import Control.Arrow (first)

import Alfin.AsmLang
import Alfin.OptimizeAsm
import Simulate.ProcDefs

import Debug.Trace

type Queues = ([Maybe RefVar], [PrimVar], [BoolVar])

type StackVal  = (Maybe RefVar, [Maybe (Either RefVar PrimVar)], Quad (Maybe PrimVar))
type StackVals = [StackVal]

type FunTable = [(FName, (FunAddr, Maybe NodeElem))]

type CAFTable = [(FName, (PtrTag, HeapRef))]

type ConTable = [(CName, ((String, Word32), ConAlt))]

asmMod :: ([FName], AsmModule) -> (FunTable, [Instruction])
asmMod (fps, AsmModule _ ds fs) = (ft, is) where
  (rfs, cfs, vcs) = filterCAFs fs
  ct = concatMap buildCTable ds
  ~(ft, cvt, is) = flip evalState (AsmInfo ft fps ct cvt [] [] [] [] [] 0) $ do
    avc <- mapM (uncurry asmValueCAF) vcs
    afc <- mapM (asmFunCAF . fst) cfs
    let cinit = concatMap fst avc ++ map fst afc ++ replicate 0 (Nop (KeepRQ,popNone)) ++ [Jump (Receive defaultChannel) NoEvalCont (DropRQ, popNone)]
    afs <- mapM asmFun $ (map (\(f, b) -> Function f Nothing Nothing [] b) cfs ++ rfs)
    let fts = zipWith (\(f, e) i -> (f, ((show f, CodeAddr $ fromIntegral i), e))) (map fst afs) (init . scanl (+) (length cinit) $ map (length . snd) afs)
    return (fts, map snd avc ++ map snd afc, cinit ++ concatMap snd afs)

buildCTable :: DataType -> ConTable
buildCTable (DataType d cs) = zip cs' $ zipWith (\c i -> ((d, fromIntegral $ length cs), (show c,i))) cs' [0..] where cs' = map fst cs

valueCAF :: AsmBlock -> Bool
valueCAF (AsmBlock xs (NodeReturn t _)) = whnfTag t && all isValueStmt xs
valueCAF _ = False

isValueStmt :: Stmt -> Bool
isValueStmt (_ :<-:  _) = True
isValueStmt (_ :<~:  _) = True
isValueStmt (_ :<-?: _) = True
isValueStmt _           = False

filterCAFs :: [Function] -> ([Function], [(FName, AsmBlock)], [(FName, AsmBlock)])
filterCAFs = fcs [] [] []
  where fcs fs cs vs [] = (reverse fs, reverse cs, reverse vs)
        fcs fs cs vs ((Function n Nothing Nothing [] b):xs)
          | valueCAF b = fcs fs cs ((n,b):vs) xs
          | otherwise  = fcs fs ((n,b):cs) vs xs
        fcs fs cs vs (x:xs) = fcs (x:fs) cs vs xs

data AsmInfo = AsmInfo {funs :: FunTable, procs :: [FName], cons :: ConTable, cafs :: CAFTable, usedVars :: [String],
  rvQ :: [Maybe RefVar], pvQ :: [PrimVar], cvQ :: [BoolVar], stvs :: StackVals, storeCount :: Int}

type AsmGen a = State AsmInfo a

pushNode :: CallResultRef -> [Parameter] -> AsmGen ()
pushNode mr xs
 | length xs > 7 = error ("too many args: " ++ showParams xs)
 | otherwise =  modify (\a -> a {stvs = (either Just (const Nothing) mr, (map Just) xs, (stackPrims xs)):(stvs a)})

pushStack :: Bool -> CallResultRef -> [Parameter] -> [PrimVar] -> AsmGen () -- Bool is push tag info
pushStack pti mr xs ys 
  | length ys > 4 = error ("Too many prim args:" ++ concatMap (" #"++) ys)
  | (length xs + length ys) > 7 = error ("too many args: " ++ showParams xs ++ " :" ++ concatMap (" #"++) ys)
  | otherwise     =  modify (\a -> a {stvs = pn:(stvs a)})
--  where zs = case (map Just ys ++ repeat Nothing) of {(h:i:j:k:_) -> Q h i j k}
  where zs = stackPrims (map (const $ Left undefined) xs ++ map Right ys)
        pn = (either Just (const Nothing) mr, (map Just) xs, zs)

stackPrims :: [Parameter] -> Quad (Maybe PrimVar)
stackPrims xs = let xs' = xs ++ repeat (Left undefined) in
  case zipWith firstPrim (take 4 xs') (drop 4 xs') of
   (h:i:j:k:_) -> Q h i j k

firstPrim :: Parameter -> Parameter -> Maybe PrimVar
firstPrim (Right a) _         = Just a
firstPrim _         (Right b) = Just b
firstPrim _         _         = Nothing

pushRef :: RefVar -> AsmGen ()
pushRef x = modify (\a -> a {rvQ = (Just x):(rvQ a)})

pushPrim :: PrimVar -> AsmGen ()
pushPrim x = modify (\a -> a {pvQ = x:(pvQ a)})

pushCond :: BoolVar -> AsmGen ()
pushCond x = modify (\a -> a {cvQ = x:(cvQ a)})

clearQueues :: AsmGen ()
clearQueues = modify (\a -> a {rvQ = [], pvQ = [], cvQ = []})

clearScope :: AsmGen ()
clearScope = modify (\a -> a {rvQ = [], pvQ = [], cvQ = [], stvs = []})

getScope :: AsmGen (Queues, StackVals)
getScope = gets (\a -> ((rvQ a, pvQ a, cvQ a), stvs a))

setScope :: (Queues, StackVals) -> AsmGen ()
setScope ((r,p,c), s) = modify (\a -> a {rvQ = r, pvQ = p, cvQ = c, stvs = s})

getSTVals :: AsmGen StackVals
getSTVals = gets stvs

setSTVals :: StackVals -> AsmGen ()
setSTVals x = modify (\a -> a {stvs = x})

setUsedVars :: [String] -> AsmGen ()
setUsedVars x = modify (\a -> a {usedVars = x})

useVar :: String -> AsmGen ()
useVar x = modify (\a -> a {usedVars = delete x (usedVars a)})

getFun :: FName -> AsmGen FunAddr
getFun f = gets (fst . fromJust . lookup f . funs)

getCAF :: FName -> AsmGen (PtrTag, HeapRef)
getCAF f = gets (fromMaybe (error ("getCAF " ++ show f)) . lookup f . cafs)

buildTag :: AsmTag -> NodeKind -> [Either r p] -> AsmGen (Bool, NodeTag)
buildTag t k n = do
  fs <- gets funs
  cs <- gets cons
  fps <- gets procs
  let ipf = case t of {FunTag f | f `elem` fps -> True; _ -> False}
  let (as,bs) = partitionEithers n
  let n' = map Left as ++ map Right bs
  let (nkm, t') = asmTag fs cs (if ipf then n' else n) t
  return (ipf, NodeTag k (toEnum $ length n) nkm t')

getAlt :: CName -> AsmGen ConAlt
getAlt a = gets (snd . fromMaybe (error ("getAlt " ++ show a)) . lookup a . cons)

nodeSizeNum_ :: NodeSize -> Int
nodeSizeNum_ x = case x of
  SingleNode -> 1
  DoubleNode -> 1 --2 -- for now all nodes are size one

incrSCount :: NodeSize -> AsmGen ()
incrSCount n = modify (\a -> a {storeCount = nodeSizeNum_ n + storeCount a})

getSCount :: AsmGen Int
getSCount = gets storeCount

asmFunCAF :: FName -> AsmGen (Instruction, (FName, (PtrTag, HeapRef)))
asmFunCAF f = do   -- TODO all static fun node should be double size unless the result is known to be small
  t <- liftM (NodeTag Static 0 emptyKinds . \fa -> Fun fa Nothing WithUpd) $ getFun f
  hi <- getSCount
  incrSCount SingleNode
  return (Store t (listToBody []) (DropRQ, popNone), (f, (node2PtrTag t, (GlobalRef, SingleNode, hi))))

asmValueCAF :: FName -> AsmBlock -> AsmGen ([Instruction], (FName, (PtrTag, HeapRef)))
asmValueCAF f b@(AsmBlock xs (NodeReturn t n)) = do
  clearScope
  setUsedVars (readVarsB b)
  as <- mapM asmVCStmt xs
  (ipf, t') <- buildTag t Static n -- TODO deal with argument order in proc like holed funs
  nr <- indexNode n
  hi <- getSCount
  incrSCount (nodeSize__ n)
  return (as ++ [Store t' nr (DropRQ,popNone)], (f, (node2PtrTag t', (GlobalRef, (nodeSize__ n), hi))))
asmValueCAF f _ = error ("not a value CAF " ++ show f)

asmVCStmt :: Stmt -> AsmGen Instruction
asmVCStmt (x :<~: Constant c) = do
  pushPrim x
  return (PrimInstr (PrimConst (fromIntegral c)) PrimNop (KeepRQ,popNone))
asmVCStmt (x :<-: StoreNode (FunTag f) []) = do
  c <- getCAF f
  pushRef x
  return (PushCAFRef c (KeepRQ,popNone))
asmVCStmt (x :<-: StoreNode (BoxCon c) [Right (BigImm n)]) = do
  c' <- gets (asmConName c . cons)
  pushRef x
  return (StoreCVal (PrimBox c' (fromIntegral n)) (KeepRQ,popNone))
asmVCStmt (x :<-: StoreNode t []) = do
  (_,t') <- buildTag t Dynamic []
  pushRef x
  return (StoreCVal (compactTagValue t') (KeepRQ,popNone))
asmVCStmt (x :<-: StoreNode t n) = do
  (ipf, t') <- buildTag t Dynamic n
  let (as,bs) = partitionEithers n
  let pn' = map Left as ++ map Right bs
  nr <- indexNode (if ipf then pn' else n)
  incrSCount (nodeSize__ n)
  pushRef x
  case t of
    (FSelTag _ i) -> return (StoreFE (nodeArity t', kindMask t') WithUpd x (Select $ toEnum i) (KeepRQ,popNone)) where FB (T (Just (Left x)) _               _              ) _  = nr
    (ApTag     1) -> return (StoreFE (nodeArity t', kindMask t') WithUpd x (Apply1 a         ) (KeepRQ,popNone)) where FB (T (Just (Left x)) (Just (Left a)) _              ) _  = nr
    (ApTag     2) -> return (StoreFE (nodeArity t', kindMask t') WithUpd x (Apply2 a b       ) (KeepRQ,popNone)) where FB (T (Just (Left x)) (Just (Left a)) (Just (Left b))) _  = nr
    _             -> return (Store   t'                                    nr                  (KeepRQ,popNone))
asmVCStmt x = error ("not a value CAF Stmt " ++ show x)

asmFun :: Function -> AsmGen ((FName, Maybe NodeElem) , [Instruction])
asmFun (Function f mr e n b) = do
  clearScope
  isp <- gets ((f `elem`) . procs)
  let (xs,ys) = partitionEithers n
  if isp
    then pushStack True dummyResultRef (map Left xs) ys
    else pushNode (maybe dummyResultRef Left mr) n
  is <- asmBlock b
  let fixupNF = \i -> toEnum (i - if isp then length (rights $ take i n) else 0) -- fixup next fetch for procs
  return ((f, fmap fixupNF e), is)

asmBlock :: AsmBlock -> AsmGen [Instruction]
asmBlock (AsmBlock xs t) = do
  setUsedVars (readVarsB $ AsmBlock xs t)
  ps <- avoidOverSizedPops      -- workaround for when a datatype is pushed onto the stack as fifth element
  cs <- eliminateDeadNodeRefs   -- required to make lazy node ref creation work if node body is read in different instructions
  as <- mapM asmStmt xs
  bs <- asmTerm t
  return (ps ++ cs ++ concat as ++ bs)

eliminateDeadNodeRefs :: AsmGen [Instruction]  -- TODO consider merging Push instructions if this is followed by a prepareStackForCall
eliminateDeadNodeRefs = do
  vs  <- gets usedVars
  dnrs <- gets (map (deadNodeRefVars vs) . stvs)
  case unzip (rights dnrs) of
    ([], []) -> return []
    (xs, ys) -> do
      let as = concat xs
      let bs = concat ys
      nr <- mapM indexMoveR as
      wr <- mapM indexMoveP bs
      setSTVals (lefts dnrs)
      pushStack False dummyResultRef (map Left as) bs
      let pm = map (either (const Keep) (const Pop)) dnrs ++ repeat Keep
      let nwr = listToBody (map Left nr ++ map Right wr)
      return [Push nwr (KeepRQ, buildPops pm)]

deadNodeRefVars :: [String] -> StackVal -> Either StackVal ([RefVar],[PrimVar])
deadNodeRefVars vs (Just x, xs, (Q yh yi yj yk)) | (x `notElem` vs) && any (`elem` vs) (lefts $ catMaybes xs) = Right (lefts $ catMaybes xs, nub (rights (catMaybes xs) ++ catMaybes [yh,yi,yj,yk]))
deadNodeRefVars vs n                                                                                          = Left n


asmTerm :: TermStmt -> AsmGen [Instruction]
asmTerm (NodeReturn (BoxCon c) [Right (BigImm n)]) = do
  c' <- gets (asmConName c . cons)
  pm <- minimizeStack
  return [ReturnConst c' (fromIntegral n) pm]
asmTerm (NodeReturn (BoxCon c) [Right x]) = do
  c' <- gets (asmConName c . cons)
  y <- indexP x
  pm <- minimizeStack
  return [ReturnPrim c' y pm]
asmTerm (NodeReturn t []) = do
  (_,t') <- buildTag t Dynamic []
  pm <- minimizeStack
  return [ReturnTag t' pm]
asmTerm (NodeReturn RawTuple as) = do
  xs <- mapM indexR $ lefts as
  ys <- indexVS $ rights as
  pm <- minimizeStack
  let xys = listToBody (map Left xs ++ map Right ys)
  return [ReturnRaw xys pm]
asmTerm (NodeReturn t xs) = do
  (ipf, t') <- buildTag t Dynamic xs -- TODO deal with argument order in proc like holed funs
  nr <- indexNode xs
  pm <- minimizeStack
  return [Return t' nr pm]
asmTerm (TopReturn) = do
  (pq, Q _ pb pc pd) <- minimizeStack
  let pm = Q Keep pb pc pd
  return [ReturnTop (pq, pm)]
asmTerm (BoolReturn c t e) = do
  (_,t') <- buildTag t Dynamic []
  (_,e') <- buildTag e Dynamic []
  cr <- indexB c
  pm <- minimizeStack
  return [IfElse PrimNop cr (RelCodeAddr 1) pm, ReturnTag t' (KeepRQ,popNone), ReturnTag e' (KeepRQ,popNone)]
--  return [ReturnCond cr (dynTag t') (dynTag e') pm]
asmTerm (Error x) = do
  y <- indexR x
  pm <- minimizeStack
  return [Throw y pm]
asmTerm (TailCall c cc) = do
  c' <- asmCallExp c
  (pcs, cc') <- asmPostCalls cc
  pm <- minimizeStack
  return (pcs ++ [Jump c' cc' pm])
asmTerm (IfThenElse c x y) = do
  b <- indexB c
  pm <- minimizeStack
  s <- getScope
  xs <- asmBlock x
  setScope s
  ys <- asmBlock y
  return ([IfElse PrimNop b (RelCodeAddr $ length xs) pm] ++ xs ++ ys)
asmTerm (CaseOf c cc ms md xs) = do
  ps <- prepareStackForCall (readVarsCCC (c,cc))
  c' <- asmCallExp c
  (pcs,cc') <- asmPostCalls cc   -- TODO move the continuations except the first to before prepareStackForCall
  clearQueues
  pm <- minimizeStack
  s <- getScope
  nc <- gets (snd . fst . fromJust . lookup ((\(cx,_,_,_) -> cx) $ head xs) . cons)
  let sp = case (isNoDeconstructCase xs, ms) of
             (True , Left  _) -> OnlySC
             (True , Right _) -> OnlyTag
             (False, Left  _) -> NodeWSC
             (False, Right _) -> OnlyNode
  nsts <- gets (length . stvs)
  let trps = buildPops (Keep : replicate nsts Pop ++ repeat Keep) :: StackPops
  adb <- asmDefAlt ms trps md
  as <- mapM (asmAlt s ms) xs
  let aos = snd $ mapAccumL (\o ((ai, (me, na)), b) -> (o + length b, (ai, if na then (Left (me, RelCodeAddr o)) else (Right trps)))) (length $ snd adb) as
  let is = buildCaseTable $ map (fromMaybe (fst adb) . flip lookup aos) [0..nc-1]
  return (ps ++ pcs ++ (Case sp c' cc' is pm : concat (snd adb : map snd as)))

-- TODO actual usage of variables instead of presence
isNoDeconstructCase :: [(CName, [Parameter], Maybe Int, AsmBlock)] -> Bool
isNoDeconstructCase = all (\(_,xs,_,_) -> null xs)  -- FIXME return False for BigCase with TopReturn's

asmDefAlt :: CallResultRef -> StackPops -> Maybe AsmBlock -> AsmGen (Either (NextFetch, RelCodeAddr) StackPops, [Instruction])
asmDefAlt _  _  Nothing = return (error "no default alt", [])
asmDefAlt mr ps (Just (AsmBlock [] TopReturn)) = return (Right ps, [])
asmDefAlt mr _  (Just b) = do
  pushNode mr []
  is <- asmBlock b
  return (Left (Nothing, RelCodeAddr 0), is)

asmAlt :: (Queues, StackVals) -> CallResultRef -> (CName, [Parameter], Maybe Int, AsmBlock) -> AsmGen ((Word32, (NextFetch, Bool)), [Instruction])
asmAlt s _ (c, _, _, AsmBlock [] TopReturn) = do
  setScope s
  a <- getAlt c
  return ((snd a, (Nothing, False)), [])
asmAlt s mr (c, n, me, x) = do
  setScope s
  pushNode mr n
  a <- getAlt c
  is <- asmBlock x
  return ((snd a, (fmap toEnum me, True)), is)

asmStmt :: Stmt -> AsmGen [Instruction]
asmStmt (x :<~: Constant c) = do
  pm <- minimizeStack
  pushPrim x
  return [PrimInstr (PrimConst (fromIntegral c)) PrimNop pm]
asmStmt (x :<~: RunPrimOp p a Nothing) = do
  a' <- indexP a
  pm <- minimizeStack
  pushPrim x
  return [PrimInstr (PrimOp (asmOp p) a' (Im 0) CTrue) PrimNop pm]
asmStmt (x :<~: RunPrimOp p a (Just b)) = do
  a' <- indexP a
  b' <- indexP b
  pm <- minimizeStack
  pushPrim x
  return [PrimInstr (PrimOp (asmOp p) a' b' CTrue) PrimNop pm]
asmStmt (x :<-?: RunCmpOp p a b) = do
  a' <- indexP a
  b' <- indexP b
  pm <- minimizeStack
  pushCond x
  return [PrimInstr (CmpOp (asmCmp p, LogAnd) a' b' CTrue) PrimNop pm]
--asmStmt (x :<-?: RunLogicOp p a b) = do
--  a' <- indexB a
--  b' <- indexB b
--  pm <- minimizeStack
--  pushCond x
--  return [PrimInstr (LogicOp (asmLogic p) a' b') PrimNop pm]
asmStmt (x :<-: StringConstant s) = do
  pm <- minimizeStack
  modify (\a -> a {rvQ = replicate (length s) Nothing ++ rvQ a}) -- 2*len s dummy refs are pushed
  pushRef x -- TODO deal with keeping reference reachable after long string constants
  cs <- gets cons
  let sn = StoreCVal (compactTagValue $ uncurry (NodeTag Dynamic 0) $ asmTag [] cs [] (ConTag $ CName "GHCziTypes.ZMZN")) pm
  let cb = PrimBox (asmConName (CName "GHCziTypes.Czh") cs)
  let lct = NodeTag Dynamic 2 (FB (T RefK RefK PrimK) (Q PrimK PrimK PrimK PrimK)) (Con (asmConName (CName "GHCziTypes.ZC") cs))
  let bn = FB (T (Just $ Left $ RQ 0) (Just $ Left $ RQ 1) Nothing) (Q Nothing Nothing Nothing Nothing)
  return $ reverse $ foldr (\c -> ([Store lct bn (KeepRQ,popNone), StoreCVal (cb $ fromIntegral $ fromEnum c) (KeepRQ,popNone)] ++)) [sn] s
asmStmt (x :<-: StoreNode (FunTag f) []) = do
  c <- getCAF f
  pm <- minimizeStack
  pushRef x
  return [PushCAFRef c pm]
asmStmt (x :<-: StoreNode t n) = do
  (ipf, t') <- buildTag t Dynamic n
  case (plainTag t', n) of
    (Box (c, i), [Right (BigImm n)]) -> do
      pm <- minimizeStack
      pushRef x
      return [StoreCVal (PrimBox (c,i) (fromIntegral n)) pm] 
    (Box a, [Right y]) -> do
      ry <- indexP y
      pm <- minimizeStack
      pushRef x
      return [StoreBox a ry pm]
    (ct, [] ) -> do
      pm <- minimizeStack
      pushRef x
      return [StoreCVal (compactTagValue t') pm]
    _ -> do
     let (as,bs) = partitionEithers n
     let pn' = map Left as ++ map Right bs
     nr <- indexNode (if ipf then pn' else n)
     pm <- minimizeStack
     pushRef x
     case t of
       (FSelTag _ i) -> return [StoreFE (nodeArity t', kindMask t') WithUpd x (Select $ toEnum i) pm] where FB (T (Just (Left x)) _               _              ) _ = nr
       (ApTag     1) -> return [StoreFE (nodeArity t', kindMask t') WithUpd x (Apply1 a         ) pm] where FB (T (Just (Left x)) (Just (Left a)) _              ) _ = nr
       (ApTag     2) -> return [StoreFE (nodeArity t', kindMask t') WithUpd x (Apply2 a b       ) pm] where FB (T (Just (Left x)) (Just (Left a)) (Just (Left b))) _ = nr
       _             -> return [Store   t'                                     nr                 pm]
asmStmt ((ms,mn) :<=: (c,cc)) = do
  as <- prepareStackForCall (readVarsCCC (c,cc))
  c' <- asmCallExp c
  (pcs,cc') <- asmPostCalls cc   -- TODO move the continuations except the first to before prepareStackForCall
  clearQueues
  pm <- minimizeStack
  case mn of
    Nothing                       -> pushNode  ms []
    Just (BoxCon _, [Right x], _) -> pushStack True  ms [] [x]
    Just (RawTuple, xs       , _) -> pushStack False dummyResultRef (map Left $ lefts xs) (rights xs)
    Just (_       , xs       , _) -> pushNode  ms xs
  let sp = case (mn, ms) of
             (Nothing, Left  _) -> OnlySC
             (Nothing, Right _) -> OnlyTag
             (Just _ , Left  _) -> NodeWSC
             (Just _ , Right _) -> OnlyNode  
  return (as ++ pcs ++ [Call sp c' cc' (join $ fmap (\(_,_,mi) -> fmap toEnum mi) mn) pm])
asmStmt (Put_IO t n) = do
  (ipf,t') <- buildTag t Dynamic n  -- TODO deal with argument order in proc like holed funs
  nr <- indexNode n
  pm <- minimizeStack
  return [Send defaultChannel t' nr pm]
asmStmt x = error ("TODO asmStmt " ++ show x)

asmCallExp :: CallExp -> AsmGen Callable
asmCallExp (EvalRef x) = do
  y <- indexR x
  return (Eval y)
asmCallExp (LoadRef x) = do
  y <- indexR x
  return (Fetch y)
asmCallExp (UseFetched True) = return EvalFetched
asmCallExp (UseFetched False) = return PushFetched
asmCallExp (Run_Fun f []) = do
  c <- getCAF f
  return (EvalCAF c)
asmCallExp (Run_Fun f nb) = do
  f' <- getFun f
  ips <- gets ((f `elem`) . procs)
  let (as, bs) = partitionEithers nb
  if ips 
    then do
      xs <- mapM indexR as
      ys <- indexVS bs
      let xys = listToBody (map Left xs ++ map Right ys)
      return (Proc f' xys)
    else do
      xs <- indexNode nb
      return (Run f' xs)
asmCallExp (Run_Fix f as) = do
  xs <- indexNode as
  f' <- getFun f
  return (Fix f' xs)
asmCallExp (Get_IO) = return (Receive defaultChannel)

asmPostCalls :: [PostCall] -> AsmGen ([Instruction], ExtraCont)
asmPostCalls [] = return ([], NoEvalCont)
asmPostCalls xs = do
  (p:ps) <- fmap concat $ mapM asmPostCall xs
  let pm = (KeepRQ, buildPops (repeat Keep))
  return (map (flip PushCont pm) $ reverse ps, p)

asmPostCall :: PostCall -> AsmGen [ExtraCont]
asmPostCall (Applying xs) = do
  ys <- indexNode xs
  let rs = lefts $ catMaybes $ toList ys
  unless (null $ rights $ catMaybes $ toList ys) $ error ("Applying with primitive value" ++ show (rights $ catMaybes $ toList ys))
  case rs of 
   []    -> error "empty list in Applying"
   [x]   -> return [Apply1 x]
   [x,y] -> return [Apply2 x y]
   _     -> return $ map Apply1 rs
asmPostCall (Selecting _ i) = return [Select $ toEnum i]
asmPostCall (NextFetch x) = do
  y <- indexR x
  return [ThenFetch y]
asmPostCall (CatchWith x) = do
  h <- indexR x
  return [WithCatch h]
asmPostCall (WithOp p x) = do
  y <- indexP x
  return [WithPrim (asmOp p) y]
  
compactTagValue :: NodeTag -> CompactValue
compactTagValue (NodeTag _ _ _  (Con  c   )) = EnumTag c    
compactTagValue (NodeTag _ _ vs (DCon c  n)) = EmptyDCon c  n vs
compactTagValue (NodeTag _ _ vs (Pap f i n)) = EmptyPap f i n vs
compactTagValue (NodeTag _ _ vs (PE fe   n)) = EmptyPEF fe  n vs
compactTagValue t                          = error ("tag not compactable: " ++ show t)

asmTag :: FunTable -> ConTable -> [Either r p] -> AsmTag -> (KindMask, Tag)
asmTag _  _  nb (ConTag (CName ('.':'(':'#':_))) = (bodyKinds_ nb         , Unboxed                                        )
asmTag _  cs nb (ConTag c)                       = (bodyKinds_ nb         , Con   (snd $ fromJust $ lookup c cs)           )
asmTag _  cs nb (DecTag c x)                     = (bodyKinds_ (nb ++ uas), DCon  (snd $ fromJust $ lookup c cs) (toEnum x)) where uas = replicate x (Left undefined)
asmTag _  cs nb (BoxCon c)                       = (singlePrimK           , Box   (snd $ fromJust $ lookup c cs)           )
asmTag fs _  nb (FunTag f)                       = (bodyKinds_ nb         , uncurry Fun (fromJust $ lookup f fs) WithUpd   )
asmTag fs _  nb (PapTag f x)                     = (bodyKinds_ (nb ++ uas), uncurry Pap (fromJust $ lookup f fs) (toEnum x)) where uas = replicate x (Left undefined)
asmTag _  _  nb (ApTag 1)                        = (bodyKinds_ nb         , FE E_ap1              WithUpd                  )
asmTag _  _  nb (ApTag 2)                        = (bodyKinds_ nb         , FE E_ap2              WithUpd                  )
asmTag _  _  nb (FSelTag _ i)                    = (bodyKinds_ nb         , FE (E_sel $ toEnum i) WithUpd                  )
asmTag _  _  [] (PSelTag _ i)                    = (singleRefK            , PE (E_sel $ toEnum i) 1                        )
asmTag _  _  [] (PIdTag)                         = (singleRefK            , PE (E_id) 1                                    )

asmConName :: CName -> ConTable -> ConAlt
asmConName c cs = snd $ fromJust $ lookup c cs

asmOp :: OpName -> PrimOp
asmOp (OpName "zmzh"       ) = OpSub
asmOp (OpName "zpzh"       ) = OpAdd
asmOp (OpName "ztzh"       ) = OpMul
asmOp (OpName "+"          ) = OpAdd
asmOp (OpName "*"          ) = OpMul
asmOp (OpName "negateIntzh") = OpNeg
asmOp (OpName "modIntzh"   ) = OpMod
asmOp x                      = error ("asmBinOp " ++ show x)

asmCmp :: OpName -> CmpOp
asmCmp (OpName "zlzh"  ) = CmpLT
asmCmp (OpName "zlzezh") = CmpLE
asmCmp (OpName "zgzh"  ) = CmpGT
asmCmp (OpName "zgzezh") = CmpGE
asmCmp (OpName "zezezh") = CmpEQ
asmCmp (OpName "zszezh") = CmpNE
asmCmp (OpName ">"     ) = CmpGT
asmCmp x                 = error ("asmCmpOp " ++ show x)

asmLogic :: OpName -> LogicOp
asmLogic (OpName "and") = LogAnd
asmLogic (OpName "or" ) = LogOr
asmLogic x              = error ("asmLogicOp " ++ show x)

prepareStackForCall :: [String] -> AsmGen [Instruction]
prepareStackForCall cvs = do
  vs <- gets usedVars
  rs <- gets (catMaybes . rvQ)
  ps <- gets pvQ
  let rvs = vs \\ cvs
  nstns <- gets (length . catMaybes . map (snd . minimizeNode rvs) . stvs)
  case (nstns > 3) of -- limit stack depth to 4 -- FIXME may need spilling to heap in some cases  -- TODO allow deep stack as long as they are not read
    False -> do
      let xs = filter (`elem` rvs) rs
      let ys = filter (`elem` rvs) ps
      as <- mapM indexMoveR xs
      bs <- mapM indexMoveP ys
      modify (\a -> a {rvQ = map (\r -> if (r `elem` map Just rvs) then Nothing else r) (rvQ a)})
      case (xs,ys) of
        ([],[]) -> return []
        _       -> do
          pushStack False dummyResultRef (map Left xs) ys
          let abs = listToBody (map Left as ++ map Right bs)
          return [Push abs (KeepRQ, popNone)]
    True  -> do
      (stx:stxs) <- gets (reverse . sortBy (comparing (stackNodeSizeMeasure . snd)) . zip [0..] . stvs)   -- TODO also select what stack nodes to merge on which are not read by call stuff
--      trace ("\nSORTED STACK: " ++ show (stx:stxs)) $ return ()
      let mvs = nub $ concatMap (\(nr,xs,(Q yh yi yj yk)) -> maybeToList (fmap Left nr) ++ catMaybes xs ++ map Right (catMaybes [yh,yi,yj,yk])) $ map snd stxs
--      trace ("\nMERGE PUSH " ++ show mvs) $ return ()
      let xs = filter (`elem` rvs) rs ++ lefts  mvs
      let ys = filter (`elem` rvs) ps ++ rights mvs
      when (length ys > 4) $ error "generating impossible stack fixup Push"
      when ((length xs + length ys) > 8) $ error "generating impossible stack fixup Push"
      as <- mapM indexMoveR xs
      bs <- mapM indexMoveP ys
      modify (\a -> a {rvQ = map (\r -> if (r `elem` map Just rvs) then Nothing else r) (rvQ a)})
      setSTVals [snd stx]
      pushStack False dummyResultRef (map Left xs) ys
      let ps = replicate (length stxs) Pop
      let pm = buildPops $ take (fst stx) ps ++ [Keep] ++ drop (fst stx) ps ++ repeat Keep  -- generate popmask
      let abs = listToBody (map Left as ++ map Right bs)
      return [Push abs (KeepRQ, pm)]

stackNodeSizeMeasure :: StackVal -> Int
stackNodeSizeMeasure (nr,xs,(Q yh yi yj yk)) = (if isJust nr then 1 else 0) + length (catMaybes xs) + (2 * length (catMaybes [yh,yi,yj,yk]))

avoidOverSizedPops :: AsmGen [Instruction]
avoidOverSizedPops = do
  vs <- gets usedVars
  stxs <- gets stvs
  if (length stxs <= 4)
    then return []
    else do
      let (pm, mvs) = unzip $ map (minimizeNode vs) $ take 4 stxs
      setSTVals (catMaybes mvs ++ drop 4 stxs)
      return [Nop (KeepRQ, buildPops (pm ++ repeat Keep))]

minimizeRQ :: AsmGen PopRQ
minimizeRQ = do
  vs <- gets usedVars
  rqs <- gets (catMaybes . rvQ)
  return (if (any (`elem` vs) rqs) then KeepRQ else DropRQ)

minimizeStack :: AsmGen (PopRQ, StackPops)
minimizeStack = do
  prq <- minimizeRQ
  vs <- gets usedVars
  (pm, mvs) <- gets (unzip . map (minimizeNode vs) . stvs)
  setSTVals $ catMaybes mvs
  when (length (reverse $ dropWhile (==Keep) $ reverse pm) > 4) $ error ("popMask too big: " ++ show pm ++ "\n" ++ show mvs)
  return (prq, buildPops (pm ++ repeat Keep))

minimizeNode :: [String] -> StackVal -> (PopNode, Maybe StackVal)
minimizeNode vs sn
  | any (`elem` vs) (stackNodeVars sn) = (Keep, Just sn)
  | otherwise                          = (Pop,  Nothing)

stackNodeVars :: StackVal -> [String]
stackNodeVars (nr,xs,(Q yh yi yj yk)) = nub (map (either id id) (catMaybes xs) ++ catMaybes [yh,yi,yj,yk] ++ maybeToList nr)

indexNode :: [Argument] -> AsmGen NodeRead
indexNode = fmap listToBody . mapM indexElem

indexElem :: Argument -> AsmGen (Either RefRead WordRead)
indexElem (Left x)  = liftM Left  $ indexR x
indexElem (Right x) = liftM Right $ indexNW x

indexMoveR :: RefVar -> AsmGen RefRead   -- destructive move that does not change usedVar
indexMoveR x = do
  rqs <- gets rvQ
  vs  <- gets (map (\(_,b,_) -> b) . stvs)
  nrs <- gets (map (\(a,_,_) -> a) . stvs)
  let mqi = elemIndex (Just x) rqs
  let msi = findIndex ((Just (Left x)) `elem`) vs
  case (mqi, msi) of
    (Just qi, _) -> do
       modify (\a -> a {rvQ = map (\r -> if (r == Just x) then Nothing else r) (rvQ a)})
       return (RQ qi)
    (Nothing, Just si) -> do
      modify (\a -> a {stvs = map (\(k,l,m) -> (k, map (\r -> if (r == Just (Left x)) then Nothing else r) l, m)) (stvs a)})
      let me = fmap toEnum (elemIndex (Just (Left x)) (vs!!si))
      return $ fromMaybe (error ("indexR " ++ x)) $ liftM2 R msi me
    (Nothing, Nothing) -> do
      modify (\a -> a {stvs = map (\(k,l,m) -> ((if (k == Just x) then Nothing else k), l, m)) (stvs a)})
      let ni = elemIndex (Just x) nrs
      return (NR $ fromMaybe (error ("indexR " ++ x)) ni)

indexR :: RefVal -> AsmGen RefRead
indexR (SmallCon c) = gets (SCC . asmConName c . cons)
indexR (RefVar x) = do
  rqs <- gets rvQ
  vs  <- gets (map (\(_,b,_) -> b) . stvs)
  nrs <- gets (map (\(a,_,_) -> a) . stvs)
  useVar x
  isCopy <- gets ((x `elem`) . usedVars)
  let mqi = elemIndex (Just x) rqs
  let msi = findIndex ((Just (Left x)) `elem`) vs
  case (isCopy, mqi, msi) of
    (True , Just qi, _) -> return (CRQ qi)
    (False, Just qi, _) -> do
       modify (\a -> a {rvQ = map (\r -> if (r == Just x) then Nothing else r) (rvQ a)})
       return (RQ qi)
    (True , Nothing, Just si) -> do
      let me = fmap toEnum (elemIndex (Just (Left x)) (vs!!si)) 
      return $ fromMaybe (error ("indexR " ++ x)) $ liftM2 CR msi me
    (False, Nothing, Just si) -> do
      modify (\a -> a {stvs = map (\(k,l,m) -> (k, map (\r -> if (r == Just (Left x)) then Nothing else r) l, m)) (stvs a)})
      let me = fmap toEnum (elemIndex (Just (Left x)) (vs!!si))
      return $ fromMaybe (error ("indexR " ++ x)) $ liftM2 R msi me
    (True , Nothing, Nothing) -> do
      let ni = elemIndex (Just x) nrs
      return (CNR $ fromMaybe (error ("indexR " ++ x)) ni)
    (False, Nothing, Nothing) -> do
      modify (\a -> a {stvs = map (\(k,l,m) -> ((if (k == Just x) then Nothing else k), l, m)) (stvs a)})
      let ni = elemIndex (Just x) nrs
      return (NR $ fromMaybe (error ("indexR " ++ x)) ni)

indexNW :: PrimVal -> AsmGen WordRead
indexNW (SmallImm i) = return (PA (Im i))
indexNW (PrimVar x)  = do
  ps <- gets pvQ
  mv <- readPofV x
  mw <- readPofW x
  useVar x
  return $ fromMaybe (error ("indexNW " ++ x)) (mw `mplus` fmap (PA . PQ) (elemIndex x ps) `mplus` fmap PA mv)

indexVS :: [PrimVal] -> AsmGen [PrimRead]
indexVS = mapM indexP

indexMoveP :: PrimVar -> AsmGen PrimRead   -- does not change usedVar
indexMoveP x = do
  ps <- gets pvQ
  mv <- readPofV x
  return $ fromMaybe (error ("indexMoveP " ++ x)) (fmap PQ (elemIndex x ps) `mplus` mv)

indexW :: PrimVal -> AsmGen WordRead
indexW (SmallImm i) = return (PA (Im i))
indexW (PrimVar x)  = do
  ps <- gets pvQ
  mv <- readPofV x
  mw <- readPofW x
  useVar x
  return $ fromMaybe (error ("indexW " ++ x)) (fmap (PA . PQ) (elemIndex x ps) `mplus` fmap PA mv `mplus` mw)

indexP :: PrimVal -> AsmGen PrimRead
indexP (SmallImm i) = return (Im i)
indexP (PrimVar x) = do
  ps <- gets pvQ
  mv <- readPofV x
  vs <- gets usedVars
  useVar x
  return $ fromMaybe (error ("indexP " ++ x ++ "\n" ++ show vs)) $ (liftM PQ (elemIndex x ps) `mplus` mv)

readPofV :: PrimVar -> AsmGen (Maybe PrimRead)
readPofV x = do
  vs <- gets (map (\(_,_,c) -> c) . stvs)
  let mi = findIndex (\(Q h i j k) -> x `elem` catMaybes [h,i,j,k]) vs
  let me = fmap toEnum (fmap (vs !!) mi >>= \(Q h i j k) -> elemIndex (Just x) [h,i,j,k])
  return $ liftM2 V mi me

readPofW :: PrimVar -> AsmGen (Maybe WordRead)
readPofW x = do
  vs <- gets (map (\(_,b,_) -> b) . stvs)
  let mi = findIndex ((Just (Right x)) `elem`) vs
  let me = fmap toEnum (fmap (vs !!) mi >>= elemIndex (Just (Right x)))
  return $ liftM2 W mi me

indexB :: BoolVar -> AsmGen CondRead
indexB x = gets (CQ False . fromJust . elemIndex x . cvQ)

buildPops :: [PopNode] -> StackPops
buildPops (pa:pb:pc:pd:_) = Q pa pb pc pd

buildCaseTable :: [AltInfo] -> CaseTable
buildCaseTable [a,b] = CaseTab2 a b
buildCaseTable [a,b,c]   = CaseTab4 (Q (Just a) (Just b) (Just c) Nothing )
buildCaseTable [a,b,c,d] = CaseTab4 (Q (Just a) (Just b) (Just c) (Just d))
buildCaseTable [a,b,c,d,e]       = CaseTab8 (Q a b c d) (Q (Just e) Nothing  Nothing  Nothing )
buildCaseTable [a,b,c,d,e,f]     = CaseTab8 (Q a b c d) (Q (Just e) (Just f) Nothing  Nothing )
buildCaseTable [a,b,c,d,e,f,g]   = CaseTab8 (Q a b c d) (Q (Just e) (Just f) (Just g) Nothing )
buildCaseTable [a,b,c,d,e,f,g,h] = CaseTab8 (Q a b c d) (Q (Just e) (Just f) (Just g) (Just h))
