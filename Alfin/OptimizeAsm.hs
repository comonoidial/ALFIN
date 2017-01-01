module Alfin.OptimizeAsm (preOptimMod, optimMod, substBlock, readVarsB, readVarsCCC, whnfTag) where

import Data.Either
import Data.List (lookup, elemIndex)
import Data.Map (Map, fromList, (!))
import Data.Maybe (fromMaybe, catMaybes, listToMaybe)
import Debug.Trace

import Alfin.AsmLang

preOptimMod :: String -> AsmModule -> AsmModule
preOptimMod main (AsmModule m ds fs) = AsmModule m ds fs'' where
  fs' = map preOptimFun fs
  rfs = transReachFun [FName (m ++ "." ++ main)] (fromList $ map reachableFuns fs')
  fs'' = filter (\f -> fName f `elem` rfs) fs'

transReachFun :: [FName] -> Map FName [FName] -> [FName]
transReachFun fs rfm = trf [] fs where
  trf xs [] = xs
  trf xs (y:ys) | y `elem` xs = trf xs ys
                | otherwise   = trf (y:xs) (rfm!y ++ ys)

reachableFuns :: Function -> (FName, [FName])
reachableFuns f = (fName f, reachFunB (body f))

reachFunB :: Block -> [FName]
reachFunB (Block xs t) = concatMap reachFunS xs ++ reachFunT t

reachFunT :: TermStmt -> [FName]
reachFunT (NodeReturn t _     ) = fmap snd $ getHeapFunTag t
reachFunT (IfThenElse _ x y   ) = reachFunB x ++ reachFunB y
reachFunT (TailCall ce _      ) = reachFunC ce
reachFunT (CaseOf ce _ _ md xs) = reachFunC ce ++ maybe [] reachFunB md ++ concatMap (\(_,_,_,a) -> reachFunB a) xs
reachFunT _                     = []

reachFunS :: Stmt -> [FName]
reachFunS (_ :<-: (StoreNode t _)) = fmap snd $ getHeapFunTag t
reachFunS (_ :<=: (ce, _))         = reachFunC ce
reachFunS _                        = []

reachFunC :: CallExp -> [FName]
reachFunC (Run_Fun f _) = [f]
reachFunC (Run_Fix f _) = [f]
reachFunC _             = []

optimMod :: AsmModule -> ([FName], AsmModule)
optimMod (AsmModule m ds fs) = (nps, AsmModule m ds fs') where
  nfs = map (setFirstEvalFun [] . optimFun) $ inlineTrivCafs fs
  fes = concatMap getFunEvalIndex nfs
  fs' = map (setFirstEvalFun fes) nfs
  hfs = concatMap getHeapFuns fs'
  nps = catMaybes $ map (newProc hfs) fs'

data FunUse = FullFun | PartApply deriving Eq

newProc :: [(FunUse,FName)] -> Function -> Maybe FName
newProc fs (Function f Nothing _ [] _) = Nothing   -- do not proc cafs
newProc fs (Function f Nothing _ xs _)
  | (PartApply, f) `elem` fs = Nothing
  | (FullFun  , f) `elem` fs = Just f
  | otherwise                = Just f
newProc _  _                 = Nothing

getHeapFuns :: Function -> [(FunUse, FName)]
getHeapFuns (Function  _ _ _ _ c) = getHeapFunsB c

getHeapFunsB :: Block -> [(FunUse, FName)]
getHeapFunsB (Block xs t) = concatMap getHeapFunS xs ++ getHeapFunsTerm t

getHeapFunsTerm :: TermStmt -> [(FunUse, FName)]
getHeapFunsTerm (NodeReturn t _    ) = getHeapFunTag t
getHeapFunsTerm (IfThenElse _ x y  ) = getHeapFunsB x ++ getHeapFunsB y
getHeapFunsTerm (CaseOf _ _ _ md xs) = maybe [] getHeapFunsB md ++ concatMap (\(_,_,_,a) -> getHeapFunsB a) xs
getHeapFunsTerm _                    = []

getHeapFunS :: Stmt -> [(FunUse, FName)]
getHeapFunS (_ :<-: (StoreNode t _)) = getHeapFunTag t
getHeapFunS _                        = []

getHeapFunTag :: AsmTag -> [(FunUse, FName)]
getHeapFunTag (FunTag f)   = [(FullFun  , f)]
getHeapFunTag (PapTag f _) = [(PartApply, f)]
getHeapFunTag _            = [              ]

inlineTrivCafs :: [Function] -> [Function]
inlineTrivCafs fs = filter isUsed fs'' where
  (fs', tcs) = partitionEithers $ map splitTrivCaf fs
  (fs'', bs) = unzip $ map (substTCafFun tcs) fs'
  ucs        = concat bs
  isUsed (Function f@(FName n) Nothing Nothing [] _) = f `elem` ucs || take 4 (dropWhile (/='.') n) /= ".lvl"  -- TODO keep track of exported function instead of the "lvl" heuristic
  isUsed _                                           = True

splitTrivCaf :: Function -> Either Function (FName, RefExp)
splitTrivCaf (Function f Nothing Nothing [] (Block [_ :<~: Constant n] (NodeReturn (BoxCon b) [_]))) = Right (f, StoreNode (BoxCon b) [Right $ BigImm $ fromIntegral n])
splitTrivCaf (Function f Nothing Nothing [] (Block [] (NodeReturn t []))) | whnfTag t = Right (f, StoreNode t [])
splitTrivCaf f = Left f

optimFun :: Function -> Function
optimFun (Function f r e xs c)   = Function f r e xs (optimBlock [] [] c)

preOptimFun :: Function -> Function
preOptimFun (Function f r e xs c) = Function f r e xs (preOptimBlock [] [] c)

setFirstEvalFun :: [(FName, Int)] -> Function -> Function
setFirstEvalFun fes (Function f Nothing Nothing [] c) = Function f Nothing Nothing [] (setFirstEvalBlock fes c)
setFirstEvalFun fes (Function f r       _       xs c) = let (c', e) = setFirstEval fes xs c in
  case e of   -- restrict next fetch ref index to single use variables
    Just i | length (filter (== fx) $ readVarsB c') == 1 -> Function f r e       xs c' 
--           | otherwise -> trace ("shared fetch ref " ++ fx) $ Function f r Nothing xs c' 
           where Left fx = xs!!i
    _                                                    -> Function f r Nothing xs c' 

setFirstEval :: [(FName, Int)] -> [Parameter] -> Block -> (Block, Maybe Int)
setFirstEval fes vs (Block xs t) = case (dropWhile (not . withCtrlStmt) xs) of
  []    -> let (t',e) = setFirstEvalTerm fes vs t in (Block xs t', e)
  (x:_) -> let (t',_) = setFirstEvalTerm fes vs t in (Block xs t', firstEvalStmt fes vs x)

setFirstEvalTerm :: [(FName, Int)] -> [Parameter] -> TermStmt -> (TermStmt, Maybe Int)
setFirstEvalTerm fes vs t@(TailCall c _)       = (t, indexOfEval fes vs c)
setFirstEvalTerm fes vs (CaseOf c cc ms md xs) = (CaseOf c cc ms (fmap (setFirstEvalBlock fes) md) (map (setFirstEvalAlt fes) xs), indexOfEval fes vs c)
setFirstEvalTerm fes _  (IfThenElse c x y)     = (IfThenElse c (setFirstEvalBlock fes x) (setFirstEvalBlock fes y), Nothing)
setFirstEvalTerm _   _  t                      = (t, Nothing)

setFirstEvalAlt :: [(FName, Int)] -> (CName, [Parameter], Maybe Int, Block) -> (CName, [Parameter], Maybe Int, Block)
setFirstEvalAlt fes (c, xs, _, b) =  let (b', e) = setFirstEval fes xs b in
  case e of   -- restrict next fetch ref index to single use variables
    Just i | length (filter (== fx) $ readVarsB b') == 1 -> (c, xs, e      , b')
--           | otherwise -> trace ("shared fetch ref " ++ fx) $ (c, xs, Nothing, b')
           where Left fx = xs!!i
    _                                                    -> (c, xs, Nothing, b')

setFirstEvalBlock :: [(FName, Int)] -> Block -> Block
setFirstEvalBlock fes (Block xs t) = Block xs (fst $ setFirstEvalTerm fes [] t)

firstEvalStmt :: [(FName, Int)] -> [Parameter] -> Stmt -> Maybe Int
firstEvalStmt fes vs (_ :<=: (c, _)) = indexOfEval fes vs c
firstEvalStmt _   _  _               = Nothing

indexOfEval :: [(FName, Int)] -> [Parameter] -> CallExp -> Maybe Int
indexOfEval _   vs (EvalRef (RefVar x)) = elemIndex (Left x) vs
indexOfEval _   vs (LoadRef (RefVar x)) = elemIndex (Left x) vs
indexOfEval fes vs (Run_Fun f xs)       = lookup f fes >>= listToMaybe . flip drop xs >>= arg2MParam >>= flip elemIndex vs
indexOfEval _   _  _                    = Nothing

arg2MParam :: Argument -> Maybe Parameter
arg2MParam (Left (RefVar x))   = Just (Left x)
arg2MParam (Right (PrimVar x)) = Just (Right x)
arg2MParam _                   = Nothing

getFunEvalIndex :: Function -> [(FName, Int)]
getFunEvalIndex (Function f _ (Just e) _ _)  = [(f,e)]
getFunEvalIndex _                            = []

type ValueName = (Either RefExp PrimExp, String)
type KnownNode = (RefVar, (AsmTag, [Argument]))


preOptimBlock :: [KnownNode] -> [ValueName] -> Block -> Block
preOptimBlock ns vs (Block xs t) = remDeadExpsBlock $ Block (reverse rxs') t' where
  (rxs', ns', vs', s) = preOptimSequence ns vs [] [] xs
  t'                  = preOptimTerm ns' vs' $ substTerm s t
  
preOptimTerm :: [KnownNode] -> [ValueName] -> TermStmt -> TermStmt
preOptimTerm ns _  (TailCall (EvalRef (RefVar x)) [])   -- TODO check if this is a good idea, it might cause some memory duplication if x is a case scrutinee
  | Just (ConTag t, ys) <- lookup x ns    = NodeReturn (ConTag t) ys
preOptimTerm ns _  (TailCall c cc)        = uncurry TailCall (optimCE ns (c,cc))
preOptimTerm ns _  (CaseOf c cc ms md xs) = uncurry CaseOf (optimCE ns (c,cc)) ms (fmap (preOptimBlock ns []) md) (map (preOptimAlt ms ns) xs)
preOptimTerm ns vs (IfThenElse c x y)     = IfThenElse c (preOptimBlock ns vs x) (preOptimBlock ns vs y)
preOptimTerm _  _  t                      = t

preOptimAlt :: CallResultRef -> [KnownNode] -> (CName, [Parameter], Maybe Int, Block) -> (CName, [Parameter], Maybe Int, Block)
preOptimAlt (Left s ) ns (t, xs, me, a) = (t, xs, me, preOptimBlock ((s, (ConTag t, map (either (Left . RefVar) (Right . PrimVar)) xs)) : ns) [] a)  -- known constructor
preOptimAlt (Right _) ns (t, xs, me, a) = (t, xs, me, preOptimBlock ns [] a)


preOptimSequence :: [KnownNode] -> [ValueName] -> [VarSubst] -> [Stmt] -> [Stmt] -> ([Stmt], [KnownNode], [ValueName], [VarSubst])
preOptimSequence ns vs s rs [] = (rs, ns, vs, s)
preOptimSequence ns vs s rs ((x :<-: (StoreNode (FunTag f) [])):ys) = case (lookup (Left (StoreNode (FunTag f) [])) vs) of
  Nothing -> preOptimSequence ns ((Left (StoreNode (FunTag f) []), x) : vs) s ((x :<-: (StoreNode (FunTag f) [])) : rs) ys
  Just r  -> preOptimSequence ns vs ((x, ra r):s) rs (map (substStmt ((x, ra r):s)) ys)
preOptimSequence ns vs s rs ((x :<-: (StoreNode t n)):ys) 
  | whnfTag t = case (lookup (Left (StoreNode t n)) vs) of
    Nothing -> preOptimSequence ((x, (t, n)) : ns) ((Left (StoreNode t n), x) : vs) s ((x :<-: (StoreNode t n)) : rs) ys
    Just r  -> preOptimSequence ns vs ((x, ra r):s) rs (map (substStmt ((x, ra r):s)) ys)
  | otherwise = preOptimSequence ((x, (t, n)) : ns) vs s ((x :<-: (StoreNode t n)) : rs) ys
preOptimSequence ns vs s rs ((x :<-: e) : ys) = preOptimSequence ns vs s ((x :<-: e) : rs) ys
preOptimSequence ns vs s rs ((x :<~: e) : ys) = case (lookup (Right e) vs) of
  Nothing -> preOptimSequence ns ((Right e, x) : vs) s ((x :<~: e) : rs) ys
  Just r  -> preOptimSequence ns vs ((x, pa r):s) rs (map (substStmt ((x, pa r):s)) ys)
preOptimSequence ns vs s rs ((x :<-?: e) : ys) = preOptimSequence ns vs s ((x :<-?: e) : rs) ys
preOptimSequence ns _  s rs ((x :<=: (c,cc)) : ys) = preOptimSequence ns [] s ((x :<=: optimCE ns (c,cc)) : rs) ys
preOptimSequence ns _  s rs ((Put_IO t n)    : ys) = preOptimSequence ns [] s ((Put_IO t n              ) : rs) ys

  
optimBlock :: [KnownNode] -> [ValueName] -> Block -> Block
optimBlock ns vs (Block xs t) = tryUsePrefetchBlock [] $ remDeadExpsBlock $ Block xs'' t'' where
  (rxs', ns', vs', s) = optimSequence ns vs [] [] (pullUpCalls [] $ reverse $ optimCallExps (readVarsT t) $ reverse xs)
  (ys', t')           = optimTerm ns' vs' $ substTerm s t
  (xs'', t'')         = case (optimCallExps (readVarsT t') (reverse ys' ++ rxs'), t') of
    ((((Right _, Just (BoxCon pt, [Right v], _)) :<=: (p, cc)) : rxs''), NodeReturn (BoxCon a) [Right w])
      | PrimVar v == w && pt == a -> (reverse rxs'', TailCall p cc)
    (rxs'', _) -> (reverse rxs'', t')

optimCallExps :: [String] -> [Stmt] -> [Stmt]  -- optimCallExps works on a reversed statement list
optimCallExps _ [] = []
optimCallExps vs ((w :<~: RunPrimOp p x (Just y)):((ms, Just (BoxCon pt, [Right v], Nothing)) :<=: (c, [])):xs)
 | PrimVar v == y && x /= y && v `notElem` vs = optimCallExps vs (((ms, Just (BoxCon pt, [Right w], Nothing)) :<=: (c, [WithOp p x])) : xs)
optimCallExps vs (((Left s, nb) :<=: ccc):xs) -- FIXME only want RefVars from vs here
   | s `notElem` vs = optimCallExps vs (((Right s, nb) :<=: ccc):xs)
optimCallExps vs (x:xs) = x : optimCallExps (readVarsS x ++ vs) xs

pullUpCalls :: [Stmt] -> [Stmt] -> [Stmt]
pullUpCalls rs [] = reverse rs
pullUpCalls ((y@(_ :<=: _ )):rs) (x:xs) = pullUpCalls (x:y:rs) xs
pullUpCalls ((y@(yv :<-: _)):rs) ((x@(_ :<=: (c,cc))):xs)
  | yv `elem` readVarsCCC (c,cc) = pullUpCalls (x:y:rs) xs
  | otherwise                    = pullUpCalls rs (x:y:xs)
pullUpCalls ((y@(yv :<~: pe)):rs) ((x@(_ :<=: (c,cc))):xs)
  | yv `elem` readVarsCCC (c,cc) = pullUpCalls (x:y:rs) xs
  | otherwise                    = pullUpCalls rs (x:y:xs)
pullUpCalls rs (x:xs) = pullUpCalls (x:rs) xs

smallCommonCons :: [CName]
smallCommonCons = 
  [CName "GHCziBool.False", CName "GHCziBool.True"
  ,CName "GHCziTypes.ZMZN", CName "Flite.Nil", CName "Flite.Nothing"
  ,CName "Flite.LT", CName "Flite.EQ", CName "Flite.GT"
  ]

optimSequence :: [KnownNode] -> [ValueName] -> [VarSubst] -> [Stmt] -> [Stmt] -> ([Stmt], [KnownNode], [ValueName], [VarSubst])
optimSequence ns vs s rs [] = (rs, ns, vs, s)
optimSequence ns vs s rs ((x :<-: (StoreNode (ConTag ct) [])):ys)
  | ct `elem` smallCommonCons = optimSequence ns vs ((x, rca ct):s) rs (map (substStmt ((x, rca ct):s)) ys)
optimSequence ns vs s rs ((x :<-: (StoreNode (BoxCon ct) [Right (PrimVar n)])):ys) = 
  case (lookup n (map (\(a,b) -> (b,a)) vs)) of
    Just (Right (Constant i)) -> optimSequence ns ((Left (StoreNode (BoxCon ct) [Right (BigImm i )]), x) : vs) s ((x :<-: (StoreNode (BoxCon ct) [Right (BigImm i )])) : rs) ys
    _                         -> optimSequence ns ((Left (StoreNode (BoxCon ct) [Right (PrimVar n)]), x) : vs) s ((x :<-: (StoreNode (BoxCon ct) [Right (PrimVar n)])) : rs) ys
optimSequence ns vs s rs ((x :<-: (StoreNode (FunTag f) [])):ys) = case (lookup (Left (StoreNode (FunTag f) [])) vs) of
  Nothing -> optimSequence ns ((Left (StoreNode (FunTag f) []), x) : vs) s ((x :<-: (StoreNode (FunTag f) [])) : rs) ys
  Just r  -> optimSequence ns vs ((x, ra r):s) rs (map (substStmt ((x, ra r):s)) ys)
optimSequence ns vs s rs ((x :<-: (StoreNode t n)):ys) 
  | whnfTag t = case (lookup (Left (StoreNode t n)) vs) of
    Nothing -> optimSequence ((x, (t, n)) : ns) ((Left (StoreNode t n), x) : vs) s ((x :<-: (StoreNode t n)) : rs) ys
    Just r  -> optimSequence ns vs ((x, ra r):s) rs (map (substStmt ((x, ra r):s)) ys)
  | otherwise = optimSequence ((x, (t, n)) : ns) vs s ((x :<-: (StoreNode t n)) : rs) ys
optimSequence ns vs s rs ((x :<-: e) : ys) = optimSequence ns vs s ((x :<-: e) : rs) ys
optimSequence ns vs s rs ((x :<~: Constant i) : ys)
  | i < 16 && i >= 0 = optimSequence ns vs ((x, pia i):s) rs (map (substStmt ((x, pia i):s)) ys)   -- was  i < 8 && i >= -8
optimSequence ns vs s rs ((x :<~: e) : ys) = case (lookup (Right e) vs) of
  Nothing -> optimSequence ns ((Right e, x) : vs) s ((x :<~: e) : rs) ys
  Just r  -> optimSequence ns vs ((x, pa r):s) rs (map (substStmt ((x, pa r):s)) ys)
optimSequence ns vs s rs ((x :<-?: e) : ys) = optimSequence ns vs s ((x :<-?: e) : rs) ys
optimSequence ns _  s rs ((x :<=: (c,cc)) : ys) = optimSequence ns [] s ((x :<=: optimCE ns (c,cc)) : rs) ys
optimSequence ns _  s rs ((Put_IO t n)    : ys) = optimSequence ns [] s ((Put_IO t n              ) : rs) ys

optimTerm :: [KnownNode] -> [ValueName] -> TermStmt -> ([Stmt], TermStmt)
optimTerm _  _  (NodeReturn t xs)      = ([], NodeReturn t xs)
optimTerm _  _  (BoolReturn c t e)     = ([], BoolReturn c t e)
optimTerm _  _  (TopReturn)            = ([], TopReturn)
optimTerm ns _  (TailCall (EvalRef (RefVar x)) [])   -- TODO check if this is a good idea, it might cause some memory duplication if x is a case scrutinee
  | Just (ConTag t, ys) <- lookup x ns = ([], NodeReturn (ConTag t) ys)
optimTerm ns _  (TailCall c cc)        = ([], uncurry TailCall (optimCE ns (c,cc)))
optimTerm ns _  (CaseOf c cc ms md xs) = optimCase ns ms (c,cc) md xs
optimTerm _  _  (Error x)              = ([], Error x)
optimTerm ns vs (IfThenElse c x y)     = optimIfThenElse c (optimBlock ns vs x) (optimBlock ns vs y)

optimCase :: [KnownNode] -> CallResultRef -> (CallExp, [PostCall]) -> (Maybe Block) -> [(CName, [Parameter], Maybe Int, Block)] -> ([Stmt], TermStmt)
optimCase ns (Right s)  ccc md xs = ([], uncurry CaseOf (optimCE ns ccc) (Right s) (fmap (optimDefAlt Nothing ns ccc) md) (map (optimAlt Nothing ns) xs))
optimCase ns (Left s) ccc md xs = ([], uncurry CaseOf (optimCE ns ccc) (if s `elem` vs then Left s else Right s) md' xs') where
  md' = fmap (optimDefAlt (Just s) ns ccc) md
  xs' = map (optimAlt (Just s) ns) xs
  vs  = maybe [] readVarsB md' ++ concatMap (\(_,_,_,a) -> readVarsB a) xs' -- FIXME only want refVars here

optimDefAlt :: Maybe RefVar -> [KnownNode] -> (CallExp, [PostCall]) -> Block -> Block
optimDefAlt (Just s) _ _ (Block [] (TailCall (EvalRef (RefVar x)) []))
  | s == x        = Block [] TopReturn
optimDefAlt _ _ ccc (Block [] (TailCall c cc))
  | ccc == (c,cc) = Block [] TopReturn
optimDefAlt _ ns _ b = optimBlock ns [] b

optimAlt :: Maybe RefVar -> [KnownNode] -> (CName, [Parameter], Maybe Int, Block) -> (CName, [Parameter], Maybe Int, Block)
optimAlt (Just s) _ (t, xs, me, (Block [] (TailCall (EvalRef (RefVar x)) [])))
   | s == x = (t, xs, me, Block [] TopReturn)
optimAlt _ _ (t, xs, me, (Block [] (NodeReturn (ConTag c) ys)))
   | t == c && (map rv $ lefts xs) == lefts ys && (map pv $ rights xs) == rights ys = (t, xs, me, Block [] TopReturn)
optimAlt (Just s) ns (t, xs, me, a) = (t, xs, me, optimBlock ((s, (ConTag t, map (either (Left . RefVar) (Right . PrimVar)) xs)) : ns) [] a)  -- known constructor
optimAlt Nothing  ns (t, xs, me, a) = (t, xs, me, optimBlock ns [] a)

optimIfThenElse :: BoolVar -> Block -> Block -> ([Stmt], TermStmt)
-- optimIfThenElse c (Block xs (IfThenElse c2 t2 e2)) e
--   | length xs <= 5 && all isSimplePrimStmt xs && e == e2 = (xs ++ [(c++c2) :<-?: (RunLogicOp (QName "" "and") c c2)], IfThenElse (c++c2) t2 e)
-- optimIfThenElse c t (Block xs (IfThenElse c2 t2 e2))
--   | length xs <= 5 && all isSimplePrimStmt xs && t == t2 = (xs ++ [(c++c2) :<-?: (RunLogicOp (QName "" "or") c c2)], IfThenElse (c++c2) t e2)
-- -- TODO add variations involving negation
--optimIfThenElse c (Block [] (NodeReturn x@(ConTag (_, i)) [])) (Block [] (NodeReturn y@(ConTag (_, j)) []))
--  | abs (i-j) == 1 = ([], BoolReturn c x y)
optimIfThenElse c t e = ([], IfThenElse c t e)

optimCE :: [KnownNode] -> (CallExp, [PostCall]) -> (CallExp, [PostCall])
optimCE ns (EvalRef (RefVar x), [Applying as]) = case (lookup x ns) of
  Nothing                -> (EvalRef (RefVar x), [Applying as])
  Just (FunTag f, xs)    -> (Run_Fun f xs      , [Applying as])
  Just (PapTag f na, xs) -> 
    case compare (length as) na of
      GT -> (Run_Fun f (xs ++ take na as), [Applying (drop na as)])
      EQ -> (Run_Fun f (xs ++ as        ), [])
      LT -> (EvalRef (RefVar x)          , [Applying as])
  Just _ -> (EvalRef (RefVar x)          , [Applying as])
optimCE _ e = e

tryUsePrefetchBlock :: [Stmt] -> Block -> Block
tryUsePrefetchBlock rs (Block [] (CaseOf c [] ms Nothing xs)) = case unzip (map tryPreNextA xs) of   -- TODO make it work for case with default alternative
  (pf:pfs, xs') | all (== pf) pfs -> Block (reverse rs) (CaseOf c pf ms Nothing $ map (\(cn,ns,mi,b) -> (cn,ns,mi, tryUsePrefetchBlock [] b)) xs')
  _                               -> Block (reverse rs) (CaseOf c [] ms Nothing $ map (\(cn,ns,mi,b) -> (cn,ns,mi, tryUsePrefetchBlock [] b)) xs)
tryUsePrefetchBlock rs (Block [] (CaseOf c cc ms md xs)) = Block (reverse rs) (CaseOf c cc ms md $ map (\(cn,ns,mi,b) -> (cn,ns,mi, tryUsePrefetchBlock [] b)) xs)
tryUsePrefetchBlock rs (Block [] (IfThenElse c x y))     = Block (reverse rs) (IfThenElse c (tryUsePrefetchBlock [] x) (tryUsePrefetchBlock [] y))
tryUsePrefetchBlock rs (Block [] t) = Block (reverse rs) t
tryUsePrefetchBlock rs (Block (((mr,nb) :<=: (ce, cc)   ):xs) t) = case (nb, tryPreNextB (Block xs t)) of
  (Just (nt,ns,_), ([NextFetch (RefVar r)], _ )) | Left r `elem` ns -> tryUsePrefetchBlock (((mr, Just (nt, ns, elemIndex (Left r) ns)) :<=: (ce, cc)):rs) (Block xs t)    -- FIXME? set elemIndex (Left r) ns in setFirstEval instead
  (_             , (pf                    , b')) | [] <- cc         -> tryUsePrefetchBlock (((mr,nb) :<=: (ce, pf       )):rs) b'
  _                                                                 -> tryUsePrefetchBlock (((mr,nb) :<=: (ce, cc)):rs) (Block xs t)

tryUsePrefetchBlock rs (Block (x:xs) t) = tryUsePrefetchBlock (x:rs) (Block xs t)

tryPreNextA :: (CName, [Parameter], Maybe Int, Block) -> ([PostCall], (CName, [Parameter], Maybe Int, Block))
tryPreNextA (c, ns, mi, b) = case tryPreNextB b of
  ([NextFetch (RefVar x)], _ ) | Left x `elem` ns -> ([], (c, ns, mi, b))
  (pf                    , b')                    -> (pf, (c, ns, mi, b'))

tryPreNextB :: Block -> ([PostCall], Block)
tryPreNextB (Block (x:xs) t) = let (pf,x') = tryPreNextS x in (pf, Block (x':xs) t)
tryPreNextB (Block [] t) = fmap (Block []) $ tryPreNextT t

tryPreNextS :: Stmt -> ([PostCall], Stmt)
tryPreNextS (nb :<=: (ce, cc)) = let (pf, ce') = tryPreNextCE ce in (pf, (nb :<=: (ce', cc)))
tryPreNextS s                  = ([], s)

tryPreNextT :: TermStmt -> ([PostCall], TermStmt)
tryPreNextT (TailCall ce cc       ) = let (pf, ce') = tryPreNextCE ce in (pf, TailCall ce' cc)
tryPreNextT (CaseOf ce cc ms md xs) = let (pf, ce') = tryPreNextCE ce in (pf, CaseOf ce' cc ms md xs)
tryPreNextT t                       = ([], t)

tryPreNextCE :: CallExp -> ([PostCall], CallExp)
tryPreNextCE (EvalRef x) = ([NextFetch x] ,UseFetched True)
tryPreNextCE (LoadRef x) = ([NextFetch x] ,UseFetched False)
tryPreNextCE ce          = ([]            , ce)

isSimplePrimStmt :: Stmt -> Bool
isSimplePrimStmt (_ :<~:  _) = True
isSimplePrimStmt (_ :<-?: _) = True
isSimplePrimStmt _           = False

withCtrlStmt :: Stmt -> Bool
withCtrlStmt (_ :<-: _  ) = False
withCtrlStmt (_ :<~: _  ) = False
withCtrlStmt (_ :<-?: _ ) = False
withCtrlStmt (_ :<=: _  ) = True
withCtrlStmt (Put_IO _ _) = False

remDeadExpsBlock :: Block -> Block
remDeadExpsBlock (Block xs t) = Block (remDeadExpsStmts (readVarsT t') xs) t' where
  t' = remDeadExpsTerm t

remDeadExpsTerm :: TermStmt -> TermStmt
remDeadExpsTerm (IfThenElse c x y)     = IfThenElse c (remDeadExpsBlock x) (remDeadExpsBlock y)
remDeadExpsTerm (CaseOf ms c cc md xs) = CaseOf ms c cc (fmap remDeadExpsBlock md) (map (\(t, ys, me, a) -> (t, ys, me, remDeadExpsBlock a)) xs)
remDeadExpsTerm t = t

remDeadExpsStmts :: [String] -> [Stmt] -> [Stmt]
remDeadExpsStmts vs = snd . foldr remDeadExpsStmt (vs,[])

remDeadExpsStmt :: Stmt -> ([String], [Stmt]) -> ([String], [Stmt])
remDeadExpsStmt x@(a :<-: _) (vs, xs)
  | a `elem` vs = (readVarsS x ++ vs, (x:xs))
  | otherwise   = (vs, xs)
remDeadExpsStmt x@(a :<~: p) (vs, xs)
  | a `elem` vs = (readVarsS x ++ vs, (x:xs))
  | otherwise                     = (vs, xs)
remDeadExpsStmt x@(a :<-?: _) (vs, xs)
  | a `elem` vs = (readVarsS x ++ vs, (x:xs))
  | otherwise   = (vs, xs)
remDeadExpsStmt x (vs,xs) = (readVarsS x ++ vs, (x:xs))

-- also gathers used CAFs
substTCafFun :: [(FName, RefExp)] -> Function -> (Function, [FName])
substTCafFun s (Function f r e xs c)   = let (b, cs) = substTCafBlock s c in (Function f r e xs b, cs)

substTCafBlock :: [(FName, RefExp)] -> Block -> (Block, [FName])
substTCafBlock s (Block xs y) = (Block xs' t', concat as ++ bs) where
  (xs', as) = unzip $ map (substTCafStmt s) xs
  (t' , bs) = substTCafTerm s y

substTCafStmt :: [(FName, RefExp)] -> Stmt -> (Stmt, [FName])
substTCafStmt s (x :<-: (StoreNode (FunTag f) [])) = case lookup f s of
  Nothing -> (x :<-: StoreNode (FunTag f) [], [f])
  Just e  -> (x :<-: e                      , [] )          
substTCafStmt s ((mc, n) :<=: (Run_Fun f [], [])) = case lookup f s of
  Nothing -> ((mc, n) :<=: (Run_Fun f [], []), [f])
  Just _  -> error "substTCafStmt Call Eval_CAF"
substTCafStmt s ((mc, n) :<=: (Run_Fun f [], cc)) = ((mc, n) :<=: (Run_Fun f [], cc), [f])
substTCafStmt s x = (x, [])

substTCafTerm :: [(FName, RefExp)] -> TermStmt -> (TermStmt, [FName])
substTCafTerm s (IfThenElse c x y) = (IfThenElse c x' y', as ++ bs) where
  (x', as) = substTCafBlock s x
  (y', bs) = substTCafBlock s y
substTCafTerm s (CaseOf (c@(Run_Fun f [])) (cc@([])) ms md xs) = case lookup f s of
  Nothing                                        -> (CaseOf c cc ms (fmap fst mdx) xs', f : fromMaybe [] (fmap snd mdx) ++ concat cs)
  Just (StoreNode (BoxCon b) [Right (BigImm n)]) -> error "TODO substTCafTerm CaseOf BoxCon"
  where
    mdx       = fmap (substTCafBlock s) md
    (xs', cs) = unzip $ map (substTCafAlt s) xs
substTCafTerm s (CaseOf c cc ms md xs) = (CaseOf c cc ms (fmap fst mdx) xs', fromMaybe [] (fmap snd mdx) ++ concat cs) where
  mdx       = fmap (substTCafBlock s) md
  (xs', cs) = unzip $ map (substTCafAlt s) xs
substTCafTerm s (TailCall (Run_Fun f []) []) = case lookup f s of
  Nothing                                        -> (TailCall (Run_Fun f []) [], [f])
  Just (StoreNode (BoxCon b) [Right (BigImm n)]) -> (NodeReturn (BoxCon b) [Right $ BigImm n], [])
substTCafTerm s (TailCall (Run_Fun f []) cc) = (TailCall (Run_Fun f []) cc, [f])
substTCafTerm s t = (t, [])

substTCafAlt :: [(FName, RefExp)] -> (CName, [Parameter], Maybe Int, Block) -> ((CName, [Parameter], Maybe Int, Block), [FName])
substTCafAlt s (t, ys, me, a) = ((t, ys, me, b), as) where
  (b, as) = substTCafBlock s a

type VarSubst  = (String, Argument)

substBlock :: [VarSubst] -> Block -> Block
substBlock s (Block xs y) = Block (map (substStmt s) xs) (substTerm s y)

substStmt :: [VarSubst] -> Stmt -> Stmt
substStmt s (x :<-: (StoreNode t n))     = x :<-: (StoreNode t (substNode s n))
-- substStmt _ (x :<-: (StoreBool c t e))   = x :<-: (StoreBool c t e)
substStmt s (x :<-: (StoreSel c a b))    = x :<-: (StoreSel c (substRef s a) (substRef s b))
substStmt s (x :<-: (StringConstant n))  = x :<-: (StringConstant n)
substStmt s (x :<~: (RunPrimOp f a b))   = x :<~: (RunPrimOp f (substPrim s a) (fmap (substPrim s) b))
substStmt _ (x :<~: (Constant i))        = x :<~: (Constant i)
substStmt s (x :<~: (RunPrimSel c a b))  = x :<~: (RunPrimSel c (substPrim s a) (substPrim s b))
substStmt s (x :<-?: (RunCmpOp f a b))   = x :<-?: (RunCmpOp f (substPrim s a) (substPrim s b))
--substStmt _ (x :<-?: (RunLogicOp f a b)) = x :<-?: (RunLogicOp f a b)
substStmt s (x :<=: (c,cc))              = x :<=: (substCE s c, map (substCC s) cc)
substStmt s (Put_IO t n)                 = Put_IO t (substNode s n)

substTerm :: [VarSubst] -> TermStmt -> TermStmt
substTerm s (NodeReturn t xs)      = NodeReturn t (substNode s xs)
substTerm _ (BoolReturn c t e)     = BoolReturn c t e
substTerm _ (TopReturn)            = TopReturn
substTerm s (TailCall c cc)        = TailCall (substCE s c) (map (substCC s) cc)
substTerm s (IfThenElse c x y)     = IfThenElse c (substBlock s x) (substBlock s y)
substTerm s (CaseOf c cc ms md xs) = CaseOf (substCE s c) (map (substCC s) cc) ms (fmap (substBlock s) md) (map (\(t,ys,me,a) -> (t,ys,me,substBlock s a)) xs)
substTerm s (Error x)              = Error (substRef s x)

substCE :: [VarSubst] -> CallExp -> CallExp
substCE s (EvalRef x)        = EvalRef (substRef s x)
substCE s (LoadRef x)        = LoadRef (substRef s x)
substCE s (Run_Fun f xs)     = Run_Fun f (substNode s xs)
substCE s (Run_Fix f xs)     = Run_Fix f (substNode s xs)
substCE _ (Get_IO)           = Get_IO

substCC :: [VarSubst] -> PostCall -> PostCall
substCC s (Applying as  ) = Applying (substNode s as)
substCC s (Selecting c i) = Selecting c i
substCC s (NextFetch x  ) = NextFetch (substRef s x)
substCC s (CatchWith h  ) = CatchWith (substRef s h)
substCC s (WithOp  p x  ) = WithOp p (substPrim s x)

substNode :: [VarSubst] -> [Argument] -> [Argument]
substNode s = map (either (Left . substRef s) (Right . substPrim s))

substRS :: [VarSubst] -> [RefVal] -> [RefVal]
substRS s = map (substRef s)

substPS :: [VarSubst] -> [PrimVal] -> [PrimVal]
substPS s = map (substPrim s)

substRef :: [VarSubst] -> RefVal -> RefVal
substRef s (RefVar x) = maybe (RefVar x) (either id (error "refvar expected")) (lookup x s)
substRef s x          = x 

substPrim :: [VarSubst] -> PrimVal -> PrimVal
substPrim s (PrimVar x) = maybe (PrimVar x) (either (error "primvar expected") id) (lookup x s)
substPrim _ x           = x

readVarsB :: Block -> [String]
readVarsB (Block xs y) = concatMap readVarsS xs ++ readVarsT y

readVarsT :: TermStmt -> [String]
readVarsT (NodeReturn _ xs)     = readVarsN xs
readVarsT (TopReturn)           = []
readVarsT (BoolReturn c _ _)    = [c]
readVarsT (TailCall c cc)       = readVarsCCC (c,cc)
readVarsT (IfThenElse c x y)    = [c] ++ readVarsB x ++ readVarsB y
readVarsT (CaseOf c cc _ md xs) = readVarsCCC (c,cc) ++ maybe [] readVarsB md ++ concatMap (\(_,_,_,a) -> readVarsB a) xs
readVarsT (Error x)             = readVarsR x

readVarsS :: Stmt -> [String]
readVarsS (_ :<-: (StoreNode _ n))     = readVarsN n
readVarsS (_ :<-: (StringConstant _))  = []
readVarsS (_ :<~: (RunPrimOp _ a b))   = readVarsV a ++ maybe [] readVarsV b
readVarsS (_ :<~: (Constant _))        = []
readVarsS (_ :<-?: (RunCmpOp _ a b))   = readVarsV a ++ readVarsV b
--readVarsS (_ :<-?: (RunLogicOp _ a b)) = [a, b]
readVarsS (_ :<=: (c, cc))             = readVarsCCC (c,cc)
readVarsS (Put_IO _ n)                 = readVarsN n
readVarsS x = error ("readVarsS " ++ show x)

readVarsC :: CallExp -> [String]
readVarsC (EvalRef x)    = readVarsR x
readVarsC (LoadRef x)    = readVarsR x
readVarsC (UseFetched _) = []
readVarsC (Run_Fun _ xs) = readVarsN xs
readVarsC (Run_Fix _ xs) = readVarsN xs
readVarsC (Get_IO)       = []

readVarsCC :: PostCall -> [String]
readVarsCC (Applying as  ) = readVarsN as
readVarsCC (Selecting _ _) = []
readVarsCC (NextFetch x  ) = readVarsR x
readVarsCC (CatchWith h  ) = readVarsR h
readVarsCC (WithOp _ x   ) = readVarsV x

readVarsCCC :: (CallExp, [PostCall]) -> [String]
readVarsCCC (c,cc) = readVarsC c ++ concatMap readVarsCC cc

readVarsN :: [Argument] -> [String]
readVarsN = concatMap (either readVarsR readVarsV)

readVarsRS :: [RefVal] -> [String]
readVarsRS = concatMap readVarsR

readVarsPS :: [PrimVal] -> [String]
readVarsPS = concatMap readVarsV

readVarsR :: RefVal -> [String]
readVarsR (RefVar x) = [x]
readVarsR _          = []

readVarsV :: PrimVal -> [String]
readVarsV (PrimVar x) = [x]
readVarsV _           = []

whnfTag :: AsmTag -> Bool
whnfTag (ConTag _)    = True
whnfTag (DecTag _ _)  = True
whnfTag (BoxCon _)    = True
whnfTag (FunTag _)    = False
whnfTag (PapTag _ _)  = True
whnfTag (ApTag _)     = False
whnfTag (FSelTag _ _) = False
whnfTag (PSelTag _ _) = True
whnfTag (PIdTag)      = True
