module Alfin.Optimize (preOptimM, substBlock) where

import Data.Either
import Data.List (lookup, elemIndex)
import Data.Map (Map, fromList, (!))
import Data.Maybe (fromMaybe, catMaybes, listToMaybe)
import Debug.Trace

import Alfin.Syntax

preOptimM :: String -> Module -> Module
preOptimM main (Module m ds fs) = Module m ds fs'' where
  fs' = map preOptimFun fs
  rfs = transReachFun [FunName (m ++ "." ++ main)] (fromList $ map reachableFuns fs')
  fs'' = filter (\(Definition f _ _ _) -> f `elem` rfs) fs'

transReachFun :: [FunName] -> Map FunName [FunName] -> [FunName]
transReachFun fs rfm = trf [] fs where
  trf xs [] = xs
  trf xs (y:ys) | y `elem` xs = trf xs ys
                | otherwise   = trf (y:xs) (rfm!y ++ ys)

reachableFuns :: Definition -> (FunName, [FunName])
reachableFuns (Definition f r xs b) = (f, reachFunB b)

reachFunB :: Block -> [FunName]
reachFunB (Block xs t) = concatMap reachFunS xs ++ reachFunT t

reachFunT :: Terminator -> [FunName]
reachFunT (Return t _   ) = getHeapFunTag t
reachFunT (Cond _ x y   ) = reachFunB x ++ reachFunB y
reachFunT (Jump ce _    ) = reachFunC ce
reachFunT (Case ce _  xs) = reachFunC ce ++ concatMap (reachFunB . snd) xs
reachFunT _               = []

reachFunS :: Statement -> [FunName]
reachFunS (_ := (Store t _)) = getHeapFunTag t
reachFunS _                  = []

reachFunC :: CallExpr -> [FunName]
reachFunC (Call f _) = [f]
reachFunC (Fix  f _) = [f]
reachFunC _           = []

getHeapFunTag :: NodeTag -> [FunName]
getHeapFunTag (Fun f)   = [f]
getHeapFunTag (Pap f _) = [f]
getHeapFunTag _         = [ ]

preOptimFun :: Definition -> Definition
preOptimFun (Definition f r xs c) = Definition f r xs (preOptimBlock [] [] c)

type ValueName = (Either (NodeTag, [Variable]) Expression, Variable)
type KnownNode = (Variable, (NodeTag, [Variable]))

preOptimBlock :: [KnownNode] -> [ValueName] -> Block -> Block
preOptimBlock ns vs (Block xs t) = remDeadExpsBlock $ Block (reverse rxs') t' where
  (rxs', ns', vs', s) = preOptimSequence ns vs [] [] xs
  t'                  = preOptimTerm ns' vs' $ substTerm s t
  
preOptimTerm :: [KnownNode] -> [ValueName] -> Terminator -> Terminator
preOptimTerm ns _  (Jump (Eval x) [])   -- TODO check if this is a good idea, it might cause some memory duplication if x is a case scrutinee
  | Just (Con t, ys) <- lookup (Var Ref x) ns  = Return (Con t) ys
preOptimTerm ns _  (Jump c cc)       = uncurry Jump (optimCE ns (c,cc))
preOptimTerm ns _  (Case c cc  xs)   = uncurry Case (optimCE ns (c,cc)) (map (preOptimAlt ns) xs)
preOptimTerm ns vs (Cond c x y)      = Cond c (preOptimBlock ns vs x) (preOptimBlock ns vs y)
preOptimTerm _  _  t                 = t

preOptimAlt :: [KnownNode] -> (Pattern, Block) -> (Pattern, Block)
preOptimAlt ns (ConPat (Just s) t xs, a) = (ConPat (Just s) t xs, preOptimBlock ((s, (Con t, xs)) : ns) [] a)  -- known constructor
preOptimAlt ns (p                   , a) = (p, preOptimBlock ns [] a)

preOptimSequence :: [KnownNode] -> [ValueName] -> [VarSubst] -> [Statement] -> [Statement] -> ([Statement], [KnownNode], [ValueName], [VarSubst])
preOptimSequence ns vs s rs [] = (rs, ns, vs, s)
preOptimSequence ns vs s rs ((x := (Store (Fun f) [])):ys) = case (lookup (Left (Fun f, [])) vs) of
  Nothing -> preOptimSequence ns ((Left (Fun f, []), x) : vs) s ((x := (Store (Fun f) [])) : rs) ys
  Just r  -> preOptimSequence ns vs ((x, r):s) rs (map (substStmt ((x, r):s)) ys)
preOptimSequence ns vs s rs ((x := (Store t n)):ys) 
  | whnfTag t = case (lookup (Left (t, n)) vs) of
    Nothing -> preOptimSequence ((x, (t, n)) : ns) ((Left (t, n), x) : vs) s ((x := (Store t n)) : rs) ys
    Just r  -> preOptimSequence ns vs ((x, r):s) rs (map (substStmt ((x, r):s)) ys)
  | otherwise = preOptimSequence ((x, (t, n)) : ns) vs s ((x := (Store t n)) : rs) ys
preOptimSequence ns vs s rs ((x := e) : ys) = case (lookup (Right e) vs) of
  Nothing -> preOptimSequence ns ((Right e, x) : vs) s ((x := e) : rs) ys
  Just r  -> preOptimSequence ns vs ((x, r):s) rs (map (substStmt ((x, r):s)) ys)
preOptimSequence ns _  s rs ((Send t n)    : ys) = preOptimSequence ns [] s ((Send t n              ) : rs) ys

optimCE :: [KnownNode] -> (CallExpr, [CallCont]) -> (CallExpr, [CallCont])
optimCE ns (Eval x, [Apply as]) = case lookup (Var Ref x) ns of
  Nothing             -> (Eval x   , [Apply as])
  Just (Fun f, xs)    -> (Call f xs, [Apply as])
  Just (Pap f na, xs) -> 
    case compare (length as) na of
      GT -> (Call f (xs ++ take na as), [Apply (drop na as)])
      EQ -> (Call f (xs ++ as        ), [])
      LT -> (Eval x                   , [Apply as])
  Just _ -> (Eval x                   , [Apply as])
optimCE _ e = e

remDeadExpsBlock :: Block -> Block
remDeadExpsBlock (Block xs t) = Block (remDeadExpsStmts (readVarsT t') xs) t' where
  t' = remDeadExpsTerm t

remDeadExpsTerm :: Terminator -> Terminator
remDeadExpsTerm (Cond c x y)   = Cond c (remDeadExpsBlock x) (remDeadExpsBlock y)
remDeadExpsTerm (Case c cc xs) = Case c cc (map (fmap remDeadExpsBlock) xs)
remDeadExpsTerm t              = t

remDeadExpsStmts :: [String] -> [Statement] -> [Statement]
remDeadExpsStmts vs = snd . foldr remDeadExpsStmt (vs,[])

remDeadExpsStmt :: Statement -> ([String], [Statement]) -> ([String], [Statement])
remDeadExpsStmt x@((Var _ a) := _) (vs, xs)
  | a `elem` vs = (readVarsS x ++ vs, (x:xs))
  | otherwise   = (vs, xs)
remDeadExpsStmt x (vs,xs) = (readVarsS x ++ vs, (x:xs))

type VarSubst  = (Variable, Variable)

substBlock :: [VarSubst] -> Block -> Block
substBlock s (Block xs y) = Block (map (substStmt s) xs) (substTerm s y)

substStmt :: [VarSubst] -> Statement -> Statement
substStmt s (x := (Store t n))     = x := (Store t (substNode s n))
substStmt s (x := (StringConst n)) = x := (StringConst n)
substStmt s (x := (PrimOp f xs))   = x := (PrimOp f (substNode s xs))
substStmt _ (x := (Constant i))    = x := (Constant i)
substStmt s (Send t n)             = Send t (substNode s n)

substTerm :: [VarSubst] -> Terminator -> Terminator
substTerm s (Return t xs)  = Return t (substNode s xs)
substTerm s (Jump c cc)    = Jump (substCE s c) (map (substCC s) cc)
substTerm s (Cond c x y)   = Cond c (substBlock s x) (substBlock s y)
substTerm s (Case c cc xs) = Case (substCE s c) (map (substCC s) cc) (map (fmap (substBlock s)) xs)
substTerm s (Throw x)      = Throw (substRef s x)

substCE :: [VarSubst] -> CallExpr -> CallExpr
substCE s (Eval x)    = Eval (substRef s x)
substCE s (Fetch x)   = Fetch (substRef s x)
substCE s (Call f xs) = Call f (substNode s xs)
substCE s (Fix f xs)  = Fix f (substNode s xs)
substCE _ (Receive)   = Receive

substCC :: [VarSubst] -> CallCont -> CallCont
substCC s (Apply    xs) = Apply (substNode s xs)
substCC s (ApplyAll xs) = ApplyAll (substNode s xs)
substCC s (Select c i ) = Select c i
substCC s (Catch h    ) = Catch (substRef s h)

substNode :: [VarSubst] -> [Variable] -> [Variable]
substNode s = map (substVar s)

substVar :: [VarSubst] -> Variable -> Variable
substVar s x@(Var k _) = case lookup x s of
  Nothing                      -> x
  Just y@(Var l _) | l == k    -> y
                   | otherwise -> error "substVar kind mismatch"

substRef :: [VarSubst] -> String -> String
substRef s x = case lookup (Var Ref x) s of
  Nothing          -> x
  Just (Var Ref y) -> y

readVarsB :: Block -> [String]
readVarsB (Block xs y) = concatMap readVarsS xs ++ readVarsT y

readVarsT :: Terminator -> [String]
readVarsT (Return _ xs)  = readVarsN xs
readVarsT (Jump c cc)    = readVarsCCC (c,cc)
readVarsT (Cond c x y)   = [c] ++ readVarsB x ++ readVarsB y
readVarsT (Case c cc xs) = readVarsCCC (c,cc) ++ concatMap (readVarsB . snd) xs
readVarsT (Throw x)      = [x]

readVarsS :: Statement -> [String]
readVarsS (_ := (Store _ n))     = readVarsN n
readVarsS (_ := (StringConst _)) = []
readVarsS (_ := (PrimOp _ xs))   = readVarsN xs
readVarsS (_ := (Constant _))    = []
readVarsS (Send _ n)             = readVarsN n

readVarsC :: CallExpr -> [String]
readVarsC (Eval x)    = [x]
readVarsC (Fetch x)   = [x]
readVarsC (Call _ xs) = readVarsN xs
readVarsC (Fix _ xs)  = readVarsN xs
readVarsC (Receive)   = []

readVarsCC :: CallCont -> [String]
readVarsCC (Apply xs  )  = readVarsN xs
readVarsCC (ApplyAll xs) = readVarsN xs
readVarsCC (Select _ _)  = []
readVarsCC (Catch h  )   = [h]

readVarsCCC :: (CallExpr, [CallCont]) -> [String]
readVarsCCC (c,cc) = readVarsC c ++ concatMap readVarsCC cc

readVarsN :: [Variable] -> [String]
readVarsN = concatMap readVars

readVars :: Variable -> [String]
readVars (Var _ x) = [x]

whnfTag :: NodeTag -> Bool
whnfTag (Con _)    = True
whnfTag (Dec _ _)  = True
whnfTag (Box _)    = True
whnfTag (Fun _)    = False
whnfTag (Pap _ _)  = True
whnfTag (ApN _)     = False
whnfTag (FSel _ _) = False
whnfTag (PSel _ _) = True
whnfTag (PId)      = True
