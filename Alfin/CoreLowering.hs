module Alfin.CoreLowering where

import Control.Monad.State
import Data.List (lookup, intersect, elemIndex)
import Data.Maybe (maybe, fromJust, isJust)

import Debug.Trace (trace)

import Alfin.CoreConvert (cleanExp, substVExp)
import Alfin.SimpleCore
import Alfin.LowCore

type NameGen a = State Int a

newName :: String -> NameGen String
newName x = do 
  n <- get
  put (n+1)
  return (x ++ "_" ++ show n)

lowerM :: ModName -> String
lowerM (ModName _ m) = m

lowerMod :: SCModule -> LCModule
lowerMod (SCModule m ts fs) = LCModule (lowerM m) (map lowerData ts) $ evalState (fmap concat $ mapM lowerFun fs) 0

lowerData :: SCTypeDef -> DataDef
lowerData (SCNewType) = error "uneliminated newtype"
lowerData (SCData (TypeCon m n) _ cs) = DataDef (lowerM m, n) (map lowerCon cs)
  where lowerCon (SCConstr cm cn ts) = ((lowerM cm, cn), map lowerType ts)

primBoxCon :: ShapeType -> QName
primBoxCon (PType "Int") = ("GHCziTypes","Izh")

lowerFun :: SCTopDef -> NameGen [FunDef]
lowerFun (SCTopDef m f as (rt, e)) = do
  let vs = map (fmap lowerType) as
  (fs, e') <- lowerTopExp vs e
  return (FunDef (lowerM m, f) vs (lowerType rt) (simplifyTE e') : fs)

lowerTopExp :: [(String,ShapeType)] -> SCExp -> NameGen ([FunDef], TopExp)
lowerTopExp _   (SCVar n) = return ([], SimpleExp (VarExp n))
lowerTopExp _   (SCLit x) = return ([], SimpleExp (LitExp (lowerLit x)))
lowerTopExp tfs (SCFun (m, f) xs) = do
  ys <- mapM (lowerSubExp tfs) xs
  return (concatMap fst ys, foldr id (SimpleExp $ FunVal (lowerM m, f) (map (snd . snd) ys)) (concat (map (fst . snd) ys)))
lowerTopExp tfs (SCCon (DataCon m c) xs) = do
  ys <- mapM (lowerSubExp tfs) xs
  return (concatMap fst ys, foldr id (SimpleExp $ ConExp (lowerM m, c) (map (snd . snd) ys)) (concat (map (fst . snd) ys)))
lowerTopExp tfs (SCApply f xs) = do
  ys <- mapM (lowerSubExp tfs) xs
  f' <- lowerSubExp tfs f
  return (fst f' ++ concatMap fst ys, foldr id (SimpleExp $ ApplyExp (snd $ snd f') (map (snd . snd) ys)) ((fst $ snd f') ++ concat (map (fst . snd) ys)))
lowerTopExp tfs (SCCase e (v, t) rt as) =
  case (lowerType t, as) of
    (pt@(PType _), [SCDefault x]) -> do
       cv <- newName v
       y <- lowerTopExp ((v, pt) : tfs) x
       e' <- lowerSubExp tfs e
       let box = primBoxCon pt
       return (fst e' ++ fst y, foldr id (CaseExp cv (snd $ snd e') RefType [ConAlt box [(v,pt)] (snd y)]) (fst $ snd e'))
    (s, xs) -> do 
      ys <- mapM (lowerAlt ((v, s) : tfs)) xs
      e' <- lowerSubExp tfs e
      return (fst e' ++ concatMap fst ys, foldr id (CaseExp v (snd $ snd e') s (map snd ys)) (fst $ snd e'))
lowerTopExp tfs (SCLam as e) = do
  let fs = filter (flip notElem $ map fst as) (freeVars e)
  let fds = map (\fv -> (fv, maybe (error ("lookup " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  let vs = map (\(a,t) -> (a, lowerType t)) as
  e' <- lowerTopExp (vs ++ tfs) e
  lf <- newName "lamt"
  return (fst e', LetExp ("",lf) (fds ++ vs) RefType (snd e') (SimpleExp $ FunVal ("",lf) $ map VarExp fs))
lowerTopExp tfs (SCLet (SCLB n as t x) e) = do
  let vs = map (fmap lowerType) as
  x' <- lowerTopExp (vs ++ tfs) x
  let n' = (n, lowerType t)
  e' <- lowerTopExp ((if null as then n' else (n,RefType)) : tfs) e
  case (as, snd x') of
    ([], SimpleExp sx) -> do
      return (fst x' ++ fst e', SLet n' sx (snd e'))
    _ -> do
      let fs = filter (flip notElem $ map fst as) (freeVars x)
      let fds = map (\fv -> (fv, maybe (error ("lookup fs " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
      lf <- newName "lf"
      let rt = lowerType $ resType (length as) t
      return (fst x' ++ fst e', LetExp ("",lf) (fds ++ vs) rt (snd x') (SLet n' (FunVal ("",lf) $ map VarExp fs) (snd e')))
lowerTopExp tfs (SCLetRec [SCLB n [] t x] e) = do
  let fs = filter (/= n) (freeVars x)
  let fds = map (\fv -> (fv, maybe (error ("lookup r fs " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  x' <- lowerTopExp ((n, lowerType t) : tfs) x
  e' <- lowerTopExp ((n, lowerType t) : tfs) e
  rf <- newName "rf"
  return (fst x' ++ fst e', LetRec ("",rf) n fds (lowerType t) (snd x') (SLet (n, lowerType t) (FunVal ("",rf) $ map VarExp fs) (snd e')))
lowerTopExp tfs (SCLetRec [SCLB n as t x] e) = do
  let fs = filter (flip notElem (n: map fst as)) (freeVars x)
  let fds = map (\fv -> (fv, maybe (error ("lookup r fs " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  let vs = map (fmap lowerType) as
  rf <- newName "trf"
  x' <- lowerTopExp ((n, RefType) : (vs ++ tfs)) (cleanExp $ substVExp (n, (SCFun (ModName "" "", rf) $ map SCVar fs)) x)
  e' <- lowerTopExp ((n, RefType) : tfs) (cleanExp $ substVExp (n, (SCFun (ModName "" "", rf) $ map SCVar fs)) e)
  return ((FunDef ("",rf) (fds++vs) (lowerType t) (simplifyTE $ snd x')) : (fst x' ++ fst e'), snd e')
lowerTopExp tfs x@(SCLetRec rs e) = do -- todo handle letrec with function/caf values
  let rn = map (\(SCLB n _ t _) -> (n, lowerType t)) rs
  let fs = filter (flip notElem (map fst rn)) (freeVars x)
  let fds = map (\fv -> (fv, maybe (error ("lookup rs fs " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  let c = ("", "(#" ++ show (length rs) ++ "#)")
  r <- newName "r"
  rs' <- mapM (lowerRecPart (rn ++ tfs)) rs
  let withparts = flip (foldr (\(n,i) -> SLet n (Selector c i (VarExp r)))) (zip rn [0..])
  e' <- lowerTopExp (rn ++ tfs) e
  lr <- newName "lr"
  sr <- newName "sr"
  return (concatMap fst rs' ++ fst e', LetRec ("",lr) r fds RefType (withparts $ foldr1 (.) (map (fst . snd) rs') (SimpleExp (ConExp c (map (snd . snd) rs'))))
    (CaseExp sr (FunVal ("",lr) $ map VarExp fs) RefType [ConAlt c rn (snd e')]))

lowerRecPart :: [(String,ShapeType)] -> SCLetBinding -> NameGen ([FunDef], (TopExp -> TopExp, SimpleExp))
lowerRecPart tfs (SCLB _ [] t x) = do
  let fs = freeVars x
  let fds = map (\fv -> (fv, maybe (error ("lookup r " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  x' <- lowerTopExp tfs x
  rf <- newName "rf"
  case (snd x') of
    SimpleExp sx -> return (fst x', (SLet (rf, lowerType t) sx, VarExp rf))
    tx           -> return (fst x', (LetExp ("",rf) fds (lowerType t) tx, FunVal ("",rf) $ map VarExp fs))

lowerSubExp :: [(String,ShapeType)] -> SCExp -> NameGen ([FunDef], ([TopExp -> TopExp], SimpleExp))
lowerSubExp _   (SCVar n) = return ([], ([], VarExp n))
lowerSubExp _   (SCLit x) = return ([], ([], LitExp (lowerLit x)))
lowerSubExp tfs (SCFun (m, f) xs) = do
  ys <- mapM (lowerSubExp tfs) xs
  return (concatMap fst ys, (concatMap (fst . snd) ys, FunVal (lowerM m, f) (map (snd . snd) ys)))
lowerSubExp tfs (SCCon (DataCon m c) xs) = do
  ys <- mapM (lowerSubExp tfs) xs
  return (concatMap fst ys, (concatMap (fst . snd) ys, ConExp (lowerM m, c) (map (snd . snd) ys)))
lowerSubExp tfs (SCApply f xs) = do
  ys <- mapM (lowerSubExp tfs) xs
  f' <- lowerSubExp tfs f
  return (fst f' ++ concatMap fst ys, ((fst $ snd f') ++ concatMap (fst . snd) ys, ApplyExp (snd $ snd f') (map (snd . snd) ys)))
lowerSubExp tfs (SCLam as e)       = lowerSubLamExp tfs as e SCTypeOther
lowerSubExp tfs (SCLetRec rs e)    = lowerTopSubExp tfs (SCLetRec rs e) SCTypeOther
lowerSubExp tfs (SCCase e v rt as) = lowerTopSubExp tfs (SCCase e v rt as) rt
lowerSubExp tfs (SCLet (SCLB n [] t x) e) = do -- instead of creating a nested let through lowerTopSubExp, flatten the let sequence, -- TODO check if similiar things happen in other cases
  (fs, (bs, sx)) <- lowerSubExp tfs x
  let n' = (n, lowerType t)
  (gs, (cs, se)) <- lowerSubExp (n':tfs) e
  return (fs++gs, (bs ++ [SLet n' sx] ++ cs, se))
--trace ("lowerSubExp SCLet " ++ show x) $ lowerTopSubExp tfs (SCLet x e) SCTypeOther
lowerSubExp tfs (SCLet x e)        = lowerTopSubExp tfs (SCLet x e) SCTypeOther

lowerSubLamExp :: [(String,ShapeType)] -> [(Name,SCType)] -> SCExp -> SCType -> NameGen ([FunDef], ([TopExp -> TopExp], SimpleExp))
lowerSubLamExp tfs as e t = do
  let fs = filter (flip notElem $ map fst as) (freeVars e)
  let fds = map (\fv -> (fv, maybe (error ("lookup " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  let vs = map (\(a,x) -> (a, lowerType x)) as
  e' <- lowerTopExp (vs ++ tfs) e
  lf <- newName "lam"
  return (fst e', ([LetExp ("",lf) (fds ++ vs) (lowerType t) (snd e')], FunVal ("",lf) $ map VarExp fs))

lowerTopSubExp :: [(String,ShapeType)] -> SCExp -> SCType -> NameGen ([FunDef], ([TopExp -> TopExp], SimpleExp))
lowerTopSubExp tfs e t = do
  let fs = freeVars e
  let fds = map (\fv -> (fv, maybe (error ("lookup " ++ fv ++ show tfs)) id $ lookup fv tfs)) fs
  e' <- lowerTopExp tfs e
  se <- newName "se"
  return (fst e', ([LetExp ("",se) fds (lowerType t) (snd e')], FunVal ("",se) $ map VarExp fs))

lowerAlt :: [(String,ShapeType)] -> SCAlt -> NameGen ([FunDef], Alternative)
lowerAlt tfs (SCDefault e) = do
  (fs, e') <- lowerTopExp tfs e
  return (fs, DefAlt e')
lowerAlt tfs (SCLitAlt (SCInt i _) e) = do
  e' <- lowerTopExp tfs e
  return (fst e', IntAlt (fromIntegral i) (snd e'))
lowerAlt tfs (SCConAlt (DataCon m c) xs e) = do
  let ys = map (\(v,t) -> (v, lowerType t)) xs
  e' <- lowerTopExp (ys ++ tfs) e
  return (fst e', ConAlt (lowerM m,c) ys (snd e'))

lowerIntAlt :: [(String,ShapeType)] -> SCAlt -> NameGen ([FunDef], (Int, TopExp))
lowerIntAlt tfs (SCLitAlt (SCInt i _) e) = do
  (fs, e') <- lowerTopExp tfs e
  return (fs, (fromInteger i, e'))
lowerIntAlt _ x = error ("lowerIntAlt " ++ show x) 

lowerLit :: SCLit -> Literal
lowerLit (SCInt i _)  = IntLit (fromInteger i)
lowerLit (SCChar c _) = IntLit (fromEnum c)
lowerLit (SCString s _) = StringLit s

lowerType :: SCType -> ShapeType
lowerType (SCTypeCon (TypeCon (ModName "ghczmprim" "GHCziPrim") "Intzh") []) = PType "Int"
lowerType (SCTypeCon _ _)   = RefType
lowerType (SCTypeArrow x y) = RefType
lowerType (SCTypeOther)     = RefType

simplifyTE :: TopExp -> TopExp
simplifyTE (SimpleExp e)         = SimpleExp e
simplifyTE (SLet n x e)          = SLet n x (simplifyTE e)
simplifyTE (LetExp f as t x e)      = LetExp f as t (simplifyTE x) (simplifyTE e)
simplifyTE (LetRec f r as t x e) = LetRec f r as t (simplifyTE x) (simplifyTE e)
simplifyTE (CaseExp sr e c xs) = let xs' = map simplifyA xs in
  case xs' of 
    [ConAlt ca ns (CaseExp xr (VarExp x) d ys)] | lookup x ns == Just RefType && null (intersect (sr : map fst ns) (concatMap usedVarsA ys)) -> 
      CaseExp xr (Selector ca (fromJust $ elemIndex x $ map fst ns) e) d (map simplifyA ys)
    [ConAlt ca ns (SimpleExp (VarExp x))] | lookup x ns == Just RefType && x /= sr ->
      SimpleExp (Selector ca (fromJust $ elemIndex x $ map fst ns) e)
    [ConAlt ca ns (SimpleExp (Selector d si (VarExp x)))] | lookup x ns == Just RefType && x /= sr ->
      SimpleExp (Selector d si $ Selector ca (fromJust $ elemIndex x $ map fst ns) e)
    _ -> CaseExp sr e c xs'

simplifyA :: Alternative -> Alternative
simplifyA (DefAlt e)      = DefAlt (simplifyTE e)
simplifyA (ConAlt c xs e) = ConAlt c xs (simplifyTE e)
simplifyA (IntAlt i e)    = IntAlt i (simplifyTE e)

usedVarsTE :: TopExp -> [String]
usedVarsTE (SimpleExp e)        = usedVarsSE e
usedVarsTE (SLet _ x e)         = usedVarsSE x ++ usedVarsTE e
usedVarsTE (LetExp _ _ _ x e)   = usedVarsTE x ++ usedVarsTE e
usedVarsTE (LetRec _ _ _ _ x e) = usedVarsTE x ++ usedVarsTE e
usedVarsTE (CaseExp _ e _ xs)   = usedVarsSE e ++ concatMap usedVarsA xs

usedVarsA :: Alternative -> [String]
usedVarsA (DefAlt e)     = usedVarsTE e
usedVarsA (IntAlt _ e)   = usedVarsTE e
usedVarsA (ConAlt _ _ e) = usedVarsTE e

usedVarsSE :: SimpleExp -> [String]
usedVarsSE (VarExp x)       = [x]
usedVarsSE (LitExp _)       = []
usedVarsSE (FunVal _ xs)    = concatMap usedVarsSE xs
usedVarsSE (ConExp _ xs)    = concatMap usedVarsSE xs
usedVarsSE (ApplyExp f xs)  = usedVarsSE f ++ concatMap usedVarsSE xs
usedVarsSE (Selector _ _ x) = usedVarsSE x
