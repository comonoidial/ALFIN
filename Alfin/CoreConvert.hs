module Alfin.CoreConvert where

import qualified Data.ByteString.Lazy.Char8 as L
import Data.List (elemIndices)
import Debug.Trace (trace)

import ExtCore.Syntax

import Alfin.SimpleCore

convertMod :: Module -> SCModule
convertMod (Module (p,m) ts vs) = SCModule (ModName (L.unpack p) (L.unpack m)) (map convertTypeDef ts) (concatMap convertTopDefs vs)

convertTypeDef :: Tdef -> SCTypeDef
convertTypeDef (Data (p,m,c) vs cs) = SCData (TypeCon (ModName (L.unpack p) (L.unpack m)) (L.unpack c)) (map (L.unpack . fst) vs) (map convertConstr cs)
convertTypeDef (Newtype _ _ _ _)    = SCNewType

convertConstr :: Cdef -> SCConstr
convertConstr (Constr (p,m,c) _ ts) = SCConstr (ModName (L.unpack p) (L.unpack m)) (L.unpack c) (map convertType ts)

convertTopDefs :: Vdefg -> [SCTopDef]
convertTopDefs (Rec ds  ) = map convertTopDef ds
convertTopDefs (Nonrec d) = [convertTopDef d]

convertTopDef :: Vdef -> SCTopDef
convertTopDef (Vdef _ (p,m,n) t e) = SCTopDef (ModName (L.unpack p) (L.unpack m)) (L.unpack n) [] (convertType t, convertExp [] e)

convertType :: Ty -> SCType
convertType (Tvar x      )       = SCTypeOther
convertType (Tcon (p,m,c))       = SCTypeCon (TypeCon (ModName (L.unpack p) (L.unpack m)) (L.unpack c)) []
convertType (Tapp a b    )       = convertTypeAp a [convertType b]
convertType (Tarrow a b  )       = SCTypeArrow (convertType a) (convertType b)
convertType (Tforall _ t )       = convertType t
convertType (UnsafeCoercion _ t) = convertType t
-- todo other coercions

convertTypeAp :: Ty -> [SCType] -> SCType
convertTypeAp (Tcon (p,m,c)) xs = SCTypeCon (TypeCon (ModName (L.unpack p) (L.unpack m)) (L.unpack c)) xs
convertTypeAp (Tapp a b)     xs = convertTypeAp a (convertType b : xs)
convertTypeAp a              xs = SCTypeOther

unQual :: Qual a -> a
unQual (_,_,x) = x

type LocalScope = [L.ByteString]

convertExp :: LocalScope -> Exp -> SCExp
convertExp s (Var (p,m,v)) 
  | L.null m && elem v s = SCVar (L.unpack v)
  | otherwise            = SCFun (ModName (L.unpack p) (L.unpack m), L.unpack v) []
convertExp _ (Dcon (p,m,c)) = SCCon (DataCon (ModName (L.unpack p) (L.unpack m)) (L.unpack c)) []
convertExp _ (Lit x) = SCLit (convertLit x)
convertExp s (App a b) = convertAp s a [convertExp s b]
convertExp s (Appt e _) = convertExp s e
convertExp s (Lam (v,t) e) = convertLam (unQual v : s) [(L.unpack $ unQual v, convertType t)] e
convertExp s (Lamt _ e) = convertExp s e
convertExp s (Let (Nonrec (Vdef _ n t x)) e) = SCLet (SCLB (L.unpack $ unQual n) [] (convertType t) (convertExp s x)) (convertExp (unQual n : s) e)
convertExp s (Let (Rec []) e) = convertExp s e
convertExp s (Let (Rec rs) e) = SCLetRec (map (\(Vdef _ n t x) -> SCLB (L.unpack $ unQual n) [] (convertType t) (convertExp s' x)) rs) (convertExp s' e)
  where s' = s ++ map (\(Vdef _ n _ _) -> unQual n) rs
convertExp s (Case e (v,vt) rt xs) = SCCase (convertExp s e) (L.unpack $ unQual v, convertType vt) (convertType rt) (map (convertAlt (unQual v : s)) xs)
convertExp s (Cast e t) = convertExp s e -- dropping Cast for now
convertExp s (Note _ e) = convertExp s e
--convertExp (External String String Ty)
--convertExp (DynExternal String Ty)
--convertExp (Label String)

convertAp :: LocalScope -> Exp -> [SCExp] -> SCExp
convertAp s (Var (p,m,v))  xs | not (L.null m && elem v s) = SCFun (ModName (L.unpack p) (L.unpack m), L.unpack v) xs
convertAp _ (Dcon (p,m,c)) xs = SCCon (DataCon (ModName (L.unpack p) (L.unpack m)) (L.unpack c)) xs
convertAp s (App a b)      xs = convertAp s a (convertExp s b : xs)
convertAp s (Appt e _)     xs = convertAp s e xs
convertAp s (Lamt _ e)     xs = convertAp s e xs
convertAp s (Note _ e)     xs = convertAp s e xs
convertAp s a              xs = SCApply (convertExp s a) xs

convertLam :: LocalScope -> [(Name,SCType)] -> Exp -> SCExp
convertLam s xs (Appt e _)    = convertLam s xs e
convertLam s xs (Lamt _ e)    = convertLam s xs e
convertLam s xs (Note _ e)    = convertLam s xs e
convertLam s xs (Lam (v,t) e) = convertLam (unQual v : s) ((L.unpack $ unQual v, convertType t) : xs) e
convertLam s xs e             = SCLam (reverse xs) (convertExp s e)

convertAlt :: LocalScope -> Alt -> SCAlt
convertAlt s (Acon (p,m,c) _ xs e) = SCConAlt (DataCon (ModName (L.unpack p) (L.unpack m)) (L.unpack c)) (map (\(x,t) -> (L.unpack $ unQual x, convertType t)) xs) (convertExp (map (unQual . fst) xs ++ s) e)
convertAlt s (Alit i e) = SCLitAlt (convertLit i) (convertExp s e)
convertAlt s (Adefault e) = SCDefault (convertExp s e)

convertLit :: Lit -> SCLit
convertLit (Lint i t     ) = SCInt i (convertType t)
convertLit (Lrational r t) = SCRational r (convertType t)
convertLit (Lchar c t    ) = SCChar c (convertType t)
convertLit (Lstring s t  ) = SCString s (convertType t)


cleanMod :: SCModule -> SCModule
cleanMod (SCModule m ts vs) = SCModule m ts (removeDeadFuns $ map cleanTopDef vs)

removeDeadFuns :: [SCTopDef] -> [SCTopDef]
removeDeadFuns vs = filter (\(SCTopDef m n _ _) -> (not $ modless m) || ((m,n) `elem` lives)) vs
  where lives = concatMap (\(SCTopDef _ _ _ (_,e)) -> usedFunsExp e) vs
        modless (ModName "" "") = True
        modless _               = False

  
cleanTopDef :: SCTopDef -> SCTopDef
cleanTopDef (SCTopDef m n as (rt, (SCLam vs x))) = SCTopDef m n (as ++ vs) (resType (length vs) rt, cleanExp x)
cleanTopDef (SCTopDef m n as (rt, e           )) = SCTopDef m n as (rt, cleanExp e)

  
cleanExp :: SCExp -> SCExp
cleanExp (SCLet (SCLB v as rt x) e)
  | n == 0    = e'
  | otherwise = case (cleanExp x) of
                  SCLam vs x' -> SCLet (SCLB v (as ++ vs) (resType (length vs) rt) x') e'
                  x'          -> SCLet (SCLB v as         rt                       x') e'
  where e' = cleanExp e
        n  = length (elemIndices v $ usedVarsExp e')
cleanExp (SCLetRec rs e) = SCLetRec (map cleanRec rs) (cleanExp e)
  where cleanRec (SCLB v as t x ) = case (cleanExp x) of
          SCLam vs x' -> SCLB v (as ++ vs) (resType (length vs) t) x'
          x'          -> SCLB v as         t                       x'
cleanExp (SCFun f xs) = SCFun f (map cleanExp xs)
cleanExp (SCCon c xs) = SCCon c (map cleanExp xs)
cleanExp (SCApply a xs) = case (cleanExp a) of
  SCFun   f ys -> SCFun f (ys ++ map cleanExp xs)
  SCApply b ys -> SCApply b (ys ++ map cleanExp xs)
  a'           -> SCApply a' (map cleanExp xs)
cleanExp (SCLam v e) = case (cleanExp e) of
  (SCApply a xs) | all (`notElem` map fst v) (usedVarsExp a) -> 
    case (etaReduce v xs) of
      ([], [] ) -> a
      ([], xs') -> SCApply a xs'
      (v', xs') -> SCLam v' (SCApply a xs')
  (SCFun f xs) -> case (etaReduce v xs) of
    ([], xs') -> SCFun f xs'
    (v', xs') -> SCLam v' (SCFun f xs')
  e'             -> SCLam v e'  
cleanExp (SCCase e t r xs) = SCCase (cleanExp e) t r (map cleanAlt xs)
cleanExp x = x

etaReduce :: [(Name,SCType)] -> [SCExp] -> ([(Name,SCType)] ,[SCExp])
etaReduce [] ys = ([],ys)
etaReduce xs [] = (xs,[])
etaReduce xs ys = let xv = fst (last xs) in case (reverse ys) of
  ((SCVar y) : ys') | y == xv && xv `notElem` concatMap usedVarsExp ys' -> etaReduce (init xs) (reverse ys')
  _  -> (xs, ys)

cleanAlt :: SCAlt -> SCAlt
cleanAlt (SCConAlt c xs e) = SCConAlt c xs (cleanExp e)
cleanAlt (SCLitAlt i e)    = SCLitAlt i (cleanExp e)
cleanAlt (SCDefault e)     = SCDefault (cleanExp e)

usedVarsExp :: SCExp -> [Name]
usedVarsExp (SCFun _ xs)      = concatMap usedVarsExp xs
usedVarsExp (SCVar n)         = [n]
usedVarsExp (SCCon _ xs)      = concatMap usedVarsExp xs
usedVarsExp (SCLit _)         = []
usedVarsExp (SCApply a xs)    = usedVarsExp a ++ concatMap usedVarsExp xs
usedVarsExp (SCLam _ e)       = usedVarsExp e
usedVarsExp (SCLet x e)       = usedVarsLB x ++ usedVarsExp e
usedVarsExp (SCLetRec rs e)   = concatMap usedVarsLB rs ++ usedVarsExp e
usedVarsExp (SCCase e _ _ xs) = usedVarsExp e ++ concatMap usedVarsAlt xs

usedVarsLB :: SCLetBinding -> [Name]
usedVarsLB = usedVarsExp . lbExp

usedVarsAlt :: SCAlt -> [Name]
usedVarsAlt (SCConAlt _ _ e) = usedVarsExp e
usedVarsAlt (SCLitAlt _ e)   = usedVarsExp e
usedVarsAlt (SCDefault e)    = usedVarsExp e

usedFunsExp :: SCExp -> [(ModName, Name)]
usedFunsExp (SCFun f xs)      = f : concatMap usedFunsExp xs
usedFunsExp (SCVar _)         = []
usedFunsExp (SCCon _ xs)      = concatMap usedFunsExp xs
usedFunsExp (SCLit _)         = []
usedFunsExp (SCApply a xs)    = usedFunsExp a ++ concatMap usedFunsExp xs
usedFunsExp (SCLam _ e)       = usedFunsExp e
usedFunsExp (SCLet x e)       = usedFunsLB x ++ usedFunsExp e
usedFunsExp (SCLetRec rs e)   = concatMap usedFunsLB rs ++ usedFunsExp e
usedFunsExp (SCCase e _ _ xs) = usedFunsExp e ++ concatMap usedFunsAlt xs

usedFunsLB :: SCLetBinding -> [(ModName, Name)]
usedFunsLB = usedFunsExp . lbExp

usedFunsAlt :: SCAlt -> [(ModName, Name)]
usedFunsAlt (SCConAlt _ _ e) = usedFunsExp e
usedFunsAlt (SCLitAlt _ e)   = usedFunsExp e
usedFunsAlt (SCDefault e)    = usedFunsExp e

substVExp :: (Name, SCExp) -> SCExp -> SCExp
substVExp s (SCFun f xs)      = SCFun f (map (substVExp s) xs)
substVExp s (SCVar n)         = if (fst s == n) then (snd s) else (SCVar n)
substVExp s (SCCon c xs)      = SCCon c (map (substVExp s) xs)
substVExp _ (SCLit i)         = SCLit i
substVExp s (SCApply a xs)    = SCApply (substVExp s a) (map (substVExp s) xs)
substVExp s (SCLam vs e)      = SCLam vs (substVExp s e)
substVExp s (SCLet x e)       = SCLet (substVLB s x) (substVExp s e) 
substVExp s (SCLetRec rs e)   = SCLetRec (map (substVLB s) rs) (substVExp s e) where
  bstVExp s (SCCase e t r xs) = SCCase (substVExp s e) t r (map (substVAlt s) xs)

substVLB :: (Name, SCExp) -> SCLetBinding  -> SCLetBinding
substVLB s (SCLB v as t x) = SCLB v as t (substVExp s x)

substVAlt :: (Name, SCExp) -> SCAlt -> SCAlt
substVAlt s (SCConAlt c xs e) = SCConAlt c xs (substVExp s e)
substVAlt s (SCLitAlt i e)    = SCLitAlt i (substVExp s e)
substVAlt s (SCDefault e)     = SCDefault (substVExp s e)
