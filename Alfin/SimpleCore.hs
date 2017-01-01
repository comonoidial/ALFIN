module Alfin.SimpleCore where

import Data.List(nub)

type Name = String

data ModName = ModName Name Name deriving Eq
  
data DataCon = DataCon ModName Name
data TypeCon = TypeCon ModName Name

data SCModule = SCModule ModName [SCTypeDef] [SCTopDef]

data SCTypeDef
  = SCData TypeCon [Name] [SCConstr]
  | SCNewType

data SCConstr = SCConstr ModName Name [SCType]

data SCTopDef = SCTopDef ModName Name [(Name,SCType)] (SCType, SCExp)

data SCType
  = SCTypeCon TypeCon [SCType]
  | SCTypeArrow SCType SCType
  | SCTypeOther

data SCExp
  = SCFun (ModName, Name) [SCExp]
  | SCVar Name
  | SCCon DataCon [SCExp]
  | SCLit SCLit
  | SCApply SCExp [SCExp]
  | SCLam [(Name,SCType)] SCExp
  | SCLet SCLetBinding SCExp
  | SCLetRec [SCLetBinding] SCExp
  | SCCase SCExp (Name, SCType) SCType [SCAlt]

data SCLetBinding = SCLB {lbName :: Name, lbArgs :: [(Name,SCType)], lbType :: SCType, lbExp :: SCExp}

data SCAlt
  = SCConAlt DataCon [(Name, SCType)] SCExp
  | SCLitAlt SCLit SCExp
  | SCDefault SCExp

data SCLit
  = SCInt Integer SCType
  | SCRational Rational SCType
  | SCChar Char SCType
  | SCString String SCType

freeVars :: SCExp -> [String]
freeVars = nub . freeVarsE

freeVarsE :: SCExp -> [String]
freeVarsE (SCFun _ xs)           = concatMap freeVars xs
freeVarsE (SCVar n)              = [n]
freeVarsE (SCCon _ xs)           = concatMap freeVars xs
freeVarsE (SCLit _)              = []
freeVarsE (SCApply f xs)         = freeVars f ++ concatMap freeVars xs
freeVarsE (SCLam vs x)           = filter (flip notElem $ map fst vs) $ freeVars x
freeVarsE (SCLet x e)            = filter (/= lbName x) (freeVarsLB x ++ freeVars e)
freeVarsE (SCLetRec rs e)        = filter (flip notElem $ map lbName rs) (concatMap freeVarsLB rs ++ freeVars e)
freeVarsE (SCCase x (v, _) _ as) = freeVars x ++ filter (/= v) (concatMap freeVarsA as)

freeVarsLB :: SCLetBinding -> [String]
freeVarsLB (SCLB _ as _ x) = filter (flip notElem (map fst as)) (freeVars x)

freeVarsA :: SCAlt -> [String]
freeVarsA (SCConAlt _ ns e) = filter (flip notElem (map fst ns)) $ freeVars e
freeVarsA (SCLitAlt _ e)    = freeVars e
freeVarsA (SCDefault e)     = freeVars e

resType :: Int -> SCType -> SCType
resType 0 x                 = x
resType n (SCTypeArrow _ y) = resType (n-1) y
resType n x                 = x -- error ("resType " ++ show x)

instance Show ModName where
  show (ModName "" "") = ""
  show (ModName p m) = p ++ ":" ++ m ++ "."

instance Show DataCon where
  show (DataCon m c) = show m ++ c

instance Show TypeCon where
  show (TypeCon m c) = show m ++ c

instance Show SCModule where
  show (SCModule m ts vs) = "module " ++ show m ++ "\n" ++ concatMap ((++ "\n") . show) ts ++ concatMap ((++ "\n") . show) vs

instance Show SCTypeDef where
  show (SCData tc vs cs) = "data " ++ show tc ++ concatMap (" " ++) vs ++ " \n" ++ concatMap show cs
  show (SCNewType) = "newtype \n"

instance Show SCConstr where
  show (SCConstr m c ts) = "  " ++ show m ++ c ++ concatMap ((" " ++) . showNestType) ts ++ "\n"

instance Show SCTopDef where
  show (SCTopDef _ n as (rt,e)) = n ++ " :: " ++ concatMap ((++ " -> ") . show . snd) as  ++ show rt ++ "\n" ++ n ++ concatMap ((" " ++) . fst) as ++ " =\n" ++ show e ++ "\n"

instance Show SCType where
  show (SCTypeCon c xs ) = show c ++ concatMap ((" " ++) . showNestType) xs
  show (SCTypeArrow x y) = showNestType x ++ " -> " ++ show y
  show (SCTypeOther    ) = "t"

showNestType :: SCType -> String
showNestType (SCTypeOther   ) = "t"
showNestType (SCTypeCon c []) = show c
showNestType t                =  "(" ++ show t ++ ")"

instance Show SCExp where
  show (SCFun (m, n) xs) = show m ++ n ++ concatMap ((" " ++) . showNestExp) xs
  show (SCVar n        ) = n
  show (SCCon c xs     ) = show c ++ concatMap ((" " ++) . showNestExp) xs
  show (SCLit i        ) = show i
  show (SCApply a xs   ) = showNestExp a ++ concatMap ((" " ++) . showNestExp) xs
  show (SCLam vs e     ) = "\\"  ++ concatMap ((" " ++) . fst) vs ++ " -> " ++ show e
  show (SCLet x e      ) = "%let " ++ show x ++ " %in\n" ++ show e
  show (SCLetRec rs e  ) = "%letrec" ++ concatMap (("\n  " ++) . show) rs ++ " %in\n" ++ show e
  show (SCCase e (v,t) r xs) = "%case " ++ showNestExp e ++ " " ++ v ++ " :: " ++ show t ++ " -> " ++ show r ++ " %of {" ++ concatMap (("\n    " ++) . show) xs ++ "\n}"

showNestExp :: SCExp -> String
showNestExp (SCFun (m, n) []) = show m ++ n
showNestExp (SCVar n) = n
showNestExp (SCCon c []) = show c
showNestExp (SCLit i) = show i
showNestExp x = "(" ++ show x ++ ")"

instance Show SCLetBinding where
  show (SCLB n as _ x) = n ++ concatMap ((" " ++) . fst) as ++ " = " ++ show x

instance Show SCAlt where
  show (SCConAlt c xs e) = show c ++ concatMap ((" " ++) . fst) xs ++ " -> " ++ show e
  show (SCLitAlt i e) = show i ++ " -> " ++ show e
  show (SCDefault e) = "_ -> " ++ show e

instance Show SCLit where
  show (SCInt i _)      = show i
  show (SCRational r _) = show r
  show (SCChar c _)     = show c
  show (SCString s _)   = show s
