module Alfin.LowCore where

data LCModule = LCModule String [DataDef] [FunDef]

data DataDef = DataDef QName [(QName, [ShapeType])]

data FunDef = FunDef QName [VarDef] ShapeType TopExp

type VarDef = (String, ShapeType)

type QName = (String, String)

data ShapeType
  = RefType
  | PType String
  deriving (Show, Eq)

data TopExp
  = SimpleExp SimpleExp
  | SLet VarDef SimpleExp TopExp
  | LetExp QName [VarDef] ShapeType TopExp TopExp
  | LetRec QName String [VarDef] ShapeType TopExp TopExp
  | CaseExp String SimpleExp ShapeType [Alternative]

data Alternative
  = ConAlt QName [VarDef] TopExp
  | IntAlt Int TopExp
  | DefAlt TopExp

data SimpleExp
  = VarExp String
  | LitExp Literal
  | FunVal QName [SimpleExp]
  | ConExp QName [SimpleExp]
  | ApplyExp SimpleExp [SimpleExp]
  | Selector QName Int SimpleExp

data Literal
  = IntLit Int
  | StringLit String

instance Show LCModule where
  show (LCModule m ds fs) = "module " ++ m ++ "\n" ++ concatMap (("\n" ++) . show) ds ++ concatMap (("\n" ++) . show) fs

instance Show DataDef where
  show (DataDef tc cs) = "data " ++ fst tc ++ "." ++ snd tc ++ concatMap (\(c, xs) -> "\n  " ++ snd c ++ concatMap ((" " ++) . show) xs) cs ++ "\n"

instance Show FunDef where
  show (FunDef f as rt x) = snd f ++ " :: "++ concatMap ((++ " -> ") . show . snd) as ++ show rt ++ "\n" ++ snd f ++ concatMap ((" " ++) . fst) as ++ " = " ++ show x ++ "\n"

instance Show TopExp where
  show (SimpleExp e)             = show e
  show (SLet n x e)              = "%var " ++ fst n ++ " = " ++ showNestedExp x ++ " %in " ++ show e
  show (LetExp (m,f) as _ x e)   = "%let " ++ m ++ "." ++ f ++ concatMap ((" " ++) . fst) as ++ " = " ++ show x ++ " %in\n" ++ show e
  show (LetRec (m,f) r as _ x e) = "%letrec " ++ m ++ "." ++ f ++ " " ++ r ++ concatMap ((" " ++) . fst) as ++ " = " ++ show x ++ " %in\n" ++ show e
  show (CaseExp s e t xs)        = "%case " ++ s ++ " <- " ++ showNestedExp e ++ " " ++ show t ++ " %of {" ++ concatMap (("\n    " ++) . show) xs ++ "\n}"

instance Show Alternative where
  show (ConAlt c xs e) = snd c ++ concatMap ((" " ++) . fst) xs ++ " -> " ++ show e
  show (IntAlt i e) = show i ++ " -> " ++ show e
  show (DefAlt e) = "_ -> " ++ show e
  
instance Show SimpleExp where
  show (VarExp n)        = n
  show (LitExp x)        = show x
  show (FunVal (m,f) xs) = m ++ "." ++ f ++ concatMap ((" " ++) . showNestedExp) xs
  show (ConExp (m,c) xs) = m ++ "." ++ c ++ concatMap ((" " ++) . showNestedExp) xs
  show (ApplyExp f xs)    = showNestedExp f ++ concatMap ((" " ++) . showNestedExp) xs
  show (Selector _ n x)  = "sel_#" ++ show n ++ " " ++ showNestedExp x
  
showNestedExp :: SimpleExp -> String
showNestedExp (VarExp n)        = n
showNestedExp (LitExp x)        = show x
showNestedExp (FunVal (m,f) []) = m ++ "." ++ f
showNestedExp (ConExp (m,c) []) = m ++ "." ++ c
showNestedExp (ApplyExp f [])   = show f
showNestedExp e                 = "(" ++ show e ++ ")"

instance Show Literal where
  show (IntLit i)    = show i
  show (StringLit s) = show s
