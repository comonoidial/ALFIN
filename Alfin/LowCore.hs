module Alfin.LowCore where

data LCModule = LCModule String [DataDef] [FunDef]

data DataDef = DataDef TCName [(ConName, [ShapeType])]

data FunDef = FunDef FunName [VarDef] ShapeType TopExp

type VarDef = (String, ShapeType)

type FunName = (String, String)
type ConName = (String, String)
type TCName = (String, String)

data ShapeType
  = RefType
  | PType String
  deriving (Show, Eq)

data TopExp
  = SimpleExp SimpleExp
  | SLet VarDef SimpleExp TopExp
  | Let FunName [VarDef] ShapeType TopExp TopExp
  | LetRec FunName String [VarDef] ShapeType TopExp TopExp
  | Case String SimpleExp ShapeType [Alternative]

data Alternative
  = ConAlt ConName [VarDef] TopExp
  | IntAlt Int TopExp
  | DefAlt TopExp

data SimpleExp
  = Var String
  | Lit Literal
  | FunVal FunName [SimpleExp]
  | Con ConName [SimpleExp]
  | Apply SimpleExp [SimpleExp]
  | Selector ConName Int SimpleExp

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
  show (Let (m,f) as _ x e)      = "%let " ++ m ++ "." ++ f ++ concatMap ((" " ++) . fst) as ++ " = " ++ show x ++ " %in\n" ++ show e
  show (LetRec (m,f) r as _ x e) = "%letrec " ++ m ++ "." ++ f ++ " " ++ r ++ concatMap ((" " ++) . fst) as ++ " = " ++ show x ++ " %in\n" ++ show e
  show (Case s e t xs)           = "%case " ++ s ++ " <- " ++ showNestedExp e ++ " " ++ show t ++ " %of {" ++ concatMap (("\n    " ++) . show) xs ++ "\n}"

instance Show Alternative where
  show (ConAlt c xs e) = snd c ++ concatMap ((" " ++) . fst) xs ++ " -> " ++ show e
  show (IntAlt i e) = show i ++ " -> " ++ show e
  show (DefAlt e) = "_ -> " ++ show e
  
instance Show SimpleExp where
  show (Var n)           = n
  show (Lit x)           = show x
  show (FunVal (m,f) xs) = m ++ "." ++ f ++ concatMap ((" " ++) . showNestedExp) xs
  show (Con (m,c) xs)    = m ++ "." ++ c ++ concatMap ((" " ++) . showNestedExp) xs
  show (Apply f xs)      = showNestedExp f ++ concatMap ((" " ++) . showNestedExp) xs
  show (Selector _ n x)  = "sel_#" ++ show n ++ " " ++ showNestedExp x
  
showNestedExp :: SimpleExp -> String
showNestedExp (Var n)           = n
showNestedExp (Lit x)           = show x
showNestedExp (FunVal (m,f) []) = m ++ "." ++ f
showNestedExp (Con (m,c) [])    = m ++ "." ++ c
showNestedExp (Apply f [])      = show f
showNestedExp e                 = "(" ++ show e ++ ")"

instance Show Literal where
  show (IntLit i)    = show i
  show (StringLit s) = show s
