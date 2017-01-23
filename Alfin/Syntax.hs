module Alfin.Syntax where

data Module = Module String [TypeCon] [Definition]

data TypeCon = TypeCon String [DataCon]

type DataCon = (ConName, [Kind])

data Kind = Ref | Word | Bool deriving (Show, Eq)

data Definition = Definition FunName (Maybe RefVar) [Variable] Block

data Block = Block [Statement] Terminator

data Statement
  = Variable := Expression
  | Send NodeTag [Variable]                      -- sending a node to the 'world'

data Terminator
  = Return NodeTag [Variable]                    -- returning a node on the stack
  | Jump CallExpr [CallCont]                     -- tail call
  | Cond BoolVar Block Block                     -- if then else statement
  | Case CallExpr [CallCont] [(Pattern, Block)]  -- case statement
  | Throw RefVar                                 -- error throwing statement

data Pattern
  = Default Variable
  | ConPat (Maybe Variable) ConName [Variable]
  | IntPat Int

data Expression
  = Store NodeTag [Variable]     -- storing a node on the heap, producing a reference
  | StringConst String           -- just an alternative for a large sequence of simple stores
  | PrimOp Operator [Variable]   -- unary or binary primitive operation
  | Constant Int                 -- just a constant
  deriving Eq

data CallExpr
  = Eval RefVar             -- loading and evaluating a reference
  | Fetch RefVar            -- loading an already evaluated reference
  | Call FunName [Variable] -- calling a plain function
  | Fix FunName [Variable]  -- calling a (fixpoint) function with a reference to its result
  | Receive                 -- retrieving a node from the 'world'
  deriving Eq

data CallCont
  = Apply [Variable]          -- applying some more arguments
  | ApplyAll [Variable]       -- applying the exact number or required arguments 
  | Select ConName ElemIndex  -- selecting a reference from the resulting node
  | Catch RefVar              -- setting exception handler for current call
  deriving Eq

data NodeTag 
  = Con ConName             -- fully applied constructor
  | Dec ConName ArgCount    -- partial constructor with number of missing args
  | Box ConName             -- boxed primitive constructor
  | Fun FunName             -- fully applied function
  | Pap FunName ArgCount    -- partial function application with number of missing args
  | ApN Int                 -- unknown function application with number of application args
  | FSel ConName ElemIndex  -- selection as a function with index
  | PSel ConName ElemIndex  -- partial applied selection with index
  | PId                     -- partial applied identity function
  | UTuple                  -- unboxed tuple
  deriving Eq

data Variable = Var Kind String deriving Eq
  
type ElemIndex = Int
type ArgCount = Int

newtype Operator = Operator String deriving (Eq, Ord)  -- prim operator name
newtype FunName  = FunName String deriving (Eq, Ord)   -- function name
newtype ConName  = ConName String deriving (Eq, Ord)   -- constructor name
type RefVar  = String
type PrimVar = String
type BoolVar = String

instance Show Operator where show (Operator p) = p
instance Show FunName where show (FunName f) = f
instance Show ConName where show (ConName c) = c

instance Show Module where
  show (Module m ds fs) = "%MODULE " ++ m ++ "\n" ++ concatMap (("\n" ++) . show) ds ++ "\n" ++ concatMap ((++ "\n\n") . show) fs

instance Show TypeCon where
  show (TypeCon tc cs) = "%DATA " ++ tc ++ "\n" ++ concatMap (\(c,x) -> "  " ++ show c ++ " " ++ show x ++ "\n") cs

instance Show Definition where
  show (Definition f Nothing [] c) = "%CAF " ++ show f ++ " =" ++ showBlock "   " c
  show (Definition f mr      xs c) = "%FUN " ++ show f ++ maybe "" ("%fix " ++) mr ++ showVars xs ++ " =" ++ showBlock "   " c

showBlock :: String -> Block -> String
showBlock is (Block xs y) = concatMap (("\n" ++) . (is ++) . show) xs ++ "\n" ++ is ++ showTerm is y

instance Show NodeTag where
  show (Con n)    = "C:" ++ show n
  show (Dec n a)  = "D"  ++ "-" ++ show a ++ ":" ++ show n
  show (Box n)    = "B:" ++ show n
  show (Fun f)    = "F:" ++ show f
  show (Pap f a)  = "P" ++ "-" ++ show a ++":" ++ show f
  show (ApN n)     = "AP^" ++ show n
  show (FSel d i) = "FSEL~" ++ show d ++ "#" ++ show i
  show (PSel d i) = "PSEL~" ++ show d ++ "#" ++ show i
  show (PId)      = "PID"
  show (UTuple)    = "(#..#)"

instance Show Statement where
  show (x  :=  e)  = show x ++ " <- " ++ show e
  show (Send t vs) = "%SEND " ++ show t ++ showVars vs

instance Show Variable where
  show (Var Ref  x) = x
  show (Var Word x) = x ++ "#"
  show (Var Bool x) = x ++ "?"

showVars :: [Variable] -> String
showVars = concatMap ((" "++) . show)

showTerm :: String -> Terminator -> String
showTerm _  (Return t xs)       = "%RETURN " ++ show t ++ showVars xs
showTerm _  (Jump c cc)         = "%JUMP " ++ show c ++ concatMap ((", " ++) . show) cc
showTerm is (Cond c x y)        = "%IF " ++ c ++ "?\n " ++ is ++ "%THEN" ++ showBlock (is ++ "    ") x ++ "\n " ++ is ++ "%ELSE" ++ showBlock (is ++ "    ") y
showTerm is (Case c cc [(p,b)]) = show p ++ " <= " ++ show c ++ concatMap ((", " ++) . show) cc ++ showBlock is b
showTerm is (Case c cc xs)      = "%CASE " ++ show c ++ concatMap ((", " ++) . show) cc ++ concatMap (showAlt is) xs
showTerm _  (Throw x)           = "%THROW " ++ show x  

showAlt :: String -> (Pattern, Block) -> String
showAlt is (p, b) = "\n   " ++ is ++ show p ++ " -> " ++ showBlock (is ++ "      ") b

instance Show Pattern where
  show (Default x     ) = "def " ++ show x
  show (IntPat i      ) = show i
  show (ConPat ms t vs) = maybe "" ((++"@") . show) ms ++ "C:" ++ show t ++ showVars vs

instance Show Expression where
  show (Store t vs)    = "%STORE " ++ show t ++ showVars vs
  show (StringConst s) = show s
  show (PrimOp p xs)   = show p ++ showVars xs
  show (Constant i)    = show i

instance Show CallExpr where
  show (Eval x)    = "%eval " ++ x
  show (Fetch x)   = "%load " ++ x
  show (Call f vs) = {- "%fun " ++ -} show f ++ showVars vs
  show (Fix f vs)  = "%fix " ++ show f ++ showVars vs
  show (Receive)   = "%receive"

instance Show CallCont where
  show (Select d i ) = "%select " ++ show d ++ " #" ++ show i
  show (Apply vs   ) = "%apply" ++ showVars vs
  show (ApplyAll vs) = "%applyAll" ++ showVars vs
  show (Catch x    ) = "%catch " ++ show x

pv :: String -> Variable
pv = Var Word

rv :: String -> Variable
rv = Var Ref

bv :: String -> Variable
bv = Var Bool