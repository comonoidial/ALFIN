module Alfin.AsmLang where

data AsmModule = AsmModule String [DataType] [Function]

data DataType = DataType String [Constructor]

type Constructor = (CName, [ArgKind])

data ArgKind = RefArg | PrimArg deriving (Show, Eq)

data Function = Function {fName :: FName, resultRef :: Maybe RefVar, fetchHint :: FetchHint, params :: [Parameter], body :: Block}

data Block = Block [Stmt] TermStmt deriving Eq

data Stmt
  = RefVar :<-: RefExp
  | PrimVar :<~:  PrimExp
  | BoolVar :<-?: CmpExp
  | (CallResultRef, Maybe (AsmTag, [Parameter], FetchHint)) :<=: (CallExp, [PostCall])  -- representing the Call instruction
  | Put_IO AsmTag [Argument]                                                            -- sending a node to the 'world'
  deriving Eq

data TermStmt
  = NodeReturn AsmTag [Argument]         -- returning a node on the stack
  | TopReturn                            -- only used for optimizations
  | BoolReturn BoolVar AsmTag AsmTag     -- returning a boolean as constructors
  | TailCall CallExp [PostCall]          -- aka Jump
  | IfThenElse BoolVar Block Block       -- if then else statement
  | CaseOf CallExp [PostCall] CallResultRef (Maybe Block) [CaseAlt]  -- case statement
  | Error RefVal                         -- error throwing statement
  deriving Eq
  
type CaseAlt = (CName, [Parameter], FetchHint, Block)

data RefExp 
  = StoreNode AsmTag [Argument]          -- storing a node on the heap, producing a reference
--  | StoreBool BoolVar AsmTag AsmTag      -- removed for now
  | StoreSel BoolVar RefVal RefVal       -- selection on references /  cond ? then : else
  | StringConstant String                -- just an alternative for a large sequence of simple stores
  deriving Eq

data PrimExp
  = RunPrimOp OpName PrimVal (Maybe PrimVal)  -- unary or binary primitive operation
  | RunPrimSel BoolVar PrimVal PrimVal        -- selection / inline if operation  /  cond ? then : else
  | Constant Int                              -- just a constant
  deriving Eq

data CmpExp
  = RunCmpOp OpName PrimVal PrimVal         -- comparison operation
--  | RunLogicOp OpName BoolVar BoolVar   -- removed for now
  deriving Eq

data CallExp
  = EvalRef RefVal               -- loading and evaluating a reference
  | LoadRef RefVal               -- loading an already evaluated reference
  | UseFetched Bool              -- use prefetched reference, Bool is requires evaluation
  | Run_Fun FName [Argument]     -- calling a plain function
  | Run_Fix FName [Argument]     -- calling a (fixpoint) function with a reference to its result
  | Get_IO                       -- retrieving a node from the 'world'
  deriving Eq

data PostCall
  = Applying [Argument]        -- applying some more arguments
  | Selecting CName ElemIndex  -- selecting a reference from the resulting node
  | NextFetch RefVal           -- set next reference to fetch
  | CatchWith RefVal           -- setting exception handler for current call
  | WithOp OpName PrimVal      -- extra prim operation on the result
  deriving Eq

data AsmTag 
  = ConTag CName             -- fully applied constructor
  | DecTag CName ArgCount    -- partial constructor with number of missing args
  | HoleCon CName ElemIndex  -- partial constructor with a single missing arg at the specified location
  | BoxCon CName             -- boxed primitive constructor
  | FunTag FName             -- fully applied function
  | PapTag FName ArgCount    -- partial function application with number of missing args
  | HoleFun FName ElemIndex  -- partial function application with a single missing arg at the specified location
  | ApTag Int                -- unknown function application with number of application args
  | FSelTag CName ElemIndex  -- selection as a function with index
  | PSelTag CName ElemIndex  -- partial applied selection with index
  | PIdTag                   -- partial applied identity function
  | RawTuple                 -- unboxed tuple from ghc
  deriving Eq

type ElemIndex = Int
type ArgCount = Int

type FetchHint = Maybe ElemIndex
type CallResultRef = Either RefVar String  -- Right is only name for constructor alt index prim/cond
dummyResultRef :: CallResultRef
dummyResultRef = Right "~"

type Parameter = Either RefVar PrimVar
type Argument  = Either RefVal PrimVal

data PrimVal
  = PrimVar PrimVar
  | SmallImm Int     -- very small constant replacing a variable (by optimization)
  | BigImm Int       -- big constant that is allowed in some specific instructions
  deriving Eq

data RefVal
  = RefVar RefVar
  | RefHole          -- representing a dummy reference that is in the place of hole in 'holed' nodes
  | SmallCon CName   -- special builtin enum constructors replacing a variable  (by optimization)
  deriving Eq

newtype OpName = OpName String deriving (Eq, Ord)  -- prim operator name
newtype FName  = FName String deriving (Eq, Ord)   -- function name
newtype CName  = CName String deriving (Eq, Ord)   -- constructor name
type RefVar  = String
type PrimVar = String
type BoolVar = String

instance Show OpName where show (OpName p) = p
instance Show FName where show (FName f) = f
instance Show CName where show (CName c) = c

instance Show AsmModule where
  show (AsmModule m ds fs) = "%MODULE " ++ m ++ "\n" ++ concatMap (("\n" ++) . show) ds ++ "\n" ++ concatMap ((++ "\n\n") . show) fs

instance Show DataType where
  show (DataType tc cs) = "%DATA " ++ tc ++ "\n" ++ concatMap (\(c,x) -> "  " ++ show c ++ " " ++ show x ++ "\n") cs

instance Show Function where
  show (Function f Nothing Nothing [] c) = "%CAF " ++ show f ++ " =" ++ showBlock "   " c
  show (Function f mr      me      xs c) = "%FUN " ++ show f ++ maybe "" ("%fix " ++) mr ++ showParams xs ++ " =" ++ maybe "" (("   -- E:" ++) . show) me ++ showBlock "   " c

showBlock :: String -> Block -> String
showBlock is (Block xs y) = concatMap (("\n" ++) . (is ++) . show) xs ++ "\n" ++ is ++ showTerm is y

instance Show AsmTag where
  show (ConTag n)    = "C:" ++ show n
  show (DecTag n a)  = "D"  ++ "-" ++ show a ++ ":" ++ show n
  show (HoleCon n i) = "H@" ++ show i ++ "C:" ++ show n
  show (BoxCon n)    = "B:" ++ show n
  show (FunTag f)    = "F:" ++ show f
  show (PapTag f a)  = "P" ++ "-" ++ show a ++":" ++ show f
  show (HoleFun f i) = "H@" ++ show i ++ "F:" ++ show f
  show (ApTag n)     = "AP^" ++ show n
  show (FSelTag d i) = "FSEL~" ++ show d ++ "#" ++ show i
  show (PSelTag d i) = "PSEL~" ++ show d ++ "#" ++ show i
  show (PIdTag)      = "PID"
  show (RawTuple)    = "(#..#)"

instance Show Stmt where
  show (x  :<-:  e)          = x ++ " <- " ++ show e
  show (x  :<~:  e)          = x ++ "# <- " ++ show e
  show (x  :<-?: e)          = x ++ "? <- " ++ show e
  show ((ms,mn) :<=: (c,cc)) = either (++ "@ ") (const "") ms ++ maybe "_" (\(t,x,_) -> show t ++ showParams x) mn ++ " <= %CALL " ++ show c ++ concatMap ((", " ++) . show) cc ++ maybe "" (\(_,_,me) -> maybe "" (("   -- E:" ++) . show) me) mn 
  show (Put_IO t vs)         = "%SEND " ++ show t ++ showBody vs

instance Show PrimVal where
  show (PrimVar x ) = x ++ "#"
  show (SmallImm i) = show i ++ "#"
  show (BigImm i  ) = show i ++ "#"

instance Show RefVal where
  show (RefVar   x) = x
  show (RefHole   ) = "_HOLE_"
  show (SmallCon c) = "C_" ++ show c

showBody :: [Argument] -> String
showBody = concatMap ((" "++) . either show show)

showParams :: [Parameter] -> String
showParams = concatMap ((" "++) . either id (++"#"))

showTerm :: String -> TermStmt -> String
showTerm _  (NodeReturn t xs)    = "%RETURN " ++ show t ++ showBody xs
showTerm _  (TopReturn)          = "%RETURN %top"
showTerm _  (BoolReturn c t e)   = "%RETURN " ++ c ++ "?  %then " ++ show t ++ " %else " ++ show e
showTerm _  (TailCall c cc)      = "%JUMP " ++ show c ++ concatMap ((", " ++) . show) cc
showTerm is (IfThenElse c x y)   = "%IF " ++ c ++ "?\n " ++ is ++ "%THEN" ++ showBlock (is ++ "    ") x ++ "\n " ++ is ++ "%ELSE" ++ showBlock (is ++ "    ") y
showTerm is (CaseOf c cc ms md xs) = "%CASE " ++ either (++ " <- ") (const "") ms ++ show c ++ concatMap ((", " ++) . show) cc ++ 
  maybe "" (\b -> "\n   " ++ is ++ "default -> " ++ showBlock (is ++ "      ") b) md ++ concatMap (showAlt is) xs
showTerm _  (Error x)            = "%THROW " ++ show x  

showAlt :: String -> (CName, [Parameter], FetchHint, Block) -> String
showAlt is (t, vs, me, b) = "\n   " ++ is ++ "C:" ++ show t ++ showParams vs ++ " ->"  ++ maybe "" (("   -- E:" ++) . show) me ++ showBlock (is ++ "      ") b

instance Show RefExp where
  show (StoreNode t vs)   = "%STORE " ++ show t ++ showBody vs
--  show (StoreBool c t e)  = "%store " ++ c ++ " ? " ++ show t ++ " : " ++ show e
  show (StoreSel c x y)   = c ++ "? %then " ++ show x ++ " %else " ++ show y
  show (StringConstant s) = show s

instance Show PrimExp where
  show (RunPrimOp p x Nothing)  = show p ++ " " ++ show x
  show (RunPrimOp p x (Just y)) = show x ++ " `" ++ show p ++ "` " ++ show y
  show (Constant i)             = show i
  show (RunPrimSel c x y)       = c ++ "? %then " ++ show x ++ " %else " ++ show y

instance Show CmpExp where
  show (RunCmpOp f a b)   = show a ++ " `" ++ show f ++ "` " ++ show b
--  show (RunLogicOp f a b) =  a ++ " " ++ show f ++ " " ++ b

instance Show CallExp where
  show (EvalRef x)        = "%eval " ++ show x
  show (LoadRef x)        = "%load " ++ show x
  show (UseFetched True)  = "%evalfetched"
  show (UseFetched False) = "%pushfetched"
  show (Run_Fun f vs)     = {- "%fun " ++ -} show f ++ showBody vs
  show (Run_Fix f vs)     = "%fix " ++ show f ++ showBody vs
  show (Get_IO)           = "%receive"

instance Show PostCall where
  show (Selecting d i) = "%select " ++ show d ++ " #" ++ show i
  show (Applying vs  ) = "%apply" ++ showBody vs
  show (NextFetch x  ) = "%thenfetch " ++ show x
  show (CatchWith x  ) = "%catch " ++ show x
  show (WithOp  f x  ) = "%with " ++ show f ++ " " ++ show x

rp, pp :: String -> Parameter
rp = Left
pp = Right

ra, pa :: String -> Argument
ra = Left . RefVar
pa = Right . PrimVar

rca :: CName -> Argument
rca = Left . SmallCon

pia :: Int -> Argument
pia = Right . SmallImm

pv :: String -> PrimVal
pv = PrimVar

rv :: String -> RefVal
rv = RefVar
