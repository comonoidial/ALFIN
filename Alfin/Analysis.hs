module Alfin.Analysis where

import Data.Map (Map, (!), insert, singleton, fromList)

import Alfin.Syntax

data VarDef
  = InputArg Int
  | FixVar
  | ScrutVar (Maybe ConName)
  | ConParam ConName Int
  | StoreCon ConName
  | StoreFun FunName
  | StorePap FunName Int
  | IntConst Int
  | OtherExp
  deriving Show

data VarUse
  = Unused
  | VarUse :&: VarUse
  | AltUses [VarUse]
  | Forced
  | Matched [Pattern]
  | Selected ConName Int
  | Applied [VarDef]
  | ConArg ConName Int
  | FunArg FunName Int
  | OtherArg
  deriving Show

data Result
  = MultiRes [Result]
  | RetCon ConName [VarDef]
  | RetPap FunName ArgCount
  | TailCall FunName
  | JumpEval VarDef
  | OtherRes
  deriving Show

faBlock :: Map Variable VarDef -> Block -> (Map Variable VarUse, Result)
faBlock vs (Block [] t) = faTerm vs t

faTerm :: Map Variable VarDef -> Terminator -> (Map Variable VarUse, Result)
faTerm vs (Return (Con c)   xs) = (fromList $ zip xs $ map (ConArg c) [0..], RetCon c (map (vs!) xs))
faTerm vs (Return (Pap f n) xs) = (fromList $ zip xs $ map (FunArg f) [0..], RetPap f n)
faTerm vs (Return t         xs) = (fromList $ zip xs $ repeat OtherArg     , OtherRes)
--faTerm vs (Jump CallExpr [CallCont])
--faTerm vs (Case CallExpr [CallCont] [(Pattern, Block)])
faTerm vs (Throw x) = (singleton (Var Ref x) OtherArg, OtherRes)
--faTerm vs (Cond BoolVar Block Block)
--faTerm vs (Switch PrimVar Block [(Int, Block)])

