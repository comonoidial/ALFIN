module Alfin.Analysis (analyseMod) where

import Data.Map (Map, (!), insert, singleton, fromList, findWithDefault, keysSet, union, unionsWith, insertWith')
import qualified Data.Set as S (unions, toList)

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

data FunAnalysis = FA Result [VarUse]

instance Show FunAnalysis where
  show (FA r us) = show r ++ concatMap (("\n  " ++) . show) us

analyseMod :: Module -> [(FunName, FunAnalysis)]
analyseMod (Module _ _ fs) = map funAnalysis fs

funAnalysis :: Definition -> (FunName, FunAnalysis)
funAnalysis (Definition f mf xs b) = (f, FA r $ map (flip (findWithDefault Unused) us) xs) where
  (r, us) = faBlock (maybe id (\fv -> insert (Var Ref fv) FixVar) mf $ fromList $ zip xs $ map InputArg [0..]) b

faBlock :: Map Variable VarDef -> Block -> (Result, Map Variable VarUse)
faBlock vs (Block [] t) = faTerm vs t
faBlock vs (Block ((Send c xs): rs) t) = fmap (addUses $ zip xs $ repeat OtherArg) $ faBlock vs (Block rs t)
faBlock vs (Block ((x := Constant i): rs) t) = faBlock (insert x (IntConst i) vs) (Block rs t)
faBlock vs (Block ((x := StringConst _): rs) t) = faBlock (insert x OtherExp vs) (Block rs t)
faBlock vs (Block ((x := PrimOp f xs): rs) t) = fmap (addUses $ zip xs $ repeat OtherArg) $ faBlock (insert x OtherExp vs) (Block rs t)
faBlock vs (Block ((x := Store (Con c) xs): rs) t) = fmap (addUses $ zip xs $ map (ConArg c) [0..]) $ faBlock (insert x (StoreCon c) vs) (Block rs t)
faBlock vs (Block ((x := Store (Fun f _) xs): rs) t) = fmap (addUses $ zip xs $ map (FunArg f) [0..]) $ faBlock (insert x (StoreFun f) vs) (Block rs t)
faBlock vs (Block ((x := Store (Pap f n) xs): rs) t) = fmap (addUses $ zip xs $ map (FunArg f) [0..]) $ faBlock (insert x (StorePap f n) vs) (Block rs t)
faBlock vs (Block ((x := Store (ApN n) xs): rs) t) = fmap (addUses $ zip xs $ repeat OtherArg) $ faBlock (insert x (OtherExp) vs) (Block rs t) -- maybe give the first arg 'Applied' use??
faBlock vs (Block ((x := Store _ xs): rs) t) = fmap (addUses $ zip xs $ repeat OtherArg) $ faBlock (insert x (OtherExp) vs) (Block rs t)

faTerm :: Map Variable VarDef -> Terminator -> (Result, Map Variable VarUse)
faTerm vs (Return (Con c)   xs) = (RetCon c (map (vs!) xs), fromList $ zip xs $ map (ConArg c) [0..])
faTerm vs (Return (Pap f n) xs) = (RetPap f n             , fromList $ zip xs $ map (FunArg f) [0..])
faTerm vs (Return t         xs) = (OtherRes               , fromList $ zip xs $ repeat OtherArg)
faTerm vs (Jump (Eval x) []   ) = (JumpEval (vs!Var Ref x), singleton (Var Ref x) Forced)
faTerm vs (Jump (Eval x) [Apply ys]) = (OtherRes, addUses (zip ys $ repeat OtherArg) $ singleton (Var Ref x) Forced) -- add JumpEvalApply as result??
faTerm vs (Jump (Eval x) [Select c n]   ) = (OtherRes, singleton (Var Ref x) (Selected c n))
faTerm vs (Jump (Call f xs) []) = (TailCall f, fromList $ zip xs $ map (FunArg f) [0..])
faTerm vs (Jump (Call f xs) [Select c n]) = (OtherRes, fromList $ zip xs $ map (FunArg f) [0..])
--faTerm vs (Jump CallExpr [CallCont])
faTerm vs (Case (Eval x) [] [a@(p@(ConPat _ _), _)]) = fmap (addUse (Var Ref x) (Matched [p])) $ faAlt vs a
faTerm vs (Case (Eval x) [] [a]) = fmap (addUse (Var Ref x) Forced) $ faAlt vs a
faTerm vs (Case (Eval x) [Select c n] [a]) = fmap (addUse (Var Ref x) (Selected c n)) $ faAlt vs a
faTerm vs (Case (Eval x) [] as) = (MultiRes rs, addUse (Var Ref x) (Matched $ map fst as) $ mergeUses us) where
  (rs, us) = unzip $ map (faAlt vs) as
faTerm vs (Case (Eval x) [Select c n] as) = (MultiRes rs, addUse (Var Ref x) (Selected c n) $ mergeUses us) where
  (rs, us) = unzip $ map (faAlt vs) as
faTerm vs (Case (Eval x) [Apply ys] as) = (MultiRes rs, addUses (zip ys $ repeat OtherArg) $ addUse (Var Ref x) (Applied $ map (vs!) ys) $ mergeUses us) where
  (rs, us) = unzip $ map (faAlt vs) as
faTerm vs (Case (Call f xs) [] [a]) = fmap (addUses $ zip xs $ map (FunArg f) [0..]) $ faAlt vs a
faTerm vs (Case (Call f xs) [Select c n] [a]) = fmap (addUses $ zip xs $ map (FunArg f) [0..]) $ faAlt vs a
faTerm vs (Case (Call f xs) [] as) = (MultiRes rs, addUses (zip xs $ map (FunArg f) [0..]) $ mergeUses us) where
  (rs, us) = unzip $ map (faAlt vs) as
faTerm vs (Case (Call f xs) [Select c n] as) = (MultiRes rs, addUses (zip xs $ map (FunArg f) [0..]) $ mergeUses us) where
  (rs, us) = unzip $ map (faAlt vs) as
--faTerm vs (Case CallExpr [CallCont] [(Pattern, Block)])
faTerm vs (Throw x) = (OtherRes, singleton (Var Ref x) OtherArg )
faTerm vs (Cond c t e) = (MultiRes [tr,er], addUse (Var Bool c) OtherArg $ mergeUses [tu,eu]) where
  (tr, tu) = faBlock vs t
  (er, eu) = faBlock vs e
faTerm vs (Switch x d as) = (MultiRes rs, addUse (Var Word x) OtherArg $ mergeUses us) where
  (rs, us) = unzip $ map (faBlock vs) (d : map snd as)
faTerm vs t = error ("TODO faTerm " ++ showTerm "" t)

faAlt :: Map Variable VarDef -> (Pattern, Block) -> (Result, Map Variable VarUse)
faAlt vs (AnyPat       , b) = faBlock vs b
faAlt vs (Default d    , b) = faBlock (insert (Var Ref d) (ScrutVar Nothing) vs) b
faAlt vs (ConPat   c xs, b) = faBlock (foldr (uncurry insert) vs $ zip xs $ map (ConParam c) [0..]) b
faAlt vs (NamedP d c xs, b) = faBlock (insert (Var Ref d) (ScrutVar Nothing) $ foldr (uncurry insert) vs $ zip xs $ map (ConParam c) [0..]) b

addUse :: Variable -> VarUse -> Map Variable VarUse -> Map Variable VarUse
addUse = insertWith' (:&:) 

addUses :: [(Variable, VarUse)] -> Map Variable VarUse -> Map Variable VarUse
addUses xs um = foldr (uncurry addUse) um xs

mergeUses :: [Map Variable VarUse] -> Map Variable VarUse
mergeUses xss = fmap AltUses $ unionsWith (++) $ map (fmap (:[]) . flip union km) xss where
  km = fromList $ zip (S.toList $ S.unions $ map keysSet xss) (repeat Unused)
