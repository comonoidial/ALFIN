module Alfin.FromCore where

import Control.Monad.State
import Data.List (lookup, partition)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

import Alfin.LowCore
import Alfin.Syntax
import Alfin.Optimize
import Alfin.Builtins

type Context a = State ([(QName, ([ShapeType], FunKind))], [(QName, Int)], [VarDef], Int) a

newName :: String -> Context String
newName x = do
  (a,b,c,n) <- get
  put (a,b,c,n+1)
  return (x ++ "_" ++ show n)

withLocalVars :: [VarDef] -> Context a -> Context a
withLocalVars vs a = do
  (fs,cs,xs,n) <- get
  put (fs,cs,vs++xs,n)
  x <- a
  (fs',cs',_,n') <- get
  put (fs',cs',xs,n')
  return x

introFun :: QName -> [ShapeType] -> ShapeType -> TopExp -> Context ()
introFun f [_] _ (SimpleExp (Var x)) = do
  let fi = (f, ([RefType], IdFun)) 
  (fs,cs,xs,n) <- get
  put (fi:fs,cs,xs,n)
introFun f [_] _ (SimpleExp (Selector c i (Var _))) = do
  let fi = (f, ([RefType], SelFun c i)) 
  (fs,cs,xs,n) <- get
  put (fi:fs,cs,xs,n)
introFun f as rt _ = do
  (fs,cs,xs,n) <- get
  put ((funInfo f as rt):fs,cs,xs,n)

funInfo :: QName -> [ShapeType] -> ShapeType -> (QName, ([ShapeType], FunKind))
funInfo f as (PType  p) = (f, (as, PrimFun p ))
funInfo f as rt         = (f, (as, RealFun rt))

introFix :: QName -> [ShapeType] -> ShapeType -> Context ()
introFix f as rt = do
  (fs,cs,xs,n) <- get
  put ((f,(as, FixFun rt)):fs,cs,xs,n)

c2aMod :: LCModule -> Module
c2aMod (LCModule m xs ys) = Module m (map c2aData ds) (map snd builtinPrimOps ++ concat (evalState (mapM c2aFun ys) ct))
  where ct = (baseFuns ++ map fst builtinPrimOps ++ map c2aFD ys, concatMap c2aCD ds, [], 0)
        ds = baseData ++ xs
        c2aFD (FunDef f [_] r (SimpleExp (VarExp _))) = (f, ([RefType], IdFun))
        c2aFD (FunDef f [_] r (SimpleExp (Selector c i (Var _)))) = (f, ([RefType], SelFun c i))
        c2aFD (FunDef f xs r _) = funInfo f (map snd xs) r
        c2aCD (DataDef _ cs) = map (fmap length) cs

c2aData :: DataDef -> TypeCon
c2aData (DataDef (m,tc) cs) = TypeCon (m ++ "." ++ tc) (map c2aCon cs)
  where c2aCon (c,xs) = ((cName c), map type2Kind xs)

c2aFun :: FunDef -> Context [Definition]
c2aFun (FunDef f xs rt e) = do
  (fs, b) <- withLocalVars xs (c2aTopExp [] rt e)
  return (Definition (fName f) Nothing (buildParams xs) b : fs)

c2aFix :: QName -> String -> [VarDef] -> ShapeType -> TopExp -> Context [Definition]
c2aFix f r xs rt e = do
  (fs, b) <- withLocalVars ((r,rt):xs) (c2aTopExp [] RefType e)
  return (Definition (fName f) (Just r) (buildParams xs) b : fs)

c2aTopExp :: [Statement] -> ShapeType -> TopExp -> Context ([Definition], Block)
c2aTopExp xs (PType pt) (SimpleExp (VarExp x)         ) = return ([], Block xs (Return (Box $ defaultPrimBox pt) [Right $ pv x]))
c2aTopExp xs (PType pt) (SimpleExp (LitExp (IntLit i))) = do
  x <- newName "i"
  return ([], Block (xs ++ [x := Constant i]) (Return (Box $ defaultPrimBox pt) [Right $ pv x]))
c2aTopExp xs (PType pt) (SimpleExp (FunVal f ys)) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  case (snd fk) of
    ErrFun e -> do
      x <- newName "n"
      y <- newName "e"
      return ([], Block (xs ++ [x := Constant e, y := Store (Box (ConName ".ErrorCode")) [pa x]]) (Throw (rv y)))
    PrimOp (PType _) -> do
      ys' <- mapM c2aArgument ys
      let as = buildArgs (map snd ys')
      case as of
        [Right n] -> do
          x <- newName "y"
          return ([], Block (xs ++ concatMap fst ys' ++ [x := PrimOper (Operator (snd f)) n Nothing]) (Return (Box $ defaultPrimBox pt) [Right $ pv x]))
        [Right n, Right m] -> do
          x <- newName "y"
          return ([], Block (xs ++ concatMap fst ys' ++ [x := PrimOper (Operator (snd f)) n (Just m)]) (Return (Box $ defaultPrimBox pt) [Right $ pv x]))
        _ -> error ("todo IntK c2aTopExp" ++ show as)
    PrimFun _ -> do
      ys' <- mapM c2aArgument ys
      let as = buildArgs $ map snd ys'
      return ([], Block (xs ++ concatMap fst ys') (Jump (Call (fName f) as) []))
    RealFun _ | null ys -> return ([], Block xs (Jump (Call (fName f) []) [])) -- could be an error throwing CAF
    _ -> error $ show fk
c2aTopExp xs RefType (SimpleExp (VarExp x)         ) = return ([], Block xs (Jump (Eval x) [])                          )
c2aTopExp xs RefType (SimpleExp (ConExp c ys)) = do
  ys' <- mapM c2aArgument ys
  (t, as) <- buildConNodeArg c (map snd ys')
  return ([], Block (xs ++ concatMap fst ys') (Return t as))
c2aTopExp xs RefType (SimpleExp (FunVal f ys)) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  case (snd fk) of
    ErrFun e -> do
      x <- newName "n"
      y <- newName "e"
      return ([], Block (xs ++ [x := Constant e, y := Store (Box (ConName ".ErrorCode")) [pa x]]) (Throw y))
    SelFun c i -> do
      case ys of
        []  -> return ([], Block xs (Return (PSel (cName c) i) []))
        [y] -> do
          (zs,ce,pcs) <- c2aCallingExp y
          return ([], Block (xs ++ zs) (Jump ce (pcs ++ [Select (cName c) i])))
        _   -> error "TODO over applying SelFun in c2aTopExp"
    _ -> do
      let na = length (fst fk)
      ys' <- mapM c2aArgument ys
      let as = buildArgs (map snd ys')
      case (snd fk) of
        RealFun _ -> do
          case compare (length as) na of
            LT -> return ([], Block (xs ++ concatMap fst ys') (Return (Pap (fName f) (na - length as)) as                  ))
            EQ -> return ([], Block (xs ++ concatMap fst ys') (Jump (Call  (fName f) as              ) []                  ))
            GT -> return ([], Block (xs ++ concatMap fst ys') (Jump (Call  (fName f) (take na as)    ) [Apply (drop na as)]))
        FixFun _ -> do
          case compare (length as) na of
            EQ -> return ([], Block (xs ++ concatMap fst ys') (Jump (Fix (fName f) as) []))
            _ -> error "FixFun with wrong number of arguments"
        CmpFun -> case as of
          [Right n, Right m] -> do
            b <- newName "b"
            return ([], Block (xs ++ concatMap fst ys' ++ [b :<-?: RunCmpOp (Operator (snd f)) n m]) (BoolReturn b (Con (ConName "GHCziBool.True")) (Con (ConName "GHCziBool.False"))))
          _ -> error ("todo CmpFun c2aTopExp" ++ show as)
        x -> error ("c2aTopExp NodeRes" ++ show f ++ " " ++ show x)
c2aTopExp xs RefType (SimpleExp (ApplyExp f ys)) = do
  (zs, c, cc) <- c2aCallingExp f
  ys' <- mapM c2aArgument ys
  return ([], Block (xs ++ zs ++ concatMap fst ys') (Jump c (cc ++ [Apply (buildArgs (map snd ys'))])))
c2aTopExp xs RefType (SimpleExp (Selector d i y)) = do
  (ys, c, cc) <- c2aCallingExp y
  return ([], Block (xs ++ ys) (Jump c (cc ++ [Select (cName d) i])))
c2aTopExp xs rt (SLet (n,t@(PType _)) x e) = do
  ys <- c2aPrimExp n x
  withLocalVars [(n,t)] (c2aTopExp (xs ++ ys) rt e)
c2aTopExp xs rt (SLet (n,t) x e) = do
  ys <- c2aLazyRefExp n x
  withLocalVars [(n,t)] (c2aTopExp (xs ++ ys) rt e)
c2aTopExp xs rt (LetExp f as t x e) = do
  introFun f (map snd as) t x
  fs <- c2aFun (FunDef f as t x)
  (gs, e') <- c2aTopExp xs rt e
  return (fs ++ gs, e')
c2aTopExp xs rt (LetRec f r as t x e) = do
  introFix f (map snd as)  t
  fs <- c2aFix f r as t x
  (gs, e') <- c2aTopExp xs rt e
  return (fs ++ gs, e')
c2aTopExp xs rt (CaseExp sr e t@(PType _) [DefAlt d, IntAlt i x]) = do
  (ys, v) <- c2aArgument e
  c <- newName "c"
  let (s,lv) = ([(sr, Right $ PrimVar $ fst v)], [(sr,t)])
  d' <- withLocalVars lv $ c2aTopExp [] rt d
  x' <- withLocalVars lv $ c2aTopExp [] rt x
  n <- newName "i"
  return (fst d' ++ fst x', Block (xs ++ ys ++ [n :<~: Constant i, c :<-?: RunCmpOp (Operator "zezezh") (PrimVar $ fst v) (PrimVar n)]) (Cond c (substBlock s $ snd x') (substBlock s $ snd d')))
c2aTopExp xs rt (CaseExp sr x t [ConAlt cn vs e]) = do
  (ys,c,cc) <- c2aCallingExp x
  (fs, Block zs z) <- withLocalVars ((sr,t) : vs) $ c2aTopExp [] rt e
  (nt, ns) <- buildConNode cn vs
  return (fs, Block (xs ++ ys ++ [(Left sr, Just (nt,ns,Nothing)) :<=: (c,cc)] ++ zs) z)
c2aTopExp xs rt (CaseExp _ (FunVal f [a,b]) _ [ConAlt _ [] e, ConAlt _ [] t]) | f `elem` compareFuns = do
  a' <- c2aArgument a
  b' <- c2aArgument b
  c <- newName "c"
  e' <- c2aTopExp [] rt e
  t' <- c2aTopExp [] rt t
  return (fst e' ++ fst t', Block (xs ++ fst a' ++ fst b' ++ [c :<-?: RunCmpOp (Operator (snd f)) (PrimVar $ fst $ snd a') (PrimVar $ fst $ snd b')]) (Cond c (snd t') (snd e')))
c2aTopExp xs rt (CaseExp sr e t [DefAlt d]) = do
  (ys, c, cc) <- c2aCallingExp e
  (fs, Block zs z) <- withLocalVars [(sr,t)] $ c2aTopExp [] rt d
  return (fs, Block (xs ++ ys ++ [(Left sr, Nothing) :<=: (c,cc)] ++ zs) z)
c2aTopExp xs rt (CaseExp sr e t ((DefAlt d) : as)) = do
  (ys, c, cc) <- c2aCallingExp e
  d' <- withLocalVars [(sr,t)] $ c2aTopExp [] rt d
  bs <- mapM (withLocalVars [(sr,t)] . c2aAlt rt) as
  return (fst d' ++ concatMap fst bs, Block (xs ++ ys) (Case c cc (Left sr) (Just $ snd d') (map snd bs)))
c2aTopExp xs rt (CaseExp sr e t as) = do
  (ys, c, cc) <- c2aCallingExp e
  bs <- mapM (withLocalVars [(sr,t)] . c2aAlt rt) as
  return (concatMap fst bs, Block (xs ++ ys) (Case c cc (Left sr) Nothing (map snd bs)))
c2aTopExp _ rt x = error ("c2aTopExp " ++ show rt ++ " " ++ show x)

c2aAlt :: ShapeType -> Alternative -> Context ([Function], (ConName, [Variable], Block))
c2aAlt rt (ConAlt c xs e) = do
  (fs,b) <- withLocalVars xs (c2aTopExp [] rt e)
  (Con d, ys) <- buildConNode c xs
  return (fs, (d, ys, b))
c2aAlt _ a = error ("c2aAlt " ++ show a)

c2aPrimExp :: String -> SimpleExp -> Context [Statement]
c2aPrimExp _ (VarExp _) = error "c2aStrictExp (Var x)"
c2aPrimExp n (LitExp (IntLit i)) = return [n := Constant i]
c2aPrimExp n (FunVal f xs) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  case (snd fk) of
    PrimFun pt -> do
      ys' <- mapM c2aArgument xs
      let as = buildArgs $ map snd ys'
      return (concatMap fst ys' ++ [(dummyResultRef, Just (Box (defaultPrimBox pt), [pp n], Nothing)) :<=: (Call (fName f) as, [])])
    PrimOp (PType _) -> do
      ys' <- mapM c2aArgument xs
      let as = buildArgs (map snd ys')
      case as of
        [Right a] -> do
          return (concatMap fst ys' ++ [n :<~: PrimOp (Operator (snd f)) [a]])
        [Right a, Right b] -> do
          return (concatMap fst ys' ++ [n :<~: PrimOp (Operator (snd f)) [a, b]])
        _ -> error ("todo IntK c2aPrimExp" ++ show as)
    x -> error ("c2aPrimExp " ++ show f ++ " " ++ show x)
c2aPrimExp n x = error ("todo c2aPrimExp " ++ show n ++ "  " ++ show x)

c2aLazyRefExp :: String -> SimpleExp -> Context [Statement]
c2aLazyRefExp _ (VarExp _) = error "c2aLazyRefExp (Var x)"
c2aLazyRefExp n (ConExp c xs) = do
  xs' <- mapM c2aArgument xs
  (t, as) <- buildConNodeArg c (map snd xs')
  return (concatMap fst xs' ++ [n := Store t as])
c2aLazyRefExp n (FunVal f xs) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  let na = length (fst fk)
  ys' <- mapM c2aArgument xs
  let as = buildArgs (map snd ys')
  case (snd fk) of
    RealFun _ -> do
      case compare (length as) na of
        LT -> return (concatMap fst ys' ++ [n := Store (Pap (fName f) (na - length as)) as])
        EQ -> return (concatMap fst ys' ++ [n := Store (Fun (fName f)) as])
    SelFun c i -> 
      case as of
        []  -> return (concatMap fst ys' ++ [n := Store (PSel (cName c) i) []])
        [a] -> return (concatMap fst ys' ++ [n := Store (FSel (cName c) i) [a]])
        _   -> error "TODO c2aLazyRefExp overapplied SelFun"
    x -> error ("c2aLazyRefExp " ++ show x ++ " " ++ show f)
c2aLazyRefExp n (Selector d i x) = do
  y' <- c2aArgument x
  let as = buildArgs [snd y']
  return (fst y' ++ [n := Store (FSel (cName d) i) as])
c2aLazyRefExp n (ApplyExp f xs) = do
  xs' <- mapM c2aArgument (f:xs)
  let as' = buildArgs (map snd xs')
  return (concatMap fst xs' ++ [n := Store (ApN (length xs)) as'])

c2aArgument :: SimpleExp -> Context ([Statement], (String, Kind))
c2aArgument (VarExp x) = do
  t <- gets (fromMaybe (error ("lookup Var " ++ show x)) . lookup x . (\(_,_,vs,_) -> vs))
  return ([], (x, type2Kind t))
c2aArgument (LitExp (IntLit i)) = do
  x <- newName "i"
  return ([x :<~: Constant i], (x, Prim))
c2aArgument (LitExp (StringLit s)) = do
  x <- newName "i"
  return ([x :<-: StringConst s], (x, Ref))
c2aArgument (Con c xs) = do
  xs' <- mapM c2aArgument xs
  (t, as) <- buildConNodeArg c (map snd xs')
  x <- newName "c"
  return (concatMap fst xs' ++ [x := Store t as], (x, Ref))
c2aArgument (FunVal f xs) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  let na = length (fst fk)
  ys' <- mapM c2aArgument xs
  case (snd fk) of
    PrimOp (PType _) -> do
      let as = buildArgs (map snd ys')
      case as of
        [Right n] -> do
          x <- newName "y"
          return (concatMap fst ys' ++ [x := PrimOper (Operator (snd f)) [n]], (x, Prim))
        [Right n, Right m] -> do
          x <- newName "y"
          return (concatMap fst ys' ++ [x := PrimOper (Operator (snd f)) [n m]], (x, Prim))
        _ -> error "todo IntK c2aArgument"
    PrimFun pt -> do
      x <- newName "z"
      let as = buildArgs $ map snd ys'
      return (concatMap fst ys' ++ [(dummyResultRef, Just (Box (defaultPrimBox pt), [pp x], Nothing)) :<=: (Call (fName f) as, [])], (x,Prim))
    RealFun _ -> do
      let as = buildArgs (map snd ys')
      case compare (length as) na of
        LT -> do
          x <- newName "p"
          return (concatMap fst ys' ++ [x := Store (Pap (fName f) (na - length as)) as], (x, Ref))
        EQ -> do
          x <- newName "f"
          return (concatMap fst ys' ++ [x := Store (Fun (fName f)) as], (x, Ref))
        GT -> do
          x <- newName "f"
          y <- newName "oa"
          return (concatMap fst ys' ++ [x := Store (Fun (fName f)) (take na as), y := Store (ApN (length as - na)) (ra x : drop na as)], (y, Ref))
    IdFun -> do
      x <- newName "i"
      let as = buildArgs (map snd ys')
      case as of
        [] -> return ([x := Store PId []], (x, Ref))
        _  -> error "TODO c2aArgument applied IdFun"
    SelFun c i -> do
      x <- newName "s"
      let as = buildArgs (map snd ys')
      case as of
        []  -> return (concatMap fst ys' ++ [x := Store (PSel (cName c) i) []], (x, Ref))
        [a] -> return (concatMap fst ys' ++ [x := Store (FSel (cName c) i) [a]], (x, Ref))
        _   -> error "TODO c2aArgument overapplied SelFun"
    _ -> error ("c2aArgument FunVal " ++ show f ++ " " ++ show fk)
c2aArgument (Selector d i x) = do
  y' <- c2aArgument x
  let as = buildArgs [snd y']
  n <- newName "s"
  return (fst y' ++ [n := Store (FSel (cName d) i) as], (n,Ref))
c2aArgument (ApplyExp f xs) = do
  xs' <- mapM c2aArgument (f:xs)
  let as = buildArgs (map snd xs')
  x <- newName "a"
  return (concatMap fst xs' ++ [x := Store (ApN (length xs)) as], (x, Ref))

c2aCallingExp :: SimpleExp -> Context ([Statement], CallExpr, [CallCont])
c2aCallingExp (VarExp x) = return ([], Eval x, [])
c2aCallingExp (FunVal f xs) = do
  ft <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  let na = length (fst ft)
  ys' <- mapM c2aArgument xs
  let as = buildArgs (map snd ys')
  case (snd ft) of
    RealFun _ -> do
      case compare (length as) na of
        LT -> error "strict arg pap"
        EQ -> return (concatMap fst ys', Call (fName f) as          , [])
        GT -> return (concatMap fst ys', Call (fName f) (take na as), [Apply (drop na as)])
    FixFun _ -> do
      case compare (length as) na of
        EQ -> return (concatMap fst ys', Fix (fName f) as, [])
        _  -> error "FixFun with wrong number of arguments"
    _ -> error ("c2aCallingExp " ++ show f ++ " " ++ show ft)
c2aCallingExp (ApplyExp f xs) = do
  (ys, c, cc) <- c2aCallingExp f
  xs' <- mapM c2aArgument xs
  return (ys ++ concatMap fst xs', c, cc ++ [Apply (buildArgs (map snd xs'))])
c2aCallingExp (Selector d i x) = do
  (ys, c, cc) <- c2aCallingExp x
  return (ys, c, cc ++ [Select (cName d) i])

buildConNodeArg :: QName -> [(String,Kind)] -> Context (NodeTag, [Variable])
buildConNodeArg c xs
  | c `elem` boxConstrs = do
    return (Box (cName c), buildArgs xs)
  | isUnboxTupleCon c   = return (UTuple, buildArgs xs)
  | otherwise           = do
    n <- gets (fromMaybe (error ("lookup Con " ++ show c)) . lookup c . (\(_,cs,_,_) -> cs))
    if (n == length xs)
      then return (Con (cName c), buildArgs xs)
      else return (Dec (cName c) (n - length xs), buildArgs xs)

buildConNode :: QName -> [VarDef] -> Context (NodeTag, [Variable])
buildConNode c xs = do
  n <- gets (fromMaybe (error ("lookup Con " ++ show c)) . lookup c . (\(_,cs,_,_) -> cs))
  case c of
     _ | c `elem` boxConstrs -> return (Box (cName c), buildParams xs)
       | isUnboxTupleCon c   -> return (UTuple                         , buildParams xs)
       | otherwise           -> return (Con (cName c), buildParams xs)

type2Kind :: ShapeType -> Kind
type2Kind (PType _) = Prim
type2Kind _         = Ref

buildArgs :: [(String, Kind)] -> [Variable]
buildArgs = map (flip Var)

buildParams :: [VarDef] -> [Variable]
buildParams = map (\(x,t) -> Var (type2Kind t) x)

fName :: QName -> FunName
fName f = FunName (fst f ++ "." ++ snd f)

cName :: QName -> ConName
cName c = ConName (fst c++"."++snd c)
