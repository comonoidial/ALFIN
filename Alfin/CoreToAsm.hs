module Alfin.CoreToAsm where

import Control.Monad.State
import Data.List (lookup, partition)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

import Alfin.LowCore
import Alfin.AsmLang
import Alfin.OptimizeAsm
import Alfin.Builtins

type Context a = State ([(FunName, ([ShapeType], FunKind))], [(ConName, Int)], [VarDef], Int) a

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

introFun :: FunName -> [ShapeType] -> ShapeType -> TopExp -> Context ()
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

funInfo :: FunName -> [ShapeType] -> ShapeType -> (FunName, ([ShapeType], FunKind))
funInfo f as (PType  p) = (f, (as, PrimFun p ))
funInfo f as rt         = (f, (as, RealFun rt))

introFix :: FunName -> [ShapeType] -> ShapeType -> Context ()
introFix f as rt = do
  (fs,cs,xs,n) <- get
  put ((f,(as, FixFun rt)):fs,cs,xs,n)

c2aMod :: LCModule -> AsmModule
c2aMod (LCModule m xs ys) = AsmModule m (map c2aData ds) (map snd builtinPrimOps ++ concat (evalState (mapM c2aFun ys) ct))
  where ct = (baseFuns ++ map fst builtinPrimOps ++ map c2aFD ys, concatMap c2aCD ds, [], 0)
        ds = baseData ++ xs
        c2aFD (FunDef f [_] r (SimpleExp (Var _))) = (f, ([RefType], IdFun))
        c2aFD (FunDef f [_] r (SimpleExp (Selector c i (Var _)))) = (f, ([RefType], SelFun c i))
        c2aFD (FunDef f xs r _) = funInfo f (map snd xs) r
        c2aCD (DataDef _ cs) = map (fmap length) cs

c2aData :: DataDef -> DataType
c2aData (DataDef (m,tc) cs) = DataType (m ++ "." ++ tc) (map c2aCon cs)
  where c2aCon ((b,c),xs) = ((CName (b ++ "." ++ c)), map type2Kind xs)

c2aFun :: FunDef -> Context [Function]
c2aFun (FunDef f xs rt e) = do
  (fs, b) <- withLocalVars xs (c2aTopExp [] rt e)
  return (Function (FName (fst f ++ "." ++ snd f)) Nothing Nothing (buildParams xs) b : fs)

c2aFix :: FunName -> String -> [VarDef] -> ShapeType -> TopExp -> Context [Function]
c2aFix f r xs rt e = do
  (fs, b) <- withLocalVars ((r,rt):xs) (c2aTopExp [] RefType e)
  return (Function (FName (fst f ++ "." ++ snd f)) (Just r) Nothing (buildParams xs) b : fs)

c2aTopExp :: [Stmt] -> ShapeType -> TopExp -> Context ([Function], AsmBlock)
c2aTopExp xs (PType pt) (SimpleExp (Var x)         ) = return ([], AsmBlock xs (NodeReturn (BoxCon $ defaultPrimBox pt) [Right $ pv x]))
c2aTopExp xs (PType pt) (SimpleExp (Lit (IntLit i))) = do
  x <- newName "i"
  return ([], AsmBlock (xs ++ [x :<~: Constant i]) (NodeReturn (BoxCon $ defaultPrimBox pt) [Right $ pv x]))
c2aTopExp xs (PType pt) (SimpleExp (FunVal f ys)) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  case (snd fk) of
    ErrFun e -> do
      x <- newName "n"
      y <- newName "e"
      return ([], AsmBlock (xs ++ [x :<~: Constant e, y :<-: StoreNode (BoxCon (CName ".ErrorCode")) [pa x]]) (Error (rv y)))
    PrimOp (PType _) -> do
      ys' <- mapM c2aArgument ys
      let as = buildArgs (map snd ys')
      case as of
        [Right n] -> do
          x <- newName "y"
          return ([], AsmBlock (xs ++ concatMap fst ys' ++ [x :<~: RunPrimOp (OpName (snd f)) n Nothing]) (NodeReturn (BoxCon $ defaultPrimBox pt) [Right $ pv x]))
        [Right n, Right m] -> do
          x <- newName "y"
          return ([], AsmBlock (xs ++ concatMap fst ys' ++ [x :<~: RunPrimOp (OpName (snd f)) n (Just m)]) (NodeReturn (BoxCon $ defaultPrimBox pt) [Right $ pv x]))
        _ -> error ("todo IntK c2aTopExp" ++ show as)
    PrimFun _ -> do
      ys' <- mapM c2aArgument ys
      let as = buildArgs $ map snd ys'
      return ([], AsmBlock (xs ++ concatMap fst ys') (TailCall (Run_Fun (FName (fst f ++ "." ++ snd f)) as) []))
    RealFun _ | null ys -> return ([], AsmBlock xs (TailCall (Run_Fun (FName (fst f ++ "." ++snd f)) []) [])) -- could be an error throwing CAF
    _ -> error $ show fk
c2aTopExp xs RefType (SimpleExp (Var x)         ) = return ([], AsmBlock xs (TailCall (EvalRef (rv x)) [])                          )
c2aTopExp xs RefType (SimpleExp (Con c ys)) = do
  ys' <- mapM c2aArgument ys
  (t, as) <- buildConNodeArg c (map snd ys')
  return ([], AsmBlock (xs ++ concatMap fst ys') (NodeReturn t as))
c2aTopExp xs RefType (SimpleExp (FunVal f ys)) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  case (snd fk) of
    ErrFun e -> do
      x <- newName "n"
      y <- newName "e"
      return ([], AsmBlock (xs ++ [x :<~: Constant e, y :<-: StoreNode (BoxCon (CName ".ErrorCode")) [pa x]]) (Error (rv y)))
    SelFun c i -> do
      case ys of
        []  -> return ([], AsmBlock xs (NodeReturn (PSelTag (CName (fst c ++ "." ++ snd c)) i) []))
        [y] -> do
          (zs,ce,pcs) <- c2aCallingExp y
          return ([], AsmBlock (xs ++ zs) (TailCall ce (pcs ++ [Selecting (CName (fst c ++ "." ++ snd c)) i])))
        _   -> error "TODO over applying SelFun in c2aTopExp"
    _ -> do
      let na = length (fst fk)
      ys' <- mapM c2aArgument ys
      let as = buildArgs (map snd ys')
      case (snd fk) of
        RealFun _ -> do
          case compare (length as) na of
            LT -> return ([], AsmBlock (xs ++ concatMap fst ys') (NodeReturn (PapTag (FName (fst f ++ "." ++ snd f)) (na - length as)) as                     ))
            EQ -> return ([], AsmBlock (xs ++ concatMap fst ys') (TailCall (Run_Fun  (FName (fst f ++ "." ++ snd f)) as              ) []                     ))
            GT -> return ([], AsmBlock (xs ++ concatMap fst ys') (TailCall (Run_Fun  (FName (fst f ++ "." ++ snd f)) (take na as)    ) [Applying (drop na as)]))
        FixFun _ -> do
          case compare (length as) na of
            EQ -> return ([], AsmBlock (xs ++ concatMap fst ys') (TailCall (Run_Fix (FName (fst f ++ "." ++ snd f)) as) []))
            _ -> error "FixFun with wrong number of arguments"
        CmpFun -> case as of
          [Right n, Right m] -> do
            b <- newName "b"
            return ([], AsmBlock (xs ++ concatMap fst ys' ++ [b :<-?: RunCmpOp (OpName (snd f)) n m]) (BoolReturn b (ConTag (CName "GHCziBool.True")) (ConTag (CName "GHCziBool.False"))))
          _ -> error ("todo CmpFun c2aTopExp" ++ show as)
        x -> error ("c2aTopExp NodeRes" ++ show f ++ " " ++ show x)
c2aTopExp xs RefType (SimpleExp (Apply f ys)) = do
  (zs, c, cc) <- c2aCallingExp f
  ys' <- mapM c2aArgument ys
  return ([], AsmBlock (xs ++ zs ++ concatMap fst ys') (TailCall c (cc ++ [Applying (buildArgs (map snd ys'))])))
c2aTopExp xs RefType (SimpleExp (Selector d i y)) = do
  (ys, c, cc) <- c2aCallingExp y
  return ([], AsmBlock (xs ++ ys) (TailCall c (cc ++ [Selecting (CName (fst d++"."++snd d)) i])))
c2aTopExp xs rt (SLet (n,t@(PType _)) x e) = do
  ys <- c2aPrimExp n x
  withLocalVars [(n,t)] (c2aTopExp (xs ++ ys) rt e)
c2aTopExp xs rt (SLet (n,t) x e) = do
  ys <- c2aLazyRefExp n x
  withLocalVars [(n,t)] (c2aTopExp (xs ++ ys) rt e)
c2aTopExp xs rt (Let f as t x e) = do
  introFun f (map snd as) t x
  fs <- c2aFun (FunDef f as t x)
  (gs, e') <- c2aTopExp xs rt e
  return (fs ++ gs, e')
c2aTopExp xs rt (LetRec f r as t x e) = do
  introFix f (map snd as)  t
  fs <- c2aFix f r as t x
  (gs, e') <- c2aTopExp xs rt e
  return (fs ++ gs, e')
c2aTopExp xs rt (Case sr e t@(PType _) [DefAlt d, IntAlt i x]) = do
  (ys, v) <- c2aArgument e
  c <- newName "c"
  let (s,lv) = ([(sr, Right $ PrimVar $ fst v)], [(sr,t)])
  d' <- withLocalVars lv $ c2aTopExp [] rt d
  x' <- withLocalVars lv $ c2aTopExp [] rt x
  n <- newName "i"
  return (fst d' ++ fst x', AsmBlock (xs ++ ys ++ [n :<~: Constant i, c :<-?: RunCmpOp (OpName "zezezh") (PrimVar $ fst v) (PrimVar n)]) (IfThenElse c (substBlock s $ snd x') (substBlock s $ snd d')))
c2aTopExp xs rt (Case sr x t [ConAlt cn vs e]) = do
  (ys,c,cc) <- c2aCallingExp x
  (fs, AsmBlock zs z) <- withLocalVars ((sr,t) : vs) $ c2aTopExp [] rt e
  (nt, ns) <- buildConNode cn vs
  return (fs, AsmBlock (xs ++ ys ++ [(Left sr, Just (nt,ns,Nothing)) :<=: (c,cc)] ++ zs) z)
c2aTopExp xs rt (Case _ (FunVal f [a,b]) _ [ConAlt _ [] e, ConAlt _ [] t]) | f `elem` compareFuns = do
  a' <- c2aArgument a
  b' <- c2aArgument b
  c <- newName "c"
  e' <- c2aTopExp [] rt e
  t' <- c2aTopExp [] rt t
  return (fst e' ++ fst t', AsmBlock (xs ++ fst a' ++ fst b' ++ [c :<-?: RunCmpOp (OpName (snd f)) (PrimVar $ fst $ snd a') (PrimVar $ fst $ snd b')]) (IfThenElse c (snd t') (snd e')))
c2aTopExp xs rt (Case sr e t [DefAlt d]) = do
  (ys, c, cc) <- c2aCallingExp e
  (fs, AsmBlock zs z) <- withLocalVars [(sr,t)] $ c2aTopExp [] rt d
  return (fs, AsmBlock (xs ++ ys ++ [(Left sr, Nothing) :<=: (c,cc)] ++ zs) z)
c2aTopExp xs rt (Case sr e t ((DefAlt d) : as)) = do
  (ys, c, cc) <- c2aCallingExp e
  d' <- withLocalVars [(sr,t)] $ c2aTopExp [] rt d
  bs <- mapM (withLocalVars [(sr,t)] . c2aAlt rt) as
  return (fst d' ++ concatMap fst bs, AsmBlock (xs ++ ys) (CaseOf c cc (Left sr) (Just $ snd d') (map snd bs)))
c2aTopExp xs rt (Case sr e t as) = do
  (ys, c, cc) <- c2aCallingExp e
  bs <- mapM (withLocalVars [(sr,t)] . c2aAlt rt) as
  return (concatMap fst bs, AsmBlock (xs ++ ys) (CaseOf c cc (Left sr) Nothing (map snd bs)))
c2aTopExp _ rt x = error ("c2aTopExp " ++ show rt ++ " " ++ show x)

c2aAlt :: ShapeType -> Alternative -> Context ([Function], (CName, [Parameter], Maybe Int, AsmBlock))
c2aAlt rt (ConAlt c xs e) = do
  (fs,b) <- withLocalVars xs (c2aTopExp [] rt e)
  (ConTag d, ys) <- buildConNode c xs
  return (fs, (d, ys, Nothing, b))
c2aAlt _ a = error ("c2aAlt " ++ show a)

c2aPrimExp :: String -> SimpleExp -> Context [Stmt]
c2aPrimExp _ (Var _) = error "c2aStrictExp (Var x)"
c2aPrimExp n (Lit (IntLit i)) = return [n :<~: Constant i]
c2aPrimExp n (FunVal f xs) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  case (snd fk) of
    PrimFun pt -> do
      ys' <- mapM c2aArgument xs
      let as = buildArgs $ map snd ys'
      return (concatMap fst ys' ++ [(dummyResultRef, Just (BoxCon (defaultPrimBox pt), [pp n], Nothing)) :<=: (Run_Fun (FName (fst f ++ "." ++ snd f)) as, [])])
    PrimOp (PType _) -> do
      ys' <- mapM c2aArgument xs
      let as = buildArgs (map snd ys')
      case as of
        [Right a] -> do
          return (concatMap fst ys' ++ [n :<~: RunPrimOp (OpName (snd f)) a Nothing])
        [Right a, Right b] -> do
          return (concatMap fst ys' ++ [n :<~: RunPrimOp (OpName (snd f)) a (Just b)])
        _ -> error ("todo IntK c2aPrimExp" ++ show as)
    x -> error ("c2aPrimExp " ++ show f ++ " " ++ show x)
c2aPrimExp n x = error ("todo c2aPrimExp " ++ show n ++ "  " ++ show x)

c2aLazyRefExp :: String -> SimpleExp -> Context [Stmt]
c2aLazyRefExp _ (Var _) = error "c2aLazyRefExp (Var x)"
c2aLazyRefExp n (Con c xs) = do
  xs' <- mapM c2aArgument xs
  (t, as) <- buildConNodeArg c (map snd xs')
  return (concatMap fst xs' ++ [n :<-: StoreNode t as])
c2aLazyRefExp n (FunVal f xs) = do
  fk <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  let na = length (fst fk)
  ys' <- mapM c2aArgument xs
  let as = buildArgs (map snd ys')
  case (snd fk) of
    RealFun _ -> do
      case compare (length as) na of
        LT -> return (concatMap fst ys' ++ [n :<-: StoreNode (PapTag (FName (fst f ++ "." ++ snd f)) (na - length as)) as])
        EQ -> return (concatMap fst ys' ++ [n :<-: StoreNode (FunTag (FName (fst f ++ "." ++ snd f))) as])
    SelFun c i -> 
      case as of
        []  -> return (concatMap fst ys' ++ [n :<-: StoreNode (PSelTag (CName (fst c ++ "." ++ snd c)) i) []])
        [a] -> return (concatMap fst ys' ++ [n :<-: StoreNode (FSelTag (CName (fst c ++ "." ++ snd c)) i) [a]])
        _   -> error "TODO c2aLazyRefExp overapplied SelFun"
    x -> error ("c2aLazyRefExp " ++ show x ++ " " ++ show f)
c2aLazyRefExp n (Selector d i x) = do
  y' <- c2aArgument x
  let as = buildArgs [snd y']
  return (fst y' ++ [n :<-: StoreNode (FSelTag (CName (fst d++"."++snd d)) i) as])
c2aLazyRefExp n (Apply f xs) = do
  xs' <- mapM c2aArgument (f:xs)
  let as' = buildArgs (map snd xs')
  return (concatMap fst xs' ++ [n :<-: StoreNode (ApTag (length xs)) as'])

c2aArgument :: SimpleExp -> Context ([Stmt], (String, ArgKind))
c2aArgument (Var x) = do
  t <- gets (fromMaybe (error ("lookup Var " ++ show x)) . lookup x . (\(_,_,vs,_) -> vs))
  return ([], (x, type2Kind t))
c2aArgument (Lit (IntLit i)) = do
  x <- newName "i"
  return ([x :<~: Constant i], (x, PrimArg))
c2aArgument (Lit (StringLit s)) = {- c2aStringLit s -} do
  x <- newName "i"
  return ([x :<-: StringConstant s], (x, RefArg))
c2aArgument (Con c xs) = do
  xs' <- mapM c2aArgument xs
  (t, as) <- buildConNodeArg c (map snd xs')
  x <- newName "c"
  return (concatMap fst xs' ++ [x :<-: StoreNode t as], (x, RefArg))
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
          return (concatMap fst ys' ++ [x :<~: RunPrimOp (OpName (snd f)) n Nothing], (x, PrimArg))
        [Right n, Right m] -> do
          x <- newName "y"
          return (concatMap fst ys' ++ [x :<~: RunPrimOp (OpName (snd f)) n (Just m)], (x, PrimArg))
        _ -> error "todo IntK c2aArgument"
    PrimFun pt -> do
      x <- newName "z"
      let as = buildArgs $ map snd ys'
      return (concatMap fst ys' ++ [(dummyResultRef, Just (BoxCon (defaultPrimBox pt), [pp x], Nothing)) :<=: (Run_Fun (FName (fst f ++ "." ++ snd f)) as, [])], (x,PrimArg))
    RealFun _ -> do
      let as = buildArgs (map snd ys')
      case compare (length as) na of
        LT -> do
          x <- newName "p"
          return (concatMap fst ys' ++ [x :<-: StoreNode (PapTag (FName (fst f ++ "." ++ snd f)) (na - length as)) as], (x, RefArg))
        EQ -> do
          x <- newName "f"
          return (concatMap fst ys' ++ [x :<-: StoreNode (FunTag (FName (fst f ++ "." ++ snd f))) as], (x, RefArg))
        GT -> do
          x <- newName "f"
          y <- newName "oa"
          return (concatMap fst ys' ++ [x :<-: StoreNode (FunTag (FName (fst f ++ "." ++ snd f))) (take na as), y :<-: StoreNode (ApTag (length as - na)) (ra x : drop na as)], (y, RefArg))
    IdFun -> do
      x <- newName "i"
      let as = buildArgs (map snd ys')
      case as of
        [] -> return ([x :<-: StoreNode PIdTag []], (x, RefArg))
        _  -> error "TODO c2aArgument applied IdFun"
    SelFun c i -> do
      x <- newName "s"
      let as = buildArgs (map snd ys')
      case as of
        []  -> return (concatMap fst ys' ++ [x :<-: StoreNode (PSelTag (CName (fst c ++ "." ++ snd c)) i) []], (x, RefArg))
        [a] -> return (concatMap fst ys' ++ [x :<-: StoreNode (FSelTag (CName (fst c ++ "." ++ snd c)) i) [a]], (x, RefArg))
        _   -> error "TODO c2aArgument overapplied SelFun"
    _ -> error ("c2aArgument FunVal " ++ show f ++ " " ++ show fk)
c2aArgument (Selector d i x) = do
  y' <- c2aArgument x
  let as = buildArgs [snd y']
  n <- newName "s"
  return (fst y' ++ [n :<-: StoreNode (FSelTag (CName (fst d++"."++snd d)) i) as], (n,RefArg))
c2aArgument (Apply f xs) = do
  xs' <- mapM c2aArgument (f:xs)
  let as = buildArgs (map snd xs')
  x <- newName "a"
  return (concatMap fst xs' ++ [x :<-: StoreNode (ApTag (length xs)) as], (x, RefArg))

c2aCallingExp :: SimpleExp -> Context ([Stmt], CallExp, [PostCall])
c2aCallingExp (Var x) = return ([], EvalRef (rv x), [])
c2aCallingExp (FunVal f xs) = do
  ft <- gets (fromMaybe (error ("lookup Fun " ++ show f)) . lookup f . (\(fs,_,_,_) -> fs))
  let na = length (fst ft)
  ys' <- mapM c2aArgument xs
  let as = buildArgs (map snd ys')
  case (snd ft) of
    RealFun _ -> do
      case compare (length as) na of
        LT -> error "strict arg pap"
        EQ -> return (concatMap fst ys', Run_Fun (FName (fst f ++ "." ++ snd f)) as          , [])
        GT -> return (concatMap fst ys', Run_Fun (FName (fst f ++ "." ++ snd f)) (take na as), [Applying (drop na as)])
    FixFun _ -> do
      case compare (length as) na of
        EQ -> return (concatMap fst ys', Run_Fix (FName (fst f ++ "." ++ snd f)) as, [])
        _  -> error "FixFun with wrong number of arguments"
    _ -> error ("c2aCallingExp " ++ show f ++ " " ++ show ft)
c2aCallingExp (Apply f xs) = do
  (ys, c, cc) <- c2aCallingExp f
  xs' <- mapM c2aArgument xs
  return (ys ++ concatMap fst xs', c, cc ++ [Applying (buildArgs (map snd xs'))])
c2aCallingExp (Selector d i x) = do
  (ys, c, cc) <- c2aCallingExp x
  return (ys, c, cc ++ [Selecting (CName (fst d++"."++snd d)) i])

{- -}
c2aStringLit :: String -> Context ([Stmt], (String, ArgKind))
c2aStringLit "" = do
  n <- newName "n"
  return ([n :<-: StoreNode (ConTag (CName "GHCziTypes.ZMZN")) []], (n, RefArg))
c2aStringLit (x:xs) = do
  (is, (ys, _)) <- c2aStringLit xs
  i <- newName "i"
  c <- newName "c"
  y <- newName "y"
  return (is ++ [i :<~: Constant (fromEnum x), c :<-: StoreNode (BoxCon (CName "GHCziTypes.Czh")) [pa i], y :<-: StoreNode (ConTag (CName "GHCziTypes.ZC")) [ra c, ra ys]], (y, RefArg))
{- -}

buildConNodeArg :: ConName -> [(String,ArgKind)] -> Context (AsmTag, [Argument])
buildConNodeArg c xs
  | c `elem` boxConstrs = do
    return (BoxCon (CName (fst c++"."++snd c)), buildArgs xs)
  | isUnboxTupleCon c   = return (RawTuple, buildArgs xs)
  | otherwise           = do
    n <- gets (fromMaybe (error ("lookup Con " ++ show c)) . lookup c . (\(_,cs,_,_) -> cs))
    if (n == length xs)
      then return (ConTag (CName (fst c++"."++snd c)), buildArgs xs)
      else return (DecTag (CName (fst c++"."++snd c)) (n - length xs), buildArgs xs)

buildConNode :: ConName -> [VarDef] -> Context (AsmTag, [Parameter])
buildConNode c xs = do
  n <- gets (fromMaybe (error ("lookup Con " ++ show c)) . lookup c . (\(_,cs,_,_) -> cs))
  case c of
     _ | c `elem` boxConstrs -> return (BoxCon (CName (fst c++"."++snd c)), buildParams xs)
       | isUnboxTupleCon c   -> return (RawTuple                          , buildParams xs)
       | otherwise           -> return (ConTag (CName (fst c++"."++snd c)), buildParams xs)

type2Kind :: ShapeType -> ArgKind
type2Kind (PType _) = PrimArg
type2Kind _         = RefArg

buildArgs :: [(String, ArgKind)] -> [Argument]
buildArgs = map (\(x,k) -> if k == RefArg then ra x else pa x)

splitArgs :: [(String, ArgKind)] -> ([RefVal], [PrimVal])
splitArgs xs = (map (rv . fst) as, map (pv . fst) bs) where
  (as, bs) = partition ((== RefArg) . snd) xs

buildParams :: [VarDef] -> [Parameter]
buildParams = map (\(x,t) -> if type2Kind t == RefArg then rp x else pp x)

splitParams :: [VarDef] -> ([RefVar], [PrimVar])
splitParams xs = (map fst as, map fst bs) where
  (as, bs) = partition ((== RefArg) . type2Kind . snd) xs
