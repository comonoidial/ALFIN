module Alfin.ReduceArity (reduceArity) where

import Control.Monad.State
import Data.List
import Data.Traversable (traverse)

import Alfin.AsmLang

maxArity :: Int
maxArity = 7

type ReduceArityState = State ReduceArity

data ReduceArity = ReduceArity {uniqueNameCounter :: Int, longConstructors :: [Constructor], longFunctions :: [Function],
    addedDecFunctions :: [(CName, [Function])], addedPapFunctions :: [(FName, [Function])], addedPSelFunctions :: [((CName,Int), Function)],
    origDataTypes :: [DataType], origFunctions :: [Function]}

-- Generate a datatype with all possible combinations of RefArg and PrimArg
generateTupleConstructors :: Int -> DataType
generateTupleConstructors n = DataType name (gentups n (CName name, [])) where
    name = "Tuple"++ show n
    gentups :: Int -> (CName, [ArgKind]) -> [(CName, [ArgKind])]
    gentups 0 base = [base]
    gentups i (CName basename, baseargs) = gentups (i-1) (CName (basename++"r"), baseargs++[RefArg]) ++ gentups (i-1) (CName (basename++"p"), baseargs++[PrimArg])

-- Gives the right AsmTag (e.g. Tuple constructor) of the given Parameter or Argument list
-- This function takes the difference between RefVar and PrimVar into account
calctag :: [Either r p] -> AsmTag
calctag ps = ConTag $ CName ("Tuple" ++ show (length ps) ++ map (either (const 'r') (const 'p')) ps)

para2arg :: [Parameter] -> [Argument]
para2arg = map (either (Left . RefVar) (Right . PrimVar))

argumentName :: Argument -> String  -- only works for variables
argumentName (Left (RefVar a)) = a
argumentName (Right (PrimVar a)) = a

parameterName :: Parameter -> String
parameterName = either id id

-- Gives the amount of arguments in the main node of an x-arity node
argsMainNode :: Int -> Int
argsMainNode x
    | x <= maxArity                          = x
    | (x-maxArity) `mod` (maxArity - 1) == 0 = maxArity - 1
    | otherwise                              = (x-maxArity) `mod` (maxArity - 1)

-- Gives the amount of extra nodes needed to store a big node
neededDepth :: Int -> Int
neededDepth i | i <= maxArity                         = 0
              | ((i-maxArity) `mod` (maxArity-1)) > 0 = (i-maxArity) `div` (maxArity-1) + 1
              | otherwise                             = (i-maxArity) `div` (maxArity-1)

uniqueName :: String -> ReduceArityState String
uniqueName s = do
    unc <- gets uniqueNameCounter
    modify (\st -> st {uniqueNameCounter = unc + 1})
    return $ show unc ++ "**" ++ s

origConsArgs :: CName -> [DataType] -> [ArgKind]
origConsArgs name [] = error $ "Constructor '" ++ show name ++ "' does not exist in the original program"
origConsArgs name (DataType _ constructors : ts) = case lookup name constructors of
    Just b -> b
    Nothing -> origConsArgs name ts

getDecStmts :: CName -> [Argument] -> ReduceArityState ([Stmt], AsmTag, [Argument])
getDecStmts c args = do
    st <- get
    case lookup c (addedDecFunctions st) of
        Just cfuns -> buildDecStmts cfuns args -- Functions were already created.
        Nothing -> do -- Functions need to be created
            prefix <- uniqueName ""
            let oArgs = origConsArgs c (origDataTypes st)
            let funs = createPartialDecFuns prefix (neededDepth $ length oArgs) (c,oArgs)
            put st {addedDecFunctions = (c,funs) : addedDecFunctions st}
            buildDecStmts funs args

buildDecStmts :: [Function] -> [Argument] -> ReduceArityState ([Stmt], AsmTag, [Argument])
buildDecStmts (c:cs) args
    | length args > maxArity = do
        let (poppedArgs, otherArgs) = splitAt maxArity args
        name <- uniqueName $ concatMap argumentName poppedArgs
        (x,y,z) <- buildDecStmts cs (Left (RefVar name) : otherArgs)
        return $ (name :<-: (StoreNode (calctag poppedArgs) poppedArgs):x, y, z)
    | otherwise = return ([], PapTag (fName c) (length (params c) - length args), args)

origFun :: FName -> [Function] -> Function
origFun name fs = case find (\f -> fName f == name) fs of
    Nothing -> error $ "Function '" ++ show name ++ "' does not exist in the original program"
    Just f  -> f

getPapStmts :: FName -> [Argument] -> ReduceArityState ([Stmt], AsmTag, [Argument])
getPapStmts f args = do
    st <- get
    let oFun = origFun f (origFunctions st)
    let realfun = Function {fName=f, params=take ((+)1 $ argsMainNode $ length $ params oFun) $ repeat (Left "a"), resultRef=Nothing, fetchHint=Nothing, body=Block [] $ Error $ RefVar "5" } -- some dummy function
    case lookup f (addedPapFunctions st) of
        Just pfuns -> buildPapStmts (pfuns++[realfun]) args -- Functions were already created.
        Nothing -> do -- Functions need to be created
            prefix <- uniqueName ""
            let funs = createPartialPapFuns prefix (neededDepth $ length $ params oFun) oFun
            put st {addedPapFunctions = (f,funs) : addedPapFunctions st}
            buildPapStmts (funs++[realfun]) args

buildPapStmts :: [Function] -> [Argument] -> ReduceArityState ([Stmt], AsmTag, [Argument])
buildPapStmts (p:ps) args
    | length args >= maxArity = do
        let (poppedArgs, otherArgs) = splitAt maxArity args
        name <- uniqueName $ concatMap argumentName poppedArgs
        (a,b,c) <- buildPapStmts ps (Left (RefVar name) : otherArgs)
        return $ (name :<-: (StoreNode (calctag poppedArgs) poppedArgs) : a, b, c)
    | otherwise = return ([], PapTag (fName p) (length (params p) - length args), args)

-- Creates functions that are used to construct partially applied constructors
-- Takes a unique prefix for the group of functions
-- Takes an index for the first function
-- Takes a datatype constructor
createPartialDecFuns :: String -> Int -> Constructor -> [Function]
createPartialDecFuns _ 0 _ = []
createPartialDecFuns prefix index ((CName cname), args) = Function name Nothing Nothing params body' : createPartialDecFuns prefix (index-1) ((CName cname), otherArgs) where
    (poppedArgs, otherArgs) = splitAt maxArity args
    params = argkinds2parameters poppedArgs
    name = FName (prefix ++ cname ++ show index)
    ptag = case index of
            1 -> PapTag (FName cname) (argsMainNode $ length args)
            _ -> PapTag (FName (prefix ++ cname ++ show (index-1))) (maxArity-1)
    body' = Block ["z" :<-: StoreNode (calctag params) (para2arg params)] $ NodeReturn ptag [Left $ RefVar "z"]

-- Small helper function that creates simple names for the arguments of a constructor.
argkinds2parameters :: [ArgKind] -> [Parameter]
argkinds2parameters as = zipWith (\k -> case k of {RefArg -> Left; PrimArg -> Right}) as $ map (('a':) . show) [0..]

-- Creates functions that are used to construct partially applied functions
-- Takes a unique prefix for the group of functions
-- Takes an index for the first function
-- Takes a datatype constructor
createPartialPapFuns :: String -> Int -> Function -> [Function]
createPartialPapFuns _ 0 _ = []
createPartialPapFuns prefix index f = Function name Nothing Nothing poppedArgs body' : createPartialPapFuns prefix (index-1) f where -- FIXME this recursive call can't be correct with passing on f unmodified
    poppedArgs = take maxArity $ params f
    name = FName (prefix ++ show (fName f) ++ "*" ++ show index)
    ptag = case index of
            1 -> PapTag (fName f) (argsMainNode $ length $ params f)
            _ -> PapTag (FName $ prefix ++ show (fName f) ++ "*" ++ show (index-1)) (maxArity-1)
    body' = Block ["z" :<-: StoreNode (calctag poppedArgs) (para2arg poppedArgs)] $ NodeReturn ptag [Left $ RefVar "z"]

-- Returns (and creates if needed) a new function that can replace a partially applied Sel-node.
getPSelFun :: (CName, Int) -> ReduceArityState FName
getPSelFun key@((CName name), index) = do
    pselfuns <- gets addedPSelFunctions
    case lookup key pselfuns of
        Just b -> return $ fName b -- Function was already created.
        Nothing -> do -- Function has to be created.
            funName <- fmap FName $ uniqueName $ "**" ++ name ++ "**" ++ show index -- The name for the new function
            postcalls <- reducePostCall $ Selecting (CName name) index
            let term = TailCall (EvalRef (RefVar "obj")) postcalls -- the terminator statement of the new function
            let newfun = Function funName Nothing Nothing [Left "obj"] $ Block [] term -- the function to create
            modify (\st -> st {addedPSelFunctions=(key, newfun) : pselfuns}) -- adding new pselfun to state
            return funName -- return the name of the newly created pselfun

-- Takes the total number of arguments
-- Takes (zero based) index of the argument to select
-- Gives a list of consequent indexes when the arity is limited to maxArity
selectIndices :: Int -> Int -> [Int]
selectIndices x i
    | x <= maxArity          = [i]                         -- Base case: constructor fits in a single node
    | x-i-1 < argsMainNode x = [maxArity-1-(x-i-1)]        -- Base case: index is in current node
    | otherwise = 0 : selectIndices (x - argsMainNode x) i -- Induction step: Do a `Selecting 0`. The new situation equals a constructor with argsMainNode less arguments.

selConstructorNames :: CName -> [ArgKind] -> [CName]
selConstructorNames name origcons = (name : cnameStack (drop (argsMainNode $ length origcons) origcons)) where
  -- Assumes `length of first argument` `mod` maxArity == 0
  -- Generates a list of Tuple constructors given a list of ArgKinds
    cnameStack [] = []
    cnameStack as = c : cnameStack (RefArg : drop maxArity as) where
      (ConTag c) = calctag $ take maxArity $ argkinds2parameters as


reduceArity :: AsmModule -> AsmModule
reduceArity (AsmModule name datatypes functions) = AsmModule name datatypes'' functions'' where
    initRA = ReduceArity {uniqueNameCounter=10, longConstructors=[], longFunctions = filter (\f -> length (params f) > maxArity) functions,
        addedDecFunctions=[], addedPapFunctions=[], addedPSelFunctions=[], origDataTypes=datatypes, origFunctions=functions}
    (datatypes', s') = runState (mapM reduceDataType datatypes) initRA
    (functions', s'') = runState (mapM reduceFunction functions) s'
    datatypes'' = generateTupleConstructors maxArity : datatypes'
    functions'' = functions' ++ concatMap snd (addedDecFunctions s'') ++ concatMap snd (addedPapFunctions s'') ++ map snd (addedPSelFunctions s'')

-- Reduces the amount of parameters of a datatype
reduceDataType :: DataType -> ReduceArityState DataType
reduceDataType (DataType dname cs) = fmap (DataType dname) $ mapM reduceConstructor cs where
    reduceConstructor (name, args)
        | length args <= maxArity = return (name,args)
        | otherwise = do
            modify (\st -> st {longConstructors = (name,args) : longConstructors st}) -- Add this constructor to the list of too long constructors
            reduceConstructor (name, RefArg : drop (length args - argsMainNode (length args)) args)

-- Reduces a node. This function might generate additional pre statements to handle a maximum arity.
reduceNode :: AsmTag -> [Argument] -> ReduceArityState ([Stmt], AsmTag, [Argument])
reduceNode tag args = do
    isLongCons <- gets (\st name -> name `elem` map fst (longConstructors st))
    let (poppedArgs, otherArgs) = splitAt maxArity args
    let concattetName = concatMap argumentName poppedArgs
    case tag of
        (ConTag _) | length args > maxArity -> do
            name <- uniqueName concattetName
            (a,b,c) <- reduceNode tag (Left (RefVar name) : otherArgs)
            return ((name :<-: StoreNode (calctag poppedArgs) poppedArgs):a, b, c)
        (DecTag cname missing) | (length args + missing) > maxArity -> 
            getDecStmts cname args
        (FunTag _) | length args > maxArity -> do
            name <- uniqueName concattetName
            (a,b,c) <- reduceNode tag (Left (RefVar name) : otherArgs)
            return ((name :<-: StoreNode (calctag poppedArgs) poppedArgs):a,b,c)
        (PapTag fname missing) | (length args + missing) > maxArity -> 
            getPapStmts fname args
        (ApTag i) | length args > maxArity -> do
            name <- uniqueName concattetName
            (a,b,c) <- reduceNode (ApTag (i-maxArity+1)) (Left (RefVar name) : otherArgs)
            return ((name:<-: StoreNode (ApTag $ maxArity -1) poppedArgs):a,b,c)
        (FSelTag cname i) | isLongCons cname -> do
            origCons <- gets (origConsArgs cname . origDataTypes)
            let neededSelects = selectIndices (length origCons) i
            storeIn <- replicateM (length neededSelects - 1) $ uniqueName ""
            let storeIn' = map (Left . RefVar) storeIn
            let readFrom = (head args) : storeIn'
            let newFSelStmt dest cname sel from = dest :<-: StoreNode (FSelTag cname sel) from
            return (zipWith4 newFSelStmt storeIn (selConstructorNames cname origCons) neededSelects (map (: []) readFrom), FSelTag cname (last neededSelects), [last storeIn'])
        (PSelTag cname i) | isLongCons cname -> do
            pselfun <- getPSelFun (cname,i)
            return ([], (PapTag pselfun 1), [])
        _ -> return ([], tag, args)

-- Reduces the amount of parameters of a function and calls `reduceBlock` on its contents
reduceFunction :: Function -> ReduceArityState Function
reduceFunction f
    | length (params f) <= maxArity = do
        newbody <- reduceBlock $ body f
        return $ f {body = newbody}
    | otherwise = do
        let (poppedargs, otherargs) = splitAt maxArity $ params f
        let (Block stmts terminator) = body f
        newName <- uniqueName $ concatMap parameterName poppedargs
        let newstmt = (dummyResultRef, Just (calctag poppedargs, poppedargs, Nothing)) :<=: (LoadRef $ RefVar newName, [])
        reduceFunction $ f {params = Left newName : otherargs, body = Block (newstmt : stmts) terminator}

-- Transforms the code in a block
reduceBlock :: Block -> ReduceArityState Block
reduceBlock (Block stmts term) = do
    newstmts <- liftM concat $ mapM reduceStatement stmts
    (stmts', term') <- reduceTerminator term
    return $ Block (newstmts++stmts') term'

-- Reduce a terminator
reduceTerminator :: TermStmt -> ReduceArityState ([Stmt], TermStmt)
reduceTerminator (NodeReturn asmtag args) = do -- Return a fully applied constructor
    (preStmts, tag, args') <- reduceNode asmtag args
    return (preStmts, NodeReturn tag args')
reduceTerminator (CaseOf (Run_Fun fname args) postcalls resref mblk alternatives) -- Case statement
    | length args > maxArity = do
        let (poppedargs, otherargs) = splitAt maxArity args
        newName <- uniqueName $ concatMap argumentName poppedargs
        let nTerm = CaseOf (Run_Fun fname ((Left $ RefVar newName):otherargs)) postcalls resref mblk alternatives
        let nStmt = newName :<-: StoreNode (calctag poppedargs) poppedargs
        (recStmts, recTerm) <- reduceTerminator nTerm
        return $ (nStmt : recStmts, recTerm)
reduceTerminator (CaseOf callexp postcalls resref mblk alternatives) = do
    mblk' <- traverse reduceBlock mblk
    alternatives' <- mapM reduceAlternative alternatives
    pcalls' <- liftM concat $ mapM reducePostCall postcalls
    return ([], CaseOf callexp pcalls' resref mblk' alternatives')
reduceTerminator (TailCall (Run_Fun fname args) postcalls) = do -- Jump statement fed with a function and arguments, This situation is very similar to the store of a Fun-Node
    (preStmts, _, args') <- reduceNode (FunTag fname) args
    pcalls' <- liftM concat $ mapM reducePostCall postcalls
    return (preStmts, TailCall (Run_Fun fname args') pcalls')
reduceTerminator (TailCall callable postcalls) = do -- Jump statement with other callable: just reduce PostCalls
    pcalls' <- liftM concat $ mapM reducePostCall postcalls
    return ([], TailCall callable pcalls')
reduceTerminator (IfThenElse boolvar b1 b2) = do -- Handling the IfThenElse terminator: just a recursive call on its Blocks
    b1' <- reduceBlock b1
    b2' <- reduceBlock b2
    return ([], IfThenElse boolvar b1' b2')
reduceTerminator term = return ([],term) -- Ignore other terminators

reduceAlternative :: CaseAlt -> ReduceArityState CaseAlt
reduceAlternative (name, params, fetchnext, Block bstmts bterm)
    | length params <= maxArity = do
        blk' <- reduceBlock $ Block bstmts bterm
        return (name, params, fetchnext, blk')
    | otherwise = do
        let poppedArgs = take maxArity params
        newName <- uniqueName $ concatMap parameterName poppedArgs
        let newParams = Left newName : drop maxArity params
        let newBlk = Block (((dummyResultRef, Just (calctag poppedArgs, poppedArgs, Nothing)) :<=: (LoadRef (RefVar newName), [])):bstmts) bterm
        reduceAlternative (name, newParams , fetchnext, newBlk)

-- Transform Statements
reduceStatement :: Stmt -> ReduceArityState [Stmt]
reduceStatement (refvar :<-: StoreNode asmtag params) = do
    (a,b,c) <- reduceNode asmtag params
    return $ a ++ [refvar :<-: StoreNode b c]
reduceStatement ((callresref, Just (origtag@(ConTag _), params, fetchnext)) :<=: (n, postcalls))
    | length params > maxArity = do
        let (poppedArgs, otherArgs) = splitAt maxArity params
        pcalls <- fmap concat $ mapM reducePostCall postcalls
        newName <- uniqueName $ concatMap parameterName poppedArgs
        rs <- reduceStatement ((callresref, Just (origtag, Left newName : otherArgs, fetchnext)) :<=: (n,pcalls))
        return $ rs ++ [(dummyResultRef, Just (calctag poppedArgs, poppedArgs, Nothing)) :<=: (LoadRef $ RefVar newName, [])]
reduceStatement ((callresref, result) :<=: (Run_Fun fname fargs, postcalls)) = do -- Reduces the arity when a F-node is stored
    (a,b,c) <- reduceNode (FunTag fname) fargs
    pcalls <- liftM concat $ mapM reducePostCall postcalls
    return $ a ++ [(callresref, result) :<=: (Run_Fun fname c, pcalls)]
reduceStatement ((a, b) :<=: (c, postcalls)) = do --Ignore other call statements: just reduce the PostCalls
    pcalls <- liftM concat $ mapM reducePostCall postcalls
    return [(a,b) :<=: (c,pcalls)]
reduceStatement s            = return [s] -- Ignore other statements

-- Reduce PostCalls
reducePostCall :: PostCall -> ReduceArityState [PostCall]
reducePostCall p@(Selecting name i) = do -- Reducing the Selecting PostCall
    origcons <- gets (origConsArgs name . origDataTypes)
    let numorigcons = length origcons
    if numorigcons <= maxArity then return [p]
        else return $ zipWith Selecting (selConstructorNames name origcons) (selectIndices numorigcons i)
reducePostCall p = return [p] -- Ignore all other PostCalls
