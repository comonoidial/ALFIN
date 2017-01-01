module RunTest where

import qualified Data.ByteString.Lazy.Char8 as L
import Control.Monad.State.Strict
import Data.List (find, isSuffixOf)
import Data.IntMap (fromList)
import Data.Maybe
import Debug.Trace (trace)
import ExtCore.Parser (parseModule)
import ExtCore.Pretty (ppModule)
import Control.Lens ((.~))

import Alfin.CoreConvert (convertMod, cleanMod)
import Alfin.CoreLowering (lowerMod)
import Alfin.CoreToAsm (c2aMod)
import Alfin.ReduceArity (reduceArity)
import Alfin.OptimizeAsm (optimMod, preOptimMod)
import Alfin.Assemble
import Simulate.ProcDefs
import Simulate.CleanEval
import Simulate.DetailEval
import Simulate.DEvalTypes (_heap, _ext, HeapNode(..), emptyNBody, elemAt, ccLineWidth, CodeMem)
import TestCases

-- shows simple core output
testCore :: TestCase -> IO ()
testCore (m,_) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ show $ cleanMod $ convertMod m

-- shows ugly intermediate of core to assembly process
testLower :: TestCase -> IO ()
testLower (m,_) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ show $ lowerMod $ cleanMod $ convertMod m

-- shows a testcase converted to pilgrim assembly
testAsm :: TestCase -> IO ()
testAsm (m,(f,_)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ show $ preOptimMod f $ c2aMod $ lowerMod $ cleanMod $ convertMod m

testReduceArity :: TestCase -> IO ()
testReduceArity (m,(f,_)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ show $ reduceArity $ preOptimMod f $ c2aMod $ lowerMod $ cleanMod $ convertMod m
 
-- shows result of lowlevel assembly optimizations and instruction preparations
testOptAsm :: TestCase -> IO ()
testOptAsm (m,(f,_)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ show $ optimMod $ c2aMod $ lowerMod $ cleanMod $ convertMod m

testInstrRA :: TestCase -> IO ()
testInstrRA (m,(f,_)) = do
  xs <- L.readFile m
  putStrLn f
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ concatMap ((++"\n") . show) $ snd $ asmMod $ optimMod $ reduceArity $ preOptimMod f $ c2aMod $ lowerMod $ cleanMod $ convertMod m

-- generates instruction on datatype level
testInstr :: TestCase -> IO ()
testInstr (m,(f,_)) = do
  xs <- L.readFile m
  putStrLn f
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> putStrLn $ concatMap ((++"\n") . show) $ snd $ asmMod $ optimMod $ c2aMod $ lowerMod $ cleanMod $ convertMod m

buildCodeMem :: [Instruction] -> CodeMem
buildCodeMem = fromList . zip [0..] . (++ replicate (fromIntegral ccLineWidth) (Nop (KeepRQ,popNone)))

-- runs a test in the simulator
runSim :: TestCase -> IO ()
runSim (m,(f,as)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> do
      putStr f
      let (fs, is) = asmMod $ optimMod $ reduceArity $ preOptimMod f $ c2aMod $ lowerMod $ cleanMod $ convertMod m
      let ftag = NodeTag Dynamic (toEnum $ length as) (bodyKinds_ $ map Left as) (uncurry Fun (lookupFun f fs) SkipUpd)
      let bodyFromList = foldr ($) emptyNBody . zipWith (\i -> (elemAt i .~)) [(A)..]
      let fnode = HNode ftag $ bodyFromList (map (RVal . CVRef . PrimBox ("Int", 0) . fromIntegral) as)
      startS <- initState (buildCodeMem is) [fnode]
      putStr ("   program size: " ++ show (length is) ++ " instructions")
      (tn, gs) <- runProc startS
      putStrLn ("result: " ++ tn)
      putStrLn (show (_heap gs) ++ " " ++ show (_ext gs))
      putStrLn ""

-- runs a test in the simulator
runSimNoRA :: TestCase -> IO ()
runSimNoRA (m,(f,as)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> do
      putStr f
      let (fs, is) = asmMod $ optimMod $ c2aMod $ lowerMod $ cleanMod $ convertMod m
      let ftag = NodeTag Dynamic (toEnum $ length as) (bodyKinds_ $ map Left as) (uncurry Fun (lookupFun f fs) SkipUpd)
      let bodyFromList = foldr ($) emptyNBody . zipWith (\i -> (elemAt i .~)) [(A)..]
      let fnode = HNode ftag $ bodyFromList (map (RVal . CVRef . PrimBox ("Int", 0) . fromIntegral) as)
      startS <- initState (buildCodeMem is) [fnode]
      putStr ("   program size: " ++ show (length is) ++ " instructions")
      (tn, gs) <- runProc startS
      putStrLn ("result: " ++ tn)
      putStrLn (show (_heap gs) ++ " " ++ show (_ext gs))
      putStrLn ""

lookupFun :: String -> FunTable -> (FunAddr, Maybe NodeElem)
lookupFun f fs = snd $ fromJust $ find (\(q,_) -> ('.':f) `isSuffixOf` show q) fs

-- runs a test in the simple simulator
runSSim :: TestCase -> IO ()
runSSim (m,(f,as)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> do
      putStr f
      let (fs, is) = asmMod $ optimMod $ reduceArity $ preOptimMod f $ c2aMod $ lowerMod $ cleanMod $ convertMod m
      let ftag = NodeTag Dynamic (toEnum $ length as) (bodyKinds_ $ map Left as) (uncurry Fun (lookupFun f fs) SkipUpd)
      let fnode = Node ftag (map (RVal . CVRef . PrimBox ("Int", 0) . fromIntegral) as)
      startS <- initStateS (buildCodeMemS is) [fnode]
      putStr ("   program size: " ++ show (length is) ++ " instructions")
      (tn, gs) <- runProcS startS
      putStrLn ("result: " ++ tn)
      putStrLn (show $ heapS gs)
      putStrLn ""

-- runs a test in the simple simulator
runSSimNoRA :: TestCase -> IO ()
runSSimNoRA (m,(f,as)) = do
  xs <- L.readFile m
  let p = parseModule "Test" xs
  case p of
    Left e -> putStrLn $ show e
    Right m -> do
      putStr f
      let (fs, is) = asmMod $ optimMod $ c2aMod $ lowerMod $ cleanMod $ convertMod m
      let ftag = NodeTag Dynamic (toEnum $ length as) (bodyKinds_ $ map Left as) (uncurry Fun (lookupFun f fs) SkipUpd)
      let fnode = Node ftag (map (RVal . CVRef . PrimBox ("Int", 0) . fromIntegral) as)
      startS <- initStateS (buildCodeMemS is) [fnode]
      putStr ("   program size: " ++ show (length is) ++ " instructions")
      (tn, gs) <- runProcS startS
      putStrLn ("result: " ++ tn)
      putStrLn (show $ heapS gs)
      putStrLn ""

