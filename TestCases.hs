module TestCases where

import System.FilePath (pathSeparator)

type TestCase = (FilePath, (String, [Int]))  -- path to external core file, function to call, arguments of function assumed to be all Ints

exampleTest :: TestCase
exampleTest = ("." ++ pathSeparator : "testcode" ++ pathSeparator : "Example.hcr", ("sumNOddSquares", [11]))

crazySelect :: TestCase
crazySelect = ("." ++ pathSeparator : "testcode" ++ pathSeparator : "Selectors.hcr", ("testSel", [7]))

selectBug :: TestCase
selectBug = ("." ++ pathSeparator : "testcode" ++ pathSeparator : "Selectors2.hcr", ("testSel", [7]))



-- -- -- ported Reduceron benchmarks for testing and comparison purposes -- -- --

rbm,rbmz :: String -> [Int] -> TestCase
rbm  f xs = ("." ++ pathSeparator : "testcode" ++ pathSeparator : f ++ ".hcr", ("test" ++ f, xs))
rbmz f xs = ("." ++ pathSeparator : "testcode" ++ pathSeparator : f ++ ".hcr", ("test" ++ f ++ "z", xs))

-- 'fast' testcases runnable in ghci
rbmFAll = [rbmFFib,rbmFQueens,rbmFOrdList,rbmFPermSort,rbmFBraun,rbmFQueens2,rbmFParts,rbmFMSS,rbmFTaut,rbmFClausify,rbmFWhile]

rbmFFib         = rbm "Fib"      [19]
rbmFQueens      = rbm "Queens"   [6]
rbmFOrdList     = rbm "OrdList"  [5]
rbmFPermSort    = rbm "PermSort" [6]
rbmFBraun       = rbm "Braun"    [2, 255]
rbmFQueens2     = rbm "Queens2"  [6]
rbmFParts       = rbm "Parts"    [16]
rbmFMSS         = rbm "MSS"      [8,10,1]
rbmFWhile       = rbm "While"    [35]
rbmFTaut        = rbm "Taut"     [7]
rbmFClausify    = rbm "Clausify" [2,0]

-- slow unless compiled
rbmMFib         = rbm "Fib"      [27]
rbmMQueens      = rbm "Queens"   [9]
rbmMOrdList     = rbm "OrdList"  [9]
rbmMPermSort    = rbm "PermSort" [8]
rbmMBraun       = rbm "Braun"    [60, 255]
rbmMQueens2     = rbm "Queens2"  [8]
rbmMParts       = rbm "Parts"    [30]
rbmMMSS         = rbm "MSS"      [35,36,5]
rbmMWhile       = rbm "While"    [1400]
rbmMTaut        = rbm "Taut"     [12]
rbmMClausify    = rbm "Clausify" [2,1]

rbmOther = [rbmAdjoxo,rbmCountDown,rbmCichelli,rbmSumPuz,rbmKnuthBendix,rbmMate]

-- big slow cases for benchmarking
rbmFib         = rbm "Fib"         [36]
rbmQueens      = rbm "Queens"      [11]            -- 67s    ~10m
rbmOrdList     = rbm "OrdList"     [12]            -- 38s    ~15m
rbmPermSort    = rbm "PermSort"    [10]            -- 65s    ~26m
rbmBraun       = rbm "Braun"       [6000, 255]     -- 24s    ~14m   >440m H
rbmQueens2     = rbm "Queens2"     [11]            -- 36s    ~23m   >440m H    -- [10]  ~5m
rbmParts       = rbm "Parts"       [30]            -- 0.6s   ~13s
rbmMSS         = rbm "MSS"         [150, 151, 10]  -- 36s    ~16m
rbmWhile       = rbm "While"       [14000]         -- 20s    ~8m
rbmTaut        = rbm "Taut"        [16]            -- 13.5   ~7.5m
rbmClausify    = rbm "Clausify"    [60,1]          -- 19s    ~9m
rbmAdjoxo      = rbm "Adjoxo"      []
rbmCountDown   = rbm "CountDown"   []
rbmSumPuz      = rbmz "SumPuz"     []   -- might need some manual realWordzh removal
rbmCichelli    = rbm "Cichelli"    []   -- might need some manual realWordzh removal
rbmMate        = rbm "Mate"        []   -- might need some manual realWordzh removal
rbmKnuthBendix = rbm "KnuthBendix" []   -- might need some manual realWordzh removal

-- misc. tests
rbmMBraun2      = rbm "Braun"    [5, 2047]
rbmMSS2         = rbm "MSS2"     [150, 151, 10]
rbmMateHP       = rbm "MateHP"   []
rbmBraunFix     = rbm "BraunFix" [1, 255]

