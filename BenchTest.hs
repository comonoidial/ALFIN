module BenchTest where

import RunTest
import TestCases

-- compile with:  ghc -O2 -rtsopts -main-is BenchTest.main --make BenchTest
-- execute with:  BenchTest +RTS -H1500m -M1900m -K50m            -- maximum feasible heap/stack limit for a 32bit GHC installation, numbers might be doubled for on 4GB+ 64bit machine

main :: IO ()
main = runSim rbmMQueens2 --mapM_ runSim rbmFAll -- mapM_ runSim rbmOther

