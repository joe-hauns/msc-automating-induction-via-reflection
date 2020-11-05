module Main where

import Benchmark.Msc
import Data.Solvers.Msc
import Data.Solvers
import Benchmark (compareSolversGroupWithFileOutput,compareSolversGroup, BenchGroup(..))
import Util
import Data.Theory (unBenchmarkInf)
import Data.Theory.Inductive
import ToTex
import System.Environment
import System.Directory

timeout = Seconds 60

main = do 
  args <- getArgs
  handlers <- case args of 
    [d] -> do 

          let dir = d ++ "/results"
          createDirectoryIfMissing True dir
          run dir indBenchmarks
          run dir reflAxBenchmarks
          run dir reflConjBenchmarks
    as -> error $ "expected ouput file as args, got: " ++ show as
  
  return ()

run :: MscBenchmark a => FilePath -> [a] -> IO ()
run dir as = compareSolversGroupWithFileOutput file timeout solvers [ toGroup <$>  as] 
  where file = dir ++ "/" ++ resultsFileId a
        solvers = getSolvers a
        a:_ = as

toGroup :: MscBenchmark a => a -> BenchGroup
toGroup x = BenchGroup { 
              bgId       = mscId x
            , bgTex      = texMath $ "\\code{" ++ mscId x ++ "}"
            , bgProblems = [ (unBenchmarkInf . toMirBenchmark) x ]
            }
