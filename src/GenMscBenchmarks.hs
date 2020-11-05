module Main where

import Benchmark.Msc
import Serialize
import Control.Monad
import Data.List
import Text.Printf
import Translations
import System.Environment
import System.Directory
import Data.Theory.ReflectiveNew
import Data.Theory.Inductive (reflInductive)

main = do
  as <- getArgs
  case as of 
    [d] -> do
        let dir = d ++ "/benchmarks"
        export (printf "%s/inductive"            dir) indBenchmarks
        export (printf "%s/reflectiveInductive"  dir) (fmap ReflInductive indBenchmarks)
        export (printf "%s/reflectiveConjecture" dir) reflConjBenchmarks
        export (printf "%s/reflectiveAxioms"     dir) reflAxBenchmarks 
    as -> error $ "expected the name of output directory as argument (args: " ++ show as ++ ")"


export :: MscBenchmark a => String -> [a] -> IO ()
export dir as = forM_ as $ \x -> do

    let fname = mscId x
    let mir = toMirBenchmark x

    createDirectoryIfMissing True dir
    putStrLn  $ "processing " ++ fname ++ " ..."

    forM_ allTranslators $  \t -> 
      case translate t mir of 
        Right content -> do
           let file = printf "%s/%s.%s" dir fname (fileExtension t)  
           toFile file content
        Left _ -> return ()

toFile = writeFile

data ReflInductive = ReflInductive IndBenchmark

instance MscBenchmark ReflInductive where
  
  mscId          (ReflInductive i) = mscId i
  toMirBenchmark (ReflInductive i) = reflInductive (toMirBenchmark i)
