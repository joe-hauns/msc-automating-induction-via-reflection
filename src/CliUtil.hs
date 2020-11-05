module CliUtil (translatorMain, serializerMain) where

import Control.Monad
import Control.Category
import Data.Theory.Interpreted
import Parse
import Serialize
import Data.Theory
import Text.Parsec
import Util

translatorMain :: (MirBenchmark -> MirBenchmark) -> IO ()
translatorMain trans = serializerMain $ 
         trans >>> genSerialize humanReadable 

serializerMain :: (MirBenchmark -> String) -> IO ()
serializerMain ser = interact $ 
              runParser problemParser () "stdin" >>> unwrapE 
          >>> benchmarkInf                       >>> unwrap 
          >>> ser
  where unwrapE (Right x) = x
        unwrapE (Left  x) = error $ show x
