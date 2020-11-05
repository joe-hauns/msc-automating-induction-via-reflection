module Inference(Compiler(..)) where

import Data.Formula.Mir
import Data.Formula
import Data.Formula

class Compiler a where 
  compile :: a -> Benchmark -> Result MirBenchmark

data SortInference = SortInference

instance Compiler SortInference where 
  compile Inference problem  = undefined

data Reflective a = Reflective a

instance Compiler a => Compiler (Reflective a) where 
  compile (Reflective a) problem = compile a problem >>= addReflection
    where addReflection = undefined

data ReflectiveInduction a = ReflectiveInduction a

instance Compiler a => Compiler (ReflectiveInduction a) where 
  compile (ReflectiveInduction a) problem = compile (Reflective a) <&> (<> induction)
    where induction = undefined
