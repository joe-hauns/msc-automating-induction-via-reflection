
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Util
import Data.Formula
import Data.Theory
import Data.Theory.RobinsonsQ
import Data.Theory.Inductive
import Data.Theory.Reflective
import Data.Theory.ReflectiveNew
import Vampire
import Benchmark.Reflective
import Benchmark.Induction
import Data.Signature
import qualified Data.Theory.RobinsonsQ as Q
--
import ToTff
import Text.Regex.Posix
import Util
import Data.List
import Control.Monad
import Data.Maybe
import Control.Lens hiding (element, Const, to)
import Benchmark
import Benchmark.Reflective
import Data.Solvers
import Data.Solvers.Vampire
import Data.Solvers.Cvc4
import Data.Solvers.Zipperposition
import ToTex
import Benchmark.Induction (indBenchmarksMsc)

-- while : BoolTerm x Prog        -> Prog
-- if    : BoolTerm x Prog x Prog -> Prog
-- (;)   : Prog     x Prog        -> Prog
-- (<-)  : Var      x Term        -> Prog
-- 
-- val(a ; b, env) = val(a, val(b, env))
-- val(if(b,p,q), env) = val(a, val(b, env))

timeout = Seconds $ 1

main :: IO ()
main = do 
  -- compareSolversGroup timeout solvers reflBenchmarks

  compareSolversGroup timeout (addReflInd =<< solvers) indBenchmarksMsc


addReflInd s = [ AnySolver s, AnySolver $ ReflIndSolver s ]

data ReflIndSolver s = ReflIndSolver s

instance (Solver s) => Solver (ReflIndSolver s) where 
  name     (ReflIndSolver s) = (name s) ++ "'"
  proveMir (ReflIndSolver s) t b = proveMir s t b'
    where b' = reflInductive b
  

solvers = 
      -- (AnySolver vampireComplexTermInduction) :
      -- (AnySolver vampireSubsFull) :
      -- (AnySolver Zeno) :
      -- (AnySolver imandra) :

      (AnySolver vampireOld) :
      (AnySolver cvc4) :
      (AnySolver zipperposition1) :

      (AnySolver cvc4gen) :
      (AnySolver zipperposition2) :
      []







































































































































































































































































































