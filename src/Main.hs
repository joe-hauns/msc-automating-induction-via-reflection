
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

-- while : BoolTerm x Prog        -> Prog
-- if    : BoolTerm x Prog x Prog -> Prog
-- (;)   : Prog     x Prog        -> Prog
-- (<-)  : Var      x Term        -> Prog
-- 
-- val(a ; b, env) = val(a, val(b, env))
-- val(if(b,p,q), env) = val(a, val(b, env))

main :: IO ()
main = reflBenchmarks
