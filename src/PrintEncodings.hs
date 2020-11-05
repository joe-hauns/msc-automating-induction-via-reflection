
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

main :: IO ()
main = printIndBenchmarks
