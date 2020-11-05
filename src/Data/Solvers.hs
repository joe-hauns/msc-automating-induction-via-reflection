{-# LANGUAGE GADTs #-}

module Data.Solvers (GenBenchmark(..), MirBenchmark, Benchmark(..), Solver(..), SolverResult(..), AnySolver(..), InputFmt(..), allInputFmts) where

import Data.Theory.Interpreted
import Data.Theory (benchmarkInf)
import Data.Formula
import Data.Formula.Mir
import Util
import ToTex
import Text.Printf

data SolverResult = Valid 
                  | TimeOut
                  | Unknown
                  | CounterSat
                  | NotApplicable String
                  | Error String deriving (Eq, Show)

class Solver a where 
  name     :: a -> String
  options  :: a -> [String]
  texName  :: a -> Tex
  texName  = toTexStr . printf "\\solver{%s}" . name
  proveMir :: a -> Seconds -> MirBenchmark -> IO SolverResult

  setup    :: a -> IO ()
  setup _ = return ()

  teardown :: a -> IO ()
  teardown _ = return ()

  inputFmt          :: a -> InputFmt
  supportsInduction :: a -> Bool
  supportsFullFol   :: a -> Bool
  supportsFullFol   _ = True

  prove :: a -> Seconds -> Benchmark -> IO SolverResult
  prove a t b = proveMir a t b'
    where b' = unwrap $ benchmarkInf b


data AnySolver where 
  AnySolver :: Solver s => s -> AnySolver

instance Solver AnySolver where
  proveMir (AnySolver s) = proveMir s
  name     (AnySolver s) = name     s
  inputFmt (AnySolver s) = inputFmt s
  texName  (AnySolver s) = texName s
  supportsInduction (AnySolver s) = supportsInduction s
  supportsFullFol   (AnySolver s) = supportsFullFol   s
  options (AnySolver s) = options s

data InputFmt = Smtlib2 | Zf | ZenoHaskell | ImandraCaml deriving (Show, Eq, Ord, Enum)
allInputFmts = [Smtlib2 ..]
