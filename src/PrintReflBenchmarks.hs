
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}

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
import ToSmtlib2
import qualified Data.Theory.RobinsonsQ as Q
--
import System.Environment
import ToTff
import Text.Regex.Posix
import Util
import Data.List
import Data.List.Index
import Control.Monad
import Data.Maybe
import Serialize
import Text.Printf

main :: IO ()
main = do 
  undefined
  -- [a] <- getArgs 
  -- forM_ (indexed reflBenchmarks) $ \(i, b) -> do
  --   let cont = genSerialize humanReadable b
  --   writeFile ( printf "%s/%0.2d.logic" a i ) cont
   
  -- intercalate "\n\n"  (genSerialize humanReadable <$> reflBenchmarks )



































































