
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Util
import Data.Formula
import Data.Theory hiding (theory)
import Data.Theory.RobinsonsQ
import Data.Theory.Inductive
import Data.Theory.Interpreted
import Data.Theory.ReflectiveNew
import Parse.QQ
import CliUtil 


main :: IO ()
main = translatorMain reflGoedel
  where reflGoedel (Benchmark th c) = Benchmark (refl th) (refl c)
