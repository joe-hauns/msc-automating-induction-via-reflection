
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Util
import Data.Formula
import Data.Theory hiding (theory)
import Data.Theory.RobinsonsQ
import Data.Theory.Inductive
import Data.Theory.ReflectiveNew
import Parse.QQ
import CliUtil 


main :: IO ()
main = translatorMain reflInductive 
