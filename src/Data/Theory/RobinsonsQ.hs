
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Data.Theory.RobinsonsQ (
    robinsonsQ 
  , robinsonsQlax
  , zero 
  , succ 
  , add
  , mul
  )  where

import Prelude hiding (succ)
--
import Util
import Data.Formula
import Data.Theory.Interpreted
import Data.Theory (theoryInf)
import Data.Signature
import Parse
import Parse.QQ

funDecl id ts t = (Id id, (Function ts t))

-- fundecls 

add :: FunId
add = Id "+" 

mul :: FunId
mul = Id "*" 

succ :: FunId
succ = Id "s"   
 
zero :: FunId
zero = Id "zero" 

robinsonsQ :: MirTheory
robinsonsQ = unwrap . theoryInf $ robinsonsQlax

robinsonsQlax :: Theory
robinsonsQlax = mapName $ [theory|
      zero : () -> nat.
      s : (nat) -> nat.
      inductive zero.
      inductive    s.

      + : (nat,nat) -> nat.
      forall   y. zero() + y = y.
      forall x,y.   s(x) + y   = s(x + y).

      * : (nat,nat) -> nat.
      forall   y. zero() * y = zero().
      forall x,y.   s(x) * y   = y + (x * y).

      -- forall x. s(x) /= zero().
    |]
   where mapName (Theory _ sig as dtys)  = Theory "Q" sig as dtys
