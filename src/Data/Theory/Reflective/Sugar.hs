
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Theory.Reflective.Sugar (
    module Data.Theory.Reflective.Sugar
  ) where

import Util
import Prelude hiding ((&&), (||))
import Data.Formula hiding (subs)
import Data.Signature
import Data.Theory
import Data.Theory.Reflective

top :: Term
top = not' bot

bot :: Term
bot = botR!()

not' :: (ToTerm a) => a -> Term
not' = unary notR 

dual (*) a b = not' ( not' a * not' b )

(&&) :: (ToTerm a, ToTerm b) => a -> b -> Term
(&&) = dual (||)

(||) :: (ToTerm a, ToTerm b) => a -> b -> Term
a || b = orR!(a,b)

(~~>) :: (ToTerm a, ToTerm b) => a -> b -> Term
a ~~> b = (not' a) ||  b 

tr :: (ToTerm a) => a -> Formula
tr a = BaseAtom $ true (to a)

forall' :: SortId -> forall a . (ToTerm a) => a -> Term
forall' s a = (forallR s![a])

v0 :: SortId -> Term 
v0 s = nullary  ( v0R s )

var :: SortId -> Term -> Term
var s = unary (vTermR s)

subs   srt = ternary (subsFR srt)
subsT  s s' = ternary (subsTR s s')

allVars' :: SortId ->  [Term]
allVars' s = iterate (nVarR s!) (v0 s)

vTerm' :: SortId -> Term -> Term
vTerm' s a = (vTermR s![a])

-- (!!) :: ToTerm a0 => a0 
--      -> ToTerm a1 => a1 
--      -> Term
-- phi !! t = sbs ty phi (v0 ty) t
--   where sbs = case btSort (to phi) of 
--                   Just x | x == form -> subs
--                          | otherwise -> subsT x
--                   Nothing -> undefined
--         ty = case btSort (to t) of 
--                   Just t -> t
--                   Nothing -> undefined
