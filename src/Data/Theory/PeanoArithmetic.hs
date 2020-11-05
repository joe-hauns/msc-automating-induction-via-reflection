
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Theory.RobinsonsQ (
    robinsonsQ 
  , zero 
  , succ 
  , add
  , mul
  )  where

import Prelude hiding (succ)
--
import Util
import Data.Formula
import Data.Theory 
import Data.Signature

binary :: FunId -> forall a b . (ToTerm a, ToTerm b) => a -> b -> Term 
binary n a b = TFun n [ to a, to b ]

unary :: FunId -> forall a . (ToTerm a) => a -> Term 
unary n a = TFun n [ to a ]

funDecl id ts t = (Id id, (Function ts t))

-- fundecls 

add :: FunId
add = Id "add" 

mul :: FunId
mul = Id "mul" 

succ :: FunId
succ = Id "s"   
 
zero :: FunId
zero = Id "zero" 

robinsonsQ :: SortId -> Theory
robinsonsQ nat = unwrap $ theory "Robinsons Q" sig ax
  where 
        x = Id "x" :: VarId
        y = Id "y" :: VarId
       
        zero' = zero!()
        (+) :: (ToTerm a, ToTerm b) => a -> b -> Term
        (+) = binary add
        (*) :: (ToTerm a, ToTerm b) => a -> b -> Term
        (*) = binary mul
        s :: ToTerm a => a -> Term 
        s = unary succ

        ax = [ axiom "inj0" (s x !~ zero' )
             , axiom "inj1" (s x ~~ s y --> x ~~ y)
             , axiom "add0" (zero' + x ~~ x)
             , axiom "add1" (s x  + y ~~ s(x + y))
             , axiom "mul0" (zero' * x ~~ zero')
             , axiom "mul1" (s x  * y ~~ (x * y) + y)
             ] where axiom s f = Axiom s (universalClosure f)

        sig = mkSig     [ zero :::: [   ] :-> nat  
                        , succ :::: [nat] :-> nat
                        , add  :::: [nat, nat] :-> nat
                        , mul  :::: [nat, nat] :-> nat ]

