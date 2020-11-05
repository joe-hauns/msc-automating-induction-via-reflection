
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Data.Theory.Lists (
    lists
  , listsLax
  )  where

import Util
import Data.Formula
import Data.Theory.Interpreted
import Data.Signature
import Parse
import Parse.QQ
import Data.Theory (theoryInf)

app :: FunId
app = Id "append" 

cons :: FunId
cons = Id "cons"   
 
nil :: FunId
nil = Id "nil" 

listsLax :: Theory
listsLax = [theory|
      nil  : () -> list.
      cons : (alpha, list) -> list.
      ++   : (list , list) -> list.
      inductive  nil.
      inductive cons.
      forall     y.      nil() ++ y = y.
      forall e,x,y. cons(e, x) ++ y = cons(e, x ++ y).

      -- forall e,x. cons(e,x) /= nil().
      -- forall e,e',x,y. (cons(e,x) = cons(e',y)  <-> (e = e' /\ x = y)).
    |]

  -- where mapSort = fmap (\x -> if x == (Just $ Id "a") then Just alpha else x)
  --       mapName (Theory _ sig as dtys)  = Theory ("list_" ++ show alpha) sig as dtys

lists :: MirTheory
lists = unwrap . theoryInf $ listsLax


-- lists alpha = unwrap 
--                  $ theory "Lists" 
--                  (mkSig [ tid nil  :::: [   ] :-> list  
--                         , tid cons :::: [alpha, list] :-> list
--                         , tid app  :::: [list , list] :-> list ])
--                  [ axiom "inj0" $ cons!(x, y) =/= nil!() 
--                  , axiom "inj1" $ cons!(x, y) === cons!(z, u) --> x === z /\ y === u
--                  , axiom "app0" $ (  nil!()    ) ++ x === x
--                  , axiom "app1" $ ( cons!(u,y) ) ++ x === cons!(u, y ++ x)
--                  -- TODO: reverse
--                  ] 
--   where 
--         x = Id "x" :: VarId
--         y = Id "y" :: VarId
--         z = Id "z" :: VarId
--         u = Id "u" :: VarId
--         list = Id "list" :: SortId
--        
--         (++) :: (ToTerm a, ToTerm b) => a -> b -> Term
--         (++) = binary app
--         axiom s f = Axiom s (universalClosure f)
