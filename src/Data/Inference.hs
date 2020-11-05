
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}

module Data.Inference where

import Util
import Data.Formula.Common
--
import Data.List
import Control.Monad
import Control.Arrow
import Data.Hashable
import GHC.Generics (Generic)
import Control.Lens hiding (element, to)
--
-- import Data.HashSet hiding (filter)
-- import qualified Data.HashSet as Set

class Lattice a where 
  (/\) :: a -> a -> a
  (\/) :: a -> a -> a
  top :: a
  bot :: a

data FlatLattice a = Flat  a
                   | FlatBot 
                   | FlatTop
                    deriving ( Generic, Eq, Ord, Functor )
instance Hashable a => Hashable (FlatLattice a)


instance Eq a => Lattice (FlatLattice a) where 

  Flat  x \/ Flat y  | x == y = Flat x
  FlatBot \/ x                = x
  x       \/ FlatBot          = x 
  _       \/ _                = FlatTop 

  Flat  x /\ Flat y  | x == y = Flat x
  FlatTop /\ x                = x
  x       /\ FlatTop          = x
  _       /\ _                = FlatBot

  top = FlatTop
  bot = FlatBot


data InfLattice loc a = Inf loc a
                      | Incons [(loc, a)]
                      | Unknown
                    deriving ( Generic, Eq, Ord, Functor )
instance (Hashable loc, Hashable a ) => Hashable (InfLattice loc a)


-- instance (Ord loc, Eq a) => Lattice (InfLattice loc a) where 
--
--   x \/ Unknown = x
--   Unknown \/ x = x
--
--   ( Inf  l a ) \/ ( Inf l' a' )  
--       | a == a' = Inf (max l l') a
--       | otherwise = Incons [(l,a), (l',a')]
--
--   ( Inf l a   ) \/ ( Incons as    ) = Incons ( as `union` [(l,a)] )
--   ( Incons as ) \/ ( Inf l a      ) = Incons ( as `union` [(l,a)] )
--
--   ( Incons as ) \/ ( Incons bs    ) = Incons ( as `union` bs )
--   ( Inf l a   ) \/ ( Incons as    ) = Incons ( as `union` [(l,a)] )
--
--
--   ( Inf  l a ) /\ ( Inf l' a' )  
--       | a == a' = Inf (max l l') a
--       | otherwise = Incons [(l,a), (l',a')]
--
--   ( Inf l a   ) /\ ( Incons as    ) = Incons ( as `union` [(l,a)] )
--   ( Incons as ) /\ ( Inf l a      ) = Incons ( as `union` [(l,a)] )
--
--   ( Incons as ) /\ ( Incons bs    ) = Incons ( as `union` bs )
--   ( Inf l a   ) /\ ( Incons as    ) = Incons ( as `union` [(l,a)] )
--
--
--   -- Inf  x /\ Inf y  | x == y = Inf x
--   -- Unknown /\ x                = x
--   -- x       /\ Unknown          = x
--   -- _       /\ _                = Incons
--
--   top = Unknown
--   bot = Incons []
--
--
