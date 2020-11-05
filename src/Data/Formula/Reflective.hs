
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

module Data.Formula.Reflective ( ReflForm 
                               -- , ReflectionPrinciple(..)
                               -- , ReflAtom(..) 
                               ) where


import Util
import Data.Formula.Common
import Data.Formula.Mir
--
import Data.List
import Control.Monad
import Control.Arrow
import Data.Hashable
import GHC.Generics (Generic)
import Control.Lens hiding (element, to)
--
import Data.HashSet hiding (filter)
import qualified Data.HashSet as Set

type ReflForm s = BaseForm BaseAtom s

-- data ReflAtom s = NonRefl (BaseAtom s)
--                 | Refl    (BaseForm BaseAtom s)
--
-- class ReflectionPrinciple a where 
--   trans :: a -> ReflForm SortId -> BaseForm BaseAtom SortId
--
--   trans r = mapAtom transAtom'
--     where transAtom' (NonRefl a) = a
--           transAtom' (   Refl a) = transAtom r a
--
--   transAtom :: a -> BaseForm BaseAtom SortId -> BaseAtom SortId
