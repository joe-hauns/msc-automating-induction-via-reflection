
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Formula.Mir (
    MirForm(..)
  , MirTerm(..)
  , MirAtom(..)
  , mirSort
  ) where

import Util
--
import Data.Formula.Common
--
import Data.List
import Control.Monad
import Control.Arrow

type MirForm = BaseForm BaseAtom SortId
type MirTerm = BaseTerm SortId
type MirAtom = BaseAtom SortId

mirSort :: MirTerm -> SortId
mirSort (BaseFun _ _ s) = s
mirSort (BaseVar _   s) = s
-- mirSort (BaseConst _ s) = s


instance Show MirTerm where
  show (BaseVar v _)    = show v
  -- show (BaseConst c _)  = show c
  show (BaseFun f [] _) = show f
  show (BaseFun f vs _) = showFunOrPred f vs

instance Show MirForm where
  show = show'
    where 

          show' (BaseAtom (BaseEq Pos a1 a2) )   = join2 "=" a1 a2
          show' (BaseAtom (BaseEq Neg a1 a2) )   = join2 "/=" a1 a2
          show' (BaseAtom (BasePred f vs) )    = showFunOrPred f vs
          show' (BaseCon c a1 a2)   = par $ join2 (show c) a1 a2
          show' (BaseNot a) 
             | needsPar a = join [ "¬", par $ show a ]
             | otw        = join [ "¬", show a ]
          show'      (BaseCon0 c)            = show c
          show' (BaseQuant q v s f)  = join [show q, show v, ":", show s, ". ", show f]

          join2 sep a b = intercalate ( " " ++ sep ++ " " ) $ show <$> [a,b]
          connective a b c = par $ join2 a b c

needsPar (BaseCon _ _ _) = True
needsPar _ = False
-- needsPar (BaseAtom _) = False
-- needsPar (BaseQuant _ _ _ _) = False
-- needsPar _            = True
