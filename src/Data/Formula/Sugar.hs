
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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Data.Formula.Sugar (module Data.Formula.Sugar) where

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
import Data.HashSet hiding (filter)
import qualified Data.HashSet as Set

infixr 5 !
infixr 4 ===
infixr 4 =/=
infixr 3 /\
infixr 3 \/
infixr 2 -->
infixl 2 <--
infixr 1 <->

type Formula = BaseForm BaseAtom (Maybe SortId)
type Term    = BaseTerm (Maybe SortId)


fn0 :: s
      -> FunId
      -> BaseTerm s
fn0 s n = BaseFun n [] s

fn1 :: s
      -> FunId
      -> forall a . ToBaseTerm s a => a 
      -> BaseTerm s
fn1 s n a = BaseFun n [ trm a ] s

fn2 :: s
      -> FunId
      -> forall a . ToBaseTerm s a => a 
      -> forall b . ToBaseTerm s b => b 
      -> BaseTerm s
fn2 s n a b = BaseFun n [ trm a , trm b ] s

fn3 :: s
      -> FunId
      -> forall a0 . ToBaseTerm s a0 => a0
      -> forall a1 . ToBaseTerm s a1 => a1
      -> forall a2 . ToBaseTerm s a2 => a2
      -> BaseTerm s
fn3 s n a0 a1 a2 = BaseFun n [ trm a0 , trm a1, trm a2 ] s

nullary :: FunId 
        -> Term 
nullary n = BaseFun n [] Nothing

unary :: FunId 
      -> forall a . ToTerm a => a 
      -> Term
unary n a = BaseFun n [ to a ] Nothing

binary :: FunId 
       -> forall a . ToTerm a => a 
       -> forall b . ToTerm b => b
       -> Term 
binary n a0 a1 = BaseFun n [ to a0, to a1 ] Nothing

ternary :: FunId 
        -> forall a . ToTerm a => a 
        -> forall b . ToTerm b => b
        -> forall c . ToTerm c => c 
        -> Term 
ternary n a0 a1 a2 = BaseFun n [ to a0, to a1, to a2 ] Nothing


class ToBaseTerm s a where 
  trm :: a -> BaseTerm s

instance ToBaseTerm s (BaseTerm s) where 
  trm = id

class ToTerm a where 
  to :: a -> Term 

-- instance ToTerm a => ToBaseTerm (Maybe SortId) a where 
--   trm = to

instance ToTerm Term where 
  to = id

instance ToTerm VarId where 
  to = (flip BaseVar) Nothing

eqSugar :: (ToTerm a, ToTerm b) => Polarity -> a -> b -> Formula
eqSugar pol a b = BaseAtom (BaseEq pol (to a) (to b))

(===) :: (ToTerm a, ToTerm b) => a -> b -> Formula
(===) = eqSugar Pos

(=/=) :: (ToTerm a, ToTerm b) => a -> b -> Formula
(=/=) = eqSugar Neg

(/\) :: BaseForm a s -> BaseForm a s -> BaseForm a s
(/\) = BaseCon And

(\/) :: BaseForm a s -> BaseForm a s -> BaseForm a s
(\/) = BaseCon Or

(-->):: BaseForm a s -> BaseForm a s -> BaseForm a s
(-->) = BaseCon Implies

(<->):: BaseForm a s -> BaseForm a s -> BaseForm a s
(<->) = BaseCon Iff

(<--):: BaseForm a s -> BaseForm a s -> BaseForm a s
(<--) = BaseCon If

lnot :: BaseForm a s -> BaseForm a s 
lnot = BaseNot

class ToTerms a where 
  toTerms :: a -> [Term]

instance ToTerm a => ToTerms [a] where 
  toTerms = fmap to

instance ToTerms () where 
  toTerms () = []

instance ToTerms Term where 
  toTerms = return . to

instance ToTerms VarId where 
  toTerms = return . to

instance ( ToTerm a0, ToTerm a1 ) => ToTerms (a0, a1) where 
  toTerms (a0, a1) = [ to a0, to a1 ]

instance ( ToTerm a0, ToTerm a1, ToTerm a2 ) => ToTerms (a0, a1, a2) where 
  toTerms (a0, a1, a2) = [ to a0, to a1, to a2 ]

class Apply a where 
 type Out a 
 (!) :: ToTerms b => a -> b -> Out a

instance Apply FunId where 
  type Out FunId = Term
  f ! args = BaseFun f (toTerms args) Nothing

instance Apply PredId where 
  type Out PredId = Formula
  p ! args = BaseAtom ( BasePred p (toTerms args))

quant :: Quantifier -> [VarId] -> Formula -> Formula
quant q []     = id
quant q (x:xs) = BaseQuant q x Nothing . quant q xs

quantS :: Quantifier -> [VarId] -> SortId -> Formula -> Formula
quantS q []     s = id
quantS q (v:xs) s = BaseQuant q v (Just s) . quantS q xs s

forallS = quantS Universal
existsS = quantS Existential

forall = quant Universal
exists = quant Existential


instance Show Term where
  show (BaseVar v _)    = show v
  show (BaseFun f vs _) = showFunOrPred f vs

instance Show Formula where
  show = show'
    where bracket s = "( " ++ s ++ " )"
          show' (BaseAtom (BaseEq Pos a1 a2) )   = join2 "=" a1 a2
          show' (BaseAtom (BaseEq Neg a1 a2) )   = join2 "/=" a1 a2
          show' (BaseAtom (BasePred f vs) )    = showFunOrPred f vs
          show' (BaseCon c a1 a2)   = bracket $ join2 (show c) a1 a2 --a b c connective "&" a1 a2
          show' (BaseNot a)         = join [ "~",  bracket $ show a ]
          show' (BaseQuant q v Nothing f)  = join [show q, show v, ".", show f]
          show' (BaseQuant q v (Just s) f)  = join [show q, show v, ":", show s, ".", show f]
          join2 sep a b = intercalate ( " " ++ sep ++ " " ) $ show <$> [a,b]
          connective a b c = bracket $ join2 a b c


-- instance Serialize Term where
--   serialize (BaseVar v _)    = serialize v
--   serialize (BaseFun f vs _) = serializeFunOrPred f vs
--
-- instance Serialize Formula where
--   serialize = serialize'
--     where bracket s = "( " ++ s ++ " )"
--           serialize' (BaseAtom (BaseEq Pos a1 a2) )   = join2 "=" a1 a2
--           serialize' (BaseAtom (BaseEq Neg a1 a2) )   = join2 "/=" a1 a2
--           serialize' (BaseAtom (BasePred f vs) )    = serializeFunOrPred f vs
--           serialize' (BaseCon c a1 a2)   = bracket $ join2 (serialize c) a1 a2 --a b c connective "&" a1 a2
--           serialize' (BaseNot a)         = join [ "~",  bracket $ serialize a ]
--           serialize' (BaseQuant q v Nothing f)  = join [serialize q, serialize v, ".", serialize f]
--           serialize' (BaseQuant q v (Just s) f)  = join [serialize q, serialize v, ":", serialize s, ".", serialize f]
--           join2 sep a b = intercalate ( " " ++ sep ++ " " ) $ serialize <$> [a,b]
--           connective a b c = bracket $ join2 a b c
--
--
