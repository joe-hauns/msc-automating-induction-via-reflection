
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

module Data.Formula.Inference (module Data.Formula.Inference) where

import Util
import Data.Formula.Common
import Data.Inference hiding ((/\), (\/))
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

-- infixr 5 !
-- infixr 4 ===
-- infixr 4 =/=
-- infixr 3 /\
-- infixr 3 \/
-- infixr 2 -->
-- infixr 2 <--
-- infixr 2 <->

data Formula = Equal Polarity Term Term
             | FPred PredId [Term]
             | Not   Formula
             | Quant Quantifier VarId (FlatLattice SortId) Formula
             | Con   Connective Formula Formula
               deriving ( Eq, Ord ) -- FormulaDerivation

data Term = Term (FlatLattice SortId) TKind
          deriving ( Generic, Eq, Ord )
instance Hashable TKind

data TKind = TVar VarId
           | TFun [Term]
          deriving ( Generic, Eq, Ord )

instance Hashable Term

-- instance Hashable a => Hashable (Sorted a)

-- mapId :: (String -> String) -> Sorted VarId -> Sorted VarId
-- mapId f = fmap (\(Id s) -> Id (f s))
--
-- class ToTerm a where 
--   to :: a -> Term 
--
-- instance ToTerm Term where 
--   to = id
--
-- instance ToTerm VarId where 
--   to = Term FlatTop . TVar 
--
-- instance Closable Formula where
--   closure q f = seqA [ Quant q v FlatTop | v <- vs ]  f
--     where vs = reverse $ sort $ freeVars f
--
-- freeVars :: Formula -> [Sorted VarId] 
-- freeVars =  nub . fv
--   where fv (Equal _ t1 t2) = fv' =<< [t1, t2]
--         fv (FPred _ ts)    = fv' =<<  ts
--         fv (Con   _ f1 f2) = fv  =<< [f1, f2]
--         fv (Not   f)       = fv f
--         fv (Quant q v f)   = filter ((/= unSorted v ). unSorted)
--                            $ fv f
--
--         fv' :: Term -> [Sorted VarId] 
--         fv' (TFun f ts) = fv' =<< ts
--         fv' (TVar v)    = [v]
--
-- instance Subs Term Term where
--   subs v t' (TVar v') | unSorted v' == v = t'
--                           | otherwise        = TVar v'
--   subs v t' (TFun f ts) = TFun f [ subs v t' t | t <- ts ]
--
-- instance Subs Formula Term where
--     subs v t (Equal e a1 a2) = (Equal e (subs v t a1)  (subs v t a2))
--     subs v t (FPred p ts)    = (FPred p (subs v t <$> ts))    
--     subs v t (Con   c a1 a2) = (Con   c (subs v t a1) (subs v t a2)) 
--     subs v t (Not   f)       = (Not   (subs v t f))       
--     subs v t (Quant q v' f)  = let f' = if unSorted v' == v 
--                                             then (Quant q v' (subs (unSorted v') (TVar v'') f))   
--                                             else f
--                                    in Quant q v' (subs v t f') 
--                                                where v'' = mapId (++ "_") v'
--
-- instance NormalForm Formula where 
--   norm f = dbr 0 f
--     where dbr :: Int -> Formula -> Formula
--           dbr i (Quant q v f)   = Quant q v' (dbr (i+1) (subs (unSorted v) (TVar v') f))
--            where v' = AnySort $ Id ("v" ++ show i) 
--           dbr i (Equal e t1 t2) = (Equal e t1 t2)
--           dbr i (FPred p ts)    = (FPred p ts)
--           dbr i (Con   c f1 f2) = (Con   c (dbr i f1) (dbr i f2)) 
--           dbr i (Not   f)       = (Not   (dbr i f))       
--
-- -- betaEquiv :: Term -> [Sorted VarId] 
-- -- fv (TFun f ts) = fv' =<< ts
-- -- fv (TVar v)    = [v]
--
-- eqSugar :: (ToTerm a, ToTerm b) => Polarity -> a -> b -> Formula
-- eqSugar pol a b = Equal pol (to a) (to b)
--
-- (~~) :: (ToTerm a, ToTerm b) => a -> b -> Formula
-- (~~) = eqSugar Pos
-- (===) :: (ToTerm a, ToTerm b) => a -> b -> Formula
-- (===) = (~~)
--
-- (!~) :: (ToTerm a, ToTerm b) => a -> b -> Formula
-- (!~) = eqSugar Neg
-- (=/=) :: (ToTerm a, ToTerm b) => a -> b -> Formula
-- (=/=) = (!~)
--
-- (/\) :: Formula -> Formula -> Formula
-- (/\) = Con And
--
-- (\/) :: Formula -> Formula -> Formula
-- (\/) = Con Or
--
-- (-->):: Formula -> Formula -> Formula
-- (-->) = Con Implies
--
-- (<->):: Formula -> Formula -> Formula
-- (<->) = Con Iff
--
-- (<--):: Formula -> Formula -> Formula
-- (<--) = Con If
--
-- lnot :: Formula -> Formula
-- lnot = Not
--
-- class ToTerms a where 
--   toTerms :: a -> [Term]
--
-- instance ToTerm a => ToTerms [a] where 
--   toTerms = fmap to
--
-- instance ToTerms () where 
--   toTerms () = []
--
-- instance ToTerms Term where 
--   toTerms = return . to
--
-- instance ToTerms VarId where 
--   toTerms = return . to
--
-- instance ( ToTerm a0, ToTerm a1 ) => ToTerms (a0, a1) where 
--   toTerms (a0, a1) = [ to a0, to a1 ]
--
-- instance ( ToTerm a0, ToTerm a1, ToTerm a2 ) => ToTerms (a0, a1, a2) where 
--   toTerms (a0, a1, a2) = [ to a0, to a1, to a2 ]
--
-- class Apply a where 
--  type Out a 
--  (!) :: ToTerms b => a -> b -> Out a
--
-- instance Apply FunId where 
--   type Out FunId = Term
--   f ! args = TFun f (toTerms args)
--
-- instance Apply PredId where 
--   type Out PredId = Formula
--   p ! args = FPred p (toTerms args)
--
-- quant :: Quantifier -> [VarId] -> Formula -> Formula
-- quant q []     = id
-- quant q (x:xs) = Quant q (AnySort x) . quant q xs
--
-- quantS :: Quantifier -> [Sorted VarId] -> Formula -> Formula
-- quantS q []     = id
-- quantS q (x:xs) = Quant q x . quantS q xs
--
-- forallS = quantS Universal
-- existsS = quantS Existential
-- forall = quant Universal
-- exists = quant Existential
--
--
--
-- instance Show a => Show (Sorted a) where
--   show (a:::s)     = join [show a, ": ", show s]
--   show (AnySort a) = show a
--
-- instance Show Term where
--   show (TVar v)    = show v
--   show (TFun f vs) = showFunOrPred f vs
--
-- instance Show Formula where
--   show = show'
--     where bracket s = "( " ++ s ++ " )"
--           show' (Equal Pos a1 a2)   = join2 "==" a1 a2
--           show' (Equal Neg a1 a2)   = join2 "/=" a1 a2
--           show' (FPred f vs)    = showFunOrPred f vs
--           show' (Con c a1 a2)   = bracket $ join2 (show c) a1 a2 --a b c connective "&" a1 a2
--           show' (Not a)         = join [ "~",  bracket $ show a ]
--           show' (Quant q v f)  = join [show q, show v, ".", show f]
--           join2 sep a b = intercalate ( " " ++ sep ++ " " ) $ show <$> [a,b]
--           connective a b c = bracket $ join2 a b c
--
-- makeLenses ''Term
