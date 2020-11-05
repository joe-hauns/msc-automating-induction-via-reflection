
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Data.Theory.Inductive (inductive, safeInductive, mirInductive, ReflInductive(..)) where

import Util
import Data.Formula hiding (subs, forall, forallS)
import Data.Formula.Mir
import Data.Signature
import Data.Theory (theoryInf, fromMir, toMir)
import Data.Theory.Interpreted
import Data.Theory.ReflectiveNew
-- import Data.Theory.Reflective
-- import Data.Theory.Reflective.Sugar
--
import Prelude hiding ((&&))
import Data.Composition
import Data.List
import Data.Maybe
import Control.Lens hiding (to)
import Control.Monad

inductive :: Theory -> MirTheory
inductive = unwrap . safeInductive


class ReflInductive a where
  reflInductive :: a -> a 

instance ReflInductive MirTheory where
  reflInductive = mirInductive

instance ReflInductive MirBenchmark where
  reflInductive (Benchmark thry conj) = 
      Benchmark {
        bTheory     = reflInductive thry
      , bConjecture = conj
      }

mirInductive :: MirTheory -> MirTheory
mirInductive orig =  removeDatatypes $ addAxioms reflAx reflTheory
  where reflTheory = mirReflective orig
        reflAx = [ reflIndAxiom dty | dty <- datatypes orig]
              ++ ( datatypes orig >>= disjointess )
              ++ ( datatypes orig >>= injectivity )

        removeDatatypes (Theory n sig as dtys) = Theory n sig as []
        injectivity (DataType s ctors) = catMaybes [ inj f | f <- ctors ]
          where inj (_, Function [] _) = Nothing
                inj (f, Function as _) = Just . universalClosure $ 
                    -- f(v1, ..., vn) = f(w1, ..., wn)
                    (BaseAtom  (BaseEq Pos (BaseFun f vs s) (BaseFun f vs' s)))
                    --> 
                    -- ( v1 = w1 /\ .. /\ vN = wN )
                    foldl1 (/\) [ BaseAtom (BaseEq Pos v v') | (v,v') <- vs `zip` vs' ]
                  where vs  = zipWith ($) vars as
                        vs' = zipWith ($) (drop (length vs) vars) as

        disjointess (DataType s ctors) = [ disj f f' | (f,f') <- subs2 ctors  ]
                where 
                  subs2 :: [a] ->[(a,a)]
                  subs2 []   = []
                  subs2 (a:[]) = []
                  subs2 (a:xs) = (fmap (a,) xs) ++ subs2 xs
                  disj (f, Function as _) (f', Function bs _) 
                      = universalClosure $ BaseAtom $ BaseEq Neg (BaseFun f aVars s) (BaseFun f' bVars s)
                    where 
                       aVars = zipWith ($) vars as
                       bVars = zipWith ($) (drop (length as) vars) bs
        vars = [ \sort -> BaseVar (Id $ "x" ++ show i) sort | i <- [0..] ]

        reflIndAxiom :: DataType -> MirForm
        reflIndAxiom (DataType sort ctors) = forall phi ( 
            conj [ premise c | c <- ctors ] 
              --> forall x (true phi x)
            )
          where 
            premise :: FunDecl -> MirForm
            premise (f, Function as _) = foralls xs $ conj [ true phi x | x <- xs, let BaseVar _ a = x,  a == sort ] --> true phi (BaseFun f xs sort)
                  where xs = [ BaseVar (Id ("x" ++ show i)) a | (i, a) <- [0..] `zip` as ]

            true :: MirTerm -> MirTerm -> MirForm
            true phi x = tPush sort tEmpty (tVar0 sort) x |= phi
            conj [] = BaseCon0 Top
            conj xs = foldl1 (/\) xs
            x   = BaseVar (Id "x"  ) sort  :: MirTerm
            phi = BaseVar (Id "phi") rForm :: MirTerm

    -- TODO make sure theory algebra axioms are added

foralls :: [MirTerm] -> MirForm -> MirForm
foralls = foldr ((.) . forall) id
-- foralls [] = id
-- foralls (x:rest) = forall x . foralls rest

forall :: MirTerm -> MirForm -> MirForm
forall (BaseVar x s) = BaseQuant Universal x s 


safeInductive :: Theory -> Result MirTheory
safeInductive t = theoryInf t <&> mirInductive
