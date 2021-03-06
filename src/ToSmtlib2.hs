
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module ToSmtlib2(
  ToSmtlib2(..)
  ) where 

import Util
import Data.Solvers
import Data.List.Index
import Data.Signature
import Data.Formula
import Data.Formula.Mir
import Data.Theory.Interpreted
import Control.Monad
import Data.List
import Data.Maybe
import Data.Semigroup
import Data.Functor
import Control.Applicative

cvt :: ToSmtlib2 a => a -> String
cvt = toSmtlib2

class ToSmtlib2 a where 
  toSmtlib2 :: a -> String

instance ToSmtlib2 MirTheory where
  toSmtlib2 t = unlines $  []
                          ++ (toLisp <$> [
                            [ "set-info" , ":smt-lib-version", "2.6" ]
                          , [ "set-logic" , if dtypes t == [] then "UF" else "UFDT"]
                          , [ "set-info"  , unlines [ ":source |"
                                                    , "Generated by: Johannes Schoisswohl"
                                                    , "Generated on: 2020-12-21"
                                                    , "Application: Replacing structural induction by a conservative extension"
                                                    , "Target solver: CVC4, Vampire, Z3"
                                                    , "Generator: https://github.com/joe-hauns/msc-automating-induction-via-reflection"
                                                    , "Publications: Automated Induction by Reflection ( https://doi.org/10.34726/hss.2020.75342 )"
                                                    ] ++ "|"
                            ]
                            , [ "set-logic" , ":category", "\"crafted\"" ]
                            ])
                          ++ declSorts t
                          ++ [declDtypes t]
                          ++ declFuns t
                          ++ declPreds t
                          ++ ( cvtF <$> thAxioms t )

instance ToSmtlib2 MirBenchmark where 

  toSmtlib2 (Benchmark t conj) = toSmtlib2 t
                          ++ unlines [ 
                            cvtF $ BaseNot conj
                          , toLisp ["check-sat"]
                          ]

cvtF f = toLisp [ "assert", cvt f ]

declSorts  t = [ toLisp ["declare-sort", cvt s, "0"] | s <- uninterpretedSorts t ]
declDtypes t 
  | dtypes t == [] = ""
  | otherwise      = toLisp 
                      [ "declare-datatypes"
                      , toLisp arities
                      , toLisp cons ]
    where arities = [ toLisp [ cvt s, show 0 ] | s <- dtypes t ]
          cons    = [ toLisp [ toLisp ( constructor c as s ) | (c, Function as _) <- ctors t s ] | s <- dtypes t ]
          constructor c as s = [ cvt c ]  ++ [ toLisp [cvt c ++ show i, cvt a] | (i, a) <- indexed as ]  

declFuns  t = [ toLisp [ "declare-fun", cvt f, toLisp (cvt<$>as), cvt a  ] | (f, Function as a) <- functions  t ]
declPreds t = [ toLisp [ "declare-fun", cvt f, toLisp (cvt<$>as), "Bool" ] | (f, Predicate as)  <- predicates t ]

instance ToSmtlib2 SymDec where
  toSmtlib2 (i :::: Srt      ) = toLisp [ "declare-sort", cvt i, "0"]
  toSmtlib2 (i :::: as :-> a ) = toLisp [ "declare-fun", cvt i, toLisp (cvt<$>as), cvt a ]

instance ToSmtlib2 MirForm where
  toSmtlib2 (BaseAtom (BaseEq Pos t1 t2) ) = toLisp [ "=", cvt t1, cvt t2 ]
  toSmtlib2 (BaseAtom (BaseEq Neg t1 t2) ) = cvt (BaseNot (BaseAtom (BaseEq Pos t1 t2) ))
  toSmtlib2 (BaseAtom (BasePred p ts) )    = funPredSmtlib2 p ts
  toSmtlib2 (BaseCon c a1 a2)       = toLisp [ cvt c,  cvt a1, cvt a2] 
  toSmtlib2 (BaseNot a)             = toLisp [ "not",  cvt a ]
  toSmtlib2 (BaseCon0 Bot)          =          "false" 
  toSmtlib2 (BaseCon0 Top)          =          "true" 
  toSmtlib2 f@(BaseQuant q _ _ _) = to f []
    where to (BaseQuant q' v s f) vs | q' == q = to f ((v,s):vs)
          to f vs = toLisp [cvt q, toLisp vs', toSmtlib2 f ]
            where vs' = [ toLisp [cvt v, cvt s] | (v, s) <- reverse vs]


class ToLisp a where
  lisp :: a -> String

instance ToLisp String where
  lisp = id

instance ToLisp a => ToLisp [a] where 
  lisp = par . unwords . fmap lisp

toLisp :: [String] -> String
toLisp = par . unwords 

-- par :: String -> String 
-- par x = join [ "(", x, ")" ]

instance ToSmtlib2 Connective where 
  toSmtlib2 And     = "and"
  toSmtlib2 Or      = "or"
  toSmtlib2 If      = "<="
  toSmtlib2 Implies = "=>"
  toSmtlib2 Iff     = "="

instance ToSmtlib2 MirTerm where
  toSmtlib2 (BaseVar v _ )   = toSmtlib2 v
  toSmtlib2 (BaseFun f ts _) = funPredSmtlib2 f ts

instance ToSmtlib2 Quantifier where
  toSmtlib2 Existential = "exists"
  toSmtlib2 Universal   = "forall"

instance ToSmtlib2 (Id a) where
  toSmtlib2 (Id a) = transOp opName a


funPredSmtlib2 f [] = toSmtlib2 f 
funPredSmtlib2 f ts = toLisp (toSmtlib2 f : (toSmtlib2 <$> ts) )

