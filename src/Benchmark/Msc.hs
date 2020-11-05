
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Benchmark.Msc (
    reflAxBenchmarks
  , reflAxTheories
  , reflConjBenchmarks
  , indBenchmarks
  , reflConjTheories
  , allTheories
  -- , allSolvers
  -- , MscSolver(..)
  , mtTex
  , mtId
  , mtTheory
  , MscTheory(..)
  , MscBenchmark(..)
  , ReflAxBenchmark(..)
  , ReflConjBenchmark(..)
  , IndBenchmark(..)
  ) where

import Data.List
import Data.List.HT
import Data.List.Index
import System.Process
import System.Directory
import Data.Time
import System.Console.ANSI
import Text.Read
--
import Prelude hiding (succ, (||), (&&), (.))
import Util
import Control.Lens hiding (to, indexed)
import Data.Formula
import Control.Monad
import Data.Composition
import Data.Formula.Sugar
import qualified Data.Theory (benchmarkInf)
import Data.Theory.RobinsonsQ
import Data.Theory.Lists
import qualified Data.Theory.RobinsonsQ as Q
import Data.Theory.ReflectiveNew
import Data.Theory.Inductive
import Data.Signature
import Data.Char
import Data.Formula.Mir
import Data.Formula
import ToTff
import Text.Printf
import Data.Theory.Interpreted 
import Control.Category
import Data.Solvers         hiding (Benchmark, MirBenchmark(..), bTheory, bConjecture)
import Data.Solvers.Vampire 
import Debug.Trace
import Benchmark (BenchGroup(..))
import ToTex
import Data.List
import Text.Printf
import Data.Theory.RobinsonsQ
import Parse.QQ
import Data.Monoid
import Data.Solvers.Msc

class MscBenchmark a where 
  resultsFileId :: a -> String
  getSolvers :: a -> [AnySolver]
  mscId :: a -> String
  toMirBenchmark    :: a -> MirBenchmark


-----------------------------------------------------------------------------------------------------------

data MscTheory = MscTheory {
        _mtId     :: String
      , _mtTheory :: Theory
      } | MscTheoryUnion [MscTheory]
      deriving (Eq)

mtTex :: MscTheory -> String
mtTex t@(MscTheory _ _)   = thFmt $ _mtId  t
mtTex (MscTheoryUnion ts) = ensuremath $ intercalate " + " (fmap mtTex ts)

mtId :: MscTheory -> String
mtId t@(MscTheory _ _)   = _mtId  t
mtId (MscTheoryUnion ts) = intercalate "+" (fmap mtId ts)

mtTheory :: MscTheory -> Theory
mtTheory t@(MscTheory _ _)   = _mtTheory t
mtTheory (MscTheoryUnion ts) = foldl1 (<>) (fmap mtTheory ts)

instance Semigroup MscTheory where 
  t@(MscTheory _ _) <> t'@(MscTheory _ _) = MscTheoryUnion [t,t']
  MscTheoryUnion ts <> t @(MscTheory _ _) = MscTheoryUnion (nub $ ts <> [t])
  t@(MscTheory _ _) <> MscTheoryUnion ts  = MscTheoryUnion (nub $[t] <> ts )
  MscTheoryUnion ts <> MscTheoryUnion ts' = MscTheoryUnion (nub $ ts <> ts')

allTheories :: [MscTheory]
allTheories = nub $ atomic =<< reflAxTheories ++ reflConjTheories ++ indTheories
  where atomic t@(MscTheory _ _)   = [t]
        atomic (MscTheoryUnion ts) = ts >>= atomic

---------------------------------------------- theories

natDef = [theory| inductive s.
                  inductive zero.
                  zero : nat.
                  s    : nat -> nat.  |]


defNat =  MscTheory {
          _mtId = "N"
        , _mtTheory = [theory| 
                               inductive s.
                               inductive zero.
                               zero : nat.
                               s    : nat -> nat.  
                               -- forall x. s(x) /= zero().
                               -- forall x,y. (s(x) = s(y) <-> x = y).
                             |]
        }

defIdNat = MscTheory {
    _mtId   = "Id"
  , _mtTheory = [theory| 
      id : nat -> nat.
      forall   x. id(x) = x.
    |]
  }

defAdd = MscTheory {
    _mtId     = "Add"
  , _mtTheory = [theory| 
      + : (nat,nat) -> nat.
      forall   y. zero() + y = y.
      forall x,y.   s(x) + y = s(x + y). 
    |]
  }

defMul = MscTheory {
    _mtId     = "Mul"
  , _mtTheory = [theory| 
      * : (nat,nat) -> nat.
      forall   y. zero() * y = zero().
      forall x,y.   s(x) * y = y + (x * y).
    |]
  }

defLeq = MscTheory {
    _mtId     = "Leq"
  , _mtTheory = [theory| 
      <= : P(nat,nat).
      forall x   .  x <= x.
      forall x, y. (x <= y -> x <= s(y)).  
    |]
  }

defEpsilon = MscTheory {
          _mtId     = "E"
        , _mtTheory = [theory| 
              p : P(alpha).
              q : P(alpha).
              r : P(alpha).
              a : alpha.
              b : alpha.
              c : alpha.
          |]
        }

defAllEq = MscTheory {
      _mtId     = "Eq"
    , _mtTheory = [theory|
            equal : P(nat, nat, nat).
            forall. ( equal(zero(), zero(), zero()) <-> true ).
            forall. ( equal(zero(), s(y)  , z     ) <-> false).
            forall. ( equal(zero(), y     , s(z)  ) <-> false ).
            forall. ( equal(s(x)  , zero(), z     ) <-> false ).
            forall. ( equal(s(x)  , y     , zero()) <-> false ).
            forall. ( equal(s(x)  , s(y)  , s(z)  ) <-> equal(x,y,z)). 
            |]
    }


defList =  defNat <> MscTheory {
      _mtId     = "L"
    , _mtTheory = [theory|
          inductive cons.
          inductive nil.
          nil  : ()         -> lst.
          cons : (nat, lst) -> lst.
          |]
    }

defAppend = MscTheory {
      _mtId     = "App"
    , _mtTheory = [theory|
          ++ : (lst, lst)    -> lst.
          forall . nil()      ++ r = r             .
          forall . cons(a, l) ++ r = cons(a, l ++ r).
          |]
    }

defPrefix = MscTheory {
      _mtId     = "Pref"
    , _mtTheory = [theory|
          pref : P(lst, lst).
          forall .   pref(nil()     , x         ).
          forall . ~ pref(cons(a, x), nil()     ).
          forall .(pref(cons(a, x), cons(b, y)) <-> (a = b /\ pref(x,y))).
          |]
    }

defRev = MscTheory {
      _mtId     = "Rev"
    , _mtTheory = [theory|
                  rev : lst -> lst.
                  forall. rev(nil()) = nil().
                  forall. rev(cons(x,xs)) = rev(xs) ++ cons(x,nil()).
          |]
    }

defRevAcc = MscTheory {
      _mtId     = "Rev'"
    , _mtTheory = [theory|
                  rev'  : lst -> lst.
                  forall. rev'(x) = revAcc(x,nil()).

                  revAcc : (lst,lst) -> lst.
                  forall. revAcc(nil()     , acc) = acc.
                  forall. revAcc(cons(x,xs), acc) = revAcc(xs, cons(x,acc)). 
          |]
    }



ctAdd = defNat <> defAdd
ctMul = ctAdd <> defMul
ctLeq = defNat <> defLeq
ctLeqAdd = ctLeq <> defAdd
ctAppend = defList <> defAppend
ctPref       = defList <> defPrefix
ctPrefAppend = ctPref <> defAppend

ctAllEq = defNat <> defAllEq

-----------------------------------------------------------------------------------------------------------

data ReflAxBenchmark = ReflAxBenchmark {
    raTheory :: MscTheory
  , raIdx    :: Int
  } deriving (Eq)

reflAxBenchmarks :: [ReflAxBenchmark]
reflAxBenchmarks = reflAxTheories >>= axBenchmarks
  where axBenchmarks :: MscTheory -> [ReflAxBenchmark]
        axBenchmarks t = [ ReflAxBenchmark t i | (i, _) <- [0..] `zip` thAxioms (mtTheory t) ]

instance MscBenchmark ReflAxBenchmark where 
  resultsFileId _ = "reflAx"
  mscId ra = printf "%s-ax%d" (mtId (raTheory ra)) (raIdx ra)
  getSolvers _ = filter supportsFullFol allSolvers 
  toMirBenchmark (ReflAxBenchmark th i) = toMirBenchmark $ 
     ReflConjBenchmark { 
         rcTheory = th
       , rcId     = undefined
       , rcConj   = thAxioms ( mtTheory th) !! i 
     }

reflAxTheories :: [MscTheory]
reflAxTheories = [ ctLeqAdd <> defMul , ctPrefAppend ]

------------------------------------------------------------------------------------------------------------

data ReflConjBenchmark = ReflConjBenchmark {
    rcTheory :: MscTheory
  , rcId     :: String
  , rcConj   :: Formula
  }

reflConjBenchmarks :: [ReflConjBenchmark]
reflConjBenchmarks =  [

    ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "eqRefl"
    , rcConj = [formula| forall x: alpha. x = x |]
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "eqTrans"
    , rcConj = [formula| forall x, y, z: alpha. (x = y /\ y = z -> x = z) |]
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "excludedMiddle-0"
    , rcConj = [formula|           p(a()) \/ ~p(a()) |]
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "excludedMiddle-1"
    , rcConj = [formula| forall x. (p(x) \/ ~p(x)) |]
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "universalInstance"
    , rcConj = [formula| forall x.  p(x) -> p(a())  |]
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "contraposition-0"
    , rcConj = [formula| (p(a()) -> q(b()) <-> ~q(b()) -> ~p(a()))  |] 
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "contraposition-1"
    , rcConj = [formula| forall x, y.  (p(x) -> q(y) <-> ~q(y) -> ~p(x))  |] 
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "currying-0"
    , rcConj = [formula| (p(a()) /\ q(b()) -> r(c()) <-> p(a()) -> (q(b()) -> r(c())) ) |] 
    }

  , ReflConjBenchmark {
      rcTheory = defEpsilon
    , rcId     = "currying-1"
    , rcConj = [formula| forall x, y, z.  (p(x) /\ q(y) -> r(z) <-> p(x) -> (q(y) -> r(z)) ) |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd
    , rcId     = "addGround-0"
    , rcConj = [formula| 1() + 2() = 3() |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd
    , rcId     = "addGround-1"
    , rcConj = [formula| 8() + 5() = 13() |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd
    , rcId     = "addExists"
    , rcConj = [formula| exists x . 8() + x = 13() |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd
    , rcId     = "existsZeroAdd"
    , rcConj = [formula| exists z . forall x. z + x = x |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd <> defMul
    , rcId     = "mulGround"
    , rcConj = [formula| 3() * 4() = 12() |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd <> defMul
    , rcId     = "mulExists"
    , rcConj = [formula| exists x. 3() * x = 12() |] 
    }

  , ReflConjBenchmark {
      rcTheory = defNat <> defAdd <> defMul
    , rcId     = "existsZeroMul"
    , rcConj = [formula| exists z. ( forall x. z * x = z ) |] 
    }

  , ReflConjBenchmark {
      rcTheory = ctAppend
    , rcId     = "appendGround-0"
    , rcConj = [formula| nil() ++ cons(7(), nil()) = cons(7(), nil()) |] 
    }

  , ReflConjBenchmark {
      rcTheory = ctAppend
    , rcId     = "appendGround-1"
    , rcConj = [formula| cons(3(), nil()) ++ cons(7(), nil()) = cons(3(), cons(7(), nil())) |] 
    }

  , ReflConjBenchmark {
      rcTheory = ctAppend
    , rcId     = "appendExists"
    , rcConj = [formula| exists x. cons(3(), nil()) ++ x = cons(3(), cons(7(), nil())) |] 
    }

  , ReflConjBenchmark {
      rcTheory = ctAppend
    , rcId     = "existsNil"
    , rcConj = [formula| exists n . n ++ cons(7(), nil()) = cons(7(), nil()) |] 
    }

    -- TODO make sure constructor disjointness axiom is added
  ]

compile = unwrap . Data.Theory.benchmarkInf . mapTerms transNumeral
  where transNumeral t@(BaseFun (Id a) [] s) =
            case readMaybe a :: Maybe Int of 
                Just x  -> numeral x
                Nothing -> t
        transNumeral t = t
        numeral 0 = BaseFun zero [] Nothing
        numeral n | n > 0 = BaseFun succ [ numeral (n-1) ] Nothing

instance MscBenchmark ReflConjBenchmark where  
  resultsFileId _ = "reflConj"
  mscId = rcId
  getSolvers _ = filter supportsFullFol allSolvers 
  toMirBenchmark rc@(ReflConjBenchmark _ _ _) = 
                  Benchmark {
                    bTheory     = refl (bTheory     mir)
                  , bConjecture = refl (bConjecture mir)
                  }
        where mir = compile $ 
                Benchmark {
                  bTheory     = mtTheory th
                , bConjecture = c
                }
              th = rcTheory rc
              c  = rcConj   rc

reflConjTheories :: [MscTheory]
reflConjTheories = nub $ fmap rcTheory reflConjBenchmarks

------------------------------------------------------------------------------------------------------------

data IndBenchmark = IndBenchmark {
    iTheory :: MscTheory
  , iId     :: String
  , iConj   :: Formula
  }

indBenchmarksSanity = [

    -- sanity tests
      IndBenchmark {
        iTheory = defNat
      , iId     = "inj-nat"
      , iConj   = [formula| forall. (s(x) = s(y) -> x = y) |]
    }
    , IndBenchmark {
        iTheory = defList
      , iId     = "inj-list"
      , iConj   = [formula| forall. (cons(a,x) = cons(a', x') -> (a = a' /\ x = x')) |]
    }

    , IndBenchmark {
        iTheory = defNat
      , iId     = "disj-nat"
      , iConj   = [formula| forall. (s(x) /= zero()) |]
    }
    , IndBenchmark {
        iTheory = defList
      , iId     = "disj-list"
      , iConj   = [formula| forall. (cons(a,x) /= nil()) |]
    }

  ]

indBenchmarks :: [IndBenchmark]
indBenchmarks = [

    -- commut
      IndBenchmark {
        iTheory = ctAdd
      , iId     = "addCommut"
      , iConj   = [formula| forall. x + y = y + x |]
    }
    , IndBenchmark {
        iTheory = ctMul
      , iId     = "mulCommut"
      , iConj   = [formula| forall. x * y = y * x |]
    }

    -- assoc
    , IndBenchmark {
        iTheory = ctAdd
      , iId     = "addAssoc"
      , iConj   = [formula| forall. x + (y + z) = (x + y) + z |]
    }
    , IndBenchmark {
        iTheory = ctMul
      , iId     = "mulAssoc"
      , iConj   = [formula| forall. x * (y * z) = (x * y) * z |]
    }

    -- neutral
    , IndBenchmark {
        iTheory = ctAdd
      , iId     = "addNeutral"
      , iConj   = [formula| forall. x + zero() = x |]
    }
    -- , IndBenchmark {
    --     iTheory = ctAdd
    --   , iId     = "addNeutral-1"
    --   , iConj   = [formula| forall. zero() + x = x |]
    -- }

    , IndBenchmark {
        iTheory = ctMul
      , iId     = "addNeutral-0"
      , iConj   = [formula| forall. x * 1() = x |]
    }
    , IndBenchmark {
        iTheory = ctMul
      , iId     = "addNeutral-1"
      , iConj   = [formula| forall. 1() * x = x |]
    }

    -- mul zero
    , IndBenchmark {
        iTheory = ctMul
      , iId     = "mulZero"
      , iConj   = [formula| forall. x * zero() = zero() |]
    }
    -- , IndBenchmark {
    --     iTheory = ctMul
    --   , iId     = "mulZero-1"
    --   , iConj   = [formula| forall. zero() * x = zero() |]
    -- }

    -- ditributicity
    , IndBenchmark {
        iTheory = ctMul
      , iId     = "distr-0"
      , iConj   = [formula| forall. x * (y + z) = (x * y) + (x * z) |]
    }
    , IndBenchmark {
        iTheory = ctMul
      , iId     = "distr-1"
      , iConj   = [formula| forall. (y + z) * x = (y * x) + (z * x) |]
    }

    -- -- leq add
    -- , IndBenchmark {
    --     iTheory = ctLeq
    --   , iId     = "leqRefl"
    --   , iConj   = [formula| forall. x <= x |]
    -- } 
    , IndBenchmark {
        iTheory = ctLeq
      , iId     = "leqTrans"
      , iConj   = [formula| forall . (x <= y /\ y <= z -> x <= z) |]
    } 

    , IndBenchmark {
        iTheory = ctLeq
      , iId     = "zeroMin"
      , iConj   = [formula| forall. zero() <= x |]
    }

    , IndBenchmark {
        iTheory = ctLeqAdd
      , iId     = "addMonoton-0"
      , iConj   = [formula| forall. x <= ( x + y ) |]
    }

    , IndBenchmark {
        iTheory = ctLeqAdd
      , iId     = "addMonoton-1"
      , iConj   = [formula| forall. x <= ( x + x ) |]
    }


    -- identity
    , IndBenchmark {
        iTheory = ctAdd <> defIdNat
      , iId     = "addCommutId"
      , iConj   = [formula| forall. id(x) + y = y + x |]
    } 

      -- ==================== lists ==================== -- 
      -- concat
    , IndBenchmark {
        iTheory = ctAppend
      , iId     = "appendAssoc"
      , iConj   = [formula| forall. x ++ (y ++ z) = (x ++ y) ++ z |]
    }

      -- prefix concat
    , IndBenchmark {
        iTheory = ctPrefAppend
      , iId     = "appendMonoton"
      , iConj   = [formula| forall x, y. pref(x, x ++ y) |]
    }

    -- , IndBenchmark {
    --     iTheory = ctPref
    --   , iId     = "nilMin"
    --   , iConj   = [formula| forall x. pref(nil(), x) |]
    -- }

      -- ==================== NUMBERS ==================== -- 

  , IndBenchmark {
      iTheory = ctAllEq
    , iId     = "allEqRefl"
    , iConj   = [formula| forall. equal(x,x,x) |]
  }

  , IndBenchmark {
      iTheory = ctAllEq
    , iId     = "allEqDefsEquality"
    , iConj   = [formula| forall. (equal(x,y,z) <-> x = y /\ y = z) |]
  } 


      -- reversing
  , IndBenchmark {
      iTheory = defList <> defAppend <> defRev
    , iId     = "revSelfInvers"
    , iConj   = [formula| forall. rev(rev(x)) = x |]
  }

  , IndBenchmark {
      iTheory = defList<> defAppend <> defRev 
    , iId     = "revAppend-0"
    , iConj   = [formula| forall. x ++ (rev(x) ++ x) = (x ++ rev(x)) ++ x |]
  }

  , IndBenchmark {
      iTheory = defList <> defAppend <> defRev 
    , iId     = "revAppend-1"
    , iConj   = [formula| forall. rev(x ++ (x ++ x)) = rev((x ++ x) ++ x) |]
  }

  , IndBenchmark {
      iTheory = defList <> defAppend <> defRev <> defRevAcc
    , iId     = "revsEqual"
    , iConj   = [formula| forall. rev(x) = rev'(x) |]
  } 

  ]

instance MscBenchmark IndBenchmark where 
  resultsFileId _ = "inductive"
  mscId = iId
  getSolvers _ = indSolvers
  toMirBenchmark i@(IndBenchmark _ _ _) = compile $ 
                Benchmark {
                  bTheory     = mtTheory th
                , bConjecture = c
                }
              where th = iTheory i
                    c  = iConj i

indTheories :: [MscTheory]
indTheories = fmap iTheory indBenchmarks

-- -----------------------------------------------------------------------------------------------------------
--
-- data MscSolver = MscSolver {
--     msSolver            :: AnySolver
--   , msSupportsInduction :: Bool
--   , msTex               :: String
--   }
--
-- allSolvers :: [MscSolver]
-- allSolvers = undefined

-----------------------------------------------------------------------------------------------------------


-- TEX helpers

ensuremath :: String -> String 
ensuremath = printf "\\ensuremath{%s}"

mathcal = ensuremath . ("\\mathcal{" ++) . (++"}")

-- opTheory s = ensuremath ("(" ++ s ++ ")")

thFmt :: String -> String 
thFmt s = "\\theoryFmt{"++ s ++ "}"

(.-) :: String -> String -> String
a .- b = a ++ "_{" ++  b  ++ "}"
