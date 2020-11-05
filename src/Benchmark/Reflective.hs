
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
{-# LANGUAGE LambdaCase #-}

module Benchmark.Reflective (runReflBenchmarks, reflBenchmarks) where

import Data.List
import Data.List.HT
import Data.List.Index
import System.Process
import System.Directory
import Data.Time
import System.Console.ANSI
--
import Prelude hiding (succ, (||), (&&), (.))
import Util
import Control.Lens hiding (to, indexed)
import Data.Formula
import Control.Monad
import Data.Composition
import Data.Formula.Sugar
import Data.Theory
import Data.Theory.RobinsonsQ
import Data.Theory.Lists
import qualified Data.Theory.RobinsonsQ as Q
import Data.Theory.ReflectiveNew
import Data.Theory.Inductive
import Data.Signature
import Data.Char
import Data.Formula.Mir
import ToTff
import Text.Printf
import qualified Data.Theory.Interpreted as NewTheory
import Control.Category
import Data.Solvers         hiding (Benchmark, MirBenchmark(..), bTheory, bConjecture)
import Data.Solvers.Vampire 
import Debug.Trace
import Benchmark (BenchGroup(..))
import ToTex


data Benchmark = Benchmark { 
                    bName       :: String
                  , bSignature  :: [SymDec]
                  , bTheory     :: [Formula]
                  , bReflAxioms :: [Formula]
                  , bConjecture :: Formula
                  , bMode       :: RunMode
                  , bLevel      :: Difficulty
                  } 
              | ThBenchmark {
                     tbName       :: String 
                   , tbTheory     :: NewTheory.MirTheory
                   , tbConjecture :: Formula
                   , tbMode       :: RunMode
                   , tbLevel      :: Difficulty
                   }
               | MirBenchmark {
                     bMirName       :: String 
                   , bMirBenchmark  :: NewTheory.MirBenchmark
                   , bMirMode       :: RunMode
                   , bMirLevel      :: Difficulty
                   }
               -- | ThBenchmark { 
               --       tbName       :: String 
               --     , tbTheory     :: Theory 
               --     , tbConjecture :: Formula 
               --     , tbReflAxioms :: [Formula]
               --     , tbMode       :: RunMode
               --     , tbLevel      :: Difficulty
               --     }
                           -- deriving (Eq)

data Difficulty = Easy 
                | Moderate 
                | Hard 
                deriving (Show, Eq)

data RunMode = ProofReflective
             | JustProof 
             deriving (Show, Eq)


toTh :: Benchmark -> Benchmark
toTh b@ MirBenchmark {} = b
toTh b@ ThBenchmark {} = MirBenchmark {
             bMirName       = tbName b       
           , bMirBenchmark  = (benchmarkInf >>> unwrap ) -- (benchmarkInf >>> unwrap >>> refl) 
                          $ NewTheory.Benchmark 
                              (unTheoryInf $ tbTheory b)
                              (tbConjecture b)
           , bMirMode       = tbMode b       
           , bMirLevel      = tbLevel b      
  }
toTh b@ Benchmark {} = MirBenchmark { 
             bMirName       = bName b       
           , bMirBenchmark  = (benchmarkInf >>> unwrap ) -- (benchmarkInf >>> unwrap >>> refl) 
                          $ NewTheory.Benchmark 
                              ( NewTheory.Theory {
                                    NewTheory.thName      = bName b 
                                  , NewTheory.thAxioms    = universalClosure <$> bTheory b
                                  , NewTheory.thSignature = bSignature b
                                  , NewTheory.thDataTypes = [] 
                                } )
                              ( universalClosure $ bConjecture b )
           -- , tbTheory     = unwrap $ theory (bName b) (mkSig $ bSignature b) (Axiom "" . universalClosure <$> bTheory b)
           -- , tbReflAxioms = bReflAxioms b
           -- , tbConjecture = bConjecture b 
           , bMirMode       = bMode b       
           , bMirLevel      = bLevel b      
           }

timeout = Seconds 5

runReflBenchmarks :: IO ()
runReflBenchmarks = sequence_ [ run (toTh b) | b <- benchmarks ] 
-- runBenchmarks = sequence_ [ run (toTh b) | b <- reverse benchmarks ] 
  where run b = case bMirMode b of 
                  ProofReflective -> do
                         proveMir solver timeout (bMirBenchmark b) >>= \case 
                            Valid -> proveMir solver timeout (reflAxNConj b) >>= printRes ""
                            x     -> printRes (colorYellow) x
                  JustProof -> proveMir solver timeout (reflAx b) >>= printRes ""
            where solver = vampireDefault
                  printRes fmt r = do putStr (fmt ++ showB b)
                                      putStr $ showR fmt b $ r
                                      putStrLn $ setSGRCode [ Reset ]
        showB :: Benchmark -> String
        -- showB b = printf "%20.20s: %-150.150s " (bName b) (show $ bConjecture b)
        showB b = printf "%150.150s | %-25.25s " (show $ bMirConjecture b) (bMirName b)
        showR :: String -> Benchmark -> SolverResult -> String
        showR fmt _  Valid    = printf "| %s%s |         " (col Green " ok ") fmt 
        showR fmt _  TimeOut  = printf "| %s%s | timeout " (col Red   "fail") fmt
        showR fmt _ (Error s) = printf "| %s%s | %s"       (col Red   "fail") fmt ( col Red $ s )
        showR fmt _  other    = printf "| %s%s | %s"       (col Red   "fail") fmt ( col Red $ show other )

        colorYellow  = setSGRCode [ SetColor Foreground Vivid Yellow ]
        col c s = setSGRCode [ SetColor Foreground Vivid c ] ++ s ++ setSGRCode [Reset]


nonRefl :: Benchmark -> NewTheory.MirBenchmark 
nonRefl b = 
  case toTh b of 
    b' | bMirMode b' == ProofReflective -> bMirBenchmark b'
    _ -> undefined

reflAxNConj :: Benchmark -> NewTheory.MirBenchmark 
reflAxNConj b = 
  case toTh b of 
    b' | bMirMode b' == ProofReflective -> let (NewTheory.Benchmark th conj) = bMirBenchmark b'
                                           in NewTheory.Benchmark (refl th) (refl conj)
    _ -> undefined

reflAx :: Benchmark -> NewTheory.MirBenchmark 
reflAx b = let (NewTheory.Benchmark th conj) = bMirBenchmark . toTh $ b 
           in NewTheory.Benchmark (refl th)       conj 

bMirConjecture :: Benchmark -> MirForm
bMirConjecture = NewTheory.bConjecture . bMirBenchmark

reflBenchmarks :: [[BenchGroup]]
reflBenchmarks = return $ [ BenchGroup {
                              bgId = (bMirName $ toTh $ b)
                            , bgTex = toTexStr "lalalala"
                            , bgProblems = fmap unBenchmarkInf [ nonRefl     b
                                                               , reflAxNConj b] 

                            } | b <- benchmarks ]

benchmarks :: [Benchmark]
benchmarks =
    -- 1) Conjecture Purely Reflective
      -- TODO: Every conjecture has to be proven as reflective vs non-reflective form
      
      -- a) Tautology          (3)

        -- Name: Eq-Refl
        -- Level: Easy
        -- empty
        -- -------------------------
        -- true( forall' ( v0 ~~~ v0 ))
         Benchmark {
            bName       = "Eq-Refl"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt ]
          , bTheory     = []
          , bReflAxioms = []
          , bConjecture = forallS [x] alpha (x === x)
          }:

        Benchmark {
            bName       = "Eq-Sym"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt ]
          , bTheory     = []
          , bReflAxioms = []
          , bConjecture = forallS [x,y,z] alpha (x === y --> y === x)
          } :

        Benchmark {
            bName       = "Eq-Trans"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt ]
          , bTheory     = []
          , bReflAxioms = []
          , bConjecture = forallS [x,y,z] alpha (x === y /\ y === z --> x === z)
          } :


        Benchmark {
            bName       = "Excluded-Middle"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt 
                          , tid p     :::: Pred [alpha] ]
          , bTheory     = []
          , bReflAxioms = []
          , bConjecture = forall [x] (p!x \/ lnot (p!x))
          } :

        Benchmark {
            bName       = "Contraposition"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt 
                          , tid p     :::: Pred [alpha] 
                          , tid q     :::: Pred [alpha] ]
          , bTheory     = []
          , bReflAxioms = []
          , bConjecture = forall [x,y] (p!x --> q!y <-> lnot(q!y) --> lnot(p!x))
          } :

        Benchmark {
            bName       = "Currying"
          , bMode       = ProofReflective
          , bLevel      = Moderate
          , bSignature  = [ tid alpha :::: Srt 
                          , tid p     :::: Pred [alpha] 
                          , tid q     :::: Pred [alpha] 
                          , tid r     :::: Pred [alpha] ]
          , bTheory     = []
          , bReflAxioms = []
          , bConjecture = forall [x,y,z] (p!x /\ q!y --> r!z <-> p!x --> q!y --> r!z)
          } :

      
      -- b) Axiom              (3)
         -- PA
         -- Lists
         -- Weakest Precondition
 
        benchmarkProofThAxioms robinsonsQ ++  
        benchmarkProofThAxioms lists      ++  
       
      -- c) Consequence        (6)

        ThBenchmark {
            tbName       = "EvalMul-1"
          , tbMode       = ProofReflective
          , tbLevel      = Easy
          , tbTheory     = robinsonsQ 
          , tbConjecture = numeral 2 * numeral 3 === numeral 6
          } :

        ThBenchmark {
            tbName       = "EvalMul-2"
          , tbMode       = ProofReflective
          , tbLevel      = Easy
          , tbTheory     = robinsonsQ 
          , tbConjecture = numeral 6 * numeral 9 === numeral 54
          } :

        ThBenchmark {
            tbName       = "EvalMul-3"
          , tbMode       = ProofReflective
          , tbLevel      = Easy
          , tbTheory     = robinsonsQ 
          , tbConjecture = numeral 6 * numeral 9 =/= numeral 53
          } :

        ThBenchmark {
            tbName       = "EvalMul-4"
          , tbMode       = ProofReflective
          , tbLevel      = Moderate
          , tbTheory     = robinsonsQ 
          , tbConjecture = exists [x] $ numeral 6 * x === numeral 54
          } :

        Benchmark {
            bName       = "TransRelation-1"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt 
                          , tid a     :::: [] :-> alpha
                          , tid b     :::: [] :-> alpha
                          , tid c     :::: [] :-> alpha
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x,y) /\ r!(y,z) --> r!(x,z) 
                          , r!(a!(),b!()) 
                          , r!(b!(),c!())
                          ]
          , bReflAxioms = []
          , bConjecture = r!(a!(),c!())
          } :

        Benchmark {
            bName       = "TransRelation-2"
          , bMode       = ProofReflective
          , bLevel      = Moderate
          , bSignature  = [ tid alpha :::: Srt 
                          , tid a     :::: [] :-> alpha
                          , tid b     :::: [] :-> alpha
                          , tid c     :::: [] :-> alpha
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x,y) /\ r!(y,z) --> r!(x,z) 
                          , r!(a!(),b!()) 
                          , r!(b!(),c!())
                          ]
          , bReflAxioms = []
          , bConjecture = r!(x, a!()) --> r!(x, c!())
          } :

        Benchmark {
            bName       = "TransRelation-3"
          , bMode       = ProofReflective
          , bLevel      = Moderate
          , bSignature  = [ tid alpha :::: Srt 
                          , tid a     :::: [] :-> alpha
                          , tid b     :::: [] :-> alpha
                          , tid c     :::: [] :-> alpha
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x,y) /\ r!(y,z) --> r!(x,z) 
                          , r!(a!(),b!()) 
                          , r!(b!(),c!())
                          ]
          , bReflAxioms = []
          , bConjecture = r!(x, a!()) /\ r!(c!(), y) --> r!(x,y)
          } :

        Benchmark {
            bName       = "Euclidean-1"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt 
                          , tid a     :::: [] :-> alpha
                          , tid b     :::: [] :-> alpha
                          , tid c     :::: [] :-> alpha
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x, y) /\ r!(x, z) --> r!(y,z) 
                          , r!(a!(),b!()) 
                          , r!(a!(),c!())
                          ]
          , bReflAxioms = []
          , bConjecture = r!(c!(),b!())
          } :

        Benchmark {
            bName       = "Euclidean-2"
          , bMode       = ProofReflective
          , bLevel      = Easy
          , bSignature  = [ tid alpha :::: Srt 
                          , tid a     :::: [] :-> alpha
                          , tid b     :::: [] :-> alpha
                          , tid c     :::: [] :-> alpha
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x, y) /\ r!(x, z) --> r!(y,z) 
                          , r!(a!(),b!()) 
                          , r!(a!(),c!())
                          ]
          , bReflAxioms = []
          , bConjecture = r!(b!(),c!()) /\ r!(c!(), b!())
          } :

        Benchmark {
            bName       = "Euclidean-3"
          , bMode       = ProofReflective
          , bLevel      = Moderate
          , bSignature  = [ tid alpha :::: Srt 
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x, y) /\ r!(x, z) --> r!(y,z) ]
          , bReflAxioms = []
          , bConjecture = exists [y] (r!(y,x)) --> r!(x,x)
          } :

        Benchmark {
            bName       = "Euclidean-4"
          , bMode       = ProofReflective
          , bLevel      = Moderate
          , bSignature  = [ tid alpha :::: Srt 
                          , tid r     :::: Pred [alpha, alpha] ]
          , bTheory     = [ r!(x, y) /\ r!(x, z) --> r!(y,z) ]
          , bReflAxioms = []
          , bConjecture = r!(x,y) /\ r!(x,z)  --> exists [u] (r!(y,u) /\ r!(z,u))
          } :

    -- 2) Conjecture Mixed Refl & Non-Refl
      -- a) Tautology          (3)
      -- TODO
      
        -- Name: Excluded-Middle
        -- Level: Easy
        -- p : Pred(alpha)
        -- -------------------------
        -- forall [phi] $ true( phi || not'(phi))
      
        -- Name: Universal-Elimination
        -- Level: Easy
        -- p : Pred(alpha)
        -- -------------------------
        -- forall [phi] (true( phi[x] )) --> p(x)
      
        -- Name: Existential-Introduction
        -- Level: Easy
        -- p : Pred(alpha)
        -- -------------------------
        -- p(x) --> exists [phi] (true( phi[x] )) 

      -- b) Way to reflective   (3) -- TODO (?)
      -- c) After reflective    (3) -- TODO (?)

    -- 3) Reflection Redundant
      -- a) fully redundant    (3)
      -- b) reflection = cut   (3)
 
    -- 4) Cojecture Needs Reflection
      -- a) Simple                (6)

        -- TODO revive this benchmark
        -- Benchmark {
        --     bName       = "Correspondence-1"
        --   , bMode       = JustProof
        --   , bLevel      = Easy
        --   , bSignature  = [ tid alpha :::: Srt 
        --                   , tid r     :::: Pred [alpha, alpha] ]
        --   , bTheory     = [ ]
        --   , bReflAxioms = [forall [x] $ r!(x,x)]
        --   , bConjecture = forall [phi] $ tr $ forall' alpha $ (forall' alpha $ ( r'!(v1, v0) ) ~~> phi!!v0) 
        --                                                     ~~> (forall' alpha $ phi!!v0) 
        --   } :


      -- b) PA                    (3)
        -- associativity
        -- commutativity
        -- 0 neutral
        -- 1 neutral
      -- c) Lists/Trees           (3)
        -- associativity 
        -- append neutral
        -- reverse selfinverse
      -- d) Weakest Precondition  (3)
        -- TODO
        -- number swapping
        -- multiplication program from analysis & verification
  -- ]
  []
  where alpha = Id "alpha" :: SortId

        a     = Id "a" :: FunId
        b     = Id "b" :: FunId
        c     = Id "c" :: FunId

        p     = Id "p" :: PredId
        q     = Id "q" :: PredId
        r     = Id "r" :: PredId

        p' = dot p 
        q' = dot q 
        r' = dot r 

        x     = Id "x" :: VarId
        y     = Id "y" :: VarId
        z     = Id "z" :: VarId
        u     = Id "u" :: VarId

        phi   = BaseVar (Id "phi") Nothing
        psi   = BaseVar (Id "psi") Nothing

        -- v0:v1:_ = var alpha <$> allVars' alpha

        -- v0 = Refl.v0 alpha :: Term
        -- v1 = nxt alpha!v0      :: Term

        numeral 0 = zero!()
        numeral k = succ! (numeral (k-1))
        (*) :: ToTerm a0 => a0 
            -> ToTerm a1 => a1 
            -> Term
        (*) = binary mul

        -- (!!) :: ToTerm a0 => a0 
        --      -> ToTerm a1 => a1 
        --      -> Term
        -- (!!) phi t = Refl.subs alpha phi (Refl.v0 alpha) t

        -- app :: SortId
        --     -> ToTerm a0 => a0 
        --     -> ToTerm a1 => a1 
        --     -> Term
        -- app s phi t = subs s phi (Refl.v0 s) t

        -- (~~~) :: ToTerm a0 => a0 
        --       -> ToTerm a1 => a1 
        --       -> Term
        -- (~~~) = binary (eqR alpha)

        -- unwrap $ theory "Robinsons Q" sig ax
        benchmarkProofThAxioms :: NewTheory.MirTheory -> [ Benchmark ]
        benchmarkProofThAxioms th = [ MirBenchmark {
               bMirName       = NewTheory.thName th ++ "_" ++ show ax
             , bMirBenchmark  = NewTheory.Benchmark th ax
             , bMirMode       = ProofReflective
             , bMirLevel      = Easy
        } | (ax, i) <- NewTheory.thAxioms th `zip` [0..] ]
        -- benchmarkProofThAxioms th
        --     = [Benchmark {
        --           bName       = join [join.words $ th ^.thName, "-", n]
        --         , bMode       = ProofReflective
        --         , bLevel      = Easy
        --         , bSignature  = toDecls $ th ^.thSig
        --         , bTheory     = fromMir . axForm <$> th ^. thAxioms
        --         , bReflAxioms = []
        --         , bConjecture = fromMir f
        --         } | Axiom n f <- th ^.thAxioms ]



