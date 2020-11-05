{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Data.Solvers.Msc (
    allSolvers
  , indSolvers
  -- , MscSolver(..)
  ) where


import Data.Solvers
import Data.Solvers.Z3
import Data.Solvers.Cvc4
import Data.Solvers.Vampire
import Data.Solvers.Zeno
import Data.Solvers.Zipperposition
import ToTex
import Data.Theory.Inductive
import Debug.Trace

-- data MscSolver = MscSolver {
--     msSolver :: AnySolver
--   }

allSolvers :: [AnySolver]
allSolvers = 
    [ AnySolver cvc4
    , AnySolver cvc4gen 
    , AnySolver z3
    ] ++ fmap AnySolver vampireMsc ++
    [ AnySolver zipperposition1
    , AnySolver zipperposition2
    , AnySolver Zeno
    ]


indSolvers = filter supportsInduction $ allSolvers ++ (reflInd =<< allSolvers)
  where reflInd s 
         | supportsFullFol s = [ AnySolver $ ReflInductiveSolver s ]
         | otherwise         = [ ]

newtype ReflInductiveSolver s = ReflInductiveSolver s

instance Solver s => Solver (ReflInductiveSolver s) where
  name     (ReflInductiveSolver s) = name s ++ "''"
  texName  (ReflInductiveSolver s) = texMacroCall "ensuremath" [ texMacroCall "reflIndSolver" [ texName s ] ]
  options  (ReflInductiveSolver s) = options s
  proveMir (ReflInductiveSolver s) t b = proveMir s t (reflInductive b)
  inputFmt (ReflInductiveSolver s) = inputFmt s
  supportsInduction (ReflInductiveSolver s) = True 
  supportsFullFol   (ReflInductiveSolver s) | supportsFullFol s = True


