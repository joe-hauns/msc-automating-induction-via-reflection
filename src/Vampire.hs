
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

module Vampire (proof, Sat(..), VampireOpts(..), VampireOut(..), vprove, vprove', VampireOrdering(..)) where

import Data.List
import Data.List.HT
import Data.List.Index
import System.Process
import System.Directory
import Data.Time
--
import System.Console.ANSI
import Prelude hiding (succ, (||), (&&))
import Util
import Control.Lens hiding (to, indexed)
import Data.Formula
import Control.Monad
import Data.Composition
import Data.Formula.Sugar
import Data.Theory
import qualified Data.Theory.Interpreted as I
import Data.Theory.RobinsonsQ
import qualified Data.Theory.RobinsonsQ as Q
import Data.Theory.Reflective hiding (reflective) -- TODO
import Data.Theory.Inductive hiding (inductive) -- TODO
import qualified Data.Theory.Reflective.Sugar as Refl
import Data.Theory.Reflective.Sugar
import Data.Signature
import Data.Char
import Data.Formula.Mir
import ToTff
import Text.Printf
import Data.Solvers hiding (Valid)
import qualified Data.Solvers as S
import ToSmtlib2

reflective = undefined -- TODO
inductive = undefined -- TODO

data Sat = Valid | Refutable | Other String | TimeLimit deriving (Show, Eq)

data VampireOut  = VampireOut {
                      vSat  :: Sat
                    , vTime :: Double
                    , vIn   :: String
                    , vOut  :: String
                    , vErr  :: String
                    , vArgs :: [String]
                    }

-- vampireBin = "/usr/local/bin/vampire-joe" 
 
instance Show VampireOut where 
  show o = unlines $ [ "result: " ++ show (vSat o) ]
                  ++ sect "stdin" vIn
                  ++ sect "stdout" vOut
                  ++ sect "stderr" vErr
                  where sect h f = [ h ++ ":" ] 
                                ++ (indent $ lines (f o))
                        -- indent lns = [show i ++ ")\t" ++ l | (i, l) <- indexed lns]
                        indent lns = ["\t" ++ l | (i, l) <- indexed lns]

data VampireOpts = VampireOpts { 
                       -- vTimeout :: Int 
                       -- vOrd    :: VampireOrdering
                       vBin    :: String
                     , vOpts   :: [String]
                     }


optsToId :: VampireOpts -> Seconds -> FilePath
optsToId (VampireOpts bin args) (Seconds timeOut) 
    -- = intercalate "_" [ l ++ "-" ++ r | (l,r) <- [ ("bin", bin), ("ord", show ord) , ("to", show timeOut), ("ind", show ind)]]
    = intercalate "_" (bin:args)


data VampireOrdering = Kbo | Lpo deriving (Eq,Show)

vprove' :: VampireOpts -> Seconds -> Theory -> Conjecture -> IO VampireOut
vprove' opts (Seconds timeout) th f 
                 = do (_, out, err) <- readProcessWithExitCode (vBin opts) args problem
                      return $ VampireOut {
                                  vSat  = toSat out
                                , vTime = toTime out
                                , vIn   = problem
                                , vOut  = out
                                , vErr  = err 
                                , vArgs = args
                                }
   where 
         args = [ "-t", show $ timeout
                -- , "-to", fmap toLower $ show $ vOrd opts
                , "-sp", "occurrence" 
                ] -- ++ ind2args (vInduction opts)
         -- args' = [ "--mode", "casc" ]
         vGet :: String -> String -> [String]
         vGet str out =      [ unwords ( drop (length pre) l' ) | l <- lines out  
                                                                , let l' = words l
                                                                , pre `isPrefixOf` l'] 
                              -- xs -> failure $ reverse $ ["multiple alternatives found: "] ++ fmap ("  "++) xs
                    where pre = "%":words str
         toTime out = sum $ read . (unwords . reverse . tail . reverse . words) <$> vGet "Time elapsed:" out 
         toSat out = case vGet "Termination reason:" out of
                        [] -> Other "No Termination Reason found."
                        xs -> case last xs of 
                                "Refutation" -> Valid
                                "Time limit" -> TimeLimit
                                "Refutation not found, non-redundant clauses discarded" -> TimeLimit
                                "Satisfiable"   -> Refutable
                                x               -> Other x
         problem = unlines [ toTff th
                           , toTff f  ]


-- data VampireInduction = VStructuralInduction deriving (Show)
-- ind2args :: Maybe VampireInduction -> [String]
-- ind2args Nothing  = []
-- ind2args (Just x) = ["--induction", arg x ]
--   where arg VStructuralInduction = "struct"

vprove :: VampireOpts -> Seconds -> MirBenchmark -> IO VampireOut
vprove opts (Seconds timeout) bench 
                 = do (_, out, err) <- readProcessWithExitCode (vBin opts) args problem
                      return $ VampireOut {
                                  vSat  = toSat out
                                , vTime = toTime out
                                , vIn   = problem
                                , vOut  = out
                                , vErr  = err 
                                , vArgs = args
                                }
   where 
         args = [ "-t", show $ timeout
                -- , "-to", fmap toLower $ show $ vOrd opts
                , "--input_syntax", "smtlib2"
                ] ++ vOpts opts
                -- ++ ind2args (vInduction opts)
         -- args' = [ "--mode", "casc" ]
         vGet :: String -> String -> [String]
         vGet str out =      [ unwords ( drop (length pre) l' ) | l <- lines out  
                                                                , let l' = words l
                                                                , pre `isPrefixOf` l'] 
                              -- xs -> failure $ reverse $ ["multiple alternatives found: "] ++ fmap ("  "++) xs
                    where pre = "%":words str
         toTime out = sum $ read . (unwords . reverse . tail . reverse . words) <$> vGet "Time elapsed:" out 
         toSat out = case vGet "Termination reason:" out of
                        [] -> Other "No Termination Reason found."
                        xs -> case last xs of 
                                "Refutation" -> Valid
                                "Time limit" -> TimeLimit
                                "Refutation not found, non-redundant clauses discarded" -> TimeLimit
                                "Satisfiable"   -> Refutable
                                x               -> Other x
         problem = toSmtlib2 bench

opts = [ VampireOpts { 
             -- vOrd = ord
             vBin  = bin
           , vOpts = [ "-to", ord ]
           } | ord <- [ "kbo" , "lpo" ] 
             , bin <- if ord == "kbo" then [ "vampire", "vampire-joe" ]
                                      else [ "vampire" ]
            ]

proof :: IO ()
proof = do rs <- forM (indexed scripts) $ \(i,s) -> 
                    do let psName = "ps_" ++ show i
                       putStrLn "================================================================"
                       putStrLn $ "== script: " ++ psName
                       putStrLn "================================================================"
                       forM opts $ \o -> 
                         do r <- runPs o timeout s 
                            writePs ("proofscripts/" ++ psName ++ "/" ++ optsToId o timeout) r
                            return (o, r)

           forM_ (transpose rs) $ \rs ->
             do let id = (optsToId $ fst $ head $ rs) timeout
                putStrLn $ printf "%s: %d steps" id $ sum $ fmap (length . filter ((== Valid) . vSat) . psVampires . snd) rs
      where timeout = Seconds 1


scripts = []
      ++ psPA
      ++ psQ
      ++ psEmpty
      ++ psSimple
      ++ psSimple2
      ++ psTruth

psTruth  :: [ProofScript]
psTruth  = unwrap . compilePs th <$> [
    -- [ 
    --   forall [x] (tr x --> )
    -- ]  
  ]
  where 
        th = inductive [Q.zero, Q.succ] $ robinsonsQ 

        a `and` b = lnot (lnot a \/ lnot b)

        lemma1 x = x + zero  === zero  + x
        lemma1' x = ( x `add` zero' )  ~~~ ( zero' `add` x )
        add = binary (refl sig Q.add) 

        induction :: (Term -> Formula) -> Formula
        induction phi = phi zero /\ forall [n] ( phi (trm n) --> phi (s n))  --> forall [n] ( phi (trm n) )
          where n = Id "n" :: VarId

        induction' :: (Term -> Formula) -> Formula
        induction' phi = fromMir $  unwrap $ reflForm sig $ unwrap $ mirForm th $ induction phi
        sig = th ^.thSig
        (+) = binary Q.add 
        zero =  nullary Q.zero
        zero' = nullary (refl sig Q.zero)
        v0 = Refl.v0 nat
        v1 = nVarR nat ! v0
        var0 = var nat v0
        var1 = var nat v1
        subs  v t phi = Refl.subs nat phi v t 
        trm = to
        
        val x = eval nat ! x
        t   = Id "t"   :: VarId
        phi = Id "phi" :: VarId


psPA  :: [ProofScript]
psPA  = unwrap . compilePs th <$> [
    [ 
      forall [x,y]              $ tr $ subs v0 (trm y)  $ (s' x    ~~~ s' var0)    ~~> ( trm x ~~~ var0 ),
      tr $ forall' nat $ forall' nat $ (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 )
    ]  
    , [ 
      forall [x,y]              $ tr $ subs v0 (trm y)  $ (s' x    ~~~ s' var0)    ~~> ( trm x ~~~ var0 ),
      forall [x  ]              $ tr $ forall' nat $ (s' x    ~~~ s' var0)    ~~> ( trm x ~~~ var0 ),
      tr $ forall' nat $ forall' nat $ (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 )
    ] 
    , [ 
      forall [x]              $ tr $ forall' nat $ (s' x    ~~~ s' var0)    ~~> ( trm x ~~~ var0 ),
      tr $ forall' nat $ forall' nat $ (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 )
    ] 
    , [ 
      tr $ forall' nat $ forall' nat $ (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 )
    ] 
    , [
      forall [phi]     $ tr (forall' nat                phi                    ) <-> forall [t] (tr $ subs v0 (trm t) $               phi                  )
    ,                    tr (forall' nat (lemma1' var0  ~~> lemma1' (s' var0)) ) <-> forall [t] (tr $ subs v0 (trm t) $ lemma1' var0  ~~> lemma1' (s' var0))
    ]
    , [
                     zero  + zero  === zero  + zero   
    , forall [x]   $ trm x + zero  === zero  + trm x 
                 -->   s x + zero  === zero  + s x    
    , forall [phi]     $ tr (forall' nat                phi                    ) <-> forall [t] (tr $ subs v0 (trm t) $               phi                  )
    ,                    tr (forall' nat (lemma1' var0  ~~> lemma1' (s' var0)) ) <-> forall [t] (tr $ subs v0 (trm t) $ lemma1' var0  ~~> lemma1' (s' var0))
    , induction' (\x -> x + zero  === zero  + x )   -- = tr $ (lemma1' zero' && forall' nat (lemma1' var0 ~~> lemma1' (s' var0))) ~~> forall' nat (lemma1' var0),
         ,                  tr (not' $ lemma1' zero') \/ tr (not' ( forall' nat (lemma1' var0 ~~> lemma1' (s' var0)) ) ) \/ tr ( forall' nat (lemma1' var0) )
         ,                (lnot . tr) (lemma1' zero') \/ (lnot . forall [t] . tr) (lemma1' (trm t) ~~> lemma1' (s' t))      \/ tr ( forall' nat (lemma1' var0) )
         ,                (lnot     ) (lemma1  zero ) \/ (lnot . forall [t] . tr) (lemma1' (trm t) ~~> lemma1' (s' t))      \/ tr ( forall' nat (lemma1' var0) )
         ,                (lnot     ) (lemma1  zero ) \/ (lnot . forall [t] . tr) (lemma1' (trm t) ~~> lemma1' (s' t))      \/ forall [x] ( lemma1 (trm x) )

    -- , (lemma1 zero `and` forall [x] (lemma1 (trm x) --> lemma1 (s (trm x)))) --> forall [x] ( lemma1 (trm x) )
    , lemma1 zero /\ forall [x] (lemma1 (trm x) --> lemma1 (s x)) --> forall [x] ( lemma1 (trm x) )
    -- , induction (\x -> x + zero  === zero  + x ) 
    -- , forall [x]   $ trm x + zero  === zero  + trm x  
    -- , forall [x]   $ trm x + zero  === zero  + trm x  
    -- , forall [x,y] $ trm x + trm y === trm y + trm x
    ]
  ]
  where 
        th = inductive [Q.zero, Q.succ] $ robinsonsQ 

        a `and` b = lnot (lnot a \/ lnot b)

        lemma1 = (\x -> x + zero  === zero  + x )
        lemma1' = (\x -> ( x `add` zero' )  ~~~ ( zero' `add` x ) )
        add = binary (refl sig Q.add)

        induction :: (Term -> Formula) -> Formula
        induction phi = phi zero /\ forall [n] ( phi (trm n) --> phi (s n))  --> forall [n] ( phi (trm n) )
          where n = Id "n" :: VarId

        induction' :: (Term -> Formula) -> Formula
        induction' phi = fromMir $  unwrap $ reflForm sig $ unwrap $ mirForm th $ induction phi
        sig = th ^.thSig
        -- induction' phi = phi zero && forall [n] ( phi (trm n) ~~> phi (s' n))  ~~> forall' nat ( phi (trm n) )
        --   where n = Id "n" :: VarId
        (+) = binary Q.add 
        zero = nullary Q.zero
        zero' = nullary $ refl sig Q.zero
        v0 = Refl.v0 nat
        v1 = nVarR nat ! v0
        var0 = var nat $ v0
        var1 = var nat $ v1
        subs  v t phi = Refl.subs nat phi v t 
        trm = to
        
        val x = eval nat ! x
        t   = Id "t"   :: VarId
        phi = Id "phi" :: VarId

s :: forall a. ToTerm a => a -> Term
s = unary succ 
s' :: forall a. ToTerm a => a -> Term
s' = unary (dot succ)

psQ  :: [ProofScript]
psQ  = unwrap . compilePs (reflective $ robinsonsQ ) <$> [
    [ 
      forall [x,y]              $ tr $ subs v0 (trm y)  $ (s' x    ~~~ s' var0)    ~~> ( trm x ~~~ var0 ),
      tr $ forall' nat $ forall' nat ( (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 ) )
    ] , 
    [ 
      forall [x,y]              $ tr $ (s' x    ~~~ s' y)    ~~> ( trm x ~~~ trm y ),
      forall [x,y]              $ tr $ subs v0 (trm y)  $ (s' x    ~~~ s' var0)    ~~> ( trm x ~~~ var0 ),
      tr $ forall' nat $ forall' nat ( (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 ) )
    ] , 
    [ 
      forall [x,y]              $ tr $ (s' x    ~~~ s' y)    ~~> ( trm x ~~~ trm y ),
      tr $ forall' nat $ forall' nat ( (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 ) )
    ] , 
    [ 
      -- forall [x,y]              $ tr $ subs v0 (trm y)  $ (s' var1    ~~~ s' var0)    ~~> ( var1 ~~~ var0 ),
      -- forall [x,y] $ tr $ subs v1 (trm y) $ ( (s' var1 ~~~ s' x) ~~> ( var1 ~~~ trm x ) ) ,
      -- forall [x] $ tr $ forall' nat ( (s' var1 ~~~ s' x) ~~> ( var1 ~~~ trm x ) ) ,
      forall [x,y] $ tr $ subs v0 (trm y) ( (s' x ~~~ s' var0) ~~> ( trm x ~~~ var0 ) ) ,
      forall [x] $ tr $ forall' nat ( (s' x ~~~ s' var0) ~~> ( trm x ~~~ var0 ) ) ,
      -- forall [x] $ tr $ subs v0 (trm x) $ forall' nat ( (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 ) ) ,
      tr $ forall' nat $ forall' nat ( (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 ) )
    ]  
    , [ 
      -- forall [x,y] ( ( tr (s' x ~/~ s' y) ) \/ tr (to x ~~~ to y)  ),
      tr $ forall' nat $ forall' nat ( (s' var1 ~~~ s' var0) ~~> ( var1 ~~~ var0 ) )
    ]
  ]
  where 
        v0 = Refl.v0 nat
        v1 = nVarR nat ! v0
        var0 = var nat $ v0
        var1 = var nat $ v1
        subs  v t phi = Refl.subs nat phi v t 
        trm = to
        
        val x = eval nat ! x
        t   = Id "t"   :: VarId

psEmpty :: [ProofScript]
psEmpty = unwrap . compilePs thry <$> [
          [ 
          -- fails
            tr $ forall' nat $ ( var0 ~~~ z' ) ~~> ( var0 ~~~  z' ) 
          ] , [ 
            -- fails
            forall [x] (  tr ( x ~/~ z' ) \/ tr ( x ~~~  z' )  ) 
          , tr $ forall' nat $ ( var0 ~~~ z' ) ~~> ( var0 ~~~  z' )
          ] , [ 
          -- works
            forall [x] (  tr ( ( x ~/~ z' ) || ( x ~~~  z' ) )  )
          , tr $ forall' nat $ ( var0 ~~~ z' ) ~~> ( var0 ~~~  z' )
          ] ,[ 
          -- works: minimal change from goal
            forall [x]  $ tr $ sbs ( ( var0 ~~~ z' ) ~~> ( var0 ~~~  z' ) )
          , tr $ forall' nat $ ( var0 ~~~ z' ) ~~> ( var0 ~~~  z' )
          ] ,[ 
          -- works.
            forall [x]  $ tr $ (   x  ~~~ z' ) ~~> (   x  ~~~  z' ) 
          , tr $ forall' nat $ ( var0 ~~~ z' ) ~~> ( var0 ~~~  z' )
          ]
        ]
  where vr0 = v0 nat
        var0 = var nat            $ v0 nat
        var1 = var nat $ nVarR nat ! ( v0 nat )
        -- sbsT f = subsT f vr0 x
        sbs  f = subs  f vr0 x
        subs = Refl.subs nat 
        -- subsT = Refl.subsT nat nat

        thry    = reflective $ unwrap 
                  $ theory "Empty" (
                       mkSig [  tid z  :::: []      :-> nat  ]
                   ) [] 
        nat = Id "nat"
        val x = eval nat ! x
        x   = Id "x"   :: VarId
        y   = Id "y"   :: VarId
        z   = Id "z"   :: FunId
        z'   = (Id "z_" :: FunId) !() 


psSimple2 :: [ProofScript]
psSimple2 = [
          ps  (reflThry
                  ( mkSig [ tid p :::: Pred [nat] ] )
                  [ Axiom "ax1" $ forall [x] $ p!x ])
              -- script
              [ tr $ forall' nat $ p'!var0 ]
         -- ====================================================================

        , ps  (reflThry
                  ( mkSig [ tid p :::: Pred [nat] ] )
                  [ Axiom "ax1" $ forall [x] $ p!x ])
              -- script
              [ tr $ forall' nat $ ( p'!var0 ) || ( p'!var0 ) ]

         -- ====================================================================
         -- fails 
        , ps  (reflThry
                  ( mkSig [ tid p :::: Pred [nat] ] )
                  [ Axiom "ax1" $ forall [x] $ p!x ])
              -- script
              [ tr $ forall' nat $ ( p'!var0 ) && ( p'!var0 ) ]

         -- works
        , ps  (reflThry
                  ( mkSig [ tid p :::: Pred [nat] ] )
                  [ Axiom "ax1" $ forall [x] $ p!x ])
              -- script
              [ forall [t] $ tr $ subs v0 t $ ( p'!var0 ) && ( p'!var0 )  
              , tr $ forall' nat $ ( p'!var0 ) && ( p'!var0 ) ]

         -- works
        , ps  (reflThry
                  ( mkSig [ tid p :::: Pred [nat] ] )
                  [ Axiom "ax1" $ forall [x] $ p!x ])
              -- script
              [ forall [t] $ tr $ ( p'!t ) && ( p'!t )  
              , tr $ forall' nat $ ( p'!var0 ) && ( p'!var0 ) ]

        -- , ps  (reflThry
        --           ( mkSig [ p :::: Pred [a] ] )
        --           [ Axiom "ax1" $ forall [x] $ (p!x) /\ (p!x) ])
        --       -- script
        --       [ tr $ forall' a $ ( p'!var0 ) && ( p'!var0 ) ]

        ]
  where 
        v0 = Refl.v0 nat
        var0 = var nat $ v0 
        var1 = var nat $ nVarR nat ! v0 
        ps = unwrap .: compilePs

        -- sbsT f = subsT f vr0 x
        -- subsT = Refl.subsT a :: FunId
        subs v t phi = Refl.subs nat phi v t

        reflThry = reflective . unwrap .: theory "Simple2"
        -- thry    = reflective $ unwrap 
        --           $ theory "Simple" (
        --                mkSig [  z :::: [] :-> a]
        --            ) [  Axiom "only" $ forall [x] ( x === z!() ) ]
        val x = eval nat ! x
        t   = Id "t"   :: VarId
        x   = Id "x"   :: VarId
        y   = Id "y"   :: VarId
        z   = Id "z"   :: FunId
        z'  = (Id "z_" :: FunId) !() 
        p  = Id "p" :: PredId
        p' = ( refl undefined p ) :: FunId


psSimple :: [ProofScript]
psSimple = unwrap . compilePs thry <$> [
          [ 
            -- works
            tr $ forall' nat $  ( var0 ~~~ z' ) 
          ], [ 
            -- works
            forall [x] $ tr $                ( x ~~~ z' ) && ( x ~~~ z' )
         -- ], [ 
         --    -- fails
         --    tr $ forall' nat $  ( var0 ~~~ z' ) && ( var0 ~~~ z' )
         ], [ 
            -- works
            forall [x] $ tr $   (   x  ~~~ z' ) && (  x   ~~~ z' )
          , tr $ forall' nat $  ( var0 ~~~ z' ) && ( var0 ~~~ z' )
          ], [ 
            tr $ forall' nat $  not' $ not' ( var0 ~~~ z' ) 
          ], [ 
            tr $ forall' nat $  ( var0 ~~~ z' ) || ( var0 ~~~ z' )
          -- ], [ 
          --   tr $  var0 ~~~ z' 
          -- , tr $ forall' nat $  ( var0 ~~~ z' ) && ( var0 ~~~ z' )
          -- ], [ 
          --   tr $ forall' nat $  not' ( var0 ~~~ z' ) || bot 
          ]
        ]
  where 
        var0 = var nat            $ v0 nat
        var1 = var nat $ nVarR nat ! ( v0 nat )

        thry    = reflective $ unwrap 
                  $ theory "Simple" (
                       mkSig [  tid z :::: [] :-> nat]
                   ) [  Axiom "only" $ forall [x] ( x === z!() ) ]
        val x = eval nat ! x
        z   = Id "z"   :: FunId
        z'  = (Id "z_" :: FunId) !() 
        -- p  = Id "p" :: PredId
        -- p' = ( refl undefined p ) :: FunId


x   = Id "x"   :: VarId
y   = Id "y"   :: VarId
nat = Id "nat"
(~~~) :: forall a . ToTerm a => a 
      -> forall b . ToTerm b => b
      -> Term 
(~~~) = binary (eqR nat)
(~/~) :: forall a . ToTerm a => a 
      -> forall b . ToTerm b => b
      -> Term 
(~/~) = not' .: (~~~)


data ProofScriptOut = ProofScriptOut { psIn       :: ProofScript
                                     , psVampires :: [VampireOut] 
                                     , psTime     :: NominalDiffTime    
                                     }

writePs :: FilePath -> ProofScriptOut -> IO () 
writePs path ps 
      = do putStrLn $ cleanSig $ show ps 
           removePathForcibly path
           mkdir path
           writeFile (path ++ "/summary.txt") (cleanSig $ show ps)
           forM_ (indexed $ psVampires ps) $ \(i, v) -> 
              do let dir = path ++  "/step" ++ show i
                 mkdir $ dir
                 let wrt name field = writeFile (dir ++ "/" ++ name) (field v)
                 wrt "stdin"  vIn
                 wrt "stdin.trimmed.tptp"  (cleanSig . vIn)
                 wrt "stdout" vOut
                 wrt "stderr" vErr
                 wrt "args"   (unwords . vArgs)
           putStrLn $ "wrote files to " ++ show path

    where mkdir = createDirectoryIfMissing True
          cleanSig = replace "nat_" "" . replace "nat_in_nat" "t"
                            

instance Show ProofScriptOut where 
  show ps = unlines' $ [ "Theory: " ++ (view thName . psTheory . psIn) ps ]
                   ++ [ showStep i v f | (i,(v,f)) <- indexed (psVampires ps `zip` psSteps (psIn ps)) ]
                   ++ ["total time: " ++ show ( psTime ps )]
                   ++ [ successLine ]
                  where showStep :: Int -> VampireOut -> MirForm -> String
                        showStep i v f = show i ++ ") " 
                                      ++ show (vSat v) 
                                      ++ "\t( " ++ printf "%2.5f" ( vTime v ) ++ " sec )"
                                      ++ "\t"   ++ show f
                        successLine | length psVamps == 0 = "no runs"
                                    | lastRes == Valid    = col Green "-> success"
                                    | otherwise           = col Red   "-> failure"
                          where lastRes = vSat $ last $ psVamps
                                psVamps = psVampires ps 
                                col c s = setSGRCode [ SetColor Foreground Vivid c ] ++ s ++ setSGRCode [Reset]
         
data ProofScript = ProofScript { psTheory :: Theory
                               , psSteps  :: [MirForm] }

runPs :: VampireOpts -> Seconds -> ProofScript -> IO ProofScriptOut
runPs opts timeout ps@(ProofScript th fs) 
            = do start <- getCurrentTime
                 runs  <- runProofs th fs 
                 end   <- getCurrentTime
                 return $ ProofScriptOut ps runs (diffUTCTime end start)
  where 
    runProofs :: Theory -> [MirForm] -> IO [VampireOut]
    runProofs th [] = return []
    runProofs th (f:fs) = 
      do r <- vprove' opts timeout th (Conjecture f) 
         case vSat r of 
           Valid -> (r:) <$> runProofs th' fs
           _     -> return [r]
      where th' = over thAxioms (( Axiom "lemma" f ):) th
            -- opts  = VampireOpts { 
            --            vTimeout = 5 
            --          , vOrd = Lpo
            --          }

compilePs :: Theory -> [Formula] -> Result ProofScript
compilePs th fs = ProofScript th <$> (sequence $ fmap conjFormula . conjecture th <$> fs)
  where sig = th ^.thSig

unlines' = intercalate "\n"
