{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Benchmark.Induction (indBenchmarksMsc, indBenchmarks, printIndBenchmarks) where 

import Benchmark
import Data.Theory.Interpreted
import Data.Formula
import Data.Theory (benchmarkInf)
import ToSmtlib2
import Data.Maybe
import Data.List
import Data.Solvers
import Data.Formula.Mir
import Data.Solvers.Vampire
import Data.Solvers.Zeno
import Data.Solvers.Cvc4
import Data.Solvers.Zipperposition
import Data.Solvers.Imandra
import Vampire
import Util
import Parse
import Parse.QQ
import Text.ParserCombinators.Parsec hiding (State)
import Text.RawString.QQ(r)
import Data.Composition
import Control.Monad.State
import System.Random
import Control.Conditional
import Text.Printf
import ToTex

timeout = Seconds $ 10 * 60
-- timeout = Seconds 5

printIndBenchmarks :: IO ()
printIndBenchmarks = undefined -- putStrLn $ unlines $ (fmap (toSmtlib2 . unwrap . benchmarkInf)  ( join benchmarks ))

-- TODO
-- try x+(x+x) with x+0 instead of xs

indBenchmarksMsc = toGroups benchmarksMsc

indBenchmarks :: IO ()
indBenchmarks = compareSolversGroup timeout solvers bs
  where bs = []
          ++ toGroups benchmarksPaper
          -- ++ randBenchmarks
          -- ++ toGroups benchmarksAdditional

toGroups bench = [ [ BenchGroup (show $ bConjecture b) (toTex $ bConjecture b) [b]  | b <- bs ] | bs <- bench ] 

randBenchmarks  = fmap (fmap (\(BenchGroup i t ps) -> BenchGroup i t (take cnt $ filtered ps)))
                $ evalState (sequence [ sequence [ nRand g | g <- gs ] | gs <- benchGens ]) (mkStdGen 0)
           where 
                 nRand :: ([Benchmark] -> BenchGroup, RandM Benchmark) -> RandM BenchGroup
                 nRand (cons, r) = fmap cons (sequence [ r | _ <- [1..cnt*100]  ])
                 filtered []  = []
                 filtered (b:bs) 
                    | isTrivial (bConjecture b) = filtered bs
                    | otherwise   = Benchmark (bTheory b) (norm $ bConjecture b) 
                                  : filtered [ b' | b' <- bs
                                                  , not (b ~=~ b')]
                    where isTrivial (BaseQuant _ _ _ f) = isTrivial f
                          isTrivial (BaseAtom ( BaseEq _ l r )) = l == r
                          isTrivial (BaseAtom ( BasePred _ [ l, r ] )) = l == r
                          a ~=~ b = (bConjecture a) `betaEquiv'` (bConjecture b)

benchGens :: ChoiceM m => [[([Benchmark] -> BenchGroup, m Benchmark) ]]
benchGens =  
        scenario1 natScenario :
        scenario1 lstScenario :

        scenario2 natScenario :
        scenario2 lstScenario :

        scenario3  :
        scenario4  :
      []
                         
    where withTh th c = (Benchmark th) <$> c
          natScenario = ( natDef  <> addDef    <> leqDef   , Id "<="  , Id "+" )
          lstScenario = ( listDef <> appendDef <> prefixDef, Id "pref", Id "++") 

          scenario1 ( th, rel, op ) = 
               [ (\ps -> BenchGroup {
                          bgId  = printf "%s %d" (show f) n
                        , bgTex =  texMacroCall "sumXxxSize" [ toTex (f :: Formula)
                                                             , texMath $ show n
                                                             , toTex (rel :: PredId)
                                                             , toTex (op :: FunId)
                                                             ]
                        , bgProblems = ps
                        }
                  , conj n) | n <- [3..10] ]
                          where f :: Formula
                                f = universalClosure $ BaseAtom $ BaseEq Pos (v * (v * v)) ((v * v) * v)
                                a * b = BaseFun op [ a,b ] Nothing
                                v = BaseVar ( Id "x" )  Nothing
                                conj n = do 
                                  l <- genAssoc op n
                                  r <- genAssoc op n
                                  return $ Benchmark th (universalClosure $ l === r)


          scenario4 = 
               [ (\ps -> BenchGroup {
                          bgId  = printf "%s %d %d" (show f) vs size
                        -- , bgTex = toTex (f :: Formula) <> texMath (printf "^{ %d }" k)
                        , bgTex = texMacroCall "sumVsSize" [ toTex (f :: Formula)
                                                           , texMath $ show vs 
                                                           , texMath $ show size
                                                           ] -- <> texMath (printf "^{ %d }" k)
                        , bgProblems = ps
                        }
                  , conj vs size) | size <- [3..7]
                                  , vs   <- [2..min 5 size]
                                  ]
                          where f :: Formula
                                f = universalClosure $ BaseAtom $ BaseEq Pos (x + (y + z)) ((x + y) + z)
                                a + b = BaseFun op [ a,b ] Nothing
                                x = BaseVar ( Id "x" )  Nothing
                                y = BaseVar ( Id "y" )  Nothing
                                z = BaseVar ( Id "z" )  Nothing
                                (th, rel, op) = natScenario
                                -- conj :: ChoiceM m => Int -> m Benchmark
                                conj vs size = do 
                                  l <- genScenario4 vs size
                                  r <- genEqual l
                                  return $ Benchmark th (universalClosure $ l === r)


          scenario3 = 
               [ (\ps -> BenchGroup {
                          bgId  = printf "%s %d" (show f) k
                        , bgTex = texMacroCall "sumSize"   [ toTex (f :: Formula)
                                                           , texMath $ show k
                                                           ] -- toTex (f :: Formula) <> texMath (printf "^{ %d }" k)
                        , bgProblems = ps
                        }
                  , conj k) | k <- fmap (*3) [1..10] ]
                          where f :: Formula
                                f = universalClosure $ BaseAtom $ BaseEq Pos (x + (y + z)) ((x + y) + z)
                                a + b = BaseFun op [ a,b ] Nothing
                                x = BaseVar ( Id "x" )  Nothing
                                y = BaseVar ( Id "y" )  Nothing
                                z = BaseVar ( Id "z" )  Nothing
                                (th, rel, op) = natScenario
                                -- conj :: ChoiceM m => Int -> m Benchmark
                                conj i = do 
                                  l <- genXYZ i
                                  r <- genEqual l
                                  return $ Benchmark th (universalClosure $ l === r)

          scenario2 ( th, rel, op ) = 
               [ (\ps -> BenchGroup {
                          bgId  = printf "%s (%d,%d)" (show f) m n
                        , bgTex = texMacroCall "xleqxx"   [ toTex (f :: Formula)
                                                          , texMath $ show m
                                                          , texMath $ show n
                                                          , toTex rel
                                                          , toTex op
                                                          ]
                        , bgProblems = ps
                        }
                  , scenario2conj th rel op m n) 
                          | (m, n) <- [ (i,i + j) | j <- [0..4] 
                                                  , i <- [1..5] ] ]
                          where f :: Formula
                                f = universalClosure $ BaseAtom $ BasePred rel [ v, BaseFun op [ v,v ] Nothing] 
                                v = BaseVar ( Id "x" )  Nothing

          scenario2conj th pred op m n = withTh th 
                        $ withBinPred' (\l r -> BaseAtom $ BasePred pred [l,r] ) ( genAssoc op m ) ( genAssoc op n ) 

          withBinPred' p l r = withBinPred p l (const r)
          withBinPred p l r = do 
              l' <- l
              r' <- r l'
              return $ (universalClosure .: p) l' r'



type AllM a = [a]

class Monad m => ChoiceM m where 
  choose :: [a] -> m a
  choose' :: [m a] -> m a
  choose' = join . choose

instance ChoiceM [] where 
  choose = id

instance ChoiceM (State StdGen) where 
  choose [] = error "choice from empty list"
  choose xs = fmap (xs !!) $ state $ randomR (0, length xs - 1) 

genAssoc :: ChoiceM m => FunId -> Int -> m Term
genAssoc op 0 = error "cant gen a formula with 0 xs"
genAssoc op 1 = return $ BaseVar (Id "x") Nothing
genAssoc op n = do 
    i <- choose [ 1 .. n - 1 ]
    l <- genAssoc op i
    r <- genAssoc op (n - i)
    return $ BaseFun op [l, r] Nothing
              



genScenario4 :: ChoiceM m => Int -> Int -> m Term
genScenario4 nvars size | nvars <= size = do 
                          t <- gen size
                          if length (freeVs (t :: Term)) /= nvars
                          then genScenario4 nvars size
                          else return t
  where gen 0 = error "cant gen a formula with 0 xs"
        gen 1 = choose [ BaseVar (Id $ "x" ++ show i) Nothing | i <- [1..nvars] ]
        gen n = do 
            i <- choose [ 1 .. n - 1 ]
            l <- gen i
            r <- gen (n - i)
            return $ BaseFun op [l, r] Nothing
        op = Id "+"

genXXX :: ChoiceM m => Int -> m Term
genXXX = genAssoc (Id "+")

       
genXYZ :: ChoiceM m => Int -> m Term
genXYZ n = gen n
  where gen k = choose' [ c | (c, lower, upper) <- choices
                            , lower <= k 
                            , upperOk k upper ]
             where choices = [ 
                        (plus k, 3, Nothing)
                      , (suc  k, 2, Nothing)
                      , (zero  , 1, Just 1)
                      ] ++ [(return $ var i   , 1, Just 1) | i <- [1..n] ]
                   upperOk k  Nothing  = True
                   upperOk k (Just up) = k <= up
        zero = return $ BaseFun (Id "zero") [] Nothing
        plus k = do 
              -- i <- state $ randomR (1, k - 2) 
              i  <- choose [ 1 .. k - 2 ]
              i' <- choose [ i + 1, i ]
              l <- gen i'
              r <- gen (k - i')
              return $ BaseFun (Id "+") [l, r] Nothing

        var :: Int -> Term
        var i = BaseVar (Id $ "x" ++ show i) Nothing
        -- suc :: Int -> AllM Term
        suc k = suc' <$> (gen ( k - 1 ))
          where suc' v = BaseFun ( Id "s" ) [ v ] Nothing



allXYZ :: Int -> AllM Term
allXYZ n = gen n
  where gen k = choice [ c | (c, lower, upper) <- choices
                           , lower <= k 
                           , upperOk k upper ]
             where choices = [ 
                        (plus k, 3, Nothing)
                      , (suc  k, 2, Nothing)
                      , (zero  , 1, Just 1)
                      ] ++ [(return $ var i   , 1, Just 1) | i <- [1..n] ]
                   upperOk k  Nothing  = True
                   upperOk k (Just up) = k <= up
        zero = return $ BaseFun (Id "zero") [] Nothing
        plus k = do 
              -- i <- state $ randomR (1, k - 2) 
              i <- [1..k-2]
              i' <- choice' [ i + 1, i ]
              l <- gen i'
              r <- gen (k - i')
              return $ BaseFun (Id "+") [l, r] Nothing

        var :: Int -> Term
        var i = BaseVar (Id $ "x" ++ show i) Nothing
        suc :: Int -> AllM Term
        suc k = suc' <$> (gen ( k - 1 ))
          where suc' v = BaseFun ( Id "s" ) [ v ] Nothing

        -- choice :: 
        choice' [] = error "choice from empty list"
        choice' xs = xs -- fmap (xs !!) [0, length xs - 1]
        -- choice' xs = fmap (xs !!) $ state $ randomR (0, length xs - 1) 
        choice  xs = join $ choice' xs



genEqual :: ChoiceM m => Term -> m Term
genEqual t = do 
    ss <- shuffle (symbols t)
    return $ evalRec ss -- TODO shuffle symbols 
  where symbols (BaseFun id ts _) = symPlus id ts : (symbols =<< ts)
        symbols v@(BaseVar _ _) = [ Symbol $ return v ]
        symPlus id ts = Symbol $ do 
                   ts' <- sequence [ state (fromJust . uncons) >>= evSym | _ <- ts]
                   return $ BaseFun id ts' Nothing
        evSym (Symbol s) = s
        evalRec (s:ss) = case runState (evSym s) ss of 
                           (t, []) -> t
                           (t, ss) -> evalRec (ss ++ [Symbol $ return t])
                          
shuffle :: ChoiceM m => [a] -> m [a]
shuffle [] = return []
shuffle (x:[]) = return [x]
shuffle xs = do 
  i <- choose [0 .. length xs - 2]
  let (lhs,m:rhs) = splitAt i xs
  rest <- shuffle (lhs ++ rhs)
  return $ m:rest

data Symbol = Symbol (State [Symbol] Term)

-- TODO
-- LENGTH (APPEND X Y)) is (+ (LENGTH X) (LENGTH Y)).
-- x * 2 = x + x
-- 2 * x = x + x
-- x * ( y + z ) =  (x * y) + (x * z)
  -- + permulations
-- rev(rev(x)) = x

cnt = 50

solvers = 
      (AnySolver vampireComplexTermInduction) :
      (AnySolver vampireSubsFull) :
      (AnySolver vampireOld) :
      (AnySolver cvc4) :
      (AnySolver zipperposition1) :
      (AnySolver Zeno) :
      (AnySolver imandra) :

      (AnySolver cvc4gen) :
      (AnySolver zipperposition2) :
      []


easyBenchmarks =
        -- trivial
      Benchmark {
           bTheory = natDef 
         , bConjecture = [formula| forall x: nat. x = x |]
         } :

      Benchmark {
           bTheory = natDef <> addDefL
         , bConjecture = [formula| forall. zero() /= s(y) |]
         } :

      Benchmark {
           bTheory = natDef <> addDefL
         , bConjecture = [formula| forall. x = zero() \/ exists y. x = s(y) |]
         } :

      Benchmark {
           bTheory = natDef <> addDefL
         , bConjecture = [formula| forall x: nat, y. x + y = y + x |]
         } :

      -- Benchmark {
      --      bTheory = natDef <> addDefL
      --    , bConjecture = [formula| forall x: nat, y. x + (y + z) = y + y |]
      --    } :

         []


benchmarksMsc :: [[Benchmark]]
benchmarksMsc = [
      [ 

        -- ditributicity
        Benchmark {
             bTheory = natDef <> addDefL <> mulDef
           , bConjecture = [formula| forall. x * (y + z) = (x * y) + (x * z) |]
           }

     ] , [ 

        -- add commut
        Benchmark {
             bTheory = natDef <> addDefL
           , bConjecture = [formula| forall. x + y = y + x |]
           },
        -- add assoc
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. x + (y + z) = (x + y) + z |]
           },
        -- add neutral
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. x + zero() = x |]
           },
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. zero() + x = x |]
           }
     ] , [
          -- leq add
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x. x <= x |]
           } ,
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x, y. x <= ( x + y ) |]
           } ,
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x. zero() <= x |]
           }

      ], [

          -- ==================== lists ==================== -- 
          -- concat
        Benchmark {
             bTheory = listDef <> appendDef
           , bConjecture = [formula| forall. x ++ (y ++ z) = (x ++ y) ++ z |]
           },

          -- prefix concat
        Benchmark {
             bTheory = listDef <> appendDef <> prefixDef
           , bConjecture = [formula| forall x, y. pref(x, x ++ y) |]
           },

        Benchmark {
             bTheory = listDef <> appendDef <> prefixDef
           , bConjecture = [formula| forall x. pref(nil(), x) |]
           }

      ], [
        Benchmark {
             bTheory = natDef <> addDef 
           , bConjecture = [formula| forall x,y. y + (x + x) = (x + y) + x |]
           },
      -- combine lists and addition
        Benchmark {
             bTheory = listDef <> addDef <> appendDef
           , bConjecture = [formula| forall n,x. cons(n + s(n), x) ++ (x ++ x) = (cons(s(n) + n, x) ++ x) ++ x |]
           }
      ] , [

          -- ==================== NUMBERS ==================== -- 
         
          -- multiplication
        Benchmark {
             bTheory = natDef <> addDef <> mulDef
           , bConjecture = [formula| forall. x * y = y * x |]
           },
        Benchmark {
             bTheory = natDef <> addDef <> mulDef
           , bConjecture = [formula| forall. x * (y * z) = (x * y) * z |]
           },
        Benchmark {
             bTheory = natDef <> addDef <> mulDef
           , bConjecture = [formula| forall. x * (y + z) = (x * y) + (x * z) |]
           },
        Benchmark {
             bTheory = natDef <> addDef <> mulDef
           , bConjecture = [formula| forall. ((x + y) * z) = (x * z) + (y * z) |]
           },
        Benchmark {
             bTheory = natDef <> addDef <> mulDef
           , bConjecture = [formula| forall. ( (x + y) * z ) = (z * x) + (y * z) |]
           },
        -- mul zero
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. x * zero() = zero() |]
           },
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. zero() * x = zero() |]
           },
        -- mul neutral
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. x * s(zero()) = x |]
           },
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. s(zero()) * x = x |]
           }
      ] , [

          -- identity
        Benchmark {
             bTheory = natDef <> addDefL <> idDef
           , bConjecture = [formula| forall. id(x) + y = y + x |]
           } 
      ], [

          -- commut
        Benchmark {
             bTheory = natDef <> addDefL
           , bConjecture = [formula| forall. x + y = y + x |]
           } 
      ], [

      Benchmark {
           bTheory = natDef <> allEqDef
         , bConjecture = [formula| forall. equal(x,x,x) |]
         },
      Benchmark {
           bTheory = natDef <> allEqDef
         , bConjecture = [formula| forall. equal(x,y,z) <-> (x = y /\ y = z) |]
         } 

      ], [

          -- reversing
        Benchmark {
             bTheory = listDef <> appendDef <> revDef
           , bConjecture = [formula| forall x. rev(rev(x)) = x |]
           },

        Benchmark {
             bTheory = listDef <> appendDef <> revDef
           , bConjecture = [formula| forall x. x ++ (rev(x) ++ x) = (x ++ rev(x)) ++ x |]
           },

        Benchmark {
             bTheory = listDef <> appendDef <> revDef
           , bConjecture = [formula| forall x. rev(x ++ (x ++ x)) = rev((x ++ x) ++ x) |]
           },
        Benchmark {
             bTheory = listDef <> appendDef <> revDef <> revAccDef
           , bConjecture = [formula| forall x. revAcc(x) = rev(x) |]
           } 
      ]

    ]


benchmarksPaper = [
      [ 

        -- ditributicity
        Benchmark {
             bTheory = natDef <> addDefL <> mulDef
           , bConjecture = [formula| forall. x * (y + z) = (x * y) + (x * z) |]
           }

     ] , [ 

        -- add commut
        Benchmark {
             bTheory = natDef <> addDefL
           , bConjecture = [formula| forall. x + y = y + x |]
           },
        Benchmark {
             bTheory = natDef <> addDef 
           , bConjecture = [formula| forall x. s(x) + x = x + s(x) |]
           },
        Benchmark {
             bTheory = natDef <> addDef 
           , bConjecture = [formula| forall x. x + s(x) = s(x + x) |]
           }

     ] , [

        -- add assoc
        Benchmark {
             bTheory = natDef <> addDef
           , bConjecture = [formula| forall. x + (y + z) = (x + y) + z |]
           },
        Benchmark {
             bTheory = natDef <> addDef 
           , bConjecture = [formula| forall x. x + (x + x) = (x + x) + x |]
           },
        Benchmark {
             bTheory = natDef <> addDef 
           , bConjecture = [formula| forall x. ((x + x) + ((x + x) + x)) = (x + (x + ((x + x) + x))) |]
           }

     ] , [
          -- leq add
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x. x <= x |]
           } ,
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x, y. x <= ( x + y ) |]
           } ,
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x. x <= ( x + x ) |]
           },
        Benchmark {
             bTheory = natDef <> addDef <> leqDef
           , bConjecture = [formula| forall x. ( ( x + x ) <= ( (x + x) + x ) ) |]
           }

      ], [

          -- ==================== lists ==================== -- 
          -- concat
        Benchmark {
             bTheory = listDef <> appendDef
           , bConjecture = [formula| forall. x ++ (y ++ z) = (x ++ y) ++ z |]
           },

        Benchmark {
             bTheory = listDef <> appendDef
           , bConjecture = [formula| forall x. x ++ (x ++ x) = (x ++ x) ++ x |]
           },
        Benchmark {
             bTheory = listDef <> appendDef
           , bConjecture = [formula| forall x. ((((x ++ x) ++ x) ++ x) ++ x) = ((x ++ (x ++ x)) ++ (x ++ x)) |]
           },
        Benchmark {
             bTheory = listDef <> appendDef
           , bConjecture = [formula| forall x,y. x ++ (y ++ (x ++ x)) = (x ++ y) ++ (x ++ x) |]
           }
      ], [

          -- prefix concat
        Benchmark {
             bTheory = listDef <> appendDef <> prefixDef
           , bConjecture = [formula| forall x, y. pref(x, x ++ y) |]
           },
        Benchmark {
             bTheory = listDef <> appendDef <> prefixDef
           , bConjecture = [formula| forall x. pref(x, x ++ x) |]
           } 

      ], [
        Benchmark {
             bTheory = natDef <> addDef 
           , bConjecture = [formula| forall x,y. y + (x + x) = (x + y) + x |]
           },
      -- combine lists and addition
        Benchmark {
             bTheory = listDef <> addDef <> appendDef
           , bConjecture = [formula| forall n,x. cons(n + s(n), x) ++ (x ++ x) = (cons(s(n) + n, x) ++ x) ++ x |]
           }
      ]
  ]

benchmarksAdditional = [

        -- ==================== NUMBERS ==================== -- 
       
        -- multiplication
      Benchmark {
           bTheory = natDef <> addDef <> mulDef
         , bConjecture = [formula| forall. x * y = y * x |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> mulDef
         , bConjecture = [formula| forall. x * (y * z) = (x * y) * z |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> mulDef
         , bConjecture = [formula| forall. x * (x * x) = (x * x) * x |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> mulDef
         , bConjecture = [formula| forall. x * (y + z) = (x * y) + (x * z) |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> mulDef
         , bConjecture = [formula| forall. ((x + y) * z) = (x * z) + (y * z) |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> mulDef
         , bConjecture = [formula| forall. ( (x + y) * z ) = (z * x) + (y * z) |]
         } :

        -- identity
      Benchmark {
           bTheory = natDef <> addDefL <> idDef
         , bConjecture = [formula| forall. id(x) + y = y + x |]
         } :

        -- commut
      Benchmark {
           bTheory = natDef <> addDefL
         , bConjecture = [formula| forall. x + y = y + x |]
         } :
      -- Benchmark {
      --      bTheory = natDef <> addDefR 
      --    , bConjecture = [formula| forall. x + y = y + x |]
      --    } :

      Benchmark {
           bTheory = natDef <> allEqDef
         , bConjecture = [formula| forall. equal(x,x,x) |]
         } :
      Benchmark {
           bTheory = natDef <> allEqDef
         , bConjecture = [formula| forall. equal(x,y,z) <-> (x = y /\ y = z) |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> allEqDef 
         , bConjecture = [formula| forall. equal( x + (x + x) 
                                                , (x + x) + x
                                                , (x + x) + x  ) |]
         } :
      Benchmark {
           bTheory = natDef <> addDef <> allEqDef 
         , bConjecture = [formula| forall. equal( x + ( (x + x) + x )
                                                , x + ( x + (x + x) )
                                                , (x + x) + (x + x)) |]
         } :

      [],

        -- reversing
      Benchmark {
           bTheory = listDef <> appendDef <> revDef
         , bConjecture = [formula| forall x. rev(rev(x)) = x |]
         } :

      Benchmark {
           bTheory = listDef <> appendDef <> revDef
         , bConjecture = [formula| forall x. x ++ (rev(x) ++ x) = (x ++ rev(x)) ++ x |]
         } :

      Benchmark {
           bTheory = listDef <> appendDef <> revDef
         , bConjecture = [formula| forall x. rev(x ++ (x ++ x)) = rev((x ++ x) ++ x) |]
         } :
      Benchmark {
           bTheory = listDef <> appendDef <> revDef <> revAccDef
         , bConjecture = [formula| forall x. revAcc(x) = rev(x) |]
         } : 
         []

      ]

unwrap' (Left err) = error $ show err
unwrap' (Right x)  = x

listDef = [theory|
          inductive cons.
          inductive nil.
          nil  : ()         -> lst.
          cons : (nat, lst) -> lst.
          |] <> natDef

appendDef = [theory|
          ++ : (lst, lst)    -> lst.

          forall . nil()      ++ r = r             .
          forall . cons(a, l) ++ r = cons(a, l ++ r).
          |]


prefixDef = [theory|
          pref : P(lst, lst).

          forall .   pref(nil()     , x         ).
          forall . ~ pref(cons(a, x), nil()     ).
          forall .   pref(cons(a, x), cons(b, y)) <-> a = b /\ pref(x,y).
          |]

natDef = [theory|
          inductive s.
          inductive zero.
          zero : () -> nat.
          s    : nat -> nat.
        |]

leqDef = [theory|

          <= : P(nat, nat).

          forall .  zero() <=   y            .
          forall .~(s(x)   <= zero())        .
          forall .  s(x)   <= s(y) <-> x <= y.
          |]


mulDef  = [theory| * : (nat, nat) -> nat.
                   forall. ( zero() * y  = zero()   ) .
                   forall. ( s(x)   * y  = (x * y) + y ).  |]


addAssoc = [theory| forall. x + y  = y + x. |]

idDef = [theory| id : nat -> nat.
                 forall x. id(x) = x. |]

revDef = [theory| rev : lst -> lst.
                  forall. rev(nil()) = nil().
                  forall. rev(cons(x,xs)) = rev(xs) ++ cons(x,nil()). |]

revAccDef = [theory|
                  revAcc  : lst -> lst.
                  forall. revAcc(x) = revAccInner(x,nil()).

                  revAccInner : (lst,lst) -> lst.
                  forall. revAccInner(nil()     , acc) = acc.
                  forall. revAccInner(cons(x,xs), acc) = revAccInner(xs, cons(x,acc)). |]

addDef = addDefL
addDefL = [theory| + : (nat, nat) -> nat              .
                   forall. ( zero() + y  = y        ) .
                   forall. ( s(x)   + y  = s(x + y) ) . |]

addDefR = [theory| + : (nat, nat) -> nat             .
                   forall. ( x + zero()  = x        ).
                   forall. ( x +   s(y)  = s(x + y) ).  |]

allEqDef = [theory| equal : P(nat, nat, nat).
                    forall. equal(zero(), zero(), zero()) <-> true.
                    forall. equal(zero(), s(y)  , z     ) <-> false.
                    forall. equal(zero(), y     , s(z)  ) <-> false.
                    forall. equal(s(x)  , zero(), z     ) <-> false.
                    forall. equal(s(x)  , y     , zero()) <-> false.
                    forall. equal(s(x)  , s(y)  , s(z)  ) <-> equal(x,y,z).  |]

form = unwrap' . parse formulaParser ""
