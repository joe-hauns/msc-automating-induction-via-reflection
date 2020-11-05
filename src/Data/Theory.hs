
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Theory ( Theory 
                   , theory
                   , benchmarkInf
                   , unBenchmarkInf
                   , theoryInf
                   , unTheoryInf
                   -- , inferTypes
                   , Axiom (..)
                   , decl 
                   , Decls
                   , Conjecture(..)
                   , conjecture
                   , mirForm
                   , typeChecked
                   , fromMir
                   , toMir
                   -- , compileMir
                   , formulaInf
                   , thName, thSig, thAxioms
                   , Problem (..)
                   , inferSorts
                   ) where

import Util
import Data.Signature hiding (override)
import Data.Formula hiding ((/\), (\/))
import Data.Formula.Mir
--
import Prelude hiding ( (.), id )
import Control.Arrow
import Control.Monad
import Data.Theory.Interpreted (Benchmark, MirBenchmark, GenBenchmark(..))
import Control.Category
import Control.Lens hiding (element, to)
import Data.Maybe
import Data.Char
import Data.List hiding (insert, union)
import Debug.Trace
import qualified Data.Theory.Interpreted as NewTheory
--
import Data.Composition
import qualified Data.HashSet as Set
import qualified Data.Signature as Sig
import Control.Monad.HT hiding (filter)

data Problem = Problem Theory Conjecture

data Conjecture = Conjecture { conjFormula :: MirForm }

data Axiom a = Axiom { axName :: String, axForm :: a } deriving ( Eq, Ord, Functor )

data Theory = Theory { _thName   :: String
                     , _thSig    :: Sig
                     , _thAxioms :: [Axiom MirForm] }
                    deriving (Eq)
makeLenses ''Theory

inferSorts :: Sig -> Term -> Result MirTerm
inferSorts s t = toMir s t

class Mirable a b where 
  toMir :: Sig -> a -> Result b
  fromMir :: b -> a 

instance Mirable Formula Conjecture where 
  toMir   = fmap Conjecture .: toMir
  fromMir = fromMir . conjFormula

instance Mirable Formula MirForm where
  fromMir (BaseAtom (BaseEq p a1 a2) ) = BaseAtom (BaseEq  p (fromMir a1) (fromMir a2))
  fromMir (BaseAtom (BasePred f ts    ) ) = BaseAtom (BasePred f [ fromMir t | t <- ts ])
  fromMir (BaseCon0 c) = BaseCon0 c
  fromMir (BaseCon c a1 a2  ) = BaseCon c (fromMir a1) (fromMir a2)
  fromMir (BaseNot a        ) = BaseNot (fromMir a)
  fromMir (BaseQuant q v s f) = BaseQuant q v (Just s) (fromMir f)

  toMir = mir
    where 
          
          mir :: Sig -> Formula -> Result MirForm
          mir s t = pushTrace (show t) (mir' s t)
          mir' sig (BaseCon0 c) = return (BaseCon0 c)
          mir' sig (BaseAtom (BaseEq p a1 a2) ) = 
                    do a1' <- toMir sig a1 
                       a2' <- toMir sig a2 
                       return $ (BaseAtom (BaseEq p a1' a2'))

          mir' sig (BaseAtom (BasePred f ts   )) = BaseAtom . BasePred f <$> sequence [ toMir sig t | t <- ts ]
          mir' sig (BaseCon c a1 a2  ) =
                    do a1' <- mir sig a1 
                       a2' <- mir sig a2 
                       return $ BaseCon c a1' a2'

          mir' sig (BaseNot a        ) = BaseNot <$> (mir sig a)
          mir' sig (BaseQuant q v (Just s) f) = BaseQuant q v s <$> (mir sig f)
          mir' sig (BaseQuant q v Nothing  f) = failure $  reverse $  [ "could not infer sort of " ++ show v
                                                      , "over signagure:"] ++ fmap ("\t"++) ( lines $ show sig )

instance (Mirable a b, Mirable a' b') => Mirable (a, a') (b, b') where
  fromMir (a, a') = (fromMir a, fromMir a')
  toMir s (l, r) 
      = do l' <- toMir s l
           r' <- toMir s r
           return (l', r')

instance Mirable a b => Mirable (Axiom a) (Axiom b) where
  fromMir = fmap fromMir
  toMir s (Axiom n a) = do a' <- toMir s a 
                           return $  Axiom n a'

instance Mirable a b => Mirable [a] [b] where
  fromMir = fmap fromMir
  toMir s = sequence . fmap (toMir s)

instance Mirable a a where
  fromMir = id
  toMir s = return . id

instance Mirable Term MirTerm where
  fromMir (BaseFun f ts s) = BaseFun f (fromMir <$> ts) (Just s)
  fromMir (BaseVar v    s) = BaseVar v                  (Just s)

  toMir = mir
    where 
      mir s t = pushTrace (show t) (mir' s t)
      mir' sig (BaseVar v (Just s)) = return $ BaseVar v s
      mir' sig (BaseVar v Nothing ) = failure ["could not infer sort of " ++ show v ]
      -- mir' sig (BaseVar v s) = (return . BaseVar v <$> s) <|> failure ["could not infer sort of " ++ show v ] -- TODO try me
      mir' sig t@(BaseFun f ts s)  = 
        do ts' <- sequence (mir sig <$> ts) 
           s   <- termSort' sig t
           return $ BaseFun f ts' s 


instance Mirable (String, [Axiom Formula]) Theory where
  fromMir (Theory n sig as) = (n, fromMir as)
  toMir sig (n, as) = theory n sig as

termSort' sig t = case termSort sig t of 
                   Just s -> return s
                   Nothing -> failure[ "could not infer sort of " ++ show t ]

-- inferTypes :: Theory -> Formula -> Result Formula
-- inferTypes th f = do
--       let s = th ^.thSig
--       let fs = [ a | Axiom _ a <- th ^.thAxioms ]
--       (s', fs') <- infer s (f:( fromMir <$> fs ))
--       let f' = head fs'
--       if s' /= s
--       then Left $ reverse $ [ "signature changed due to formula:"
--                             , "old:" , show' s
--                             , "new:", show' s'
--                             ]
--       else Right $ f'
--                               where show' s = unlines $ sort $ ("\t"++) <$> ( lines $ show s )

-- axiom :: Sig -> Formula -> Result (MirForm)
-- axiom s = toMir s >=> ( return . Axiom )

mirForm    :: Theory -> Formula -> Result MirForm
mirForm    t f = infer s f  
             >>= checkSig s
             >>= toMir s
        where s = (t ^. thSig)

-- mirTheory :: Benchmark -> Formula -> Result MirForm
-- mirTheory 

conjecture :: Theory -> Formula -> Result Conjecture
conjecture t f = infer s f  
             >>= checkSig s
             >>= toMir s
             >>= ( return . Conjecture )
        where s = (t ^. thSig)

                            

unBenchmarkInf :: MirBenchmark -> Benchmark
unBenchmarkInf (Benchmark th c) = (Benchmark (unTheoryInf th) (fromMir c))

benchmarkInf :: Benchmark -> Result MirBenchmark
benchmarkInf ( Benchmark (NewTheory.Theory n as s d) c ) 
     = do Problem (Theory _ s' as') (Conjecture c') <- problemInferred n s (Axiom "" <$> as) c 
          return $ Benchmark (NewTheory.Theory n ( axForm <$> as' ) (toDecls s') d) c'
                            

unTheoryInf :: NewTheory.MirTheory -> NewTheory.Theory
unTheoryInf (NewTheory.Theory n as s d) = NewTheory.Theory n (fromMir as) s d

theoryInf :: NewTheory.Theory -> Result NewTheory.MirTheory
theoryInf (NewTheory.Theory n as s d)
     = do Problem (Theory _ s' as') _ <- problemInferred n s (Axiom "" <$> as) (BaseCon0 Bot)
          return $ NewTheory.Theory n ( axForm <$> as' ) (toDecls s') d 

formulaInf :: Sig -> Formula -> Result MirForm
formulaInf s form = snd <$> (compileMir s form) 

-- instance Mirable   NewTheory.Theory NewTheory.MirTheory where
--
-- instance Inferable NewTheory.Theory where
--                  -- . compileMir Sig.empty

-- theoryInferred :: String -> [Axiom Formula] -> Result Theory
-- theoryInferred n = fmap (uncurry (Theory n)) 
--                  . compileMir Sig.empty

problemInferred :: String -> [SymDec] -> [Axiom Formula] -> Formula -> Result Problem
problemInferred n ds = curry (compileMir s 
                           >=> return.snd
                           -- >=> checkSig s
                           >>> fmap (\(as, c) -> Problem (Theory n s as) c))
  where s = mkSig ds

problem :: String -> [SymDec] -> [Axiom Formula] -> Formula -> Result Problem
problem n ds = curry (compileMir s 
         >=> checkSig s
         >>> fmap (\(as, c) -> Problem (Theory n s as) c))
  where s = mkSig ds

theory :: String -> Sig -> [Axiom Formula] -> Result Theory
theory n s = compileMir s 
         >=> checkSig s
         >>> fmap (Theory n s)



checkSig s (s', x) | s == s'  = return $ x
                   | otherwise = failure $ reverse 
                               $ [ "incomplete signature:" 
                                 , "difference:"
                                 , showDiff "+" s' s
                                 , showDiff "-" s' s
                                 ]
                    where show' s = unlines $ sort $ ("\t"++) <$> ( lines $ show s )
                          showDiff c s s' = unlines  
                                          $ fmap ((( "\t" ++ c ++ " " ) ++) . show)
                                          $ diff s s'
                          diff s' s = [ d | d <- toDecls s', not (d `elem` toDecls s) ]


typeChecked :: Sig -> MirForm -> Result MirForm
typeChecked s f = compileMir s (fromMir f :: Formula)
              >>= checkSig s


compileMir :: (Inferable a, Eq a, Mirable a b) => Sig -> a -> Result (Sig, b)
compileMir s as = do
      (s', as') <- infer s as
      as'' <- toMir s' as' 
      return (s', as'')

class InfState a where 
  initial  :: Sig -> a
  (/\)     :: a -> a -> Result a
  remove   ::        VarId -> a -> a
  override :: VarId -> Maybe SortId -> a -> a
  push     :: VarId -> Maybe SortId -> a -> Result a
  findVar   ::        VarId -> a -> Maybe SortId
  findTerm  ::         Term -> a -> Result (Maybe SortId)
  findFun   ::        FunId -> a -> Result Function
  findPred  ::       PredId -> a -> Result Predicate
  assertEq   ::         Term -> Term   -> a -> Result a
  assertSort ::         Term -> SortId -> a -> Result a

instance InfState Sig where 
  initial s = s
  s1 /\ s2 = do funs   <- meet' sgFuns   s1 s2
                sorts  <- meet' sgSorts  s1 s2
                vars   <- meet' sgVars   s1 s2
                preds  <- meet' sgPreds  s1 s2
                return $ Sig funs sorts  vars preds  
    where meet :: ( Eq t, Show t ) => Decls t -> Decls t -> Result ( Decls t )
          meet m1 m2 | sameDecls m1 m2 = Right $ m1 `union` m2
                     | otherwise       = Left $ reverse $ [ "inconsistent use of symbols:" ]  
                                             ++ [ join ["\t", show id, ": ", show d, " /= ", show d'] | (id, (d, d')) <- wrongDecls m1 m2 ]

          meet' :: (Eq t, Show t) => Lens' Sig (Decls t) -> Sig -> Sig -> Result (Decls t)
          meet' f s s' = meet ( s^.f ) ( s'^.f )

          wrongDecls ::  Eq t => Decls t -> Decls t -> [ (Id t, ( t, t ))]
          -- wrongDecls = nonEqIntersection
          wrongDecls = filter (uncurry (/=) . snd) .: Sig.intersectionWith mkPair
          mkPair a b = (a,b)

          sameDecls :: Eq t => Decls t -> Decls t -> Bool
          sameDecls = all snd .: Sig.intersectionWith (==)

  override v Nothing  = remove v
  override v (Just s) = ( Sig.override sgSorts s Sort )
                      . ( Sig.override sgVars  v (Var s) )
  push v Nothing  sig = return $ sig 
  push v (Just s) sig = case findSym sgVars v sig of 
                           Nothing               -> Right ( Sig.override sgVars v (Var s)  sig)
                           Just s' | s' == Var s -> Right sig
                                   | otherwise   -> Left [show v ++ ": " ++ show s ++ " /= " ++ show s' ]

  remove   v     = removeSym sgVars v
  findVar  v sig = unVar <$> findSym sgVars v sig 
                     

  assertSort (BaseVar v _) s e = push v (Just s) e -- TODO sort ignored here
  assertSort t        s e = do res <- findTerm t e
                               case res of 
                                 Just s'  | s == s' -> return e
                                          | otw     -> Left [ join [  show t, ": ", show s, "/=", show $ s' ] ]
                                 Nothing -> error "this should never happen"

  assertEq t1 t2 e = do s <- checkEq t1 t2
                        push' t1 s >=> push' t2 s $ e
                      where checkEq :: Term -> Term -> Result (Maybe SortId)
                            checkEq t1 t2 = do ft1 <- findTerm t1 e
                                               ft2 <- findTerm t2 e
                                               case (ft1, ft2) of 
                                                 (Just s1, Just s2) | s1 /= s2 -> Left [ join [show t1, ": ", show s1, " /= ", show t2, ": ", show s2] ]
                                                                    | s1 == s2 -> Right $ Just s1
                                                 (Nothing, x)                  -> Right x
                                                 (x, Nothing)                  -> Right x
                            push' :: Term -> Maybe SortId -> Sig -> Result Sig
                            push' t Nothing  = return
                            push' t (Just s) = assertSort t s

  findFun   = findSym' "fun" sgFuns 
  findPred  = findSym' "pred" sgPreds
  findTerm (BaseVar v _) s = return $ findVar v s -- TODO: sort ignored here

  findTerm (BaseFun f _ _) s = fmap (Just . (^. funSort) ) $ findFun f s  -- TODO: sort ignored here


findSym' :: String -> Lens' Sig (Decls a) -> Id a -> Sig -> Either [String] a
findSym' n field sym s = case findSym field sym s of 
                          Just x -> return x
                          Nothing -> Left [ "undeclared " ++ n ++ " symbol: " ++ show sym ]


mu :: ( Monad m, Eq a ) => (a -> m a) -> a -> m a
mu f x = do y <- f x
            if x == y 
            then return y
            else mu f y 

class Inferable a where 
  infer :: ( InfState e, Eq e ) => e -> a -> Result (e, a)

instance (Inferable a, Inferable b) => Inferable (a, b) where 
  infer e (l, r) = do (e' , l') <- infer e l 
                      (e'', r') <- infer e r
                      return (e'', (l', r'))

instance Inferable a => Inferable (Axiom a) where 
  infer e (Axiom n f) = do (e', f') <- infer e f 
                           return (e', Axiom n f')

instance ( Inferable a, Eq a ) => Inferable [a] where 
  infer = curry $ mu (uncurry infer') 
        where infer' e fs = do (es, fs') <- unzip <$> sequence [ infer e f | f <- fs ] 
                               e' <- foldM (/\) e es
                               return (e', fs')

instance Inferable Formula where 
  infer = curry $ mu (uncurry $ flip inferFormula)
    where 

          inferTerm :: InfState e => Term -> e -> Result (e, Term)
          inferTerm t e = pushTrace (show t) ( inferTerm_ t e )

          inferFormula :: InfState e => Formula -> e -> Result (e, Formula)
          inferFormula f e 
                   = case inferFormula_ f e of 
                         Left msgs -> Left $ ("  in " ++ show f):msgs
                         Right r -> Right r

          inferFormula_ :: InfState e => Formula -> e -> Result (e, Formula)
          inferFormula_ (BaseCon0 c) e 
                   = return (e, BaseCon0 c)
          inferFormula_ (BaseAtom (BasePred p ts)) e 
                   = inferFunPred ts (findPred p) predArgs (BaseAtom . BasePred p) e

          inferFormula_ (BaseAtom (BaseEq eq t1 t2)) e 
                   = do (e1, a1') <- inferTerm t1 e 
                        (e2, a2') <- inferTerm t2 e
                        e' <- e1 /\ e2
                        e'' <- assertEq t1 t2 e' 
                        let f = BaseAtom (BaseEq eq a1' a2')
                        return (e'', f)

          inferFormula_ (BaseCon c a1 a2)   e                                     
                   = do (e1, a1') <- inferFormula a1 e 
                        (e2, a2') <- inferFormula a2 e
                        e' <- e1 /\ e2
                        let f = BaseCon c a1' a2'
                        return (e', f)

          inferFormula_ (BaseNot a)         e                                  
                   = do (e', a') <- inferFormula a e
                        let f = BaseNot a'
                        return (e', f)

          inferFormula_ (BaseQuant q v s f)   e                                               
                   = do (e',f') <- inferFormula f (override v s e) 
                        let f'' = BaseQuant q v (findVar v e') f'
                        return $ (remove v e', f'')

          inferTerm_ :: InfState e => Term -> e -> Result (e, Term)

          inferTerm_ t@(BaseVar v s)    e                     
                   = do e' <- push v s e 
                        return (e', BaseVar v (findVar v e'))

          inferTerm_ t@(BaseFun f ts s) e = inferFunPred ts (findFun f) funArgs (\ts -> BaseFun f ts s) e


          inferFunPred :: forall a b e .(InfState e) => 
                          [Term] -> (e -> Result a) -> (Lens' a [SortId]) -> ([Term] -> b) -> e -> Result (e, b)
          inferFunPred    ts         find                args                  build           e      
               = do dec <- find e
                    let as = dec ^. args
                    checkArity ts as
                    (es, ts') <- unzip <$> sequence [ process t s e | (t, s) <- zip ts as ]
                    e' <- foldM (/\) e es
                    let f = build ts'
                    return (e', f)
                      where process :: Term -> SortId -> e -> Result (e, Term)
                            process t s sig = do 
                                (sig', t') <- inferTerm t sig
                                sig'' <- assertSort t' s sig'
                                return (sig'', t')
                            checkArity ts as | lts == las = Right ()
                                             | otherwise = Left [join [ "wrong arity: (expected) ", show las, " /= ", show lts, " (got) " ]]
                                             where lts = length ts
                                                   las = length as
                            

instance Show Conjecture where 
  show (Conjecture f) = show f

instance Show a => Show (Axiom a) where 
  show (Axiom n f) = "(" ++ n ++ ")\t" ++ show f

instance Show Theory where 
  show t = unlines $ [ "Theory: " ++ t^.thName, "" ]
                   ++ sect "Signature" (lines $ show $ t^.thSig )
                   ++ sect "Axioms"    (show <$> t^.thAxioms )
              where sect n lns = ["", n ++ ":" ] ++ [ "\t" ++ l | l <- sort lns ]

