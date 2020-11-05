{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Theory.Interpreted (
       Theory(..), GenTheory(..), MirTheory(..)
     , Benchmark(..), GenBenchmark(..), MirBenchmark(..)
     , ctors 
     , uninterpretedSorts
     , dtypes
     , functions
     , predicates
     , DataType(..)
     , datatypes
     , RecDef(..)
     , RecCase(..)
     , recDefs
     , nonRecDefs
     , addAxioms
     , nonRecFuns
     , nonRecPreds
    ) where

import Util
import Data.Data hiding (DataType)
import Data.Maybe
import Data.Map hiding (mapMaybe)
import qualified Data.Map as Map
import Data.Formula
import Data.Formula.Mir
import Data.List
import Data.Signature
import Debug.Trace

data DataType = DataType {
                   dtSort  :: SortId 
                 , dtCtors :: [ FunDecl ]
                 } deriving (Eq, Show)

instance Ord DataType where 
   x <= y | x == y = True
   (DataType s cs) <= (DataType s' cs') 
      | any (s  `usedBy`) cs' = True
      | any (s' `usedBy`) cs  = False
      | s <  s' = True
      | s == s' = cs <= cs'
      | otherwise = False
        where usedBy s (_, Function as _) = s `elem` as

data GenTheory s = Theory {
                thName      :: String
              , thAxioms    :: [ BaseForm BaseAtom s ]
              , thSignature :: [ SymDec ]
              , thDataTypes :: [ FunId ]
              } deriving ( Data, Functor, Eq )

addAxioms :: [ BaseForm BaseAtom s ] -> GenTheory s -> GenTheory s
addAxioms as t = Theory {
                thName      = thName t      
              , thAxioms    = thAxioms t    ++ as
              , thSignature = thSignature t 
              , thDataTypes = thDataTypes t 
              }

type Theory    = GenTheory (Maybe SortId)
type MirTheory = GenTheory SortId

instance Semigroup (GenTheory s) where
  t1 <> t2 = Theory {
                thName      = thName      t1 <> thName      t2
              , thAxioms    = thAxioms    t1 <> thAxioms    t2
              , thSignature = thSignature t1 <> thSignature t2
              , thDataTypes = thDataTypes t1 <> thDataTypes t2
              }


type Benchmark    = GenBenchmark (Maybe SortId)
type MirBenchmark = GenBenchmark SortId
data GenBenchmark s = Benchmark {
                    bTheory     :: GenTheory s
                  , bConjecture :: BaseForm BaseAtom s
                  } deriving (Data, Eq)

instance MapTerms (GenBenchmark s) s where
  mapTerms f (Benchmark t c) = (Benchmark (mapTerms f t) (mapTerms f c))

instance MapTerms (GenTheory s) s where
  mapTerms f (Theory n ax sig dtys) = (Theory n (mapTerms f <$> ax) sig dtys)

predicates :: GenTheory s -> [ PredDecl ]
predicates t = [ decl (Id p) (Predicate as) | Id p :::: Pred as  <- thSignature t ]

functions :: GenTheory s -> [ FunDecl ]
functions t = [ decl (Id f) (Function as b) | Id f :::: as :-> b  <- thSignature t
                                            , not $ Id f `elem` thDataTypes t ]
ctors :: GenTheory s -> SortId -> [ FunDecl ]
ctors t s = [ decl (Id f) (Function as s) | Id f :::: as :-> s'  <- thSignature t
                                          , s == s'
                                          , Id f `elem` thDataTypes t ]

-- trace' a = trace (show a) a

datatypes :: GenTheory s -> [ DataType ] 
-- datatypes t = nub [ s | Id f :::: as :-> s  <- thSignature t
--                       , Id f `elem` thDataTypes t ]
datatypes t = sort [ DataType s (ctors t s) | s <- dtypes t ]

dtypes :: GenTheory s -> [ SortId ] 
-- dtypes t = [ (Id s) | Id s <- sorts t 
--                     , ctors t (Id s) /= []     ]
dtypes t = nub [ s | Id f :::: as :-> s  <- thSignature t
                   , Id f `elem` thDataTypes t ]

uninterpretedSorts :: GenTheory s -> [ SortId ] 
uninterpretedSorts t = [ (Id s) | Id s :::: Srt <- thSignature t
                                , not $ Id s `elem` dtypes t ]


pdecl :: MirTheory -> PredId -> Predicate
pdecl th fid = snd 
             . fromJust 
             . find ((== fid).fst) 
             $ predicates th

fdecl :: MirTheory -> FunId -> Function
fdecl th fid = snd 
             . fromJust 
             . find ((== fid).fst) 
             $ functions th

nonRecDefs :: MirTheory -> [ MirForm ]
nonRecDefs th = [ f | f <- thAxioms th 
                   , Nothing == transDef f ]

nonRecFuns :: MirTheory -> [ FunDecl ]
nonRecFuns th = [ f | f <- functions th  
                    , not $ f `elem` [ (i, f') | RecFunDef i f' _ <- recDefs th ] ]

nonRecPreds :: MirTheory -> [ PredDecl ]
nonRecPreds th = [ f | f <- predicates th  
                     , not $ f `elem` [ (i, f') | RecPredDef i f' _ <- recDefs th ] ]

recDefs :: MirTheory -> [ RecDef ]
recDefs th = funCaseDefs ++ predCaseDefs
    where caseDefs = mapMaybe transDef (thAxioms th)
          funCaseDefs  = uncurry ( toRecDef RecFunDef  fdecl ) <$> groupByFst [ x | Left  x <- caseDefs ]
          predCaseDefs = uncurry ( toRecDef RecPredDef pdecl ) <$> groupByFst [ x | Right x <- caseDefs ]

          toRecDef cons decl id cs = cons id (decl th id) cs

type IndexedCaseDef = Either (FunId, RecCase MirTerm) (PredId, RecCase MirForm)

transDef :: MirForm -> Maybe IndexedCaseDef
transDef frm@(BaseQuant Universal _ _ f)                = case transDef f of
  Just ( Left (f, RecCase _ as r) ) -> Just $ Left (f, RecCase frm as r)
  Just ( Right(f, RecCase _ as r) ) -> Just $ Right(f, RecCase frm as r)
  Nothing                           -> Nothing

transDef frm@(BaseAtom (BaseEq Pos (BaseFun f as _) r)) = Just $ Left  (f, RecCase frm as r)
transDef frm@          (BaseAtom (BasePred f as))       = Just $ Right (f, RecCase frm as (BaseCon0 Top))
transDef frm@(BaseNot  (BaseAtom (BasePred f as)))      = Just $ Right (f, RecCase frm as (BaseCon0 Bot))
transDef frm@(BaseCon Iff (BaseAtom (BasePred f as)) r) = Just $ Right (f, RecCase frm as r)
transDef f@_ = Nothing

data RecCase t = RecCase { recFormula :: MirForm 
                         , recLhs     :: [MirTerm] 
                         , recRhs     :: t } deriving (Eq)


data RecDef = RecFunDef  FunId  Function  [RecCase MirTerm] 
            | RecPredDef PredId Predicate [RecCase MirForm]
          deriving (Eq)


instance MapIds s => MapIds (GenTheory s) where
  mapIds f (Theory name ax sig dtys) = Theory name (mapIds f <$> ax) (mapIds f <$> sig) (f <$> dtys)

instance MapIds s => MapIds (GenBenchmark s) where
  mapIds f (Benchmark t c) = Benchmark  (mapIds f t) (mapIds f c)
