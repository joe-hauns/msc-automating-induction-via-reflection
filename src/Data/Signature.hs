{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}

module Data.Signature(
      SortDecl(..)
    , FunDecl(..)
    , VarDecl(..)
    , PredDecl(..)
    , decl
    , tid
    , decls
    , Decls
    , findSym
    , union
    , removeSym
    , intersectionWith
    , override
    , empty
    , member
    , declList
    , termSort
    , Sig(..)
    , sgVars, sgFuns, sgSorts, sgPreds
    , declId
    , Decl (..)
    , mkSig, Type(..), SymDec(..), toDecls
  ) where

import Data.Formula
--
import Control.Lens hiding (element, Const, to)
import Control.Monad
import Control.Applicative hiding (empty)
--
import Data.Function
import Data.Data
import Data.HashMap hiding (filter, lookup, union, member, intersectionWith, empty)
import Data.HashSet hiding (filter, lookup, union, member, empty)
import Data.List    hiding ( union, lookup)
import Prelude      hiding (lookup)
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.HashSet as Set
import qualified Data.HashMap as Map

type Decls t = [(Id t, t)]
type Decl a = (Id a, a)
declId = fst
decl a b = (a, b)

decls :: [Decl a] -> Decls a
decls = id

declList :: Lens' Sig (Decls a) -> Sig -> [ Decl a ]
declList = view

lookup :: Id a -> Decls a -> Maybe a
lookup id = fmap snd . find ((==id).fst)

union :: (Eq t) => Decls t -> Decls t -> Decls t
union = List.union

intersectionWith ::  (a -> a -> b) -> Decls a ->  Decls a -> [(Id a, b)]
intersectionWith f as bs = [ ( id, f a b ) | (id, a) <- as
                                           , b <- lookup' id bs ]
                                   where lookup' a b = case lookup a b of 
                                                        Just a -> [a]
                                                        Nothing -> []


member ::  Id a -> Decls a -> Bool
member id decls = or [ id == id' | (id',_) <- decls  ]

type SortDecl  = Decl Sort
type VarDecl   = Decl Var
type PredDecl  = Decl Predicate 
type FunDecl   = Decl Function 

data Type   = Srt 
            | Pred [SortId]
            | [SortId] :-> SortId
               deriving (Show, Eq, Ord, Data)
infixr 4 :->
infixr 3 ::::

tid :: Id a -> Id b
tid (Id a) = Id a

data SymDec = Id () :::: Type  deriving (Data)

instance Eq SymDec where 
  ( (Id i) :::: a ) == ( (Id j) :::: b ) = i == j && a == b

instance Show SymDec where 
  show (id :::: ty) = (show id) ++ ": " ++ (show ty)

instance Ord SymDec where 
  compare = ( compare `on` dec ) <> ( compare `on` sym ) 
    where sym  (Id s :::: _) = s
          dec  (_ :::: d) = d

mkSig :: [SymDec] -> Sig
mkSig syms = Sig { _sgFuns   =     [ decl (id f) (Function as b) | f :::: as :-> b <- syms               ]
               , _sgSorts  = nub [ decl (id s) Sort            | s <- [ id s | s :::: Srt <- syms   ]
                                                                   ++ [ s | _ :::: Pred as <- syms 
                                                                          , s <- as                 ]
                                                                   ++ [ s | _ :::: as :-> _ <- syms 
                                                                          , s <- as                 ]
                                                                   ++ [ s | _ :::: _ :-> s <- syms  ]
                                                                                                       ]
               , _sgVars   = []
               , _sgPreds  = [ decl (id p) (Predicate as)      | p :::: Pred as  <- syms               ] 
               }
  where id :: Id a -> Id b
        id (Id s) = Id s


empty :: Sig
empty = Sig { 
    _sgFuns   = []
  , _sgSorts  = []
  , _sgVars   = []
  , _sgPreds  = []
  }

data Sig = Sig { _sgFuns   :: Decls Function
               , _sgSorts  :: Decls Sort
               , _sgVars   :: Decls Var
               , _sgPreds  :: Decls Predicate }
makeLenses ''Sig

instance Eq Sig where 
  (Sig a0 a1 a2 a3) == (Sig b0 b1 b2 b3)
     = a0 ~~ b0
    && a1 ~~ b1
    && a2 ~~ b2
    && a3 ~~ b3
      where a ~~ b = sort a == sort b
  


override :: Lens' Sig (Decls a) -> Id a -> a -> Sig -> Sig
override field id dec = (field %~ ((id,dec):))
                      . (removeSym field id)

removeSym :: Lens' Sig (Decls a) -> Id a -> Sig -> Sig
removeSym field id = field %~ filter ( (/= id).fst )


findSym :: Lens' Sig (Decls a) -> Id a -> Sig -> Maybe a
findSym field sym = fmap snd 
                   . List.find ((== sym).fst)  
                   . view field

termSort :: Sig -> Term -> Maybe SortId
termSort sig (BaseFun f _ s) = s <|> (view funSort <$> findSym sgFuns f sig)
termSort sig (BaseVar v   s) = s <|> (view varSort <$> findSym sgVars v sig)

instance Show Sig where
  show s = unlines $ join [  decls sgSorts
                           , decls sgPreds
                           , decls sgFuns
                           , decls sgVars
                           ]
    where decls :: ( Show a ) => Lens' Sig (Decls a) -> [ String ]
          decls field = [ show n ++ ": " ++ show f | (n, f) <- declList field s ]


toDecls :: Sig -> [SymDec]
toDecls s = [ Id f :::: as :-> b | (Id f, Function as b) <- s ^.sgFuns  ]
         ++ [ Id p :::: Pred as  | (Id p, Predicate as ) <- s ^.sgPreds ]
         ++ [ error (show v)     | v                  <- s ^.sgVars  ]
         ++ [ Id s :::: Srt      | (Id s, Sort)          <- s ^.sgSorts ]

  where id :: Id a -> Id b
        id (Id s) = Id s

instance MapIds SymDec where 
  mapIds f (id :::: ty) = f id :::: mapIds f ty

instance MapIds Type where 
  mapIds _ Srt = Srt
  mapIds f (as :-> a) = fmap f as :-> f a
  mapIds f (Pred as)  = Pred $ fmap f as

