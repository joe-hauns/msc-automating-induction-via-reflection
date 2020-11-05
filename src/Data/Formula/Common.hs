
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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes #-}
module Data.Formula.Common ( 
                    module Data.Formula.Common
) where
import Util
--
import Data.Char
import Data.List
import Data.Data
import Control.Monad
import Control.Arrow
import Data.Hashable
import GHC.Generics (Generic)
import Control.Lens hiding (element, Const, to)
import Debug.Trace

--
import Data.HashSet hiding (filter)
import qualified Data.HashSet as Set


data BaseForm a s  = BaseAtom (a s)
                   | BaseCon0 Con0
                   | BaseNot   (BaseForm a s)
                   | BaseQuant Quantifier VarId s (BaseForm a s)
                   | BaseCon   Connective (BaseForm a s) (BaseForm a s)
                     deriving ( Eq, Ord, Generic, Functor, Data )

dropQ :: Quantifier -> BaseForm a s -> BaseForm a s
dropQ q (BaseQuant q' _ _ f') | q == q' = dropQ q f'
dropQ _ f = f

mapAtom :: (a s -> a' s) -> BaseForm a s -> BaseForm a' s
mapAtom f (BaseCon0 c)        = BaseCon0 c
mapAtom f (BaseAtom a)        = BaseAtom (f a)
mapAtom f (BaseNot x)         = BaseNot (mapAtom f x)
mapAtom f (BaseQuant q v s x) = BaseQuant q v s (mapAtom f x)
mapAtom f (BaseCon c x y)     = BaseCon c (mapAtom f x) (mapAtom f y)

class MapFunIds a where 
  mapFunIds :: (FunId -> FunId) -> a -> a

class MapTerms a s | a -> s where 
  mapTerms :: (BaseTerm s -> BaseTerm s) -> a -> a

instance (MapTerms (a s) s) => MapTerms (BaseForm a s) s where
  mapTerms f = mapAtom (mapTerms f)

instance MapTerms (BaseAtom s) s where
  mapTerms f (BaseEq p s t) = BaseEq p (mapTerms f s) (mapTerms f t)
  mapTerms f (BasePred p ts) = BasePred p (fmap f ts)

instance MapTerms (BaseTerm s) s where 
  mapTerms f (BaseFun fn ts s) = f $ BaseFun fn (fmap (mapTerms f) ts) s
  mapTerms f v@(BaseVar _ _) = f v

instance MapFunIds (a s) => MapFunIds ( BaseForm a s ) where
  mapFunIds f = mapAtom (mapFunIds f)

instance MapFunIds (BaseAtom s) where
  mapFunIds f a = mapTerms ( mapFunIds f ) a
  
instance MapFunIds (BaseTerm s) where
  mapFunIds f (BaseFun fn ts s) = BaseFun (f fn) (mapFunIds f <$> ts) s
  mapFunIds f v@(BaseVar _ _) = v


data BaseAtom s = BaseEq Polarity (BaseTerm s) (BaseTerm s)
                | BasePred PredId  [(BaseTerm s)]
                     deriving ( Eq, Ord, Generic, Data, Functor )
instance (Hashable s) => Hashable (BaseAtom s)

data BaseTerm s = BaseFun   FunId [(BaseTerm s)] s
                | BaseVar   VarId                s
                -- | BaseConst ConstId              s
               deriving ( Eq, Ord, Generic, Data, Functor )
instance (Hashable s) => Hashable (BaseTerm s)

btSort :: BaseTerm s -> s
btSort (BaseFun _ _ s) = s
btSort (BaseVar _   s) = s
-- btSort (BaseConst _ s) = s

instance (Hashable (a s), Hashable s) => Hashable (BaseForm a s)

class SortAnnotation s where 
  fromSort :: SortId -> s

instance SortAnnotation SortId where 
  fromSort = id

instance SortAnnotation (Maybe SortId) where 
  fromSort = Just 

class FreeVars a s | a -> s where 
  freeVs :: a -> [(VarId, s)]


data NegationConnective = NegationConnective

instance (Eq s, FreeVars (a s) s) => FreeVars (BaseForm a s) s where 
  -- freeVs :: BaseForm a s -> [(VarId, s)] 
  freeVs =  nub . fv
    where fv (BaseAtom a) = freeVs a
          fv (BaseCon   _ f1 f2) = fv  =<< [f1, f2]
          fv (BaseNot   f)       = fv f
          fv (BaseCon0 _) = []
          fv (BaseQuant q v s f) = filter ((/= v) . fst)
                                 $ fv f

instance (Eq s) => FreeVars (BaseAtom s) s where 
  freeVs (BaseEq _ s t)  = nub $ freeVs =<< [ s, t ]
  freeVs (BasePred _ ts) = nub $ freeVs =<< ts

instance (Eq s) => FreeVars (BaseTerm s) s where
  freeVs (BaseFun _ ts _) = nub $ freeVs =<< ts
  freeVs (BaseVar v s)    = [(v,s)]
  -- freeVs (BaseConst _ _)  = []

-- instance FreeVars (BaseForm a s) s => Closable (BaseForm a s) where 
instance (Ord s, FreeVars (a s) s) => Closable (BaseForm a s) where 
  closure q f = seqA [ BaseQuant q v s | (v, s) <- vs ] f
    where vs = reverse $ sort $ freeVs f




class AllVars a s | a -> s where 
  allVs :: a -> [(VarId, s)]

instance (Eq s, AllVars (a s) s) => AllVars (BaseForm a s) s where 
  allVs =  nub . av
    where av (BaseAtom a) = allVs a
          av (BaseCon   _ f1 f2) = av  =<< [f1, f2]
          av (BaseNot   f)       = av f
          av (BaseCon0 _) = []
          av (BaseQuant q v s f) = (v,s):av f

instance (Eq s) => AllVars (BaseAtom s) s where 
  allVs (BaseEq _ s t)  = nub $ allVs =<< [ s, t ]
  allVs (BasePred _ ts) = nub $ allVs =<< ts

instance (Eq s) => AllVars (BaseTerm s) s where
  allVs (BaseFun _ ts _) = nub $ allVs =<< ts
  allVs (BaseVar v s)    = [(v,s)]
  -- allVs (BaseConst _ _)  = []






class Closable a where 
  closure :: Quantifier -> a -> a
  universalClosure :: a -> a
  universalClosure = closure Universal
  existentialClosure :: a -> a
  existentialClosure = closure Existential

class NormalForm a where 
  norm :: a -> a

class Subs a t | a -> t where 
  subs :: VarId -> t -> a -> a

instance Subs (BaseTerm s) (BaseTerm s) where
  -- subs v t' (BaseConst c s) = BaseConst c s
  subs v t' (BaseVar v' s) | v' == v   = t'
                           | otherwise = BaseVar v' s
  subs v t' (BaseFun f ts s) = BaseFun f [ subs v t' t | t <- ts ] s

instance Subs (BaseForm BaseAtom s) (BaseTerm s) where
    subs v t (BaseAtom (BaseEq e a1 a2) ) = (BaseAtom (BaseEq e (subs v t a1)  (subs v t a2)) )
    subs v t (BaseAtom (BasePred p ts) )     = (BaseAtom (BasePred  p (subs v t <$> ts)) )    
    subs v t (BaseCon   c a1 a2) = (BaseCon   c (subs v t a1) (subs v t a2)) 
    subs v t (BaseNot   f)       = (BaseNot     (subs v t f))       
    subs v t (BaseCon0 c)          = BaseCon0 c
    subs v t (BaseQuant q v' s f)  = let f' = if v' == v 
                                             then (BaseQuant q v' s (subs v' (BaseVar v'' s) f))   
                                             else f
                                    in BaseQuant q v' s (subs v t f') 
                                               where v'' = (\(Id i) -> Id (i ++ "_")) v'

instance NormalForm (BaseForm BaseAtom s) where 
  norm f = dbr 0 f
    where dbr :: Int -> (BaseForm BaseAtom s) -> (BaseForm BaseAtom s)
          dbr i (BaseQuant q v s f)   = BaseQuant q v' s (dbr (i+1) (subs v (BaseVar v' s) f))
           where v' = Id ("v" ++ show i) 

          dbr i (BaseAtom (BaseEq e t1 t2) ) = (BaseAtom (BaseEq e t1 t2) )
          dbr i (BaseAtom (BasePred p ts) )     = (BaseAtom (BasePred p ts) )
          dbr i (BaseCon  c f1 f2) = (BaseCon   c (dbr i f1) (dbr i f2)) 
          dbr i (BaseNot  f)       = (BaseNot   (dbr i f))       
          dbr i (BaseCon0 c)       = BaseCon0 c

betaEquiv :: ( NormalForm a, Eq a ) => a -> a -> Bool
betaEquiv a b = norm a == norm b

-- Beta equivalence without equality orientation
betaEquiv' :: ( Ord s, Eq s ) => BaseForm BaseAtom s -> BaseForm BaseAtom s -> Bool
betaEquiv' a b = norm' a == norm' b
  where norm' = normEq . norm
        normEq (BaseAtom (BaseEq e l r) ) | l > r = (BaseAtom (BaseEq e r l) )
        normEq (BaseAtom a)  = (BaseAtom a)
        normEq (BaseCon c f1 f2) = (BaseCon   c (normEq f1) (normEq f2)) 
        normEq (BaseNot f)       = (BaseNot   (normEq f))       
        normEq (BaseQuant q v s f) = (BaseQuant q v s (normEq f))
        normEq (BaseCon0 c)        = (BaseCon0 c)

data Function = Function { _funArgs :: [SortId] 
                         , _funSort :: SortId 
                         } deriving ( Eq, Ord, Data )

instance Show Function where 
  show (Function as o) = intercalate " , " (fmap show as) ++ " -> " ++ show o

data Predicate = Predicate { _predArgs :: [SortId] 
                           } deriving ( Eq, Ord, Data )

instance Show Predicate where 
  show (Predicate as) = "P(" ++ intercalate " , " (fmap show as)++ ")"

data Sort = Sort deriving ( Eq, Ord, Data )
instance Show Sort where 
  show Sort = "Sort"

data Const = Const { _constSort :: SortId } deriving ( Eq, Ord, Data )
instance Show Const where 
  show (Const c) = show c

data Var = Var { _varSort :: SortId} deriving ( Eq, Ord, Data )

unVar (Var s) = s

instance Show Var where 
  show (Var v) = "Var("++ show v ++ ")"

mapId :: (String -> String) -> Id a -> Id a
mapId f (Id a) = (Id a)

data Id a = Id String 
          -- | Dot (Id a)
          -- | SubScript (Id a) (Id a)
          deriving ( Eq, Generic, Ord, Data )

instance Hashable (Id a)

type FunId = Id Function
type PredId = Id Predicate
type ConstId = Id Const 
type VarId = Id Var
type SortId = Id Sort

data Con0 = Bot | Top
               deriving ( Eq, Ord, Generic, Data, Enum ) -- FormulaDerivation
allCon0 = [Bot ..]
instance Hashable Con0

data Connective = And | Or | Iff | Implies | If 
               deriving ( Eq, Ord, Generic, Data, Enum ) -- FormulaDerivation
allConnectives = [And ..]
instance Hashable Connective
            
data Quantifier = Universal | Existential
               deriving ( Eq, Ord, Generic, Data, Enum ) -- FormulaDerivation
allQuantifiers = [Universal ..]
instance Hashable Quantifier



instance Show NegationConnective where
  show NegationConnective = "¬"


data Polarity = Pos | Neg
               deriving ( Eq, Ord, Generic, Data, Enum ) -- FormulaDerivation
allPolarities = [Pos ..]
instance Hashable Polarity

instance Show Connective where 
  show And     = "∧"
  show Or      = "∨"
  show If      = "←"
  show Implies = "→"
  show Iff     = "↔"

instance Show Con0 where 
  show Bot = "⊥"
  show Top = "⊤"


instance Show Quantifier where 
  show Existential = "∃"
  show Universal   = "∀"

transOperator :: Id a -> Id a
transOperator (Id s) = Id (transOp opName s)
-- transOperator (Id s) | any ((==s) . snd) operatorNames  = error $ show s
--                      | otw = case find ( (== s) . fst ) operatorNames of
--                                       Just (_, s') -> Id s'
--                                       Nothing      -> Id s

instance Show (Id a) where
  show (Id s) = s


showFunOrPred f [l,r] | isOperator f = join [ "(", show l, " ", show f, " ", show r,  ")"]
showFunOrPred f vs = join [show f, "(", intercalate ", " (show <$> vs),  ")"]
isOperator (Id (x:xs)) = not $ isAlphaNum x

makeLenses ''Const
makeLenses ''Predicate
makeLenses ''Function
makeLenses ''Var


class MapIds a where 
  mapIds :: (forall b. Id b -> Id b) -> a -> a

instance (MapIds (a s), MapIds s) => MapIds ( BaseForm a s ) where
  mapIds f (BaseCon0 c)        = BaseCon0 c
  mapIds f (BaseAtom a)        = BaseAtom (mapIds f a)
  mapIds f (BaseNot x)         = BaseNot (mapIds f x)
  mapIds f (BaseQuant q v s x) = BaseQuant q (f v) (mapIds f s) (mapIds f x)
  mapIds f (BaseCon c x y)     = BaseCon c (mapIds f x) (mapIds f y)

instance (MapIds s) => MapIds (BaseAtom s) where
  mapIds f (BaseEq p l r)  = BaseEq p (mapIds f l) (mapIds f r)
  mapIds f (BasePred p ts) = BasePred (f p) (mapIds f <$> ts)
  
instance (MapIds s) => MapIds (BaseTerm s) where
  mapIds f (BaseFun fn ts s) = BaseFun (f fn) (mapIds f <$> ts) (mapIds f s)
  mapIds f (BaseVar v s) = BaseVar (f v) (mapIds f s)

instance MapIds (Id s) where
  mapIds f = f

instance MapIds (Maybe(Id s)) where
  mapIds f = fmap f

alphaNumIds :: MapIds a => a -> a
alphaNumIds = mapIds $ \(Id x) -> Id (x >>= clean)
  where clean '\'' = "Dot"
        clean '+' = "Plus"
        clean '-' = "Minus"
        clean '*' = "Times"
        clean x = [x]

