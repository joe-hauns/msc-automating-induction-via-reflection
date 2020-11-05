{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}

module Serialize (
    serialize
  , allConnectiveSerializers
  , humanReadable
  , humanWritable
  , GenSerialize(..)
  , Quantifiable(..)
  , SerConf(..)
  )  where

import Data.Formula.Common
import Data.Theory.Interpreted
import Data.Signature

import Control.Monad
import Data.List

serialize :: GenSerialize a => a -> String
serialize = genSerialize humanReadable

indent = ("  " ++) 
tup = brac . intercalate ", "
brac = ("(" ++ ) . (++ ")")

class Quantifiable s where
  toQuantifierExpr :: SerConf c => c -> VarId -> s -> String

instance Quantifiable SortId where
  toQuantifierExpr ser v s =  scVar ser v ++ ": " ++  scSort ser s

instance (Quantifiable s) => Quantifiable (Maybe s) where
  toQuantifierExpr ser v  Nothing = scVar ser v 
  toQuantifierExpr ser v (Just s) = toQuantifierExpr ser v s

class SerConf a where 
  scBin   :: a -> Connective         -> String
  scNeg   :: a -> NegationConnective -> String
  scQuant :: a -> Quantifier         -> String
  scPol   :: a -> Polarity           -> String
  scCon0  :: a -> Con0               -> String

  scConst :: a -> String -> String
  scConst a s = s ++ "()"

  scTypeArrow :: a -> String

  scTypeColon :: a -> String
  scTypeColon _ = ":"

  scVar :: a -> VarId  -> String
  scVar _ = unId

  scFunc :: a -> FunId  -> String
  scFunc _ = unId

  scSort :: a -> SortId -> String
  scSort _ = unId

  scPred :: a -> PredId -> String
  scPred _ = unId

unId (Id a) = a

data AnySerConf where 
  AnySerConf :: SerConf c => c -> AnySerConf

instance SerConf AnySerConf where
  scBin   (AnySerConf c) = scBin c
  scConst (AnySerConf c) = scConst c
  scNeg   (AnySerConf c) = scNeg c
  scCon0  (AnySerConf c) = scCon0 c
  scQuant (AnySerConf c) = scQuant c
  scPol   (AnySerConf c) = scPol c
  scTypeArrow (AnySerConf c) = scTypeArrow c
  scTypeColon (AnySerConf c) = scTypeColon c
  scVar    (AnySerConf c) = scVar  c
  scFunc   (AnySerConf c) = scFunc c
  scSort   (AnySerConf c) = scSort c
  scPred   (AnySerConf c) = scPred c
  

------------------------------------------- Human readable

data HumanReadable = HumanReadable

instance SerConf HumanReadable where
  scCon0  _ = show
  scBin   _ = show
  scNeg   _ = show
  scQuant _ = show
  scTypeArrow _ = "↦"
  scTypeColon _ = ":"
  scPol _ = \case 
               Pos ->  "="
               Neg ->  "≠"

humanReadable = HumanReadable

------------------------------------------- Human writable

data HumanWritable = HumanWritable
humanWritable = HumanWritable

instance SerConf HumanWritable where
  scBin   _ = \case
                  And     -> "/\\"
                  Or      -> "\\/"
                  If      -> "<-"
                  Implies -> "->"
                  Iff     -> "<->"
  scNeg   _ = \case
                  NegationConnective -> "~"
  scCon0 _ Top = "true"
  scCon0 _ Bot = "false"
  scTypeArrow _ = "->"
  scTypeColon _ = ":"
  scPol   _ = \case 
                  Pos -> "="
                  Neg -> "/="
  scQuant _ = \case 
                  Existential -> "exists"
                  Universal   -> "forall"

allConnectiveSerializers = [ AnySerConf humanReadable, AnySerConf humanWritable ]

class GenSerialize a where 
  genSerialize :: SerConf c => c -> a -> String

instance GenSerialize FunId where
  genSerialize ser id = scFunc ser id

instance GenSerialize VarId where
  genSerialize ser id = scVar ser id

instance GenSerialize PredId where
  genSerialize ser id = scPred ser id

instance GenSerialize SortId where
  genSerialize ser id = scSort ser id

instance GenSerialize Predicate where 
  genSerialize ser (Predicate as) = "P(" ++ intercalate "," (fmap ( scSort ser ) as)++ ")"

instance GenSerialize NegationConnective where
  genSerialize ser n = scNeg ser n

instance GenSerialize Polarity where 
  genSerialize ser p = scPol ser p

instance GenSerialize Con0 where 
  genSerialize = scCon0 

instance GenSerialize Connective where 
  genSerialize ser c = scBin ser c

instance GenSerialize Quantifier where 
  genSerialize ser q = scQuant ser q

instance GenSerialize (BaseTerm s) where
  genSerialize ser (BaseVar v _)    = genSerialize ser v
  genSerialize ser (BaseFun f ts _) = genSerializeFunOrPred ser f ts

instance GenSerialize (BaseAtom s) where 
  genSerialize ser (BaseEq p t t') = intercalate " " [
        genSerialize ser t, 
        genSerialize ser p, 
        genSerialize ser t']
    -- where eq Pos = "="
    --       eq Neg = "/="
  genSerialize ser (BasePred p ts) = genSerializeFunOrPred ser p ts

instance (Quantifiable s) => GenSerialize (BaseForm BaseAtom s) where 
  genSerialize ser (BaseAtom a) = genSerialize ser a
  genSerialize ser (BaseCon0 c) = scCon0 ser c 
  genSerialize ser (BaseNot phi) = genSerialize ser NegationConnective ++ serBrac ser phi
  -- genSerialize ser (BaseQuant q v s phi) = join [ genSerialize ser q, " ", toQuantifierExpr ser v s, ". ", genSerialize ser phi]
  genSerialize ser phi@(BaseQuant q _ _ _) = join [ 
      genSerialize ser q, " ", quantString phi, ". ", serBrac ser (quantsStripped q phi)]
    where 
      quantPrefix q (BaseQuant q' v s psi) | q' == q   = (v,s):quantPrefix q psi
      quantPrefix _ _                                  = []
      quantString phi = intercalate ", " $ fmap (uncurry $ toQuantifierExpr ser) (quantPrefix q phi)
      quantsStripped q (BaseQuant q' v s psi) | q' == q = quantsStripped q psi
      quantsStripped q phi                              = phi
  genSerialize ser (BaseCon   c phi psi) = serBrac ser phi ++ " " ++ genSerialize ser c  ++ " "++ serBrac ser psi

serBrac :: (SerConf c, GenSerialize (BaseForm a s)) => c -> BaseForm a s -> String
serBrac ser phi@(BaseCon _ _ _) =  brac . genSerialize ser $ phi
serBrac ser phi                 =         genSerialize ser phi

genSerializeFunOrPred ser f [l,r] | isOperator f = brac . intercalate " " $ [ genSerialize ser l, genSerialize ser f, genSerialize ser r]
genSerializeFunOrPred ser f [] = scConst ser $  genSerialize ser f
genSerializeFunOrPred ser f vs = join [genSerialize ser f, "(", intercalate "," (genSerialize ser <$> vs), ")"]

instance (Quantifiable s) => GenSerialize (GenBenchmark s) where 
  genSerialize ser (Benchmark t c)  = unlines $ 
                       ("theory"     : ( indent <$> lines (genSerialize ser t) ))
                    ++ ("conjecture" : ( indent           (genSerialize ser c ++ ".") ) : [])
                        
instance (Quantifiable s) => GenSerialize (GenTheory s) where 
  genSerialize ser (Theory name ax sig dtypes) =  
              -- TODO genSerialize name
              unlines . fmap (++ ".") . filter (/= "") $ 
                   fmap ( genSerialize ser ) sig 
                ++ fmap ( ("inductive "++) . genSerialize ser ) dtypes
                ++ fmap ( genSerialize ser ) ax
  
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------


genSerTup ser = tup . fmap ( genSerialize ser)

instance GenSerialize Type where 
  genSerialize ser ( Pred ts  ) = "P" ++ genSerTup ser ts 
  genSerialize ser ( [] :-> t ) = genSerialize ser t
                                    

  genSerialize ser ( [a] :-> t ) = unwords [ 
                                      genSerialize ser a 
                                    , scTypeArrow ser 
                                    , genSerialize ser t
                                    ]

  genSerialize ser ( ts :-> t ) = unwords [ 
                                      genSerTup ser ts 
                                    , scTypeArrow ser 
                                    , genSerialize ser t
                                    ]

instance GenSerialize SymDec where 
  genSerialize ser (_   :::: Srt ) = ""
  genSerialize ser (sym :::: kind) = join [ id kind sym, "\t", scTypeColon ser, " ", genSerialize ser kind ] 
    where id (_ :-> _) = scFunc ser . Id . unId
          id (Pred _)  = scPred ser . Id . unId
          id  Srt      = scSort ser . Id . unId
          unId (Id a) = a


