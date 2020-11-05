{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module ToTff(
  ToTff(..)
  ) where 

import Data.Formula
import Data.Formula.Mir
import Data.Formula.Reflective
import Data.Theory
import Data.Signature
---
import Data.List
import Data.List.Index
import Data.Char
import Control.Lens hiding (Const, indexed)
import Control.Monad


tptpElem :: [String] -> String
tptpElem xs = join ["tff( ", intercalate ", " xs, ")."]

class ToTff a where  
  toTff :: a -> String


instance ToTff Connective where 
  toTff And     = "&"
  toTff Or      = "|"
  toTff If      = "<="
  toTff Implies = "=>"
  toTff Iff     = "<=>"

instance ToTff MirTerm where
  toTff (BaseVar v _ )    = toTff v
  toTff (BaseFun f ts _) = funPredTff f ts

instance ToTff Quantifier where
  toTff Existential = "?"
  toTff Universal   = "!"

instance ToTff Polarity where
  toTff Pos = "="
  toTff Neg = "!="

instance ToTff FunId where
  toTff = lower . transOperator

lower (Id (c:cs)) = toLower c : cs

instance ToTff PredId where
  toTff = lower . transOperator

instance ToTff SortId where
  toTff = lower

instance ToTff VarId where
  toTff (Id (c:cs)) = toUpper c : cs

instance ToTff MirForm where
  toTff (BaseAtom (BaseEq eq t1 t2) )    = intercalate " " [ toTff t1, toTff eq, toTff t2 ]
  toTff (BaseAtom (BasePred p ts) )         = funPredTff p ts
  toTff (BaseCon c a1 a2)       = join [ "(", intercalate " " [toTff a1, toTff c,  toTff a2], ")" ]
  toTff (BaseNot a)             = join [ "~", "(", toTff a, ")" ]
  toTff (BaseCon0 Bot)          = "$false"
  toTff (BaseCon0 Top)          = "$true"
  toTff f@(BaseQuant q _ _ _) = to f []
    where to (BaseQuant q' v s f) vs | q' == q = to f ((v,s):vs)
          to f vs = join [toTff q, "[", vs', "]:(", toTff f, ")"]
            where vs' = intercalate ", " [ toTff v ++ ": " ++ toTff s | (v, s) <- reverse vs]

funPredTff f [] = toTff f
funPredTff f ts = join [toTff f, "(", intercalate ", " (toTff <$> ts), ")"]

instance ToTff Sig where
  toTff s = unlines $ join [ decls sgSorts "Sorts"
                           , decls sgFuns "Funs"
                           , decls sgPreds "Preds"
                           , decls sgVars "Vars"
                           ]
    where decls :: ( ToTff a, ToTff (Id a) ) => Lens' Sig (Decls a) -> String -> [ String ]
          decls field name = ( join ["% ", name, ":" ] )
                           : [ tptpElem [toTff n ++ "_type", "type", toTff n  ++ ": " ++ toTff f] | (n, f) <- declList field s ]
                           ++ [""]

instance ToTff Sort where 
  toTff _ = "$tType"

instance ToTff Predicate where 
  toTff f = join ["(", intercalate " * " (toTff <$> f^.predArgs), ") > $o"]

instance ToTff Function where 
  toTff f@(Function [] o)  = join [toTff (f^.funSort)]
  toTff f                  = join ["(", intercalate " * " (toTff <$> f^.funArgs), ") > ", toTff (f^.funSort)]

instance ToTff Var where 
  toTff f = toTff $ f ^.varSort

instance ToTff Conjecture where
    toTff t = tptpElem ["conj", "conjecture", toTff $ conjFormula t ]

instance ToTff (Int, Axiom MirForm) where
    toTff (i, Axiom n f) = tptpElem ["ax"++show i ++ "_" ++ n, "axiom", toTff f ]

instance ToTff Theory where
  toTff th = intercalate "\n" ( -- header: humanReadable : 
                              join sections  )
    where header = comments [line, "Theory: " ++ name, line ]
          line = "====================================================================="
          heading h = comments [ line, h, "" ]
          sections = fmap section [ ("Signature", [ toTff sig ])
                                  , ("Axioms", toTff <$> ax) ]
          section (name, cont) = [ heading name ] ++ cont

          ax   = indexed $  th ^.thAxioms 
          name = th ^.thName 
          sig  = th ^.thSig


          bracket s = "( " ++ s ++ " )"

          comment = ("% " ++) 
          comments = unlines . fmap comment

          humanReadable = ( unlines . fmap comment . lines ) ( show th )

