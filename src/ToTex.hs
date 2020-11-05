{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module ToTex (ToTex(toTex), Tex, compileTex, texMath, toTexStr, texMacroCall) where 

import Util
import Data.Formula
import Data.List
import Text.Printf
import Control.Monad

newtype Tex = Tex String
-- newtype TexRow = TexRow [Tex]
-- newtype TexTable = TexTable [Tex]

unTex (Tex s) = s
texMacroCall :: String -> [Tex] -> Tex
texMacroCall name as = Tex ("\\" ++ name ++ (concat $ fmap ( printf "{%s}" . compileTex ) as))
compileTex (Tex s) = s
toTexStr :: String -> Tex
toTexStr = Tex . printf "\\text{%s}" 

texMath = Tex


class ToTex a where 
  toTex :: a -> Tex
  toTex = Tex . tex

  tex :: a -> String

instance ToTex Function where 
  tex (Function as o) = intercalate " \\times " (fmap tex as) ++ " \\mapsto " ++ tex o

instance ToTex Predicate where 
  tex (Predicate as ) = "\\mathcal{P}(" ++ intercalate " \\times " (fmap tex as) ++ ")"

instance ToTex (Id Var) where 
  tex = unId
unId (Id a) = a

instance ToTex (Id Sort) where 
  tex = printf "\\sortId{%s}" . unId

instance ToTex Connective where 
  tex And     = "\\land"
  tex Or      = "\\lor"
  tex If      = "\\lif"
  tex Implies = "\\limplies"
  tex Iff     = "\\liff"

instance ToTex Quantifier where 
  tex Existential = "\\exists"
  tex Universal   = "\\forall"

instance ToTex Int where tex = show

instance ToTex Sort where 
  tex Sort = "Sort"

instance ToTex Const where 
  tex (Const c) = tex c

instance ToTex Var where 
  tex (Var v) = "Var("++ tex v ++ ")"

instance ToTex Term where
  tex (BaseVar v _)    = tex v
  tex (BaseFun f vs _) = texFunOrPred f vs

instance Show Tex where show = unTex

instance ToTex Formula where
  tex (BaseAtom (BaseEq Pos a1 a2) ) = unwords [ tex a1, "\\objEq", tex a2 ]
  tex (BaseAtom (BaseEq Neg a1 a2) ) = unwords [ tex a1, "\\objNeq", tex a2 ]
  tex (BaseAtom (BasePred f vs) )    = texFunOrPred f vs
  tex (BaseCon c a1 a2)   = par $ unwords [tex a1, tex c, tex a2]
  tex (BaseNot a)         = unwords $ [ "\\lnot",  par $ tex a ]
  tex (BaseQuant q v Nothing f)  = unwords [tex q, tex v, ".", tex f]
  tex (BaseQuant q v (Just s) f) = unwords [tex q, tex v, ":", tex s, ".", tex f]
          -- join2 sep a b = intercalate ( " " ++ sep ++ " " ) $ tex <$> [a,b]
          -- connective a b c = bracket $ join2 a b c

instance Semigroup Tex where
  (Tex a) <> (Tex b) = Tex (a <> b)

texFunOrPred f [l,r] | isOperator f = par $ unwords [tex l, tex f, tex r]
texFunOrPred f vs = join [tex f, "(", intercalate ", " (tex' <$> vs),  ")"]
  where tex' (BaseFun f [l,r] _) | isOperator f = unwords [tex l, tex f, tex r] 
        tex' f = tex f

instance ToTex FunId where
  tex (Id f) = transOp opTex f

instance ToTex PredId where
  tex (Id f) = transOp opTex f

-- isOperator (Id (x:xs)) = not $ isAlphaNum x
