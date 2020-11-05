{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Solvers.Zipperposition ( Zipperposition, zipperposition1, zipperposition2, toZfLogic, toZfRewrite ) where 

import Text.Regex.Posix
import System.Process
import Data.Solvers
import Util
import Data.Signature
import Data.Theory hiding (thAxioms, thName)
import qualified Data.Theory as OldTh
import Data.Theory.Interpreted
import Text.Printf
import Data.Formula
import Data.Formula.Mir
import Data.List
import Data.List.Index
import ToTff
import Control.Arrow
import Control.Lens hiding (indexed)
import Control.Monad
import Data.Functor
import Data.Char

data Zipperposition = Zipperposition { zpName      :: String 
                                     , translation :: MirBenchmark -> String }

zipperposition1 = Zipperposition "Zipperposition" toZfLogic 
zipperposition2 = Zipperposition "ZipRewrite"     toZfRewrite

(<<) = isSubsequenceOf

instance Solver Zipperposition where
  name = zpName
  supportsInduction _ = True
  inputFmt _ = Zf
  options _ = []
  proveMir zp (Seconds s) problem 
     = do (_, out, err) <- readProcessWithExitCode bin args inp
          -- putStrLn inp
          return $ case status out of 
                         Just s -> s
                         _ -> Error $ unlines [ inp, out, err ]
          -- return $ Error $ unlines [ inp, out, err ]
          -- = return $ Error $ "TODO integrate rest of zipperposition" ++ zpos problem
    where bin  = "zipperposition"

          args = [ "--input", "zf"
                 , "--timeout", show s
                 , "--output", "none"
                 ]

          inp = translation zp problem
          status out = case find ("SZS status " <<) (lines out)  of
                             Just x | x =~ ".*SZS status GaveUp.*"             -> Just Unknown
                                    | x =~ ".*SZS status ResourceOut.*"        -> Just TimeOut
                                    | x =~ ".*SZS status Theorem.*"            -> Just Valid
                                    | x =~ ".*SZS status CounterSatisfiable.*" -> Just CounterSat --Just (Error x)
                             x -> Nothing

class ToZf a where
  zf :: a -> String

toZfLogic = alphaNumIds >>> \(Benchmark th c) -> unlines' $ []
                               ++ [ ("val  " ++ zf a  ++ " : type")            | a <- uninterpretedSorts th   ]
                               ++ [ zf d              | d <- datatypes th   ]
                               ++ [ zf a              | a <- functions th   ]
                               ++ [ zf a              | a <- predicates th  ]
                               ++ [ "assert " ++ zf a | a <- thAxioms th    ]
                               ++ [ "goal   " ++ zf c                       ]
                                where unlines' = unlines . fmap (++".")

toZfRewrite = alphaNumIds >>> \(Benchmark th c) -> unlines' $ []
-- TODO check what about non-recDefs
                               ++ [ ("val  " ++ zf a  ++ " : type")            | a <- uninterpretedSorts th   ]
                               ++ [ zf d | d <- datatypes th   ]
                               ++ [ zf p | p <- predicates th, not (or [ fst p == p' | RecPredDef p' _ _ <- recDefs th ])  ] 
                               ++ [ zf f | f <- functions th, not (or [ fst f == f' | RecFunDef f' _ _ <- recDefs th ])  ]
                               ++ (zf <$> recDefs th )
                               ++ [ "assert " ++ zf a | a <- nonRecDefs th    ]
                               ++ [ "goal   " ++ zf c                       ]
                                where unlines' = unlines . fmap (++".")

instance (ToZf a, ToZf (Id a)) => ToZf (Decl a) where
  zf (f, x) = printf "val %s : %s" (zf f) (zf x)

instance ToZf Predicate where 
  zf (Predicate as) = zf (Function as (Id "prop"))

instance ToZf Function where 
  zf (Function as b) = intercalate " -> " (zf <$> ( as ++ [b] ))

instance ToZf DataType where
  zf (DataType s cons) = intercalate "\n" 
                       $ [ printf "data %s := " (zf s)                                               ]
                      ++ [ printf "  | %s %s" (zf f) (unwords $ zf <$> as) | (f, Function as _) <- cons ]

instance ToZf ( RecCase a ) where 
  zf = zf . recFormula

instance ToZf RecDef where 
  zf (RecPredDef f ty cs) = printf "def %s : %s where\n\t" (zf f) (zf ty)
                         ++ intercalate ";\n\t"(zf <$> cs)
  zf (RecFunDef f ty cs) = printf "def %s : %s where\n\t" (zf f) (zf ty)
                        ++ intercalate ";\n\t"(zf <$> cs)
                              

instance ToZf Connective where 
  zf And     = "&&"
  zf Or      = "||"
  zf If      = "<="
  zf Implies = "=>"
  zf Iff     = "<=>"

instance ToZf MirTerm where
  zf (BaseVar v _ )    = zf v
  zf (BaseFun f ts _) = funPredZf f ts

instance ToZf Quantifier where
  zf Existential = "exists"
  zf Universal   = "forall"

lower (Id (c:cs)) = toLower c : cs

instance ToZf FunId where
  zf = lower . transOperator

instance ToZf PredId where
  zf = lower . transOperator

instance ToZf SortId where
  zf = lower

instance ToZf VarId where
  zf (Id (c:cs)) = toUpper c : cs

instance ToZf MirForm where
  zf (BaseAtom (BaseEq Pos t1 t2) )    = unwords [ zf t1, "=", zf t2 ]
  zf (BaseAtom (BaseEq Neg t1 t2) )    = zf (BaseNot $ BaseAtom $ BaseEq Pos t1 t2)
  zf (BaseAtom (BasePred p ts) )         = funPredZf p ts
  zf (BaseCon c a1 a2)       = join [ "(", intercalate " " [zf a1, zf c,  zf a2], ")" ]
  zf (BaseNot a)             = join [ "~", "(", zf a, ")" ]
  zf (BaseCon0 Bot)      = "false"
  zf (BaseCon0 Top)      = "true"
  zf (BaseQuant q v s f) = printf "(%s(%s:%s). %s)" (zf q) (zf v) (zf s) (zf f)

funPredZf f [] = zf f
funPredZf f ts = par . unwords $  zf f : (zf <$> ts) --join [zf f, "(", intercalate ", " (zf <$> ts), ")"]

instance ToZf Sort where 
  zf _ = "$tType"

tptp :: MirBenchmark -> String
tptp (Benchmark th conj) = unlines $ 
        ( sortDecl <$> uninterpretedSorts th )
     ++ ( dtypeDecls th )
     ++ ( uncurry tffDecl <$> functions th )
     ++ ( uncurry tffDecl <$> predicates th )
     ++ ( toTff <$> ( indexed $ Axiom ""  <$> thAxioms th ) )
     ++ [ toTff ( Conjecture conj ) ]

newtype DTypeDecl = DTypeDecl [FunId]

instance ToTff DTypeDecl where 
  toTff (DTypeDecl fs) = (toTff Sort) ++ ", inductive(" ++ intercalate ", " (toTff <$> fs) ++ ")"

dtypeDecls :: MirTheory -> [String]
dtypeDecls th = dtypes th 
             <&> ((id &&& ( ctors th 
                         >>> fmap fst 
                         >>> DTypeDecl )))
             <&> uncurry tffDecl

sortDecl s    = tffDecl s Sort

tffDecl s t = tff [ show ( transOperator s ) ++ "_dec"
                  , "type"
                  , toTff s ++ ": " ++ toTff t]

tff as = "tff(" ++ intercalate ", " as ++ ")."
