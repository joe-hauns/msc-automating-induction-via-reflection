{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Solvers.Imandra (Imandra, imandra, toImandra) where

import System.IO
import Text.Regex.Posix
import System.Process
import Data.Solvers
import Data.Composition
import Data.Formula.Mir
import Data.Char
import Util
import Data.Signature
import Data.Theory hiding (thAxioms, thName)
import qualified Data.Theory as OldTh
import Data.Theory.Interpreted
import Text.Printf
import Data.Formula
import Data.List
import Data.List.Index
import ToTff
import Control.Arrow
import Control.Exception
import Control.Monad
import Data.Functor
import System.IO.Temp
import Text.RawString.QQ(r)

toImandra :: MirBenchmark -> Result String
toImandra b = case transProblem Nothing b of 
                Right (th, conj) -> Right $ unlines [ th, printf "verify(%s) [@@auto]" conj, ";;" ]
                Left l -> Left [show l]

data Imandra = Imandra

imandra = Imandra

instance Solver Imandra where
  name              Imandra = "Imandra"
  supportsInduction Imandra = True
  inputFmt          Imandra = ImandraCaml
  options _ = []
  proveMir Imandra s problem 
          = case transProblem (Just s) problem of 
                  Left  e -> return $ NotApplicable $ show e
                  Right p -> runImandra p 
    where bin  = "imandra"

          runImandra x = runImandra' x `catch` (\(e ::IOException) -> return $ Error $ show e)
          runImandra' (p,c) 
            = do let (<<) = isSubsequenceOf
                 sendPost "/reset" "%s" "" 
                 out <- sendPost "/eval/by-src" [r|
                                      { "src_base64" : "%s"
                                      , "syntax"     : "iml"   }|] p

                 if not ( "success" << out ) 
                   then return $ Error $ unlines [ out, p ]
                   else do
                     verOut <- sendPost "/verify/by-src" [r|
                                      { "src_base64" : "%s"
                                      , "hints"      : { "method" : { "type" : "auto" } }
                                      , "syntax"     : "iml"   }|] c
                     return $ case verOut of 
                       x | "proved" << x                          -> Valid
                       x | "Maximum induction depth reached" << x -> TimeOut
                       _ -> Error $ unlines [ verOut, p, c ]

          readResult out err
                 | any ("Theorem proved" `isSubsequenceOf`)                  (lines out) = Valid
                 | any ("Maximum induction depth reached" `isSubsequenceOf`) (lines out) = TimeOut
                 | otw = Error $ unlines [out, err]

          sendPost path json prog = do 
              enc <- readProcess "base64" [] prog
              let enc' = case words enc of 
                          [w] -> w
                          []  -> ""
              readProcess "curl" ["-silent", "--data", printf json enc', printf "localhost:3000%s" path] ""



data TransFail = TransFail String
instance Show TransFail where 
  show (TransFail s) = "failed to translate to imandra: " ++ s

transProblem :: Maybe Seconds -> MirBenchmark -> Either TransFail (String, String)
transProblem timeout (Benchmark th conj) 
   = case nonRecDefs th of 
      [] -> do
        dts  <- sequence  $ transDType th <$> (sort $ datatypes th )
        funs <- sequence  $ transDef   th <$> recDefs th
        c    <- transConj th conj
        return $ (unlines [ 
                 "#logic               ;;"
               , case timeout of 
                   Just (Seconds s) -> printf "#timeout %d ;;" (round $ 1000 * s :: Int)
                   Nothing -> ""
               , ""
               , unlines dts
               , ""
               , unlines funs
               , ""
               -- , c
               , ";;" 
               ], c)
      xs -> Left $ TransFail $  "cannot translate axioms: \n" ++ unlines (show <$> xs)

transConj :: Trans MirForm String
transConj th conj = do
  let (vs, c) = dropForall conj
  c' <- formToTerm th c
  return $ printf "        fun %s -> %s             " (unwords $ transVar <$> vs) (transTerm th c') 
   where dropForall (BaseQuant Universal v _ f) 
                         = let (vs, f') = dropForall f
                           in (v:vs, f')
         dropForall f = ([], f)

transDef :: Trans RecDef String
transDef th     (RecPredDef (Id p) (Predicate as) cs) 
  = do cs' <- sequence [ do t' <- formToTerm th t
                            return $ RecCase phi ps t' | RecCase phi ps t <- cs ]
       transDef th (RecFunDef  (Id p) (Function as (Id "bool")) cs')

transDef th (RecFunDef f (Function as a) cs) = return $ unlines $ head : cases
  where head  = "let rec " ++ unwords (transFun f : args) 
             ++ " = match " ++ tup args ++ " with"
        cases = [ "  | " ++ tup (transTerm th <$> ps) ++ " -> " ++ transTerm th rhs | RecCase _ ps rhs <- cs ]
        args = [ "a" ++ show i | (i, _) <- indexed as ]
      
transTerm th (BaseVar v    _) =                 transVar v
transTerm th (BaseFun f as _) = case as of 
                                   [l,r] | isOp f' -> par $ unwords $ [transTerm th l, f', transTerm th r]
                                   [] -> f'
                                   _ | isCons th f -> par $ join [f', tup (transTerm th <$> as) ] 
                                     | otherwise   -> par $ unwords $ f' : (transTerm th <$> as)
 where f' =  transFunCons th f
       isOp (x:xs) = not (isAlphaNum x)


boolFun id as = BaseFun (Id id) as (Id "bool")

formToTerm :: Trans MirForm MirTerm
formToTerm th (BaseAtom (BaseEq    Pos l r))  = return $ boolFun "=" [ l, r ]
formToTerm th (BaseAtom (BaseEq    Neg l r))  = formToTerm th $ BaseNot (BaseAtom (BaseEq Pos l r))
formToTerm th (BaseAtom (BasePred (Id p) as)) = return $ boolFun p as
formToTerm th (BaseCon c l r) = do
    l' <- formToTerm th l
    r' <- formToTerm th r
    return $ boolFun (toId c) [ l', r' ]
  where toId And = "&&"
        toId Or  = "||"
        toId Iff  = "="
        toId Implies  = "==>"
        toId If    = "<=="
formToTerm th (BaseCon0 Bot) = return $ boolFun "False" [] 
formToTerm th (BaseCon0 Top) = return $ boolFun "True" [] 
formToTerm th (BaseNot f) = do 
    f' <- formToTerm th f 
    return $ boolFun "not" [f']
                               
formToTerm th x  = Left $ TransFail $ "cannot translate: " ++ show x

type Trans a b = MirTheory -> a -> Either TransFail b

mapHead f (x:xs) = f x : xs

transSort :: Id a -> String
transSort (Id s) = mapHead toLower s
transCons :: FunId -> String
transCons (Id s) = mapHead toUpper s
hdLow (Id s)  = mapHead toLower s  
transFun :: FunId -> String
transFun = hdLow . transOperator 
transVar :: VarId -> String
transVar (Id s)  = mapHead toLower s

transFunCons th f = if isCons th f
                     then transCons f
                     else transFun f

isCons th f = f `elem` cons
  where cons = datatypes th >>= (\(DataType _ funs) -> fmap fst funs )

transDType :: Trans DataType String
transDType th (DataType s cs) = return $ "type " ++ transSort s ++ " = " ++ intercalate " | " (transCons' <$> cs)
  where transCons' (c, Function [] s') | s' == s  = transCons c 
        -- transCons' (c, Function as s') | s' == s  = transCons c ++ " of " ++ ( par $ intercalate " * " (transSort <$> as) )
        transCons' (c, Function as s') | s' == s  = transCons c ++ " of " ++ intercalate " * " (transSort <$> as)
