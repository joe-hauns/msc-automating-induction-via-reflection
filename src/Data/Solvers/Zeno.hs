{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ExtendedDefaultRules #-}

module Data.Solvers.Zeno ( Zeno(..), toZeno ) where 

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
import System.Environment

data Zeno = Zeno

toZeno :: MirBenchmark -> Result String
toZeno b = case toZenoSafe b of 
             Right r -> Right r
             Left l -> Left [show l]

data TransFail = TransFail String
instance Show TransFail where 
  show (TransFail s) = "failed to translate to zeno: " ++ s

instance Exception TransFail where 

(<<) = isSubsequenceOf

instance Solver Zeno where
  name Zeno = "Zeno"
  inputFmt Zeno = ZenoHaskell
  supportsInduction Zeno = True
  supportsFullFol _ = False
  options Zeno = []
  proveMir Zeno (Seconds s) problem 
          = case toZenoSafe problem of 
                  Left  e -> return $ NotApplicable $ show e
                  Right p -> runZeno p 
    where bin  = "zeno"
    -- where bin  = "/Users/jo/Studium/induction19/bench/provers/Zeno/.stack-work/install/x86_64-osx/9a5854b4853e2b1fcba92b26ea2b95dad191b38e46ae7e0e16c744743a4b8ec8/7.10.3/bin/zeno"

          runZeno p 
            = withSystemTempFile "zeno_problem.hs" (\file handle
              -> do hPutStrLn handle p
                    let args = [ "--no-isa"
                               , "-t", show (round s)
                               , file
                               ]
                    hClose handle
                    -- putStrLn $ unwords args
                    -- putStrLn $ p
                    -- (_, out, err) <- readProcessWithExitCode bin args ""
                    e <- getEnvironment 
                    let createProc = ( proc bin args ) { 
                                           env = Just $ e >>= updateEnv 
                                         -- , std_out = NoStream
                                         -- , std_err = NoStream
                                         }
                    (_, out, err) <- readCreateProcessWithExitCode createProc ""
                    -- putStrLn $ out
                    -- putStrLn $ err
                    return $ readResult p out  err
                    -- return $ Error $ out ++ err
                    
            )
          readResult p out err 
                 | any ("Proved \"prop :" <<) (lines out) = Valid
                 | any ("Timed out" <<) (lines out) = TimeOut
                 | any ("Could neither prove nor disprove:" <<) (lines out) = Unknown
                 | otherwise = Error $ unlines [ out , err ]
          updateEnv x@("HOME", _) = [x]
          updateEnv _             = [ ]


class ToZeno a where 
  zeno :: MirTheory -> a -> Either TransFail String

toZenoSafe = alphaNumIds >>> \(Benchmark th conj)  ->
      do dts  <- sequence (zeno th <$> datatypes  th)
         fs   <- sequence (zeno th <$> functions  th)
         ps   <- sequence (zeno th <$> predicates th)
         ax   <- sequence (zeno th <$> thAxioms   th)
         prop <- transConj th conj
         return $ unlines $ 
          [ ""
          , "{-# LANGUAGE ExistentialQuantification #-}"

          , "module Thry where"
          , ""

          , "import Prelude ( Bool (..) )"
          , "infix 1 :=:"
          , "infixr 0 $"
          , ""
          , "($) :: (a -> b) -> a -> b"
          , "f $ x = f x"
          , ""
          , "otherwise :: Bool"
          , "otherwise = True"
          , ""
          , "data Equals"
          , "  = forall a . (:=:) a a"
          ,   ""
          , "data Prop"
          , "  = Given Equals Prop           "
          , "  | Prove Equals"
          , ""
          , "prove :: Equals -> Prop"
          , "prove = Prove"
          , ""
          , "given :: Equals -> Prop -> Prop"
          , "given = Given"
          , ""
          , "proveBool :: Bool -> Prop"
          , "proveBool p = Prove (p :=: True)"
          , ""
          , "givenBool :: Bool -> Prop -> Prop"
          , "givenBool p = Given (p :=: True)"
          , ""

          , ""   

          , "and :: " ++ zfunDecl ["Bool", "Bool"] "Bool"
          , zfunLhs "and" ["True", "True"] ++ " = True"
          , zfunLhs "and" ["_", "_"] ++ " = False"

          , "iff :: " ++ zfunDecl ["Bool", "Bool"] "Bool"
          , zfunLhs "iff" ["False", "False"] ++ " = True"
          , zfunLhs "iff" ["True", "True"] ++ " = True"
          , zfunLhs "iff" ["_", "_"] ++ " = False"

          , "impl :: " ++ zfunDecl ["Bool", "Bool"] "Bool"
          , zfunLhs "impl" ["l", "r"] ++ " = or (not l) r"

          , "lpmi :: " ++ zfunDecl ["Bool", "Bool"] "Bool"
          , zfunLhs "lpmi" ["l", "r"] ++ " = impl r l"

          , "or :: " ++ zfunDecl ["Bool", "Bool"] "Bool"
          , zfunLhs "or" ["False", "False"] ++ " = False"
          , zfunLhs "or" ["_", "_"] ++ " = True"

          , "not :: " ++ zfunDecl ["Bool"] "Bool"
          , zfunLhs "not" ["True"] ++ " = False"
          , zfunLhs "not" ["False"] ++ " = True"

          , ""
          , "class Eq a where"
          , "  eq :: " ++ zfunDecl ["a", "a"] "Bool"
          , ""
          ] ++ dts ++ fs ++ ps ++ ax ++ [prop]
zfunLhs f as = unwords $ f : as

-- data Pat = PatLit  String 
--          | PatAppl String [String]
--
-- data FunCase = FunCase [Pat] MirTerm
--
-- transFunDef :: MirTheory -> FunId -> Function -> [FunCase] -> Either TransFail String
-- transFunDef th f (Function as a) cases 
--    = do f'     <- zeno th f
--         as'    <- sequence (zeno th <$> as)
--         cases' <- sequence (zeno th <$> cases)
--         let decl = (f' ++ " :: " ++ intercalate " -> " as') :: String
--         return $ unlines $ decl : cases'

instance ToZeno (Id a) where

  zeno = return .: toZenoSafe
    where 
      toZenoSafe th (Id a) 
          | all isAlphaNum a       = if (Id a) `elem` inductiveStuff 
                                     then zenoCtor (Id a)
                                     else mapHead toLower a
          | all (not.isAlphaNum) a = "("++ a ++")"
          | otherwise              = error a
            where lowerHead (x:xs) = toLower x : xs
                  inductiveStuff = (datatypes th >>= (\(DataType (Id s) funs) -> Id s : fmap fst funs ))
                                ++ [ Id "True", Id "False" ]

mapHead f (x:xs) = (f x):xs

zenoCtor (Id a) = mapHead toUpper a

instance ToZeno a => ToZeno (Decl a) where
  zeno th (id, dec) = do id'  <- zeno th id 
                         dec' <- zeno th dec
                         return $ id' ++ " :: " ++ dec' 

instance ToZeno Predicate where
  zeno th (Predicate as) = do as' <- sequence (zeno th <$> as) 
                              return $ zfunDecl as' "Bool"

zfunDecl as r = intercalate " -> " (as ++ [r])
zfun f as = par $ unwords $ f : as 
zcons f as = unwords $ f : as 

instance ToZeno Function where
  zeno th (Function as a) = do as' <- sequence (zeno th <$> as) 
                               a' <- zeno th a 
                               return $ zfunDecl as' a'

instance ToZeno DataType where
  zeno th (DataType s cons) 
     = do d <- def
          e <- eq
          return $ unlines [d, e]
    where 
      eq  = do dname <- zeno th s 
               return $ unlines $ [ "instance Eq " ++ dname ++ " where" ]
                               ++ [ "  " ++ lhs ++ " = " ++ rhs 
                                        | (f, Function as _) <- cons 
                                        , let cname = zenoCtor f 
                                        , let vs = [ "a" ++ show i | (i, _) <- indexed as ]
                                        , let ws = [ "b" ++ show i | (i, _) <- indexed as ]
                                        -- , let lhs = tup [cname ++ tup vs, cname ++ tup ws ] 
                                        , let lhs = zfunLhs "eq" [ zfun cname vs
                                                                 , zfun cname ws ] 
                                        , let rhs = foldl andT "True" [ zfun "eq" [v,w] | (v,w) <- zip vs ws ]
                                        ]
                               ++ [ "  " ++ zfunLhs "eq" ["_", "_"] ++ " = False" ]

      def = do dname <- zeno th s 
               cs    <- sequence (cvt <$> cons)
               return $ "data " ++ dname ++ " = " ++ intercalate " | " cs
                 where cvt (f, Function as _) 
                          = do cname <- zeno th f 
                               as'   <- sequence (zeno th <$> as) 
                               return $ zcons cname as'

andT l r = zfun "and" [l,r]
instance ToZeno MirTerm where
  zeno th (BaseVar v _) = zeno th v
  -- zeno th (BaseFun f [] _) =  zeno th f
  zeno th (BaseFun f [] _) = zeno th f 
  zeno th (BaseFun f as _) = do f' <- zeno th f 
                                as' <- sequence (zeno th <$> as)
                                return $ zfun f' as'
  -- zeno th (BaseFun f as _) = sequence ( zeno th f : (zeno th <$> as) )
  --                         <&> par . unwords

instance ToZeno MirForm where

  zeno th f = transDef th f
   where 

    transDef th (BaseQuant Universal _ _ f)                = transDef th f
    transDef th (BaseAtom (BaseEq Pos (BaseFun f as _) r)) = definition f as (zeno th r)
    transDef th           (BaseAtom (BasePred f as))       = definition f as (return $ show True)
    transDef th (BaseNot  (BaseAtom (BasePred f as)))      = definition f as (return $ show False)
    transDef th (BaseCon Iff (BaseAtom (BasePred f as)) r) = definition f as (zeno th =<< tForm th r)
    transDef th f@(BaseCon Implies _ _) = Left $ TransFail $ "implication cannot be translated to function definition: " ++ show f 

    transDef th a = fail $ "zeno translation not yet implemented: " ++ (show a)
    funDef  _ = return ""

    definition f as r = do f'  <- zeno th f
                           as' <- sequence (zeno th <$> as)
                           r'  <- r
                           return $ zfunLhs f' as' ++ " = " ++ r' 

-- vars :: Theory -> MirForm -> Either TransFail [ String ]
vars th (BaseQuant Universal v _ f)                
   = do v' <- zeno th v 
        rest <- vars th f
        return $ v' : rest
vars th _ = return []

dropForall (BaseQuant Universal _ _ f) = dropForall f
dropForall f = f


transConj :: MirTheory -> BaseForm BaseAtom (Id Sort) -> Either TransFail String
transConj th conj 
  = do c <- zeno th =<< tForm th (dropForall conj)
       vs <- vars th conj
       return $ unwords $ ["prop"] ++ vs ++ ["=", "proveBool $ ", c ]

boolFun f as = BaseFun (Id f) as (Id "Bool")
tForm :: MirTheory -> BaseForm BaseAtom (Id Sort) -> Either TransFail MirTerm
tForm th (BaseCon0 Bot) = return $ boolFun "False" []
tForm th (BaseCon0 Top) = return $ boolFun "True" []

tForm th (BaseCon c l r) 
    = do as <- sequence (tForm th <$> [l,r]) 
         return $ boolFun (conFun c) as 
      where conFun And = "and"
            conFun Or  = "or"
            conFun Iff = "iff"
            conFun Implies = "impl"
            conFun If = "lpmi"

tForm th (BaseNot f) 
   = do inner <- tForm th f
        return $ boolFun "not" [inner]

tForm th (BaseAtom (BaseEq Neg l r)) 
   =             tForm th (BaseNot (BaseAtom (BaseEq Pos l r)))

tForm th (BaseAtom (BaseEq Pos l r)) 
   = do return $ boolFun "eq" [l,r]

tForm th (BaseAtom (BasePred (Id p) as)) 
   = do return $ boolFun p as 

tForm th x = Left $ TransFail $ show x
