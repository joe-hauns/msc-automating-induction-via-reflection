
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}

module Main where
import Parse
import Parse.QQ
import Serialize
import Data.Theory.Interpreted
import Data.Functor
import System.Environment
import Control.Category hiding ((.))
import Data.List

import CliUtil
import ToSmtlib2
import ToTff
import Util
import Data.Solvers.Zipperposition
import Data.Solvers.Imandra
import Data.Solvers.Zeno
import Translations


main = 
  (getArgs <&> \case 
      [x] -> case find ((== x).fileExtension) allTranslators of 
        Nothing          -> error . unlines $ ( "unknown target language: " ++ x ) 
                                            :   "known ones:" 
                                            : fmap (("  " ++) . fileExtension) allTranslators
        Just t  -> translate t >>> unwrap
      _ -> error $ "expected exactly one argument"
  ) >>= serializerMain

