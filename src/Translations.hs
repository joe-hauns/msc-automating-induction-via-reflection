module Translations(translate, Translator(..), allTranslators, fileExtension) where


import Data.Solvers hiding (InputFmt(..))
import Serialize
import Util
import ToSmtlib2 (toSmtlib2)
import Data.Solvers.Zeno (toZeno)
import Data.Solvers.Zipperposition (toZfLogic, toZfRewrite)
import Data.Solvers.Imandra (toImandra)

data Translator = Smtlib2 | Logic | AsciiLogic | Zf | ZfRewrite | ZenoHaskell | ImandraCaml deriving (Show, Eq, Ord, Enum)
allTranslators = [Smtlib2 ..]

translate :: Translator -> MirBenchmark -> Result String
translate Smtlib2     = return . toSmtlib2
translate ZenoHaskell =          toZeno  
translate Zf          = return . toZfLogic
translate ZfRewrite   = return . toZfRewrite
translate ImandraCaml =          toImandra
translate Logic       = return . genSerialize humanReadable
translate AsciiLogic  = return . genSerialize humanWritable

fileExtension :: Translator -> String 
fileExtension Smtlib2     = "smt2"
fileExtension ZenoHaskell = "zeno.hs" 
fileExtension Zf          = "zf"
fileExtension ZfRewrite   = "rewrite.zf"
fileExtension ImandraCaml = "icaml"
fileExtension Logic       = "logic"
fileExtension AsciiLogic  = "ascii.logic"
