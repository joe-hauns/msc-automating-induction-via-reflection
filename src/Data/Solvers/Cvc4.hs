module Data.Solvers.Cvc4 ( Cvc4, cvc4, cvc4gen ) where 

import System.Process
import Data.Solvers
import Util
import Data.Signature
import Data.Theory hiding (thAxioms, thName)
import qualified Data.Theory as OldTh
import Data.Theory.Interpreted
import Text.Printf
import ToSmtlib2

data Cvc4 = Cvc4 String [String]

cvc4    = Cvc4 "Cvc4"     ["--quant-ind"]
cvc4gen = Cvc4 "Cvc4Gen" ["--conjecture-gen", "--quant-ind"]

instance Solver Cvc4 where
  name     (Cvc4 n _) = n
  supportsInduction _ = True
  inputFmt _ = Smtlib2
  options (Cvc4 _ o) = o
  proveMir (Cvc4 _ opts) (Seconds s) problem 
     = do (_, out, err) <- readProcessWithExitCode bin args inp
          case words out of 
            ["unsat"  ] -> return Valid
            ["unknown"] -> return TimeOut
            _           -> return $ Error $ unlines $ [
                                        "unexpected response from cvc4."
                                      , "=====  CMD   =====", unwords $ bin:args
                                      , "===== STDIN  =====", inp
                                      , "===== STDOUT =====", out
                                      , "===== STDERR =====", out
                                      ]
    where bin  = "cvc4"
          inp  = toSmtlib2 problem
          args = [ "--lang=smt2"
                 , "--tlimit=" ++ show (1000 * s)]
                ++ opts

