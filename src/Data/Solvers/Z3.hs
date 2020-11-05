module Data.Solvers.Z3 ( Z3, z3 ) where 

import System.Process
import Data.Solvers
import Util
import Data.Signature
import Data.Theory hiding (thAxioms, thName)
import qualified Data.Theory as OldTh
import Data.Theory.Interpreted
import Text.Printf
import ToSmtlib2

data Z3 = Z3 String [String]

z3         = z3WithOpts []
z3WithOpts = Z3 "Z3" 

instance Solver Z3 where
  name     (Z3 n _) = n
  supportsInduction _ = False
  inputFmt _ = Smtlib2
  options (Z3 _ o) = o
  proveMir (Z3 _ opts) (Seconds s) problem 
     = do (_, out, err) <- readProcessWithExitCode bin args inp
          case words out of 
            ["unsat"  ] -> return Valid
            ["unknown"] -> return TimeOut
            ["timeout"] -> return TimeOut
            ["unsupported", "unsat"  ] -> return Valid
            ["unsupported", "timeout"] -> return TimeOut
            ["unsupported", "unknown"] -> return TimeOut
            _           -> return $ Error $ unlines $ [
                                        "unexpected response from z3."
                                      , "=====  CMD   =====", unwords $ bin:args
                                      , "===== STDIN  =====", inp
                                      , "===== STDOUT =====", out
                                      , "===== STDERR =====", out
                                      ]
    where bin  = "z3"
          inp  = toSmtlib2 problem
          args = [ "-in", "-smt2", "-T:" ++ show (round s)] 
              ++ opts

