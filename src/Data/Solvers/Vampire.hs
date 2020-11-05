module Data.Solvers.Vampire (Vampire, vampireTryout,vampireTryout2,vampireSubsFull, vampireSubs2, vampireOld, vampireComplexTermInduction, vampireDefault, vampireMsc) where

import Vampire hiding (Valid)
import Data.Solvers
import Util
import Data.Signature
import Data.Theory hiding (thAxioms, thName)
import qualified Data.Theory as OldTh
import Data.Theory.Interpreted
import qualified Vampire as V
import ToTex
import System.IO
import System.Directory
import Control.Monad
import Data.Time.Clock.POSIX

data Vampire = Vampire String VampireOpts

vampireDefault = Vampire "Vampire" VampireOpts { 
                 vBin = "vampire" 
               , vOpts = [  ]
               }

vampireMsc =  [


                Vampire "Vampire" VampireOpts { 
                               vBin = "vampire" 
                             , vOpts = [ "--schedule" , "casc"
                                       , "--induction", "struct" ]
                             }

              --   Vampire "Vampire" VampireOpts { 
              --                  vBin = "vampire" 
              --                , vOpts = [ "--induction"            , "struct" ]
              --                }

              -- , Vampire "VampireCasc" VampireOpts { 
              --                  vBin = "vampire" 
              --                , vOpts = [ "--mode"     , "casc" ]
              --                }

              , Vampire "VampireComplete" VampireOpts { 
                               vBin = "vampire" 
                             , vOpts = [ "--induction"            , "struct" 
                                       , "-s", "1" ]
                             }

              ]

vampireOld = Vampire "Vampire" VampireOpts { 
                               vBin = "vampire" 
                             , vOpts = [ "--induction"            , "struct" ]
                             }

vampireSubsFull = Vampire "Vampire*" VampireOpts { 
                               vBin = "vampire_rel_hzzv-induction1" 
                             , vOpts = [ "--induction"            , "struct" 
                                       , "--induction_term_subset", "on"
                                       ]
                             }

vampireComplexTermInduction = Vampire "Vampire+" VampireOpts { 
                               vBin = "vampire_rel_hzzv-induction4" 
                             , vOpts = [ "--induction"            , "struct" 
                                       , "-indoct"                , "on"
                                       , "--induction_gen"        , "on"
                                       ]
                             }

vampireSubs2 = Vampire "VampireSubs2" VampireOpts { 
                               vBin = "vampire_rel_hzzv-induction1" 
                             , vOpts = [ "--induction"            , "struct" 
                                       , "--induction_term_subset", "on"
                                       , "--induction_term_subset_size", "2"
                                       ]
                             }

vampireTryout = Vampire "VampNoSkInd" VampireOpts { 
                               vBin = "vampire_rel_hzzv-induction1-stats" 
                             , vOpts = [ "--induction"            , "struct" 
                                       , "--induction_term_subset", "on"
                                       , "--avatar", "on"
                                       ]
                             }

vampireTryout2 = Vampire "VampNoSkInd2" VampireOpts { 
                               vBin = "vampire_rel_hzzv-induction1-stats" 
                             , vOpts = [ "--induction"            , "struct" 
                                       , "--induction_term_subset", "on"
                                       , "--induction_term_subset_size", "2"
                                       , "--avatar", "on"
                                       ]
                             }


-- vampireTryout = Vampire "VampAv" VampireOpts { 
--                                vBin = "vampire_rel_hzzv-induction1" 
--                              , vOpts = [ "--induction"            , "struct" 
--                                        , "--induction_term_subset", "on"
--                                        , "--avatar", "on"
--                                        ]
--                              }
--
-- vampireTryout2 = Vampire "VampAv2" VampireOpts { 
--                                vBin = "vampire_rel_hzzv-induction1" 
--                              , vOpts = [ "--induction"            , "struct" 
--                                        , "--induction_term_subset", "on"
--                                        , "--induction_term_subset_size", "2"
--                                        , "--avatar", "on"
--                                        ]
--                              }


instance Solver Vampire where
  name (Vampire n _) = n

  supportsInduction (Vampire _ opts) =  any (== ("--induction", "struct")) (pairs $ vOpts opts)
  inputFmt _ = Smtlib2
  options (Vampire n opts) = vOpts opts

  proveMir (Vampire n opts) sec bench
      -- = cvtResult <$> vprove opts sec bench
      = do 
        out <- vprove opts sec bench

        -- putStrLn (vOut out)
        -- putStrLn (vErr out)

        return $ cvtResult out
  -- proveMir (Vampire n opts) sec bench =  do
  --     -- time <- getCurrentTime 
  --     -- let file f = join [ "/Users/jo/Desktop/vampire-out/", n, "/", show $ bConjecture bench, "/", show time, "/", f  ]
  --     --
  --     -- createDirectoryIfMissing True (file "")
  --     -- writeFile (file "in" ) (vIn  out)
  --     -- writeFile (file "out") (vOut out)
  --     
  --
  --     res <- (cvtResult <$> vprove opts sec bench)
  --     case res of 
  --       Valid -> print (bConjecture bench)
  --       _ -> return ()
  --     return res
    where cvtResult out = case vSat out of 
                             V.Valid     -> Valid 
                             V.TimeLimit -> TimeOut
                             x           -> Error (show out)



