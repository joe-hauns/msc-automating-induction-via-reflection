{-# LANGUAGE LambdaCase #-}

module Main(main) where

import Benchmark.Msc
import Text.Printf
import Data.List
import Data.Solvers
import Data.Solvers.Msc 
-- import Data.Composition
import Data.Formula
import Data.Signature
import Data.Theory.Interpreted
import Serialize
import Control.Monad
import System.IO
import Data.Text (strip)
import ToTex
import Data.Solvers.Msc  (allSolvers)
import Debug.Trace
import Data.List.Split
import System.Environment

comment :: String -> String
comment = ("% " ++)

separator :: String -> String
separator c = comment ( take 90 $ [0..] >>= const c ) 

command :: String -> String -> String
command = printf "\\newcommand\\%s{%s}"

main :: IO ()
main = do

  as <- getArgs
  let dir = case as of 
              [dir] -> dir
              as -> error $ "expected output dir as argument, got: " ++ show as



  resultTables <- sequence [ 
      compileResultTable dir "tabReflAxResults"   reflAxBenchmarks
    , compileResultTable dir "tabReflConjResults" reflConjBenchmarks
    , compileResultTable dir "tabIndResults"      indBenchmarks
    ] 

  writeFile (dir ++ "/mscBenchmarkDefs.tex") . unlines $ [
      separator "=-"
    , comment "theories"
    , separator "=-"
    , command "reflAxTheories" (intercalate ", " $ fmap mtTex reflAxTheories)
    , separator "=-"
    , command "tabAllTheories" (texTable theoryTabHeader $ fmap theoryTabRow allTheories) 
    , separator "=-"
    , ""
    , separator "=-"
    , comment "conjectures"
    , separator "=-"
    , command "tabReflConj"    (conjTable rcTheory rcConj mscId (\x -> printf "\\goedel{%s}" x) reflConjBenchmarks )
    , separator "=-"
    , command "tabIndConj"     (conjTable  iTheory  iConj mscId (\x -> x) indBenchmarks) 
    , separator "=-"
    , ""
    , separator "=-"
    , comment "solvers"
    , separator "=-"
    , command "tabSolvers" (texTable solverTabHeader (fmap solverTabRow allSolvers))
    , separator "=-"
    , ""
    , separator "#+"
    , ""
    , separator "=-"
    , comment "experimental results"
    , separator "=-"
    ] ++ resultTables

conjTable :: (a -> MscTheory) -> (a -> Formula) -> (a -> String) -> (String -> String) -> [a] -> String
conjTable getTh getF getId wrapFormula = texTable conjTabHeader . fmap (conjTabRow getTh getF getId wrapFormula)

------------------------------------------------ utilities

intracalate :: [a] -> [[a]] -> [a]
intracalate x = (x++) . (++x) . intercalate x

texTable :: [String] -> [[String]] -> String
texTable hdr conts = unlines $  
  [ printf "\\begin{tabular}{%s}\\hline " colFmt :: String 
  , intercalate " & " hdr  ++ "\\\\\\hline\n"
  , intracalate "\\hline " . fmap ((++ " \\\\ \n") . intercalate " & ") $ conts 
  , printf "\\end{tabular}" ]
  where colFmt = intracalate "|" (fmap (const "c") hdr)


texTable' :: [String] -> [[String]] -> String
texTable' hdr conts = unlines $  
  [ printf "\\begin{tabular}{%s} " colFmt :: String 
  , intercalate " & " hdr'  ++ "\\\\\\hline\n"
  , intracalate "\\hline " . fmap ((++ " \\\\ \n") . intercalate " & ") $ conts 
  , printf "\\end{tabular}" ]
  where colFmt = intracalate "|" (fmap (const "c") hdr)
        -- hdr' = fmap (printf "\\multicolumn{1}{c}{%s}") hdr
        hdr' = hdr


------------------------------------------------ \tabAllTheories
theoryTabHeader :: [String]
theoryTabHeader = [ "Name",  "Theory" ]

theoryTabRow :: MscTheory -> [String]
theoryTabRow t = [ 
      mtTex t
    , printf "{$ \\begin{matrix}\n %s %s %s \\end{matrix} $}" dtys sig forms
  ]
  where 
    forms   = unlines [ printf "\t%s & (%s)\\\\" (formToTex a) (show i) | (a, i)  <- ( thAxioms $ mtTheory t) `zip` [1..] ]
    sig     = unlines [ printf "\\begin{matrix} %s \\end{matrix}\\\\" (toMat 2 sigEntries) ]
    sigEntries = [ join [ser i, softype, serFun  f]  | (i,f)  <- functions  (mtTheory t) ]
              ++ [ join [ser i, softype, serPred f]  | (i,f)  <- predicates (mtTheory t) ]

    ser :: GenSerialize a => a -> String
    ser = genSerialize ToTexConf
    sertup = intercalate "\\sprod{}" . fmap ser 
    serPred (Predicate as) = printf "\\spred{%s}" $ sertup as
    serFun (Function [] d) = join [ser d]
    serFun (Function as d) = join [sertup as, sarrow, ser d]

    toMat :: Int -> [String] -> String
    toMat n es = intercalate "\\\\" ( toMat' n es )
    toMat' :: Int -> [String] -> [String]
    toMat' n [] = []
    toMat' n es = ln : toMat' n ( drop n es )  -- intercalate "\\\\\n" . fmap ("\t" ++) $ sigEntries
      where ln = "\n\t" ++ intercalate " & " (take n es) -- ++ "\\\\" 
    dtys = unlines [ dty ty ++ "\\\\\n" | ty <- datatypes $ mtTheory t  ]
    dty :: DataType -> String
    dty (DataType s fs)  = printf "\\data %s = %s" (ser s) (intercalate " \\mid " (fmap cons fs))
      where cons (fid, Function as _) = printf "%s%s" (ser fid) (args as)
            args [] = ""
            args as = printf "(%s)" (intercalate ", " (fmap ser as))


------------------------------------------------ \tabReflCon

conjTabHeader :: [String]
conjTabHeader = [ "Theory",  "Conjecture", "id" ]

conjTabRow :: (a -> MscTheory) -> (a -> Formula) -> (a -> String) -> (String -> String) -> a -> [String]
conjTabRow getTheory getConj getId wrapFormula t = [ 
      mtTex . getTheory $ t
    , printf "{$ %s $}" (wrapFormula $ formToTex $ getConj t)
    , printf "\\benchIdFmt{%s}" $ getId t
  ]

------------------------------------------------ seraialize theories & formulas to tex

formToTex :: Formula -> String
formToTex = genSerialize ToTexConf

data ToTexConf = ToTexConf

instance SerConf ToTexConf where
  scBin _ And     = "\\oand"
  scBin _ Or      = "\\oor"
  scBin _ Implies = "\\oimpl"
  scBin _ If      = "\\oif"
  scBin _ Iff     = "\\oiff"

  scCon0 _ Top = "\\otop"
  scCon0 _ Bot = "\\obot"

  scNeg   _ NegationConnective = "\\onot{}"

  scPol _ Pos = "\\oeq"
  scPol _ Neg = "\\oneq"

  scTypeArrow _ = sarrow

  scQuant _ Existential = "\\oexists"
  scQuant _ Universal   = "\\oforall"

  scFunc  _ (Id a) = scFunc' a
    where
      scFunc' "+" = "+"
      scFunc' "*" = "*"
      scFunc' "++" = "+\\hspace{-2mm}+ "
      scFunc' a   = printf "\\osyn{%s}" a

  scPred  _ = \(Id a) -> case a of 
                            "<=" -> "\\leq"
                            _    -> printf "\\osyn{%s}" a
  scSort  _ = \(Id a) -> case a of 
                           "alpha" -> "\\alpha"
                           _       -> printf "\\osyn{%s}" a
  scVar   _ = \(Id a) -> a
  scTypeColon _ = "&" ++ softype
  scConst _ f = f

softype = "\\softype{}"
sarrow = "\\sarrow{}"
------------------------------------------------ \tabSolvers

yes = "\\yes "
no = "\\no "

solverTabHeader :: [String]
solverTabHeader = [ "Solver",  "Induction", "Input format", "Commandline Options"]

solverTabRow :: AnySolver -> [String]
solverTabRow s = [ nameStr , ind , format, opts ]
  where ind | supportsInduction s = yes
            | otherwise           = no
        nameStr = compileTex $ texName s
        format = "\\" ++ (filter (not . (`elem` ['0'..'9'])) $ show (inputFmt s)) ++ " "
        opts = case options s of 
           [] -> "default mode"
           o -> "\\code{ " ++ unwords o ++ " }"



------------------------------------------------ \tabReflAxResults
readResultsCsv :: MscBenchmark a => FilePath -> [a] -> IO [[String]]
readResultsCsv dir (b:_) = do 
    let filename = dir ++ "/results/" ++ resultsFileId b
    cont <- readFile filename
    return $  splitOn "\t" <$> lines cont
    

compileResultTable dir name benchmarks = do
  results <- readResultsCsv dir benchmarks
  return $ command name (fmtTabResults benchmarks results) 

fmtTabResults :: MscBenchmark b => [b] -> [[String]] -> String
fmtTabResults (bench:_) (hdr:cont) = texTable' ("\\resultsTableBenchmarkColHeader ": solverNames) (fmap format cont)
  where 

    solverNames = fmap formatSolverName $  drop 3 hdr
    formatSolverName n = printf "\\resultTableSolverCell{%s}" n'
      where n' = compileTex $ texName ((filter ((== n).name) solvers) !! 0)


    format :: [String] -> [String]
    format row  = [row!!1] ++ fmap fmt01 (drop 3 row) 
    fmt01 :: String -> String
    fmt01 "0"    = "\\resultTabNo  "
    fmt01 "1"    = "\\resultTabYes "
    fmt01 "N.A." = "\\resultTabNA  "

    solvers = getSolvers bench
