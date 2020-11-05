{-# LANGUAGE GADTs
           , FlexibleContexts
           , MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , BangPatterns
           , ScopedTypeVariables
           , LambdaCase
           , TupleSections #-}
module Main where

import Util
import Control.Arrow
import Data.Char
import Data.List
import Control.Monad
import Data.List.Split
import Text.Printf
import Text.Regex.Posix  -- hiding ( parse )

data Cell = Cell { unCell  :: String } deriving (Show, Eq)
data Row  = Row  { unRow   :: [Cell] } deriving (Show, Eq)
data Csv = Csv { unCsv  :: [Row ] } 

instance Show Csv where 
  show (Csv gs) = printf "Csv{ rows = %d, cells = %d }" (length gs) (sum $ fmap (length .unRow  ) gs)

parseCsv :: String -> Csv
parseCsv = lines >>> fmap ( splitOn "\t" >>>  fmap (Cell . stripWs ) >>> Row   )
                 >>> Csv
      where stripWs xs =  reverse $ dropSpace $ reverse $ dropSpace xs
            dropSpace = dropWhile isSpace

data BenchRow = BenchRow { 
    bId  :: String 
  , bTex :: String 
  , bCnt :: Int 
  , bRes :: [Int] 
  } deriving Show

data BenchGroup = BenchGroup [BenchRow] deriving Show

data BenchData = BenchData {
    solvers :: [String]
  , groups :: [BenchGroup]
  } deriving Show

parseData :: Csv -> BenchData
parseData ( Csv (r:rs) ) = BenchData (parseHeader r) (fmap parseGroup (splitWhen allWs rs))
  where 
        parseGroup :: [Row] -> BenchGroup
        parseGroup = BenchGroup . fmap parseRow . fmap (fmap unCell . unRow )
        parseRow :: [String] -> BenchRow
        parseRow         (id:tex:cnt:rest)  = BenchRow id tex (read cnt) (fmap read rest)
        parseHeader (Row (id:tex:cnt:rest)) = fmap unCell rest
        allWs (Row xs) =  all isEmpty xs
          where 
            isEmpty (Cell "") = True
            isEmpty  _        = False

class ToTex a where
  tex :: a -> String

instance ToTex BenchData where 
  tex b = unlines $ [printf "\\begin{tabular}{|r%s|}" $ join [ "|c" | _ <- [1..length (solvers b)] ]]
                 ++ [printf "\\hline & %s \\\\ \\hline \\hline" $ intercalate "&" ( solvers b )]
                 ++ [  intercalate "\n\\hline \\hline\n" $ fmap tex (groups b)  ] 
                 ++ [        "\\end{tabular}" ]

instance ToTex BenchGroup where 
  tex (BenchGroup rs) = unlines $  fmap tex rs 

instance ToTex BenchRow where 
  tex r = printf "$ %s $ %s \\\\ \\hline" (bTex r) (texCells >>= (" & "++) )
    where texCells = [ printf "%s %s" (coloring v) (value v) | v <- bRes r ]
          cnt = bCnt r
          coloring :: Int -> String
          coloring v = printf "\\cellcolor{blue!%d}" (floor (fraction v * 50.0) :: Int)
          -- percent :: Int -> Double
          -- percent v =  100 * (fraction v)
          value :: Int -> String
          value v | v == 0    = "--"
                  | cnt == 1  = "$\\checkmark$"
                  | otherwise = printf "%d\\%% (%d)" ( (floor $ fraction v * 100) :: Int ) v
          fraction :: Int -> Double
          fraction v = fromIntegral v / fromIntegral cnt

main = interact $ parseCsv >>> parseData >>> tex

