{-# LANGUAGE GADTs
           , FlexibleContexts
           , MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , BangPatterns
           , ScopedTypeVariables
           , LambdaCase
           , TupleSections #-}
module Benchmark (compareSolvers, compareSolversGroup, compareSolversGroupWithFileOutput, RandM, BenchGroup(..)) where 

import Data.Theory.Interpreted
import Control.Concurrent.ParallelIO.Global
import Data.Solvers
import Data.Solvers.Zipperposition
import Data.Solvers.Zeno
import Data.Solvers.Imandra
import Data.Formula
import Data.Theory
import Util
import Text.Printf
import Data.List
import Data.List.Index
import Control.Monad
import Data.Semigroup
import Data.Functor
import Data.Time.Clock.POSIX
import System.Random
import System.Directory
import System.IO
import Control.Monad.State
import ToTex
import ToSmtlib2
import qualified GHC.Conc as Conc

data BenchGroup = BenchGroup { 
                       bgId :: String
                     , bgTex :: Tex 
                     , bgProblems :: [Benchmark]
                     }

data BenchmarkResult = BenchmarkResult { 
                          bSolver    :: AnySolver
                        , bBenchmark :: Benchmark
                        , bStatus    :: SolverResult
                        , bTime      :: Seconds
                        }

benchTitle :: Benchmark -> String
benchTitle = show . bConjecture 

compareSolvers' :: Seconds -> [AnySolver] -> [Benchmark] -> IO ()
compareSolvers' t s benchmarks = 
           compareSolvers t s ( fmap (show . bConjecture) benchmarks `zip` benchmarks)

compareSolvers :: Seconds -> [AnySolver] -> [(String, Benchmark)] -> IO ()
compareSolvers timeout solvers benchmarks 
   = do putStrLn "setting up solvers ..."
        sequence_ (setup <$> solvers)
        (t, rs) <- time $ do 
          putStrLn $ toRow $ "" : (name <$> solvers)
          -- sequence [ runBenchmark b | b <- benchmarks ]
          parallel [ runBenchmark b | b <- benchmarks ]
        putStrLn "shutting down solvers ..."
        putStrLn $ printf "total time: %s" $ fmtTime $ Seconds t
        sequence_ (teardown <$> solvers)
        putStrLn $ unlines 
                 $ filter (/= "") 
                 $ displayErr <$> join rs
        return ()

   where runBenchmark (name, b) 
             = do rs <- parallel ( runSolver b <$> solvers ) -- TODO parallel here
                  putStrLn $ toRow $ name : ( displayCell <$> rs )
                  return rs

         displayCell bench = case bStatus bench of 
                     Valid           -> printf "%5.5f s" (unSeconds $ bTime bench)
                     CounterSat      -> "!!!" 
                     TimeOut         ->  "---"
                     Unknown         -> "???"
                     NotApplicable _ -> " "
                     Error _  -> printf "error"
         displayErr bench = case bStatus bench of
                             Error         e -> unlines [ "Error for solver " ++ (name $ bSolver bench) ++ ":"         , e  ]
                             NotApplicable e -> unlines [ "Not Applicable:", e  ]
                             _       -> ""

         toRow :: [String] -> String
         toRow elems = intercalate " | " $ zipWith (uncurry crop) fmt elems
         fmt = (ARight, 80):[ (ACentre, 10) | _ <- solvers ]
         crop :: Align -> Int -> String -> String
         crop align n str = ws left ++ (take n str) ++ ws right 
           where ws n = [ ' ' | i <- [0..n - 1] ]
                 (left, right) = case align of 
                                      ARight  -> (cnt, 0)
                                      ALeft   -> (0, cnt)
                                      ACentre -> (cnt `div` 2, cnt - (cnt `div` 2))
                                  where cnt = n - length str


         runSolver bench  solver
            = do (t, r) <- time $ prove solver timeout bench
                 return $ BenchmarkResult {
                     bSolver    = solver
                   , bBenchmark = bench
                   , bStatus    = r
                   , bTime      = Seconds t
                   }

type RandM a = State StdGen a
-- type BenchGroup = [Benchmark]
type BenchRGroup = [BenchmarkResult]

class ProgressHandler a where
  progressHeader :: a -> [AnySolver] -> IO ()
  progressRow    :: a -> BenchGroup -> [BenchmarkResult] -> IO ()
  progressSeperator :: a -> IO  ()
  progressEnd    :: a -> IO ()

newtype CsvHandler = CsvHandler Handle

csvHandler path = do 
      f <- openFile path WriteMode 
      hSetBuffering f NoBuffering
      return $ CsvHandler f

instance ProgressHandler CsvHandler where

  progressHeader (CsvHandler handle) solvers = do
        hSetBuffering handle NoBuffering
        hPutStrLn handle $ csvRow $ "id" : "tex" :  "count" : fmap name solvers

  progressRow (CsvHandler handle) bs rs = do
        hPutStrLn handle $ csvRow $ bgId bs  : compileTex (bgTex bs)  : nbs             : fmap displayCell (groupBySolver rs)
    where displayCell r 
                  | all  isNA stats = "N.A."
                  | none isNA stats = show . count (== Valid) $ stats
                  | otherwise = error $ show stats
                      where stats = fmap bStatus $ r
                            isNA (NotApplicable _) = True
                            isNA _                 = False
                            none p = all (not.p) 
          nbs = show . length . bgProblems $ bs

  progressSeperator (CsvHandler handle) = do
        hPutStrLn handle "\t\t"
        hFlush handle

  progressEnd (CsvHandler handle) = do
        hFlush handle
        hClose handle

csvRow :: [String] -> String
csvRow = intercalate "\t"


newtype TexTableHandler = TexTableHandler Handle

texTableHandler path = do 
      f <- openFile path WriteMode 
      hSetBuffering f NoBuffering
      return $ TexTableHandler f

instance ProgressHandler TexTableHandler where

  progressHeader (TexTableHandler handle) solvers = do
        hSetBuffering handle NoBuffering
        hPutStrLn handle $ printf "\\begin{tabular}{|r|%s|}" (intercalate "|" [ "r" | _ <- solvers ])
        hPutStrLn handle $ toTexRow $ toTexStr "group" :  toTexStr "total" : (texName <$> solvers)
        hPutStrLn handle texLine

  progressRow (TexTableHandler handle) bs rs = do
        let nbs = length . bgProblems $  bs
        hPutStrLn handle $ toTexRow $ bgTex bs : toTex nbs : (displayCellTex <$> groupBySolver rs)
    where displayCellTex =  toTex . count (== Valid) . fmap bStatus

  progressSeperator (TexTableHandler handle) = do
        hPutStrLn handle texLine
        hFlush handle

  progressEnd (TexTableHandler handle) = do
        hPutStrLn handle $ "\\end{tabular}"
        hFlush handle
        hClose handle

groupBySolver = groupBy sameSolver
   where sameSolver r1 r2 = (name $ bSolver r1) == (name $ bSolver r2)
data StdoutHandler = StdoutHandler [AnySolver]

stdoutHandler solvers = return $ StdoutHandler solvers

instance ProgressHandler StdoutHandler where

  progressHeader h@(StdoutHandler solvers) _ = do
        hSetBuffering stdout NoBuffering
        putStrLn         $ toRow h $ ""      : (name <$> solvers)

  progressRow h bs rs = do
        let nbs = length . bgProblems $  bs
        putStrLn    $ toRow h $ bgId  bs             : (displayCell    <$> groupBySolver rs)

    where
         displayCell :: BenchRGroup -> String
         displayCell bs | cntNA  == (length bs)  = "N.A."
                        | cntErr == (length bs)  = "!!!"
                        | cntErr /= 0         = error "group of benchmarks is partially errornous"
                        | cntNA /= 0         = error "group of benchmarks is partially not applicable"
                        | cntValid  == 0  = "-" 
                        | length bs == 1 = "ok"
                        | otherwise =  printf "%1.2f" $  (fromIntegral cntValid :: Double) / (fromIntegral $ length bs)
                where 
                 cntStatus f = (count f) . fmap bStatus $ bs
                 cntValid = cntStatus (== Valid)
                 cntNA = cntStatus (\case {NotApplicable _ -> True; _ -> False })
                 cntErr = cntStatus (\case {Error _ -> True; _ -> False })


  progressSeperator h@(StdoutHandler solvers) = 
          putStrLn $ rep '|' '+' $ toRow h ( infLine:[infLine | _ <- solvers] )
            where rep l r = fmap $ \x -> if x == l then r else x
                  infLine = '-':infLine
                                  

  progressEnd (StdoutHandler solvers) = return ()


toRow :: StdoutHandler -> [String] -> String
toRow (StdoutHandler solvers) elems = intercalate " | " $ zipWith (uncurry crop) fmt elems
  where fmt = (ARight, 60):[ (ACentre, 10) | _ <- solvers ]
        crop :: Align -> Int -> String -> String
        crop align n str = ws left ++ (take n str) ++ ws right 
           where ws n = [ ' ' | i <- [0..n - 1] ]
                 (left, right) = case align of 
                                      ARight  -> (cnt, 0)
                                      ALeft   -> (0, cnt)
                                      ACentre -> (cnt `div` 2, cnt - (cnt `div` 2))
                                  where cnt = n - length (take n str)

data AnyProgHandler where 
  AnyHandler :: ProgressHandler p => p -> AnyProgHandler 

instance ProgressHandler AnyProgHandler where 
  progressHeader (AnyHandler h) = progressHeader h
  progressRow (AnyHandler h) = progressRow h
  progressSeperator (AnyHandler h)= progressSeperator h
  progressEnd (AnyHandler h)= progressEnd h

instance ProgressHandler a => ProgressHandler [a]  where 
  progressHeader hs s   = forM_ hs $ \h -> progressHeader h s
  progressRow hs rs bs  = forM_ hs $ \h -> progressRow h rs bs
  progressSeperator hs  = forM_ hs $ \h -> progressSeperator h
  progressEnd hs        = forM_ hs $ \h -> progressEnd h



texLine = "\\hline"
toTexRow xs = printf "$ %s $\\\\ \\hline" $ intercalate "$ & $" (compileTex <$> xs)

compareSolversGroup :: Seconds -> [AnySolver] -> [[BenchGroup]] -> IO ()
compareSolversGroup = compareSolversGroupWithHandlers []

compareSolversGroupWithFileOutput :: FilePath -> Seconds -> [AnySolver] -> [[BenchGroup]] -> IO ()
compareSolversGroupWithFileOutput file timeout solvers benchmarks = do  
  handler <- csvHandler file
  compareSolversGroupWithHandler handler timeout solvers benchmarks

compareSolversGroupWithHandler :: ProgressHandler p => p -> Seconds -> [AnySolver] -> [[BenchGroup]] -> IO ()
compareSolversGroupWithHandler handler = compareSolversGroupWithHandlers [AnyHandler handler]

compareSolversGroupWithHandlers :: [AnyProgHandler] -> Seconds -> [AnySolver] -> [[BenchGroup]] -> IO ()
compareSolversGroupWithHandlers handlers (Seconds timeout) solvers benchmarks = do 

        putStrLn "setting up solvers ..."
        !_ <- sequence (setup <$> solvers)

        putStrLn "generating benchmarks..."
        let !bss = [ filter ((> 0) . length . bgProblems) bs | bs <- benchmarks ]
        estimateTime solvers bss 

        t <- getCurrentTime
        stdout <- AnyHandler <$> stdoutHandler solvers
        let prog = stdout : handlers 

        progressHeader prog solvers

        (t, rs) <- time $ do 
          sequence $ intercalate 
            [ progressSeperator prog >> return [] ]
            (for bss $ \bs -> 
               for bs $  \b  -> do 
                  rs <- runBenchmarks b 
                  progressRow prog b (join rs)
                  return rs
                  )
        progressEnd prog
        putStrLn $ printf "total time: %s" $ fmtTime $ Seconds t
        putStrLn "shutting down solvers ..."
        sequence_ (teardown <$> solvers)
        putStrLn $ unlines 
                 $ filter (/= "") 
                 $ displayErr <$> (join . join) (rs)
        return ()

   where runBenchmarks :: BenchGroup -> IO [BenchRGroup]  
         runBenchmarks bs = parallel [ sequence [ runSolver b s | b <- bgProblems bs ] | s <- solvers ] 
         -- runBenchmarks bs = parallel [ parallel [ runSolver b s | b <- bgProblems bs ] | s <- solvers ]  -- TODO
         for as action = fmap action as 
         estimateTime solvers bss = do 
              putStrLn "Groups: "
              putStrLn $ unlines  $ fmap (\b -> printf "- %s: %d" (bgId b) (length . bgProblems $ b))  ( join bss )
              let nbs      = sum $ fmap (length . bgProblems) (join bss)
              let nthreads = Conc.numCapabilities
              putStrLn $ unlines [ 
                           "total benchmarks: " ++ show nbs
                         , "number of threads: " ++ show nthreads 
                         , "estimated time: " ++ (fmtTime $ Seconds $ timeout * fromIntegral nbs * fromIntegral (length solvers) / fromIntegral nthreads) 
                         , "====================="
                         ]



         displayErr bench = case bStatus bench of
                             Error         e -> unlines [ printf "Error for solver %s on benchmark:" (name.bSolver $ bench), e  ]
                             NotApplicable e -> unlines [ "Not Applicable:", e  ]
                             _       -> ""
         runSolver bench  solver
            = do (t, r) <- time $ prove solver (Seconds timeout) bench
                 return $ BenchmarkResult {
                     bSolver    = solver
                   , bBenchmark = bench
                   , bStatus    = r
                   , bTime      = Seconds t
                   }


writeBenchmarks :: FilePath -> [BenchGroup] -> IO ()
writeBenchmarks base bs = do 
    -- createDirectoryIfMissing True path
    forM_ bs $ \bg -> do
      forM (indexed $ bgProblems bg) $ \(i, b) ->  do
        forM encodings $ \(eName, eFn, eExt) -> do
          let dir  = toPath [ base, asciiFormula . bgId $ bg, eName ]
          let file = toPath [ dir , printf "%d.%s" i eExt] --printf "%s/%s/%d.%s" dir i n

          createDirectoryIfMissing True dir
          case eFn . unwrap . benchmarkInf $ b of
            Right encoded -> writeFile file encoded
            Left  _       -> return ()
  where toPath    = intercalate "/"
        encodings = [ ("smt2"      , return . toSmtlib2  , "smt2") 
                    , ("zf"        , return . toZfLogic  , "zf"  )
                    , ("zf_rewrite", return . toZfRewrite, "zf"  )
                    , ("zeno"      , toZeno              , "hs"  )
                    , ("imandra"   , toImandra           , "iml"  )
                    ]

time :: IO a -> IO (Double, a)
time act = do
  start <- getTime
  result <- act
  end <- getTime
  let !delta = end - start
  return (delta, result)

fmtTime :: Seconds -> String
fmtTime (Seconds t) 
       | time >= day  = sub day "d"
       | time >= hour = sub hour "h"
       | time >= min  = sub min "min"
       | otherwise    = printf "%2.3f s" t
  where hour = 60 * min
        min  = 60 * sec
        sec = 1 :: Int
        day  = 24 * hour
        time = floor t :: Int
        sub limit char = let t' = (time `div` limit)
                         in printf "%s %s %s" (show t' ) char (fmtTime . Seconds $ t - fromIntegral ( limit * t' ))

getTime :: IO Double
getTime = realToFrac `fmap` getPOSIXTime

data Align = ALeft | ARight | ACentre
