{-# LANGUAGE ConstraintKinds #-}

module Util (
      disjointUnions   
    , mkPair 
    -- , operatorNames
    , OperatorNaming(..)
    , transOp
    , otw 
    , count
    , unwrap
    , Result
    , seqA
    , pushTrace
    , failure
    , Seconds(..)
    , unSeconds
    , par 
    , tup
    , groupByFst
    , asciiFormula
    , pairs
    -- , toTex
    ) where


import Control.Arrow
import Text.Printf
-- import Data.HashMap
-- import qualified Data.HashMap as Map
-- import Data.Hashable
import Data.List 
import Data.List.HT
import Prelude hiding (fail)
import Data.Maybe
import Data.Composition
import qualified Data.List as List
import Debug.Trace
import Text.Printf

type Result a = Either [String] a
type Map k v = [(k, v)]


data OperatorNaming = OperatorNaming {
         opId   :: String
       , opName :: String
       , opTex  :: String
       }

operatorTable :: [OperatorNaming]
operatorTable = [ OperatorNaming "++" "app"  "\\append{}"
                , OperatorNaming "*"  "mul"  "\\times{}"
                , OperatorNaming "/\\"  "and"  "\\lanand{}"
                , OperatorNaming "\\/"  "or"  "\\lor{}"
                , OperatorNaming "/"  "div"  "/"
                , OperatorNaming "-"  "sub"  "-"
                , OperatorNaming "+"  "add"  "+"
                , OperatorNaming "<=" "leq"  "\\leq{}"
                , OperatorNaming "<"  "less" "<"
                , OperatorNaming "|="  "models" "\\vDash"
                , OperatorNaming "'"  "Prime" "'"
                ]
              
trc f x = trace (show x ++ " -> " ++ show (f x)) (f x)

-- transOp a b = trc (transOp' a) b

transOp :: (OperatorNaming -> String) -> String -> String
-- transOp f op = trace (printf "translating %s -> %s" op res) res
transOp f op = res
  where 
    res = fix transOp' op 
    transOp' op = case find ((`isInfixOf` op) . opId) $ operatorTable of
                    Just op' -> replace (opId op') (f op') op
                    Nothing  -> op
    fix f x 
      | f x == x  = x
      | otherwise = fix f (f x)
       



groupByFst :: Eq a => [(a,b)] -> [(a,[b])]
groupByFst [] = []
groupByFst ( (a,b):abs ) = (a, b:sameA):(groupByFst diffA)
  where sameA = [ b' | (a',b') <- abs, a' == a ]
        diffA = [ (a',b') | (a',b') <- abs, a' /= a ]
 
unwrap (Left msgs) = error $ unlines $  "error: " : reverse  msgs
unwrap (Right r) = r

type MapConst k v = ( Eq k, Eq v, Show v, Show k )

disjointUnions :: MapConst k v =>  [Map k v] -> Map k v
disjointUnions = foldl1 disjointUnion

disjointUnion :: MapConst k v =>  Map k v -> Map k v -> Map k v
disjointUnion a b | inter == [] = List.union a b
                  | otherwise   = error $ "maps have common keys: " ++ show [ show i ++ " -> " ++ show [ a!i, b!i ] | i <- inter ]
  where inter = [ k | k <- List.intersect (keys a) (keys b)
                    , a!k /= b!k ]
        keys = fmap fst
        l ! i = fromJust $ find ((== i).fst) l

mkPair :: a -> b -> (a,b)
mkPair a b = (a,b)

otw = otherwise

seqA :: Arrow a => [a b b] -> a b b
seqA = foldl (>>>) (arr id)
pushTrace :: String -> Result a -> Result a
pushTrace s (Left msgs) = Left $ ("\tin "++ s) : msgs
pushTrace _ (Right r)   = Right r

failure :: [String] -> Result a
failure = Left

newtype Seconds = Seconds Double
unSeconds (Seconds s) = s

par s = "(" ++ s ++ ")"
tup = par . intercalate ", "

count = length .: filter

asciiFormula = 
      replace "∧" "/\\"
    . replace "∨" "\\/"
    . replace "∃" "exists "
    . replace "∀" "forall "

pairs :: [a] -> [(a,a)]
pairs []     = []
pairs (a:[]) = []
pairs (a:b:xs) = (a,b):pairs (b:xs)
-- replace a b s | all (zipWith (==) a b) = b:replace a b s'
--                         where s' = drop (length a) s
-- replace a b (s:ss) = replace a b ss


