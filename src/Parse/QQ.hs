{-# LANGUAGE QuasiQuotes #-}

module Parse.QQ (formula, theory, benchmark) where

import Parse
import Data.Formula

import Data.Data
import Text.ParserCombinators.Parsec
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

qq :: Data t => Parser t -> QuasiQuoter
qq parser = QuasiQuoter {
      quoteExp = qexp 
    , quotePat  = undefined
    , quoteType = undefined
    , quoteDec  = undefined
    }
  where 
      qexp s = do  
          loc <- TH.location
          let pos =  (TH.loc_filename loc,
                     fst (TH.loc_start loc),
                     snd (TH.loc_start loc))
          expr <- parse' pos s
          dataToExpQ (const Nothing ) expr 
          -- dataToExpQ (const Nothing `extQ` antiExprExp) expr

      -- parse' :: Monad m => (String, Int, Int) -> String -> m t
      parse' (file, line, col) s =
          case runParser parser () "" s of
            Left err  -> fail $ show err
            Right e   -> return e

formula :: QuasiQuoter
formula = qq formulaParser

theory :: QuasiQuoter
theory = qq theoryParser

benchmark :: QuasiQuoter
benchmark = qq problemParser

parse' :: Monad m => (String, Int, Int) -> String -> m Formula
parse' (file, line, col) s =
    case runParser ( formulaParser <* eof ) () "" s of
      Left err  -> fail $ show err
      Right e   -> return e


-- antiExprExp :: Expr -> Maybe (TH.Q TH.Exp)
-- antiExprExp  (AntiIntExpr v)  = Just $ TH.appE  (TH.conE (TH.mkName "IntExpr"))
--                                                 (TH.varE (TH.mkName v))
-- antiExprExp  (AntiExpr v)     = Just $ TH.varE  (TH.mkName v)
-- antiExprExp  _                = Nothing
