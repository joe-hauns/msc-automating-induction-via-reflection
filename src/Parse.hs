{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}



module Parse (formulaParser, theoryParser, problemParser) where


import Data.Formula
import Data.Formula.Common
import Data.Signature
import Data.Theory.Interpreted
import Text.ParserCombinators.Parsec
import qualified Text.Parsec.Expr as Expr
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import Serialize
import Data.List
import Control.Monad
import Debug.Trace

formula :: Parser Formula
formula = Expr.buildExpressionParser conTable formula'

formula' :: Parser Formula
formula' =   parseAtom
        <||> parseConst
        <||> par formula
        <?> "formula"

conTable = [ [Expr.Prefix ( BaseNot <$ serShowKwOp NegationConnective )  ]
           , [Expr.Prefix ( try $ parseQuantPref Universal )  ]
           , [Expr.Prefix ( try $ parseQuantPref Existential )  ]
           , [Expr.Infix  ( con And     ) Expr.AssocLeft]
           , [Expr.Infix  ( con Or      )  Expr.AssocLeft] 
           , [Expr.Infix  ( con Implies )  Expr.AssocRight] 
           , [Expr.Infix  ( con If      )  Expr.AssocLeft] 
           , [Expr.Infix  ( con Iff     )  Expr.AssocNone]
           ]
  where con c = BaseCon c <$ serShowKwOp c

traceList x = trace (unlines $ x) x

serShowKwOp c = foldl1 (<||>) [ kwOp ( genSerialize s c) | s <- allConnectiveSerializers ]

opTable = [[Expr.Infix (fun <$> operator ) Expr.AssocLeft]]
  where fun f l r = BaseFun f [l,r] Nothing

-- parseEq = do lhs <- term
--              eq <-  parseEqSym Pos <||> parseEqSym Neg 
--              rhs <- term
--              return $ BaseAtom $ BaseEq eq lhs rhs

parseEqSym pol = pol <$ foldl1 (<||>) [ kwOp (genSerialize s pol) | s <- allConnectiveSerializers ]

parsePred = do p <- ident
               ts <- args
               return $ BaseAtom $ BasePred p ts

parseConst =  BaseCon0 <$> ( parse Bot <||> parse Top 
                                <?> "zero-ary connective")
  where parse c = c <$  ( kw (genSerialize humanWritable c) <||>  kwOp (genSerialize humanReadable c) )
               

parseAtom = do t <- term
               BaseAtom <$> (parseRestEq t
                             <||> (toPred t) 
                             <?> "atom")
    where 
      parseRestEq lhs = do eq <-  parseEqSym Neg <|> parseEqSym Pos
                           rhs <- term
                           return $ BaseEq eq lhs rhs
      toPred (BaseVar _ _) = fail "expected atom, got variable"
      toPred (BaseFun (Id p) as _) = return $ BasePred (Id p) as
args = par $ term `sepBy` (kwOp ",")
               
term :: Parser Term
term = Expr.buildExpressionParser opTable term'
               
term' :: Parser Term
term' = par term
    <||> funTerm
    <||> ((flip BaseVar) Nothing  <$> ident )
    <?> "term"

infixr 1 <||>
l <||> r = (try l) <|> r

funTerm = do f <- ident
             ts <- args
             return $ BaseFun f ts Nothing

parseQuantPref q = do 
          q <- parseQuant q 
          vs <- vars
          kwOp "." 
          return $ if  vs == [] 
            then closure q 
            else quantify q vs 
        where quantify q vs = foldl (.) id ( uncurry (BaseQuant q) <$> vs )
              parseQuant q = q <$ ( kw (genSerialize humanWritable q) <||>  kwOp (genSerialize humanReadable q) )


vars :: Parser [( VarId, Maybe SortId )]
vars =  (try sorted <||> unsorted) `sepBy` (kwOp ",")
  where sorted   = do v <- ident 
                      kwOp ":"
                      s <- ident
                      return (v, Just s)
        unsorted = fmap (, Nothing) ident 

kw = T.reserved tp
kwOp k = T.reservedOp tp k 
operator = Id <$> T.operator tp
ident = Id <$> T.identifier tp 
par = T.parens tp



theoryParser = do T.whiteSpace tp
                  elems <- many item -- `endBy` (kwOp ".") 
                  -- elems <- (Left  <$> formula 
                  --       <||> Right <$> declaration) `endBy` (kwOp ".") 
                  return $ Theory { 
                               thName      = "<parsing not implemented>"
                             , thAxioms    = [ f | ItFormula     f <- elems ] 
                             , thSignature = [ d | ItDeclaration d <- elems ]
                             , thDataTypes = [ i | ItInductive   i <- elems ]
                             --   thAxioms    = [ f | Left f  <- elems ] 
                             -- , thSignature = [ d | Right d <- elems ]
                             -- , thDataTypes = []
                             } 

problemParser = do T.whiteSpace tp

                   kw "theory"
                   thry <- theoryParser
                   
                   kw "conjecture"
                   conj <- formula
                   kwOp "."
                   return $ Benchmark {
                       bTheory     = thry
                     , bConjecture = conj
                     }

data Item = ItFormula Formula
          | ItDeclaration SymDec
          | ItInductive FunId

item =  (( ItInductive <$> inductive )
    <||> ( ItDeclaration <$> declaration )
    <||> ( ItFormula <$> formula )
    <?> "item") <* kwOp "."

inductive = kw "inductive" *> ident
              

formulaParser = T.whiteSpace tp >> formula <* eof


declaration :: Parser SymDec
declaration = do id <- (ident <|> operator <?> "declaration id")
                 kwOp ":"
                 (id ::::) <$> (pred <||> fun <||> const <?> "function declaration" )
      where pred = do kw "P"
                      as <- sortList
                      return $ Pred as
            fun = do 
                  as <- sortList
                  sortArrow  
                  ret <- ident
                  return $ as :-> ret
            const = do x <- ident  
                       return $ [] :-> x

            sortList = ( return <$> ident ) 
                    <||> ( par $ ident `sepBy` (kwOp ",")  )

            sortArrow = foldl1 (<||>) ((kwOp . scTypeArrow) <$> allConnectiveSerializers)
                     

tp = T.makeTokenParser lang

lang :: LanguageDef a
lang = T.LanguageDef {

    -- | Describes the start of a block comment. Use the empty string if the
    -- language doesn't support block comments. For example \"\/*\".

    T.commentStart   = "/*",

    -- | Describes the end of a block comment. Use the empty string if the
    -- language doesn't support block comments. For example \"*\/\".

    T.commentEnd     = "*/",

    -- | Describes the start of a line comment. Use the empty string if the
    -- language doesn't support line comments. For example \"\/\/\".

    T.commentLine   = "--",

    -- | Set to 'True' if the language supports nested block comments.

    T.nestedComments = True,

    -- | This parser should accept any start characters of identifiers. For
    -- example @letter \<|> char \'_\'@.

    T.identStart     =  oneOf identChars, -- letter <|> upper,

    -- | This parser should accept any legal tail characters of identifiers.
    -- For example @alphaNum \<|> char \'_\'@.

    T.identLetter    = oneOf $ identChars ++ "'",

    -- | This parser should accept any start characters of operators. For
    -- example @oneOf \":!#$%&*+.\/\<=>?\@\\\\^|-~\"@

    T.opStart        = oneOf opLetters,

    -- | This parser should accept any legal tail characters of operators.
    -- Note that this parser should even be defined if the language doesn't
    -- support user-defined operators, or otherwise the 'reservedOp'
    -- parser won't work correctly.

    T.opLetter       = oneOf $  opLetters,

    -- | The list of reserved identifiers.

    T.reservedNames  = ["forall", "exists", "inductive", "true", "false", "theory", "conjecture"],

    -- | The list of reserved operators.

    T.reservedOpNames = nub [".", ",",  ":", "<->", "<-", "->", "~", "=", "/=", "\\/", "/\\"] 
                     ++ filter (all (`elem` opLetters)) allShowSerOps,

    -- | Set to 'True' if the language is case sensitive.

    T.caseSensitive  =  True

    }
    where 
       showSerOps xs = join [ fmap (genSerialize s) xs | s <- allConnectiveSerializers ] 
       allShowSerOps = showSerOps allQuantifiers 
                    ++ showSerOps allConnectives 
                    ++ showSerOps [NegationConnective]
                    ++ showSerOps allPolarities
                    ++ showSerOps allCon0
                    ++ (scTypeArrow <$> allConnectiveSerializers)
       identChars =  ['a'..'z'] ++ ['A'..'Z'] ++ join ( fmap show [0..9] ) ++ "_"
       opLetters = nub . filter (not . (`elem` identChars)) 
                 $ "~:,.+-*/\\<>='|" 
                ++ join allShowSerOps

