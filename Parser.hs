module Parser where

import ParseLib
import Dctl

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S


parseFormula :: String -> Formula
parseFormula s = fst (head (papply pFormula s))

parseSpecification :: String -> Set Formula
parseSpecification s =  S.fromList . fst . head $ papply pSpec s


pSpec :: Parser [Formula]
pSpec = pFormula `sepby1` (symbol ";")


-- Formula parsers

pFormula :: Parser Formula
pFormula = pIff


--  Iff
--
pIff :: Parser Formula
pIff = pOr `chainl1` pIffOp

pIffOp = symbol "<->" >> return Iff



--  Or
--
pOr :: Parser Formula
pOr = pAnd `chainl1` pOrOp

pOrOp = symbol "||" >> return Or


--  And
--
pAnd :: Parser Formula
pAnd = pQ `chainl1` pAndOp

pAndOp = symbol "&&" >> return And


-- Quantifiers
--
pQ :: Parser Formula
pQ = do { q <- pQuan; pf <- pPath; return (q pf) } +++ pLowLevel

pQuan =   (symbol "A" >> return A) +++ 
          (symbol "E" >> return E) +++
          (symbol "O" >> return O) +++
          (symbol "P" >> return P)


-- Path formulas
--
pPath :: Parser PFormula
pPath = pX +++ pU +++ pW

pX = do { symbol "X"; f <- pLowLevel; return (X f) }

pU = do { f1 <- pLowLevel; symbol "U"; f2 <- pLowLevel; return (U f1 f2) }

pW = do { f1 <- pLowLevel; symbol "W"; f2 <- pLowLevel; return (W f1 f2) }




-- Path formulas
--
pLowLevel :: Parser Formula
pLowLevel = pNot +++ pProp +++ pTrue +++ pFalse +++ pParenthesis

pTrue = do {symbol "True"; return T}

pFalse = do {symbol "False"; return F}

pNot = do { symbol "!"; f <- pLowLevel; return (Not f) }

pProp = do { f <- myident; return (Prop f) }

pParenthesis = bracket (symbol "(") pFormula (symbol ")")



reserved_words :: [String]
reserved_words = ["A", "E", "O", "P", "G", "F", "U", "W", "X", "True", "False"]

myident :: Parser String
myident = identifier reserved_words

