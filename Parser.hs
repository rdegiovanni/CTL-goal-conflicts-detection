module Parser where

import ParseLib
import Dctl

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S


parseFormula :: String -> Formula
parseFormula s = fst (head (papply pFormula s))

parseSpecification :: String -> Set Formula
parseSpecification s = case papply pSpec s of
							[(x,[])] -> S.fromList x
							[(_,s)] -> error ("Parser error - unable to parse: " ++ s)
							z -> error ("Parser error: " ++ s)


pSpec :: Parser [Formula]
pSpec = pFormula `sepby1` (symbol ";")


-- Formula parsers

pFormula :: Parser Formula
pFormula = pIff


--  Iff
--
pIff :: Parser Formula
pIff = pIf `chainl1` pIffOp

pIffOp = symbol "<->" >> return Iff

--  If
--
pIf :: Parser Formula
pIf = pOr `chainl1` pIfOp

pIfOp = symbol "->" >> return If

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
pPath = pX +++ pU +++ pW +++ pG

pX = do { symbol "X"; f <- pLowLevel; return (X f) }

pU = do { f1 <- pLowLevel; symbol "U"; f2 <- pLowLevel; return (U f1 f2) }

pW = do { f1 <- pLowLevel; symbol "W"; f2 <- pLowLevel; return (W f1 f2) }

pG = do { f1 <- symbol "G"; f <- pLowLevel; return (G f) }




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

