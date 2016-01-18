module Parser where

import ParseLib
import Dctl

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import Data.List	(sortBy, (\\))
import Data.List as L

import Data.Maybe as M
import Data.Char as C
import Debug.Trace

parseFormula :: String -> Formula
parseFormula s = fst (head (papply pFormula s))

parseDOMandGOALS :: String -> (Set Formula,Set Formula)
parseDOMandGOALS s = let no_comments = (remove_comments s) ;
						 (dom,goals) = split_DOM_and_GOALS no_comments ;
						 dom_forms = if (dom=="") then S.empty else parseSpecification dom ;
						 goals_forms = if (goals=="") then S.empty else parseSpecification goals
					 in
					 	 (dom_forms,goals_forms)

parseSpecification :: String -> Set Formula
parseSpecification s = 	case papply pSpec s of
							[(x,[])] -> S.fromList x
							[(_,str)] -> error ("Parser error - unable to parse: " ++ str)
							z -> error ("Parser error: " ++ s)

remove_comments :: String -> String
remove_comments s = let splitted = L.lines s in
						let no_comments = L.filter (\l -> not $ L.isPrefixOf "--" l) splitted ;
							add_newline = L.map (\l -> l++"\n") no_comments
						in
							L.foldl (++) ""  add_newline

split_DOM_and_GOALS :: String -> (String,String)
split_DOM_and_GOALS s = let splitted = L.lines s ;
							upper_s = L.map (L.map C.toUpper) splitted ;
							dom_index = L.findIndex (\l -> L.isPrefixOf "DOM" l) upper_s ;
							goal_index = L.findIndex (\l -> L.isPrefixOf "GOAL" l) upper_s	;	
							dom_i = if (M.isJust dom_index) then ((M.fromJust dom_index)+1) else 0 ;
							goal_i = if (M.isJust goal_index) then ((M.fromJust goal_index)+1) else 0 
						in
							if (dom_i < goal_i) then
								let dom_str = if (dom_i==0) then "" else (foldl (++) "" (L.drop dom_i (L.take (goal_i -1) splitted))) ;
									goal_str = if (goal_i==0) then "" else foldl (++) "" (L.drop goal_i splitted)
								in
									(trace ("dom_i = " ++ show dom_i))
									(trace ("goal_i = " ++ show goal_i))
									(dom_str,goal_str)
							else
								let dom_str = if (dom_i==0) then "" else (foldl (++) "" (L.drop dom_i splitted)) ;
									goal_str = if (goal_i==0) then "" else (foldl (++) ""  (L.drop goal_i (L.take (dom_i -1) splitted)))
								in
									(trace ("dom_i = " ++ show dom_i))
									(trace ("goal_i = " ++ show goal_i))
									(dom_str,goal_str)

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
pPath = pX +++ pU +++ pW +++ pG +++ pF

pX = do { symbol "X"; f <- pLowLevel; return (X f) }

pU = do { f1 <- pLowLevel; symbol "U"; f2 <- pLowLevel; return (U f1 f2) }

pW = do { f1 <- pLowLevel; symbol "W"; f2 <- pLowLevel; return (W f1 f2) }

pG = do { f1 <- symbol "G"; f <- pLowLevel; return (G f) }

pF = do { f1 <- symbol "F"; f <- pLowLevel; return (U T f) }



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

