{-# LANGUAGE DeriveGeneric #-}
module Dctl where

import GHC.Generics (Generic)
import Data.Hashable

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import Data.List	(sortBy, (\\))
import Data.List as L

import Prelude hiding (break, negate)

import Debug.Trace

-- dCTL Formulas 
data Formula = 	And Formula Formula
			|	Or Formula Formula
			|	If Formula Formula
			|	Iff Formula Formula
			|	Not Formula
			-- 	Quantifiers
			|	A PFormula
			|	E PFormula
			|	O PFormula
			|	P PFormula
			--	Atomic formulas 		
			|	Prop String
			|	Norm
			|	T
			|	F
			deriving (Eq,Ord,Generic)

data PFormula 	= 	U Formula Formula
				|	W Formula Formula
				|	X Formula
				|	G Formula
				|	FF Formula
				deriving (Eq,Ord,Generic)



instance Show Formula where
	show (And p q) 	=	show p ++ " && " ++ show q
	show (Or p q) 	=	"("++ show p ++ " || " ++ show q ++")"
	show (If p q)	=	show p ++ " -> " ++ show q 
	show (Iff p q) 	=	show p ++ " <-> " ++ show q
	show (Not p)		=	"!" ++ show p
	show (A f) 		= 	"A" ++ show f
	show (O f) 		= 	"O" ++ show f
	show (P f) 		= 	"P" ++ show f
	show (E f) 		= 	"E" ++ show f
	show (Prop s) 	= 	s	
	show Norm		= 	"n"
	show T 			= 	"true"
	show F 			= 	"false"

instance Show PFormula where
	show (U p q) 	=	"(" ++ show p ++ " U " ++ show q ++ ")"
	show (W p q) 	=	"(" ++ show p ++ " W " ++ show q ++ ")"
	show (X p) 		=	"X" ++ "(" ++  show p ++ ")"
	show (G p) 		=	"G (" ++ show p ++ ")"
	show (FF p) 	= 	"F (" ++ show p ++ ")"
	 


isAX :: Formula -> Bool
isAX (A(X _)) = True
isAX _ = False

isEX :: Formula -> Bool
isEX (E(X _)) = True
isEX _ = False

isEU :: Formula -> Bool
isEU (E(U _ _)) = True
isEU _ = False

isAU :: Formula -> Bool
isAU (A(U _ _)) = True
isAU _ = False

isF :: Formula -> Bool
isF (A(U T _)) = True
isF (E(U T _)) = True
isF (A(FF _)) = True
isF (E(FF _)) = True
isF _ = False

isG :: Formula -> Bool
isG (A(W _ F)) = True
isG (E(W _ F)) = True
isG (A(G _)) = True
isG (E(G _)) = True
isG _ = False

isGF :: Formula -> Bool
isGF f = if (isG f) then
			let f_subs = break_rule (chopG f) in
				L.or $ L.map (L.any isF) f_subs
		 else False

isFG :: Formula -> Bool
isFG f = if (isF f) then
			let f_subs = break_rule (chopF f) in
				L.or $ L.map (L.any isG) f_subs
		 else False

isProp :: Formula -> Bool
isProp (Prop _) = True
isProp _ = False

isNegLiteral :: Formula -> Bool
isNegLiteral (Not f) = isProp f
isNegLiteral _ = False

isLiteral :: Formula -> Bool
isLiteral f = (isProp f) || (isNegLiteral f)

isNLit = isNegLiteral

isPLit = isProp

isTrue :: Formula -> Bool
isTrue T = True
isTrue _ = False

isFalse :: Formula -> Bool
isFalse F = True
isFalse _ = False

chopEX :: Formula -> Formula
chopEX (E (X f)) = f
chopEX f = f

chopAX :: Formula -> Formula
chopAX (A (X f)) = f
chopAX f = f 

chopF :: Formula -> Formula
chopF (A(U T f)) = f
chopF (E(U T f)) = f
chopF (A(FF f)) = f
chopF (E(FF f)) = f

chopG :: Formula -> Formula
chopG (A(W f F)) = f
chopG (E(W f F)) = f
chopG (A(G f)) = f
chopG (E(G f)) = f




elementary :: Formula -> Bool
elementary (Not f) = elementary f
elementary (E (X _)) = True
elementary (A (X _)) = True
elementary (Prop _) = True
elementary Norm = True
elementary T = True
elementary F = True
elementary _ = False
--elementary P (X _) = True
--elementary O (X _) = True

isAlpha :: Formula -> Bool
isAlpha f = if elementary f then 
				False 
			else 
				1 == (length $ break_rule f) 

isBeta :: Formula -> Bool
isBeta f = if elementary f then 
				False 
			else 
				1 < (length $ break_rule f)  




break :: Formula -> Set (Set Formula)
break f = S.fromList (map S.fromList (break_rule f))

break_rule :: Formula -> [[Formula]]
-- Propositional
break_rule (Prop p)		= 	[[(Prop p)]]
break_rule (Or p q)		=	[[p],[q]]
break_rule (And p q)	= 	[[p,q]]
break_rule (Not p)		=	break_rule (negate p)
break_rule (If p q)		=	[[negate p],[q]]
break_rule (Iff p q)	=	[[negate p, negate q],[p,q]]
-- All
break_rule (A (X p))	= 	L.map (L.map (\f -> A (X f))) (break_rule p)
break_rule (A (U p q))	=	[[q],[p, A (X (A (U p q)))]]
break_rule (A (W p q))	=	[[q],[p, A (X (A (W p q)))]]
break_rule (A (G p))	=	[[p, A (X (A (G p)))]]
break_rule (A (FF p))	=	[[p], [A (X (A (FF p)))]]

-- Exists
break_rule (E (U p q))	=	[[q],[p, E (X (E (U p q)))]]
break_rule (E (W p q))	=	[[q],[p, E (X (E (W p q)))]]
break_rule (E (G p))	=	[[p, E (X (E (G p)))]]
break_rule (E (FF p))	=	[[p], [E (X (E (FF p)))]]

-- Obligation
break_rule (O (U p q))	=	[[Norm, q],[Norm, p, O (X (O (U p q)))]]
break_rule (O (W p q))	=	[[Norm, q],[Norm, p, O (X (O (W p q)))]]
break_rule (O (X p))	=	[[A(X (Or (Not Norm) p))]]
-- Permission
break_rule (P (U p q))	=	[[Norm, q],[Norm, p, P (X (P (U p q)))]]
break_rule (P (W p q))	=	[[Norm, q],[Norm, p, P (X (P (W p q)))]]
break_rule (P (X p))	=	[[E(X (And Norm p))]]

break_rule f 			=  error ("ERROR break_rule: " ++ (show f))



negate :: Formula -> Formula
-- Propositional
negate (Not f) 		= 	f
negate (Or p q)		=	And (negate p) (negate q)
negate (And p q)	= 	Or (negate p) (negate q)
negate (If p q)		=	And p (negate q)
negate (Iff p q)	=	Or (And (negate p) q) (And p (negate q))
negate (Prop p)		=	Not (Prop p)
negate Norm			=	Not Norm
negate T 			=	F
negate F 			=	T
-- All
negate (A (X p))	=	E (X (negate p))
negate (A (U p q))	=	E (W (negate q) (And (negate p) (negate q)))
negate (A (W p q))	=	E (U (negate q) (And (negate p) (negate q)))
negate (A (G p))	=	E (FF (negate p))
negate (A (FF p))	=	E (G (negate p))
-- Exists
negate (E (X p))	=	A (X (negate p))
negate (E (U p q))	=	A (W (negate q) (And (negate p) (negate q)))
negate (E (W p q))	=	A (U (negate q) (And (negate p) (negate q)))
negate (E (G p))	=	A (FF (negate p))
negate (E (FF p))	=	A (G (negate p))
-- Obligation
negate (O (U p q))	=	P (W (negate q) (And (negate p) (negate q)))
negate (O (W p q))	=	P (U (negate q) (And (negate p) (negate q)))
negate (O (X p))	=	P (X (negate p))
-- Permission
negate (P (U p q))	=	O (W (negate q) (And (negate p) (negate q)))
negate (P (W p q))	=	O (U (negate q) (And (negate p) (negate q)))
negate (P (X p))	=	O (X (negate p))


-- Branching rank: determines how many branches are introduced by the formula			
brrk :: Formula -> Int
brrk (Or p q)		=	brrk p + brrk q
brrk (And p q)		= 	brrk p * brrk q	
brrk (If p q)		=	brrk p + brrk q
brrk (Iff p q)	=	2 * (brrk p + brrk q)
brrk (Prop p)		=	1
brrk Norm			=	1
brrk T 			=	1
brrk F 			=	0
-- we assume NNF
brrk (Not f) 		= 	brrk f
-- All
brrk (A (X p))	=	1
brrk (A (U p q))	=	brrk p + brrk q
brrk (A (W p q))	=	brrk p + brrk q
-- Exists
brrk (E (X p))	=	1
brrk (E (U p q))	=	brrk p + brrk q
brrk (E (W p q))	=	brrk p + brrk q
-- Obligation
brrk (O (U p q))	=	brrk p + brrk q
brrk (O (W p q))	=	brrk p + brrk q
brrk (O (X p))	=	1
-- Permission
brrk (P (U p q))	=	brrk p + brrk q
brrk (P (W p q))	=	brrk p + brrk q
brrk (P (X p))	=	1



inconsistent :: Set Formula -> Bool
inconsistent s | (S.member F s) = True
inconsistent s | (S.member Norm s && S.member (Not Norm) s) = True
inconsistent s = (S.member F s) || (not $ S.null $ S.intersection pos (S.map chopNeg neg))
					where
						pos = S.filter isProp s
						neg = S.filter isNegLiteral s
						chopNeg = \f -> case f of
											(Not x) -> x
											_ -> f


{-
closure :: Set Formula -> Set (Set Formula)
closure s = let r1 = S.filter (not . inconsistent) (closure_impl s) in
				S.fromList (pick_one_of_each (S.toList r1) [])

pick_one_of_each :: [Set Formula] -> [Set Formula] -> [Set Formula]
pick_one_of_each [] r = r
pick_one_of_each (s:xs) r = if (any (\x -> filter_elem x == filter_elem s) r) then
								pick_one_of_each xs r
							else
								pick_one_of_each xs (s:r)	

	where filter_elem = S.filter $ elementary



closure_impl :: Set Formula -> Set (Set Formula)
closure_impl s =  case S.toList (S.filter (not . elementary) s) of 
				(f:fs) 	-> let sminf = S.delete f s in 
								let subcalls = S.map (sminf `S.union`) (break f) in
				 					let subresults = S.fold S.union S.empty (S.map closure subcalls) in
				 						S.map (f `S.insert`) subresults
				[] 	-> 	S.singleton s



-}


