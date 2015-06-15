module Dctl where

import Set	

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
			deriving (Eq, Show)

data PFormula 	= 	U Formula Formula
				|	W Formula Formula
				|	X Formula
				deriving (Eq, Show)




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

deco :: Formula -> Set (Set Formula)
deco _ = 

