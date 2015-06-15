module Set where

data (Eq e) => Set e = S [e]
		deriving (Eq,Show)

empty :: (Eq e) => Set e
empty = S []

union :: (Eq e) => Set e -> Set e -> Set e
union s1 (S (x:xs))	=	union (add s1 x) (S xs)
union s1 (S [])		=	s1

add	:: (Eq e) => Set e -> e -> Set e
add (S s1) x = if elem x s1 then (S s1) else S (s1 ++ [x])
