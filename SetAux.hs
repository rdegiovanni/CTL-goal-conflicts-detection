module SetAux where

import qualified Data.Set as S
import Data.Set (Set)


infixl 6 + 
infixl 7 <+ 
infixl 7 <\\

-- Useful renames

(+) :: Ord a => Set a -> Set a -> Set a
(+) = S.union

(<+) :: Ord a => Set a -> a -> Set a
(<+) = flip S.insert

(<\\) :: Ord a => Set a -> a -> Set a
(<\\) = flip S.delete


-- other functions

pick :: Set a -> Maybe a
pick s = case S.toList s of
			[] -> Nothing
			x:_ -> Just x 

some :: Ord a => (a -> Bool) -> Set a -> Bool
some p s = S.fold (||) False (S.map p s)

all :: Ord a => (a -> Bool) -> Set a -> Bool
all p s = S.fold (&&) True (S.map p s)


