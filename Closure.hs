module Closure (
	closure
	) 

where

import Dctl
import Data.List 		(sortBy, find)
import Data.Ord

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import Data.Maybe        (isJust, fromJust, fromMaybe)

import Prelude hiding ((+), (-))
import qualified Prelude as P ((+), (-))

import Debug.Trace


data CLSet = CLSet {
				alpha :: Set Formula,
				beta :: Set Formula,
				used :: Set Formula,
				pvs :: Set Formula,
				nvs :: Set Formula,
				consistent :: Bool
			} deriving (Show, Eq)

empty :: CLSet
empty = CLSet S.empty S.empty S.empty S.empty S.empty True

make_cls :: Set Formula -> CLSet
make_cls s = if repOK res then res else error "repOk violation in make_cls"

	where res = S.fold (flip (+++)) empty s

formulas :: CLSet -> Set Formula
formulas s = used s

closed :: CLSet -> Bool
closed s = S.null (alpha s) && S.null (beta s)


(+) :: Ord a => a -> Set a -> Set a
(+) = S.insert

(-) :: Ord a => Set a -> a -> Set a
(-) = flip $ S.delete


(+++) :: CLSet -> Formula -> CLSet
s@(CLSet a b u p n c) +++ f@(Prop _) 			= let c' = c && (not $ S.member f n) in
													let res = CLSet a b (f + u) (f + p) n c' in
														if repOK res then res else error "repOk violation in +++"

s@(CLSet a b u p n c) +++ f@(Not f'@(Prop _)) = let c' = c && (not $ S.member f' p) in
													let res = CLSet a b (f + u) p (f' + n) c' in
														if repOK res then res else error "repOk violation in +++"


s@(CLSet a b u p n c) +++ F  = CLSet a b (F + u) p n False

s@(CLSet a b u p n c) +++ f | elementary f 	= CLSet a b (f + u) p n c

s@(CLSet a b u p n c) +++ f | splits  		= CLSet a (f + b) (f + u) p n c
	where splits = 1 < (length $ break_rule f)	

s@(CLSet a b u p n c) +++ f | otherwise		= CLSet (f + a) b (f + u) p n c




process :: CLSet -> [CLSet]
process s@(CLSet a b u p n True) | not $ S.null a = map process_alt alts

		where
			process_alt = \alt -> foldl (+++) (CLSet (a - fa) b u p n True) alt
			alts = break_rule fa
			fa = fromJust $ S.pick a

process s@(CLSet a b u p n True) | not $ S.null b = map process_alt alts

		where
			process_alt = \alt -> foldl (+++) (CLSet a (b - fb) u p n True) alt
			alts = break_rule fb
			fb = fromJust $ S.pick b

process s@(CLSet a b u p n True) | otherwise = error "CLSet process: error in pattern matching"
process s@(CLSet a b u p n False) = error "CLSet process: can't process inconsistent set"





cl_impl :: [CLSet] -> [CLSet] -> [CLSet]
cl_impl [] ys = {-trace ("0, " ++ (show $ length ys) ++ " - closed") chcheck-} ys
cl_impl (x:xs) ys | closed x = {-trace (show (dup $ x:xs ++ ys) ++ " --- " ++ (show $ length xs) ++ ", " ++ (show $ length ys) ++ " - closed") $ -} cl_impl xs (x:ys)
cl_impl (x:xs) ys | not $ closed x = {-trace (show (dup $ x:xs ++ ys) ++ " --- " ++ (show $ length xs) ++ ", " ++ (show $ length ys) ++ " - open") $ -} cl_impl ((filter consistent (process x)) ++ xs) ys

-- for debuging
chcheck :: [CLSet] -> [CLSet]
chcheck ys = case ccc of
				(Just s) -> error ("XXX : " ++ show s)
				Nothing -> ys

	where
		ccc = find (not . repOK) ys

repOK :: CLSet -> Bool
repOK s@(CLSet _ _ _ _ _ False) = (inconsistent . formulas) s == True
repOK s@(CLSet _ _ _ _ _ True) = (inconsistent . formulas) s == False

-- for debbuging
dup :: [CLSet] -> Bool
dup xs = null [(i, j) | i <- [0 .. length xs P.- 1], j <- [0 .. length xs P.- 1], xs!!i == xs!!j && i /= j] 


closure :: Set Formula -> Set (Set Formula)
closure s = S.fromList $ map formulas (cl_impl (filter consistent [make_cls s]) [])		
	where
		cost = (show $ foldl ((*)) 1 x) ++ " - " ++ (show x) 
		x = map brrk (S.toList s)




pick_one_of_each :: [Set Formula] -> [Set Formula] -> [Set Formula]
pick_one_of_each [] r = r
pick_one_of_each (s:xs) r = if (any (\x -> filter_elem x == filter_elem s) r) then
								pick_one_of_each xs r
							else
								pick_one_of_each xs (s:r)	

	where filter_elem = S.filter $ elementary











				

