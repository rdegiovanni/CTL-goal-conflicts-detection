module Closure (
	closure,
	old_closure
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
				consistent :: Bool,
				label :: [Formula]
			} deriving (Show, Eq)

empty :: CLSet
empty = CLSet S.empty S.empty S.empty S.empty S.empty True []

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
s@(CLSet a b u p n c l) +++ f@(Prop _) 			= let c' = c && (not $ S.member f n) in
													let res = CLSet a b (f + u) (f + p) n c' l in
														if repOK res then res else error "repOk violation in +++"

s@(CLSet a b u p n c l) +++ f@(Not f'@(Prop _)) = let c' = c && (not $ S.member f' p) in
													let res = CLSet a b (f + u) p (f' + n) c' l in
														if repOK res then res else error "repOk violation in +++"


s@(CLSet a b u p n c l) +++ F  = CLSet a b (F + u) p n False l

s@(CLSet a b u p n c l) +++ f | elementary f 	= CLSet a b (f + u) p n c l

-- case And _ _
s@(CLSet a b u p n c l) +++ f | splits  		= CLSet a (f + b) (f + u) p n c l
	where splits = 1 < (length $ break_rule f)	

s@(CLSet a b u p n c l) +++ f | otherwise		= CLSet (f + a) b (f + u) p n c l




process :: CLSet -> [CLSet]
process s@(CLSet a b u p n True l) | not $ S.null a = map process_alt alts

		where
			process_alt = \alt -> foldl (+++) (CLSet (a - fa) b u p n True l) alt
			alts = break_rule fa
			fa = fromJust $ S.pick a

process s@(CLSet a b u p n True l) | not $ S.null b = map process_alt alts

		where
			process_alt = \alt -> foldl (+++) (CLSet a (b - fb) u p n True (l++alt)) alt
			alts = break_rule fb
			fb = fromJust $ S.pick b

process s@(CLSet a b u p n True l) | otherwise = error "CLSet process: error in pattern matching"
process s@(CLSet a b u p n False l) = [] --(trace ("s = " ++ (show s))) error "CLSet process: can't process inconsistent set"





cl_impl :: [CLSet] -> [CLSet] -> [CLSet]
cl_impl [] ys = ys
cl_impl (x:xs) ys | closed x = cl_impl xs (x:ys)
cl_impl (x:xs) ys | not $ closed x = cl_impl ((process x) ++ xs) ys

-- for debuging
chcheck :: [CLSet] -> [CLSet]
chcheck ys = case ccc of
				(Just s) -> error ("XXX : " ++ show s)
				Nothing -> ys

	where
		ccc = find (not . repOK) ys

repOK :: CLSet -> Bool
repOK s@(CLSet _ _ _ _ _ False _) = (inconsistent . formulas) s == True
repOK s@(CLSet _ _ _ _ _ True _) = (inconsistent . formulas) s == False

-- for debbuging
dup :: [CLSet] -> Bool
dup xs = null [(i, j) | i <- [0 .. length xs P.- 1], j <- [0 .. length xs P.- 1], xs!!i == xs!!j && i /= j] 


closure :: Set Formula -> Set (Set Formula, [Formula])
closure s = S.fromList $ map (\c -> (formulas c, label c)) (cl_impl [make_cls s] [])		
	--where
	--	cost = (show $ foldl ((*)) 1 x) ++ " - " ++ (show x) 
	--	x = map brrk (S.toList s)




pick_one_of_each :: [Set Formula] -> [Set Formula] -> [Set Formula]
pick_one_of_each [] r = r
pick_one_of_each (s:xs) r = if (any (\x -> filter_elem x == filter_elem s) r) then
								pick_one_of_each xs r
							else
								pick_one_of_each xs (s:r)	

	where filter_elem = S.filter $ elementary







-- Original Version

old_closure :: Set Formula -> Set (Set Formula)
old_closure s =  case S.toList (S.filter (not . elementary) s) of 
				(f:fs) 	-> let sminf = S.delete f s in 
								let subcalls = S.map (sminf `S.union`) (Dctl.break f) in
				 					let subresults = S.fold S.union S.empty (S.map old_closure subcalls) in
				 						S.map (f `S.insert`) subresults
				[] 	-> 	S.singleton s








				

