module Conflict where

import Parser
import Dctl
import Closure
import Tableaux as T

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import qualified Relation as R
import Relation (Relation)

import qualified Data.Map as M
import Data.Map (Map)

import Data.List	(sortBy, (\\))
import Data.List as L
import Data.Ord

import Debug.Trace

--Compute conflicts
conflicts :: Tableaux -> Set [Formula]
conflicts t = let candidate_nodes = S.filter isAnd (last_inconsistent_nodes t) in
					--(trace ("candidate_nodes = " ++ show (S.toList candidate_nodes)))
					let candidate_conflicts = S.map (common_path_to t) candidate_nodes in
					(trace ("candidate_nodes = " ++ show candidate_nodes)) 
						candidate_conflicts


--return the inconsistent OR nodes: all sons are inconsistent
{-inconsistent_OR_nodes :: Tableaux -> Set Node
inconsistent_OR_nodes t = let orNodes = S.filter isOr (nodes t) in
							let inconsistent_orNodes = S.filter (\n -> S.all (inconsistent_node) (succesors t n)) orNodes in
								inconsistent_orNodes
-}

-- last nodes (AND , OR) in the frontier with all inconsistent successors
last_inconsistent_nodes :: Tableaux -> Set Node
last_inconsistent_nodes t = let inc_nodes = S.filter inconsistent_node (nodes t) in
								--(trace ("inc_nodes = " ++ show (S.toList inc_nodes))) 
								last_inconsistent_nodes_aux t inc_nodes


last_inconsistent_nodes_aux :: Tableaux -> Set Node -> Set Node
last_inconsistent_nodes_aux t visited = let not_visited = S.difference (nodes t) visited  in
											--(trace ("not_visited = " ++ show (S.size not_visited)))
											-- nodes with all sons inconsistents
											let candidate_inconsistents =  S.filter (\n -> S.all (\e -> S.member e visited) (succesors t n)) not_visited in
												--(trace ("candidate_inconsistents = " ++ show (S.size candidate_inconsistents)))
												if (S.null candidate_inconsistents) then
													S.empty
												else
													let cand_inc_parents =  S.unions (S.toList (S.map (succesors t) candidate_inconsistents)) in
														let visited' = S.union visited (S.union candidate_inconsistents cand_inc_parents) in
															let next_inc = last_inconsistent_nodes_aux t visited' in
																if (S.null next_inc) then
																	candidate_inconsistents
																else
																	next_inc

common_path :: Tableaux -> Set Node -> [Formula]
common_path t ns = let ns_paths = S.map (common_path_to t) ns in
						--(trace ("ns_paths = " ++ show ns_paths)) 
						L.nub $ concat (S.toList ns_paths) --unions
						--multiple_intersect (S.toList ns_paths)

common_path_to :: Tableaux -> Node -> [Formula]
common_path_to t n = let n_parents = predecesors t n in
						let n_props = S.toList $ S.filter isLiteral (formulas n) in
							let n_parent_paths = S.map (\p -> S.fromList (n_props ++ (branch_condition t p n)) ) n_parents in 
							--(trace ("n_props = " ++ show n_props))
							--(trace ("n_parents = " ++ show n_parents))
							--(trace ("n_parent_paths = " ++ show n_parent_paths))
								S.toList (S.unions (S.toList n_parent_paths))


multiple_intersect :: [[Formula]] -> [Formula]
multiple_intersect [] = []
multiple_intersect [xs] = xs
multiple_intersect xss = L.intersect xs (multiple_intersect yss)
						where
							xs = head xss
							yss = tail xss


--branch condition in one step
branch_condition :: Tableaux -> Node -> Node -> [Formula]
branch_condition t n n' = (label t) M.! (n,n')


make_safety_conflicts :: Set [Formula] -> Set Formula
make_safety_conflicts c = S.map (\f -> A (FF f)) (S.map (make_safety_formula) c)

make_safety_formula :: [Formula] -> Formula
make_safety_formula [] = T
make_safety_formula [x] = x
make_safety_formula [x,y] = And x y
make_safety_formula (x:y:xs) = let f = make_safety_formula xs in
									if isTrue f then
										And x y
									else
										And x (And y f)

