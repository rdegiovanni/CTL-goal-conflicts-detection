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
conflicts :: Tableaux -> Set Formula
conflicts t = if S.null (inconsistent_frontier t) then 
			  	compute_conflicts t (S.singleton (root t)) [] (root t)
			  else
			  	total_conflicts t

total_conflicts :: Tableaux -> Set Formula
total_conflicts t = let candidate_nodes = S.filter isAnd (last_inconsistent_nodes t) in
					--(trace ("candidate_nodes = " ++ show (S.toList candidate_nodes)))
					let candidate_conflicts = S.map (common_path_to t) candidate_nodes in
					--(trace ("candidate_nodes = " ++ show candidate_nodes)) 
						S.map make_and candidate_conflicts


inconsistent_frontier :: Tableaux -> Set Node
inconsistent_frontier t = (last_inconsistent_nodes t)

-- last nodes (AND , OR) in the frontier with all inconsistent successors
last_inconsistent_nodes :: Tableaux -> Set Node
last_inconsistent_nodes t = let inc_nodes = S.filter inconsistent_node (nodes t) in
								--(trace ("inc_nodes = " ++ show (S.toList inc_nodes))) 
								last_inconsistent_nodes_aux t inc_nodes


last_inconsistent_nodes_aux :: Tableaux -> Set Node -> Set Node
last_inconsistent_nodes_aux t visited = let not_visited = S.difference (nodes t) visited  in
											--(trace ("not_visited = " ++ show (S.size not_visited)))
											-- nodes with all sons inconsistent
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

make_safety_conflicts :: Set Formula -> Set Formula
make_safety_conflicts c = let no_empty_forms = S.filter (\f -> not $ isTrue f) c in
							S.map (\f -> A (FF f)) no_empty_forms


--compute_conflicts visited level_path current
-- visited: all nodes already visited
-- level_path: path from the root to the current node
-- current: current OR-node from which we are going to expand
compute_conflicts :: Tableaux -> Set Node -> [Formula] -> Node -> Set Formula
compute_conflicts t vs lp c = let and_succs = succesors t c in
								--OR-nodes successors from and_succs
								let or_succs = S.unions $ S.toList (S.map (succesors t) and_succs) in
									--inconsistent AND nodes at current level,
									let incons_lc = S.filter inconsistent_node and_succs in
										--vs' increment visited nodes 
										let vs' = S.union vs (S.union and_succs or_succs) in
											--consistent AND nodes at current level.
											let cons_lc = and_succs S.\\ incons_lc in
												--compute potential conflicts: path conditions to reach inconsistent nodes.
												let incons_paths = S.filter (\fs -> not $ inconsistent (S.fromList fs)) $ S.map (branch_condition t c) incons_lc in
												let reduced_incons_paths = S.toList $ S.map make_and (remove_inconsistencies incons_paths) in
												let one_conflict = S.singleton $ buildPathFormula (lp ++ [make_or reduced_incons_paths]) in
												--no more nodes to be expanded
												if (vs'== (nodes t) || (S.null cons_lc) ) then
													one_conflict
												else
													--compute successors OR nodes, different from already visited nodes.
													let cons_OR_succs = (S.unions (S.toList (S.map (succesors t) cons_lc) )) S.\\ vs in
														--filter consistent AND nodes that has at least one successor different from OR-node c.
														let cons_lc_with_succs = S.filter (\cn -> not $ S.null (S.intersection cons_OR_succs (succesors t cn)) ) cons_lc in 
															--branch condition to each consistent successor. Filter inconsistent branches.
															let cons_path = S.map (\n -> L.union (S.toList $ (S.filter isLiteral (formulas n))) (branch_condition t c n)) cons_lc_with_succs in
																--reduce formulas removing irrelevant literals. 
																let reduced_cons_paths = remove_inconsistencies $ S.filter (\fs -> not $ inconsistent (S.fromList fs)) cons_path in
																	let cons_forms = make_or $ S.toList (S.map make_and reduced_cons_paths) in
																		--compute common path to reach these nodes to extend the level path.
																		let common_cons_path = lp ++ [cons_forms] in
																			--compute next level conflicts
																			let next_level_conflicts = S.map (compute_conflicts t vs' common_cons_path) cons_OR_succs in
																				--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
																				if (S.null one_conflict) then
																					S.unions $ (S.toList next_level_conflicts)
																				else
																					S.unions $ [one_conflict] ++ (S.toList next_level_conflicts)


-- formulas_to_inconsistencies 
-- computes CTL formulas that lead us to inconsistent nodes.
formulas_to_inconsistencies :: Tableaux -> Set Formula
formulas_to_inconsistencies t = let xss = compute_inconsistent_paths t (S.singleton (root t)) [] (root t) in
										S.fromList $ L.map (buildPathFormula) xss
														
-- compute_inconsistent_paths tableaux
-- computes all paths to inconsistent nodes, applying a BFS-like algorithm.
compute_inconsistent_paths :: Tableaux -> Set Node -> [Formula] -> Node -> [[Formula]]
compute_inconsistent_paths t vs lp c = let and_succs = succesors t c in
								--OR-nodes successors from and_succs
								let or_succs = S.unions $ S.toList (S.map (succesors t) and_succs) in
									--inconsistent AND nodes at current level,
									let incons_lc = S.filter inconsistent_node and_succs in
										--vs' increment visited nodes 
										let vs' = S.union vs (S.union and_succs or_succs) in
											--no more nodes to be expanded
											if (vs'== (nodes t)) then
												--compute potential conflicts: path conditions to reach inconsistent nodes.
												let incons_paths = (S.map (branch_condition t c) incons_lc) in
													let reduced_incons_paths = remove_inconsistencies incons_paths in
														S.toList $ S.map (\f ->  (lp ++ [make_and f]) ) reduced_incons_paths
											else
												--consistent AND nodes at current level.
												let cons_lc = and_succs S.\\ incons_lc in
													--compute successors OR nodes, different from current c.
													let cons_OR_succs = (S.unions (S.toList (S.map (succesors t) cons_lc) )) S.\\ (S.singleton c) in
														--filter consistent AND nodes that has at least one successor different from OR-node c.
														let cons_lc_with_succs = S.filter (\cn -> not $ S.null (S.intersection cons_OR_succs (succesors t cn)) ) cons_lc in 
															--branch condition to each consistent successor.
															let cons_path = S.filter (\fs -> not $ inconsistent (S.fromList fs)) (S.map (branch_condition t c) cons_lc_with_succs) in
																--reduce formulas removing irrelevant literals. 
																let reduced_cons_paths = remove_inconsistencies cons_path in
																	--compute common path to reach these nodes to extend the level path.
																	let common_cons_path = S.toList $ S.map (\f ->lp ++[make_and f]) reduced_cons_paths in
																		--compute next level conflicts
																		let next_level_conflicts = [xs | p <- common_cons_path, or_n <- S.toList$cons_OR_succs, xs <- (compute_inconsistent_paths t vs' p or_n)] in
																			--S.map (\or_n -> S.map (\p -> compute_conflicts t vs' p or_n) common_cons_path) cons_OR_succs in
																			--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
																			--S.unions next_level_conflicts
																			next_level_conflicts



buildPathFormula :: [Formula] -> Formula
buildPathFormula [] = T
buildPathFormula [x] = x
buildPathFormula (x:y:xs) = And x (E (X (buildPathFormula (y:xs))))

remove_inconsistencies :: Set [Formula] -> Set [Formula]
remove_inconsistencies forms =	let cons_forms = S.filter (\fs -> not $ inconsistent (S.fromList fs)) forms in
									let all_forms = (foldl L.union []) (S.toList cons_forms) in
										let reduced_cons_forms = S.map (\lf -> L.filter (\x -> L.notElem (Dctl.negate x) all_forms) lf) cons_forms in
											--(trace ("reduced_cons_forms = " ++ show reduced_cons_forms)) 
											S.filter (\l -> not $ L.null l) reduced_cons_forms
											--let no_empty_forms =  forms in


{-generate_one_conflict :: [[Formula]] -> Formula
generate_one_conflict xss = let state_list = L.transpose xss in
								let state_forms = L.map make_or (L.map L.nub state_list) in
									buildPathFormula state_forms
-}
