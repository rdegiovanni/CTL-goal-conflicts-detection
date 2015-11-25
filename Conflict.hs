module Conflict where

import Parser
import Dctl
import Closure
import Tableaux as T
--import BDD

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

-- Compute WEAK conflicts
-- spec: all formulas that conform the specification.
-- potential_conflicts: potential conflicts computed.
-- returns the seat of portential conflicts that meet with the definition of weak conflicts.
weak_conflicts :: Set Formula -> Set Formula -> Set Formula
weak_conflicts spec pot_conflicts = let incons_conflicts = S.filter (logical_inconsistency spec) pot_conflicts in
										let min_conflicts = S.filter (minimality spec) incons_conflicts in
											min_conflicts

-- check logical inconsistency 
logical_inconsistency :: Set Formula -> Formula -> Bool
logical_inconsistency spec pc = let t = do_tableaux $ make_tableaux (spec S.<+ pc) in
									let t2 = refine_tableaux t in
										S.null (nodes t2)
--check minimality
minimality :: Set Formula -> Formula -> Bool
minimality spec ic = let all_comb = S.map (\n -> S.delete n spec) spec in
						S.all (\comb -> not$ logical_inconsistency comb ic) all_comb

--Compute potential conflicts
potential_conflicts :: Tableaux -> Set Formula
potential_conflicts t = compute_conflicts t (S.singleton (root t)) [] (root t)
			  

--compute_conflicts visited level_path current
-- visited: all nodes already visited
-- level_path: path from the root to the current node
-- current: current OR-node from which we are going to expand
compute_conflicts :: Tableaux -> Set Node -> [Formula] -> Node -> Set Formula
compute_conflicts t vs lp c = let and_succs = succesors t c in
								--OR-nodes successors from and_succs
								let or_succs = S.unions $ S.toList (S.map (succesors t) and_succs) in
									--vs' increment visited nodes 
									let vs' = S.union vs (S.union and_succs or_succs) in
										--compute potential conflicts: path conditions to reach inconsistent nodes.
										--let incons_paths = S.map (branch_condition t c) and_succs in
										let incons_paths = S.map (\n -> S.toList $ S.filter isLiteral (formulas n)) and_succs in
											let reduced_incons_paths =  (S.map (\l -> map Dctl.negate l) incons_paths) in
												let incons_form = (trace ("reduced_incons_paths = " ++ show reduced_incons_paths)) make_and $ S.toList (S.map make_or reduced_incons_paths) in
												let one_conflict = S.singleton $ buildPathFormula (lp ++ [incons_form]) in
												--no more nodes to be expanded
												if (vs'== (nodes t)) then
													one_conflict
												else
													--compute successors OR nodes, different from already visited nodes.
													let cons_OR_succs = (S.unions (S.toList (S.map (succesors t) and_succs) )) S.\\ vs in
														--filter consistent AND nodes that has at least one successor different from OR-node c.
														let filter_and_nodes = \s -> S.intersection and_succs (predecesors t s) in 
															--branch condition to each consistent successor. Filter inconsistent branches.
															--let cons_path = S.map (branch_condition t c) cons_lc_with_succs in
															let cons_path = \s -> S.map (\n -> S.toList $ S.filter isLiteral (formulas n)) (filter_and_nodes s) in
																--reduce formulas removing irrelevant literals. 	
																let cons_forms = \s -> make_or $ S.toList ( S.map make_and (cons_path s)) in
																	--compute common path to reach these nodes to extend the level path.
																	let common_cons_path = \s -> lp ++ [cons_forms s] in
																		--compute next level conflicts
																		let next_level_conflicts = S.map (\s -> compute_conflicts t vs' (common_cons_path s) s) cons_OR_succs in
																			--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
																			if (S.null one_conflict) then
																				S.unions $ (S.toList next_level_conflicts)
																			else
																				S.unions $ [one_conflict] ++ (S.toList next_level_conflicts)


--branch condition in one step
branch_condition :: Tableaux -> Node -> Node -> [Formula]
branch_condition t n n' = (label t) M.! (n,n')

make_safety_conflicts :: Set Formula -> Set Formula
make_safety_conflicts c = let no_empty_forms = S.filter (\f -> not $ isTrue f) c in
							S.map (\f -> E (U T f)) no_empty_forms



buildPathFormula :: [Formula] -> Formula
buildPathFormula [] = T
buildPathFormula [x] = x
buildPathFormula (x:y:xs) = And x (E (X (buildPathFormula (y:xs))))




{- Auxiliary methods irrelevant for now
total_conflicts :: Tableaux -> Set Formula
total_conflicts t = let candidate_nodes = S.filter isAnd (last_inconsistent_nodes t) in
					--(trace ("candidate_nodes = " ++ show (S.toList candidate_nodes)))
					let candidate_conflicts = S.map (common_path_to t) candidate_nodes in
					--(trace ("candidate_nodes = " ++ show candidate_nodes)) 
						S.map make_and candidate_conflicts


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



generate_one_conflict :: [[Formula]] -> Formula
generate_one_conflict xss = let state_list = L.transpose xss in
								let state_forms = L.map make_or (L.map L.nub state_list) in
									buildPathFormula state_forms
-}
