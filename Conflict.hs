module Conflict where

import Parser
import Dctl
import Closure
import Tableaux as T
import BDD as B

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
										let incons_paths = S.map (branch_condition t c) and_succs in
											let incons_form = Dctl.negate $ make_or (S.toList incons_paths) in
												let local_conflict = S.singleton $ buildPathFormula (lp ++ [incons_form]) in
												--no more nodes to be expanded
												if (vs'== (nodes t)) then
													local_conflict
												else
													--compute successors OR nodes, different from already visited nodes.
													let cons_OR_succs = (S.unions (S.toList (S.map (succesors t) and_succs) )) S.\\ vs in
														--filter consistent AND nodes that has at least one successor different from OR-node c.
														--let filter_and_nodes = \s -> S.intersection and_succs (predecesors t s) in 
														let filter_and_nodes = \s -> (S.intersection and_succs (predecesors t s)) in 
															--branch condition to each consistent successor. Filter inconsistent branches.
															let in_path = \s -> S.map (branch_condition t c) (filter_and_nodes s) in
															let out_path = \s -> S.map (branch_condition t c) (and_succs S.\\ (filter_and_nodes s)) in
																--reduce formulas removing irrelevant literals. 	
																let in_form = \s -> make_or $ S.toList (in_path s) in
																let out_form = \s -> Dctl.negate $ make_or $ S.toList (out_path s) in
																let cons_forms = \s -> And (in_form s) (out_form s) in
																	--compute common path to reach these nodes to extend the level path.
																	let common_cons_path = \s -> lp ++ [cons_forms s] in
																		--compute next level conflicts
																		let next_level_conflicts = S.map (\s -> compute_conflicts t vs' (common_cons_path s) s) cons_OR_succs in
																			--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
																			if (S.null local_conflict) then
																				S.unions $ (S.toList next_level_conflicts)
																			else
																				S.unions $ [local_conflict] ++ (S.toList next_level_conflicts)


--branch condition in one step
branch_condition :: Tableaux -> Node -> Node -> Formula
branch_condition t n n' = 	--let l = (label t) M.! (n,n') in
							--if (l == Dctl.F) then
								make_and $ S.toList $ S.filter isLiteral (formulas n')
							--else
							--	l

make_safety_conflicts :: Set Formula -> Set Formula
make_safety_conflicts c = let no_empty_forms = S.filter (\f -> not $ isTrue f) c in
							S.map (\f -> E (U T f)) no_empty_forms



buildPathFormula :: [Formula] -> Formula
buildPathFormula [] = T
buildPathFormula [x] = B.reduce_formula x
buildPathFormula (x:y:xs) = And (B.reduce_formula x) (E (X (buildPathFormula (y:xs))))


