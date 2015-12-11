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

import Data.Maybe        (isJust, fromJust, isJust, fromMaybe)

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
--potential_conflicts :: Set Formula -> Tableaux -> Tableaux -> Set Formula
--potential_conflicts spec t t2 = 
potential_conflicts = \spec -> \t -> \t2 -> do {
		reach <- return $ S.filter Dctl.isF spec;
		putStrLn ("Computing REACH conflicts ...");
		reach_conflicts <- return $ compute_reach_conflicts t reach;
		putStrLn (show reach_conflicts);

		progress <- return $ S.filter isGF spec;
		putStrLn ("Computing PROGRESS conflicts ...");
		progress_conflicts <- return $ compute_progress_conflicts t progress;
		putStrLn (show progress_conflicts);

		if spec == S.union reach progress then
				return (S.union reach_conflicts progress_conflicts)
		else
			do{
				putStrLn ("Computing SAFETY conflicts ...");
				safety_conflicts <- return $ compute_safety_conflicts t t2;
				putStrLn (show safety_conflicts);
				return (S.union (S.union reach_conflicts progress_conflicts) safety_conflicts)
		}
}
	{-
	let reach = S.filter Dctl.isF spec in
							 		let reach_conflicts = compute_reach_conflicts t reach in
							 --	let progress  = S.filter Dctl.isGF spec in
							 --	let progress_conflicts = compute_progress_conflicts t progress in
							 		if spec == reach then
							 			reach_conflicts
							 		else
							 			let safety_conflicts = compute_safety_conflicts t t2 in
							 				S.union safety_conflicts reach_conflicts
	-}		  

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


compute_safety_conflicts :: Tableaux ->  Tableaux -> Set Formula
compute_safety_conflicts t t2 = let frontier = (nodes t) S.\\ (nodes t2) in
									let forms = compute_conditions t frontier (S.singleton (root t)) [] (root t) in
										S.map make_safety_conflicts forms


compute_reach_conflicts :: Tableaux -> Set Formula -> Set Formula
compute_reach_conflicts t reach = let t' = refine_tableaux_for_reach t in
									let tmap = \g -> tagmap t' g  in
										let frontier = \g -> S.filter (\n -> (fromJust (M.lookup n (tmap g))) == pinf) (nodes t') in
											let reach_conflict = \g -> compute_conditions t' (frontier g) (S.singleton (root t')) [] (root t') in
												let reach_forms = \g -> S.map (make_reach_conflicts (chopF g)) (reach_conflict g) in
												S.unions $ S.toList $ S.map (\g -> reach_forms g) reach

refine_tableaux_for_reach :: Tableaux -> Tableaux
refine_tableaux_for_reach t = let t' = (delete_or . delete_unreachable . delete_inconsistent) t in
								if t' == t then t else refine_tableaux_for_reach t'



compute_progress_conflicts :: Tableaux -> Set Formula -> Set Formula
compute_progress_conflicts t pr = let f_subs = \f -> S.unions $ S.toList $ Dctl.break (chopG f) in
								let evs = \f -> S.filter isF (f_subs f) in
								let progress = S.unions $ S.toList $ S.map evs pr in 
									let t' = refine_tableaux_for_reach t in
										let tmap = \g -> tagmap t' g  in
										let frontier = \g -> S.filter (\n -> (fromJust (M.lookup n (tmap g))) == pinf) (nodes t') in
											let progress_conflict = \g -> compute_conditions t' (frontier g) (S.singleton (root t')) [] (root t') in
												let progress_forms = \g -> S.map make_safety_conflicts (progress_conflict g) in
													(trace ("progress evs: " ++ show progress))
													S.unions $ S.toList $ S.map (\g -> progress_forms g) progress

--compute_conditions tableaux frontier visited level_path current
-- tableaux generated from the specification.
-- frontier: portion of the tableaux we should avoid reaching.
-- visited: all nodes already visited
-- level_path: path from the root to the current node
-- current: current OR-node from which we are going to expand
compute_conditions :: Tableaux -> Set Node -> Set Node -> [Formula] -> Node -> Set Formula
compute_conditions t frontier vs lp c = let and_succs = succesors t c in
								--OR-nodes successors from and_succs
								let or_succs = S.unions $ S.toList (S.map (succesors t) and_succs) in
									--vs' increment visited nodes 
									let vs' = S.union vs (S.union and_succs or_succs) in
										--compute potential conflicts: path conditions to reach inconsistent nodes.
										--let incons_paths = S.map (branch_condition t c) and_succs in
										--let incons_form = Dctl.negate $ make_or (S.toList incons_paths) in
										--let local_conflict = S.singleton $ buildPathFormula (lp ++ [incons_form]) in
										let cons_and_succs = and_succs S.\\ frontier in
											let local_conflict = condition_to_frontier t lp cons_and_succs  in
												--no more nodes to be expanded
												if (vs'== (nodes t)) then
													local_conflict
												else
													--compute successors OR nodes, different from already visited nodes.
													let cons_OR_succs = (S.unions (S.toList (S.map (succesors t) cons_and_succs) )) S.\\ vs in
														--filter consistent AND nodes that has at least one successor different from OR-node c.
														--let filter_and_nodes = \s -> S.intersection and_succs (predecesors t s) in 
														let filter_and_nodes = \s -> (S.intersection cons_and_succs (predecesors t s)) in 
															--branch condition to each consistent successor. Filter inconsistent branches.
															let in_path = \s -> S.map (branch_condition t) (filter_and_nodes s) in
															let out_path = \s -> S.map (branch_condition t) (cons_and_succs S.\\ (filter_and_nodes s)) in
																--reduce formulas removing irrelevant literals. 	
																let in_form = \s -> make_or $ S.toList (in_path s) in
																let out_form = \s -> Dctl.negate $ make_or $ S.toList (out_path s) in
																let cons_forms = \s -> And (in_form s) (out_form s) in
																	--compute common path to reach these nodes to extend the level path.
																	let common_cons_path = \s -> lp ++ [cons_forms s] in
																		--compute next level conflicts
																		let next_level_conflicts = S.map (\s -> compute_conditions t frontier vs' (common_cons_path s) s) cons_OR_succs in
																			--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
																			if (S.null local_conflict) then
																				S.unions $ (S.toList next_level_conflicts)
																			else
																				S.unions $ [local_conflict] ++ (S.toList next_level_conflicts)


condition_to_frontier :: Tableaux -> [Formula] -> Set Node -> Set Formula
condition_to_frontier t lp conflict_nodes = if S.null conflict_nodes then 
											S.empty
										else
											let incons_paths = S.map (branch_condition t) conflict_nodes in
												let incons_form = Dctl.negate $ make_or (S.toList incons_paths) in
													S.singleton $ buildPathFormula (lp ++ [incons_form])
														

--branch condition in one step
branch_condition :: Tableaux -> Node -> Formula
branch_condition t n' = make_and $ S.toList $ S.filter isLiteral (formulas n')
						
make_safety_conflicts :: Formula -> Formula
make_safety_conflicts f = E (U T f)

make_reach_conflicts :: Formula -> Formula -> Formula
make_reach_conflicts f g = A (W (Not f) g) 

buildPathFormula :: [Formula] -> Formula
buildPathFormula [] = T
buildPathFormula [x] = B.reduce_formula x
buildPathFormula (x:y:xs) = And (B.reduce_formula x) (E (X (buildPathFormula (y:xs))))


