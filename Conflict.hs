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
weak_conflicts :: Set Formula -> Set Formula -> Set Formula -> Bool -> Set Formula
weak_conflicts dom goals pot_conflicts cm = let spec = S.union dom goals ;
										 		incons_conflicts = S.filter (logical_inconsistency spec) pot_conflicts ;
												min_conflicts 	 = S.filter (if cm then (minimality dom goals) else (domain_consistency dom)) incons_conflicts ;
										 		no_trivials 	 = S.filter (no_trivial_BCs goals) min_conflicts
										 	in	
												no_trivials

-- check logical inconsistency 
logical_inconsistency :: Set Formula -> Formula -> Bool
logical_inconsistency spec pc = not $ isSAT (spec S.<+ pc)

--check minimality
minimality :: Set Formula -> Set Formula -> Formula -> Bool
minimality dom goals ic = 	let spec = S.union dom goals;
								all_comb = S.map (\n -> S.delete n spec) goals
								
						 	in
						 		(trace ".")
						 		S.all (\comb -> isSAT (comb S.<+ ic)) all_comb

-- check logical inconsistency 
domain_consistency :: Set Formula -> Formula -> Bool
domain_consistency dom bc = isSAT (dom S.<+ bc)

no_trivial_BCs :: Set Formula -> Formula -> Bool
no_trivial_BCs goals bc = 	let neg_goals = Dctl.negate (make_and (S.toList goals)) ;
							  	neg_bc = Dctl.negate bc
							in
								if not $ isSAT (goals S.<+ bc) then 
									isSAT (S.singleton (Dctl.And neg_goals neg_bc))
								else
									True

--Compute potential conflicts
--potential_conflicts :: Set Formula -> Tableaux -> Tableaux -> Set Formula
--potential_conflicts spec t t2 = 
potential_conflicts = \spec -> \t -> \t2 -> do {
		reach <- return $ S.filter Dctl.isF spec;
		putStrLn ("Computing REACH conflicts ...");
		reach_conflicts <- return $ compute_reach_conflicts t reach;
		print_Conflicts_info "REACH" reach_conflicts;

		response <- return $ S.filter (\f -> isGF f || isResponse f) spec;
		putStrLn ("Computing RESPONSE conflicts ...");
		response_conflicts <- return $ compute_response_conflicts t response;
		print_Conflicts_info "PROGRESS" response_conflicts;

		if spec == S.union reach response then
				return (S.union reach_conflicts response_conflicts)
		else
			do{
				putStrLn ("Computing SAFETY conflicts ...");
				safety_conflicts <- return $ compute_safety_conflicts t t2;
				print_Conflicts_info "SAFE" safety_conflicts;

				return (S.union (S.union reach_conflicts response_conflicts) safety_conflicts)
		}
}

compute_safety_conflicts :: Tableaux ->  Tableaux -> Set Formula
compute_safety_conflicts t t2 = let frontier = (nodes t) S.\\ (nodes t2) ;
									forms = compute_conditions t frontier (S.singleton (root t)) [] (root t) 
								in
									(trace ("#frontier-safe: " ++ show (S.size frontier)))
									S.map make_safety_conflicts forms


compute_reach_conflicts :: Tableaux -> Set Formula -> Set Formula
compute_reach_conflicts t reach = 	let t' = refine_tableaux_for_reach t ;
									  	tmap = \g -> tagmap t' g ;
										frontier_inf = \g -> S.filter (\n -> (fromJust (M.lookup n (tmap g))) == pinf) (nodes t') ;
										frontier = \g -> S.filter (\n -> S.member g (formulas n)) (frontier_inf g) ;
										live_frontier = \g -> S.filter (\n -> isAnd n && (fromJust (M.lookup n (tmap g))) == 0) (nodes t') ;
										reach_conflict = \g -> (trace (show g ++ " #frontier-prog: " ++ show (S.size (frontier g)) ++ " #live-frontier:" ++ show (S.size (live_frontier g)))) 
																	 compute_liveness_conditions t' (frontier g) (live_frontier g) S.empty [] (root t') ;
										reach_forms = \g -> make_reach_conflicts (make_or $ S.toList $(reach_conflict g)) 
									in
										S.map reach_forms reach

refine_tableaux_for_reach :: Tableaux -> Tableaux
refine_tableaux_for_reach t = let t' = (delete_or . delete_unreachable . delete_inconsistent) t in
								if t' == t then (trace ("#tableaux_for_reach: " ++ show (S.size (nodes t)))) t else refine_tableaux_for_reach t'


compute_response_conflicts :: Tableaux -> Set Formula -> Set Formula
compute_response_conflicts t pr =	let evs = \f -> chopProgress f ;
										response = S.map evs pr ; 
										t' = refine_tableaux_for_reach t ;
										tmap = \g -> tagmap t' g ;
										frontier_inf = \g -> S.filter (\n -> (fromJust (M.lookup n (tmap g))) == pinf) (nodes t') ;
										frontier = \g -> S.filter (\n -> S.member g (formulas n)) (frontier_inf g) ;
										live_frontier = \g -> S.filter (\n -> isAnd n && (fromJust (M.lookup n (tmap g))) == 0) (nodes t') ;
										response_conflict =  \g -> (trace (show g ++ " #frontier-prog: " ++ show (S.size (frontier g)) ++ " #live-frontier:" ++ show (S.size (live_frontier g)))) 
																	compute_liveness_conditions t' (frontier g) (live_frontier g) S.empty [] (root t') ;
										response_forms = \(If p q) -> make_response_conflicts p q (make_or $ S.toList $ (response_conflict q)) 
									in
										(trace ("response evs: " ++ show response))
										S.map response_forms response


chopProgress :: Formula -> Formula
chopProgress g = let f = chopG g in
					if isResponse g then 
						f
					else 
						If T f

--compute_conditions tableaux frontier visited level_path current
-- tableaux generated from the specification.
-- frontier: portion of the tableaux we should avoid reaching.
-- visited: all nodes already visited
-- level_path: path from the root to the current node
-- current: current OR-node from which we are going to expand
compute_conditions :: Tableaux -> Set Node -> Set Node -> [Formula] -> Node -> Set Formula
compute_conditions t frontier vs lp c = let and_succs = succesors t c ;
										--vs' increment visited nodes 
											vs' = S.union vs (S.union and_succs (S.singleton c)) ;
										--compute potential conflicts: path conditions to reach inconsistent nodes.
										--let incons_paths = S.map (branch_condition t c) and_succs in
										--let incons_form = Dctl.negate $ make_or (S.toList incons_paths) in
										--let local_conflict = S.singleton $ buildPathFormula (lp ++ [incons_form]) in
											cons_and_succs = and_succs S.\\ frontier ;
											local_conflict = condition_to_frontier t lp cons_and_succs 
										in
											--no more nodes to be expanded
											if (vs'== (nodes t)) then
												local_conflict
											else
												--OR-nodes successors from and_succs
												--or_succs = S.unions $ S.toList (S.map (succesors t) and_succs) ;
												--compute successors OR nodes, different from already visited nodes.
												let cons_OR_succs = (S.unions (S.toList (S.map (succesors t) cons_and_succs) )) S.\\ vs ;
												--filter consistent AND nodes that has at least one successor different from OR-node c.
												--let filter_and_nodes = \s -> S.intersection and_succs (predecesors t s) in 
													filter_and_nodes = \s -> (S.intersection cons_and_succs (predecesors t s)) ; 
												--branch condition to each consistent successor. Filter inconsistent branches.
													in_path = \s -> S.map (branch_condition t) (filter_and_nodes s) ;
													out_path = \s -> S.map (branch_condition t) (cons_and_succs S.\\ (filter_and_nodes s)) ;
												--reduce formulas removing irrelevant literals. 	
													in_form = \s -> make_or $ S.toList (in_path s) ;
													out_form = \s -> Dctl.negate $ make_or $ S.toList (out_path s) ;
													cons_forms = \s -> And (in_form s) (out_form s) ;
												--compute common path to reach these nodes to extend the level path.
													common_cons_path = \s -> lp ++ [cons_forms s] ;
												--compute next level conflicts
													next_level_conflicts = S.map (\s -> compute_conditions t frontier vs' (common_cons_path s) s) cons_OR_succs
												in
													--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
													if (S.null local_conflict) then
														S.unions $ (S.toList next_level_conflicts)
													else
														S.unions $ [local_conflict] ++ (S.toList next_level_conflicts)


condition_to_frontier :: Tableaux -> [Formula] -> Set Node -> Set Formula
condition_to_frontier t lp conflict_nodes = if S.null conflict_nodes then 
												S.empty
											else
												let incons_paths = S.map (branch_condition t) conflict_nodes ;
													incons_form = Dctl.negate $ make_or (S.toList incons_paths) ;
													path_form = buildPathFormula (lp ++ [incons_form])
												in
													if path_form == Dctl.F then
														S.empty
													else
														S.singleton $ path_form
														

--branch condition in one step
branch_condition :: Tableaux -> Node -> Formula
branch_condition t n' = make_and $ S.toList $ S.filter isLiteral (formulas n')
						
make_safety_conflicts :: Formula -> Formula
make_safety_conflicts f = E (U T f)

make_reach_conflicts :: Formula -> Formula
make_reach_conflicts f = (A (G f))
						--E (W (Not f) (And g (A (G (Not f))))) 
						--E (W (Not f) (And g (A (X (A (G (Not f)))))))
						--A (W (Not f) g)
make_progress_conflicts :: Formula -> Formula -> Formula
make_progress_conflicts f g = E (U T (And g (A (FF (A (G (Not f)))))))
							--E (U T (And g (A (X (A (G (Not f)))))))

make_response_conflicts :: Formula -> Formula -> Formula -> Formula
make_response_conflicts p q f = E (U T (And p (A (G f))))
							--E (U T (And g (A (X (A (G (Not f)))))))

buildPathFormula :: [Formula] -> Formula
buildPathFormula [] = T
buildPathFormula [x] = B.reduce_formula x
buildPathFormula (x:y:xs) = let x_form = (B.reduce_formula x) ;
								tail_form = buildPathFormula (y:xs)
							in
								if ((x_form == Dctl.F) || (tail_form == Dctl.F)) then
									Dctl.F
								else
									And x_form (E (X (tail_form)))


conflictsToString :: [Formula] -> [String]
conflictsToString [] = []
conflictsToString (x:xs) = (show x):(conflictsToString xs)

print_Conflicts_info = \str -> \bcs -> do {
	putStrLn ("#"++show str ++"-conflicts= " ++ show (S.size bcs) );
	bcs_str <- return $ conflictsToString (S.toList bcs);
	mapM_ putStrLn bcs_str
}



compute_liveness_conditions :: Tableaux -> Set Node -> Set Node -> Set Node -> [Formula] -> Node -> Set Formula
compute_liveness_conditions t frontier live_frontier vs lp c = let and_succs = succesors t c ;
										
										--vs' increment visited nodes 
											vs' = S.union vs (S.union and_succs (S.singleton c)) ;
										--compute potential conflicts: path conditions to reach inconsistent nodes.
										--let incons_paths = S.map (branch_condition t c) and_succs in
										--let incons_form = Dctl.negate $ make_or (S.toList incons_paths) in
										--let local_conflict = S.singleton $ buildPathFormula (lp ++ [incons_form]) in
											cons_and_succs = and_succs S.\\ frontier ;
											local_conflict = condition_to_frontier t lp live_frontier
										in
											--no more nodes to be expanded
											--(trace ("vs' = " ++ show (S.size vs')))
											if (vs'== (nodes t)) then
												local_conflict
											else
												let
												--OR-nodes successors from and_succs
												--or_succs = S.unions $ S.toList (S.map (succesors t) and_succs) ; 
												--all nodes that don't fulfil the eventuality (i.e., the nodes not contained in live_frontier)
												live_cons_and_succs = cons_and_succs S.\\ live_frontier ; 
												--compute successors OR nodes, different from already visited nodes.
												cons_OR_succs = (S.unions (S.toList (S.map (succesors t) live_cons_and_succs) )) S.\\ vs ;
												--filter consistent AND nodes that has at least one successor different from OR-node c.
												--let filter_and_nodes = \s -> S.intersection and_succs (predecesors t s) in 
													filter_and_nodes = \s -> (S.intersection live_cons_and_succs (predecesors t s)) ; 
												--branch condition to each consistent successor. Filter inconsistent branches.
													in_path = \s -> S.map (branch_condition t) (filter_and_nodes s) ;
													out_path = \s -> S.map (branch_condition t) (cons_and_succs S.\\ (filter_and_nodes s)) ;
												--reduce formulas removing irrelevant literals. 	
													in_form = \s -> make_or $ S.toList (in_path s) ;
													out_form = \s -> Dctl.negate $ make_or $ S.toList (out_path s) ;
													cons_forms = \s -> And (in_form s) (out_form s) ;
												--compute common path to reach these nodes to extend the level path.
													common_cons_path = \s -> lp ++ [cons_forms s] ;
												--compute next level conflicts
													next_level_conflicts = S.map (\s -> compute_liveness_conditions t frontier live_frontier vs' (common_cons_path s) s) cons_OR_succs
												in
													if (S.null local_conflict) then
														S.unions $ (S.toList next_level_conflicts)
													else
														S.unions $ [local_conflict] ++ (S.toList next_level_conflicts)
