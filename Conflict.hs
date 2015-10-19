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
--conflicts t | not S.null (inconsistent_nodes t) = []
conflicts t = let inconsistent_nodes = S.filter (\n -> (inconsistent_node n) && (isOr n)) (nodes t) in
					let inconsistent_predecesors = {-(trace ("inconsistent_nodes = " ++ show inconsistent_nodes))-} S.map (predecesors t) inconsistent_nodes in
						let candidate_nodes = {-(trace ("inconsistent_predecesors = " ++ show inconsistent_predecesors))-} S.map (\s -> S.filter (\n -> not $ inconsistent_node n) s) inconsistent_predecesors in
						--S.map (\ip -> ip S.\\ inconsistent_nodes) inconsistent_predecesors in
							let candidate_conflicts = {-(trace ("candidate_nodes = " ++ show candidate_nodes))-} S.map (common_path t) candidate_nodes in
								--(trace ("candidate_conflicts = " ++ show candidate_conflicts)) 
								candidate_conflicts

{-common_path :: Tableaux -> Set Node -> [Formula]
common_path t cand = let cand_parents = S.map (predecesors t) cand inconsistent_nodes in 
						let 
	S.intersection 
-}
common_path :: Tableaux -> Set Node -> [Formula]
common_path t ns = let ns_paths = S.map (common_path_to t) ns in
						--(trace ("ns_paths = " ++ show ns_paths)) 
						multiple_intersect (S.toList ns_paths)

common_path_to :: Tableaux -> Node -> [Formula]
common_path_to t n = let n_parents = predecesors t n in
						let n_parent_paths = S.map (\p -> branch_condition t p n) n_parents in 
							--(trace ("n_parents = " ++ show n_parents))
							--(trace ("n_parent_paths = " ++ show n_parent_paths))
							multiple_intersect (S.toList n_parent_paths)


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

--Path Condition
--  It characterises uniquely the path from node n to node n' 
--  when n' is reachable from n.

--path_condition_one_step :: Tableaux -> Node -> Node -> [[Formula]]
--path_condition_one_step t n n' | not (S.member n' (succesors t n)) = []
--path_condition_one_step t n n' | otherwise = let others = S.delete n' (succesors t n) in
--												map (branch_condition t n) (S.toList others)



