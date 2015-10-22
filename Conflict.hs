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
conflicts t = let inconsistent_nodes = inconsistent_OR_nodes t in
					let inconsistent_predecesors =  S.map (predecesors t) inconsistent_nodes in
						let candidate_nodes =  S.map (\s -> S.filter (\n -> not $ inconsistent_node n) s) inconsistent_predecesors in
							let candidate_conflicts = S.map (common_path t) candidate_nodes in
								--(trace ("candidate_conflicts = " ++ show candidate_conflicts)) 
								candidate_conflicts


--return the inconsistent OR nodes: all sons are inconsistent
inconsistent_OR_nodes :: Tableaux -> Set Node
inconsistent_OR_nodes t = let orNodes = S.filter isOr (nodes t) in
							let inconsistent_orNodes = S.filter (\n -> S.all (inconsistent_node) (succesors t n)) orNodes in
								inconsistent_orNodes

common_path :: Tableaux -> Set Node -> [Formula]
common_path t ns = let ns_paths = S.map (common_path_to t) ns in
						(trace ("ns_paths = " ++ show ns_paths)) 
						L.nub $ concat (S.toList ns_paths) --unions
						--multiple_intersect (S.toList ns_paths)

common_path_to :: Tableaux -> Node -> [Formula]
common_path_to t n = let n_parents = predecesors t n in
						let n_parent_paths = S.map (\p -> (S.fromList $ branch_condition t p n)) n_parents in 
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

