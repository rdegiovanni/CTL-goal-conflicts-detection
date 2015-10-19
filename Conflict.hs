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

import Data.List 		(sortBy, (\\))
import Data.Ord

import Debug.Trace

--branch condition in one step
branch_condition :: Tableaux -> Node -> Node -> [Formula]
branch_condition t n n' = (label t) M.! (n,n')

--Path Condition
--  It characterises uniquely the path from node n to node n' 
--  when n' is reachable from n.

path_condition_one_step :: Tableaux -> Node -> Node -> [[Formula]]
path_condition_one_step t n n' | not (S.member n' (succesors t n)) = []
path_condition_one_step t n n' | otherwise = let others = S.delete n' (succesors t n) in
												map (branch_condition t n) (S.toList others)


{-
path_condition :: Tableaux -> Node -> Node -> [[Formula]]
path_condition t [] = []
path_condition t [x]  = []
path_condition t x:(y:xs) = (branch_condition t x y) ++ (path_condition t y:xs) 

| not (isReachable t n n') = []
path_condition t n n' | otherwise = path_condition_aux t n n' []

path_condition_aux :: Tableaux -> Node -> Node -> [[Formula]]-}
