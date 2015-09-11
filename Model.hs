module Model where

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import qualified Relation as R
import Relation (Relation)

import qualified Data.Map as M
import Data.Map (Map)

import Prelude hiding (id)

import Data.List (sortBy, (\\))
import Data.Ord

import Control.Exception.Base

import Debug.Trace

import Dctl




data Node = Node {id :: Int, formulas :: Set Formula}	deriving (Eq, Ord, Show)

--instance Show Node where
--	show s = "<Node id=" ++ (show $ id s) ++ ", " ++ show (S.toList $ formulas s) ++ ">"

data Model = Model {
					root :: Node, 					--root  
					nodes :: Set Node,				-- nodes 
					rel :: Relation Node Node		-- relation
				} deriving Eq

instance Show Model where
	show = model2dot



size :: Model -> Int
size = S.size . nodes 

frontier :: Model -> Set Node
frontier m = nodes m S.\\ (R.dom . rel) m


identify :: Model -> (Node, Node) -> Model
identify m@(Model root nodes rel) (n,n') | require = assert ensure result

	where
		-- require
		require = S.member n nodes && S.member n' nodes && formulas n == formulas n'
		-- ensure
		ensure = S.member n new_nodes || S.member n' new_nodes
		-- aux 
		result = Model root new_nodes new_rel
		new_nodes = if n == n' then nodes else (nodes S.<\\ n')
		new_rel = if n == n' then R.insert n n' rel else R.fromList $ map (\(x,y) -> (if x == n' then n else x, if y == n' then n else y)) rel_pairs
		--new_rel = R.fromList ((rel_pairs \\ to_remove) ++ to_add)
		--to_add = map (\p -> (if fst p == n' then n else fst p, if snd p == n' then n else snd p)) to_remove
		--to_remove = filter (\p -> (fst p)  == n' || (snd p) == n') rel_pairs
		rel_pairs = R.toList rel

identify m p | otherwise = error $ "identify: precondition violation. Called with " ++ (show p) ++ (show m)







identifyFrontier :: Model -> Model
identifyFrontier m = 	if null idents then
							m
						else
							identifyFrontier $ identify m (head idents)	 

	where idents = [(x, y) | x <- S.toList $ frontier m, y <- S.toList $ frontier m, formulas x == formulas y && (x /= y)]


-- pastes model m' (rooted at r) into model m at node i. r and i are identified.
paste :: Model -> Node -> Model -> Node -> Model
paste m i m' r = (flip identify) (i, r) $ Model (root m) (nodes m S.+ nodes m') (rel m R.+ rel m')










 
(+++) :: String -> String -> String
(+++) = (\x y -> x ++ ("\n" ++ y))

model2dot :: Model -> String
model2dot m@(Model root nodes rel) = 	"digraph {\n" ++ 
										(S.fold (+++) "" (S.map renderNode nodes)) ++ 
										"\n" ++ 
										renderArcs m
										++ "\n}"

order_flas :: Set Formula -> [String]
order_flas s = reverse $ sortBy (comparing length) (S.toList (S.map show selection))

	where selection = s --S.filter elementary s 	

renderNode :: Node -> String
renderNode n = let label = foldr (+++) "" (order_flas $ formulas n) in
										"n" ++ (show $ id n) ++ " [shape=egg, label=\"" ++ label ++ "\"];" 





renderArcs :: Model -> String
renderArcs m@(Model root nodes rel) = foldl (+++) "" (map (uncurry renderOneArc) (R.toList rel))

renderOneArc :: Node -> Node -> String
renderOneArc n n' = "n" ++ (show $ id n) ++ " -> " ++ "n" ++ (show $ id n')




{-


tab2dotWithTags :: (Show a) => Tableaux -> Map Node a -> String
tab2dotWithTags t@(Tableaux r nodes rel) m =  let num = numberNodes t in
								"digraph {\n" ++ 
								(S.fold (+++) "" (S.map (renderNodeWithTags num m) nodes)) ++ 
								"\n" ++ 
								renderArcs num t
								++ "\n}"

renderNodeWithTags :: (Show a) => Map Node Int -> Map Node a -> Node -> String
renderNodeWithTags num tag n@(OrNode s) = let label = "tag = " ++ (show $ tag M.! n) ++ "\n" ++ foldr (+++) "" (order_flas s) in
										"n" ++ show (num M.! n) ++ " [shape=circle, label=\"" ++ label ++ "\"];" 
renderNodeWithTags num tag n@(AndNode s) = let label = "tag = " ++ (show $ tag M.! n) ++ "\n" ++ foldr (+++) "" (order_flas s) in
										"n" ++ show (num M.! n) ++ " [shape=square, label=\"" ++ label ++ "\"];" 

-}
