module Tableaux where

import Parser

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import qualified Relation as R
import Relation (Relation)

import qualified Data.Map as M
import Data.Map (Map)

import Dctl
import Closure

import Data.Maybe        (isJust, fromJust, isJust, fromMaybe)
import Data.List 		(sortBy)
import Data.Ord

import Debug.Trace

import Control.Monad





-- NODE
--
--
--
--


data Node 	= 	OrNode {formulas :: Set Formula} 
			|	AndNode {formulas :: Set Formula} 
			deriving (Eq, Ord)

instance Show Node where
	show (AndNode s) = "<AndNode " ++ show (S.toList s) ++ ">"
	show (OrNode s) = "<OrNode " ++ show (S.toList s) ++ ">"


isOr :: Node -> Bool
isOr (OrNode _) = True
isOr _ = False

isAnd :: Node -> Bool
isAnd (AndNode _) = True
isAnd _ = False


-- TABLEAUX
--
--
--
--

 
type Tableaux = (
					Node, 					--root  
					Set Node,				-- nodes 
					Relation Node Node		-- relation
				)

-- TEMPORARY
root :: Tableaux -> Node
root (r,_,_) = r

-- TEMPORARY
nodes :: Tableaux -> Set Node
nodes (_,n,_) = n

-- TEMPORARY
rel :: Tableaux -> Relation Node Node
rel (_,_,r) = r




--
--
--
--
--





make_tableaux :: Formula -> Tableaux
make_tableaux f = let root = OrNode (S.singleton f) in 
					(root, S.singleton root, R.empty)

make_tableaux_spec :: Set Formula -> Tableaux
make_tableaux_spec s = let root = OrNode s in 
					(root, S.singleton root, R.empty)

frontier :: Tableaux -> Set Node
frontier (_, nodes, rel) = nodes S.\\ R.dom rel


blocks :: Node -> Set Node
blocks (OrNode s) = S.map AndNode (closure s)


tiles :: Node -> Set Node
tiles (AndNode s) = let ex = S.map chopEX (S.filter isEX s) in
						let ax = S.map chopAX (S.filter isAX s) in
							if (S.null ex) && (S.null ax) then
								S.empty
							else
								if (S.null ex) && not (S.null ax) then
									S.singleton (OrNode ax)
								else
									let new_ex = (if not (S.null ex) then ex else S.singleton (E(X T))) in
										(\ex -> S.map OrNode (S.map (`S.insert` ax) ex)) new_ex




expand :: Tableaux -> Tableaux
expand t@(root, nodes, rel) = case S.pick $ frontier t of
								Nothing -> t
								Just (n@(OrNode _)) ->	(root, nodes', rel')
														where
															succs = S.toList (blocks n)
															nodes' = nodes `S.union` S.fromList succs
															rel' = rel `R.union` R.fromList [(n,succ) | succ <- succs]
								Just (n@(AndNode s)) -> case succs of
															[] ->	(root, nodes', rel')
																	where
																		dummy = (OrNode s)
																		nodes' = dummy `S.insert` nodes
																		rel' = rel `R.union` R.fromList [(n,dummy), (dummy,n)]
															x:_ -> (root, nodes', rel')
																	where 
																		nodes' = nodes `S.union` S.fromList succs
																		rel' = rel `R.union` R.fromList [(n,succ) | succ <- succs]
														where succs = S.toList (tiles n)



do_tableaux :: Tableaux -> Tableaux
do_tableaux t = let t' = expand t in
					if trace ("step : " ++ (show $ S.size $ nodes t)) t' == t then t else do_tableaux t'



{-------------------------


		DELETION


--------------------------}			


delete_node :: Node -> Tableaux -> Tableaux
delete_node n t@(root, nodes, rel) = case n of
										(AndNode _) -> (root, nodes', rel')
										(OrNode _) -> S.fold delete_node (root, nodes', rel') (predecesors t n)

		where
			rel' = nodes' R.<| rel R.|> nodes'
			nodes' = nodes S.\\ nn			
			nn = S.singleton n 

delete_nodes :: Set Node -> Tableaux -> Tableaux
delete_nodes s t = S.fold delete_node t s

delete_inconsistent :: Tableaux -> Tableaux
delete_inconsistent t@(_, nodes, _) = let inc = S.filter inconsistent_node nodes in
												S.fold delete_node t inc


inconsistent_node :: Node -> Bool
inconsistent_node (AndNode s) = inconsistent s
inconsistent_node (OrNode s) = inconsistent s



delete_unreachable :: Tableaux -> Tableaux
delete_unreachable t@(root, nodes, rel) = let lookup = R.lookupDom root (R.closure rel) in
											let reach = if isJust lookup then fromJust lookup else S.empty in 
												S.fold delete_node t (nodes S.\\ reach)


delete_or :: Tableaux -> Tableaux
delete_or t@(_, nodes, _) = let to_delete = S.filter (\n -> isOr n && S.null (succesors t n)) nodes in
												S.fold delete_node t to_delete




checkEU :: Tableaux -> Node -> Formula -> Bool
checkEU t n f = checkEU_impl t n f S.empty


checkEU_impl :: Tableaux -> Node -> Formula -> Set Node -> Bool
checkEU_impl t n@(OrNode s) f@(E (U g h)) v = S.some (\m -> checkEU_impl t m f v) ((succesors t n) `S.difference` v)
checkEU_impl t n@(AndNode s) f@(E (U g h)) v = if S.member h s then 
													True
												else
													S.member g s && S.some (\m -> checkEU_impl t m f (n `S.insert` v)) ((succesors t n) `S.difference` v)


delete_EU :: Tableaux -> Tableaux
delete_EU t = let eus = [(n,f) | n <- S.toList $ nodes t, f <- S.toList $ formulas n, isEU f] in
				let to_delete0 = filter (\(m,g) -> not (checkEU t m g)) eus in
					let to_delete1 = map fst to_delete0 in 
						foldl (flip delete_node) t to_delete1




checkAU :: Tableaux -> Node -> Formula -> Bool
checkAU t n f = checkAU_impl t n f S.empty


checkAU_impl :: Tableaux -> Node -> Formula -> Set Node -> Bool
checkAU_impl t n@(OrNode s) f@(A (U g h)) v = S.some (\m -> checkAU_impl t m f (n `S.insert` v)) ((succesors t n) `S.difference` v)
checkAU_impl t n@(AndNode s) f@(A (U g h)) v = if S.member h s then 
											True
										else
											S.member g s && S.all (\m -> checkAU_impl t m f (n `S.insert` v)) ((succesors t n) `S.difference` v)


delete_AU :: Tableaux -> Tableaux
delete_AU t = let aus = [(n,f) | n <- S.toList $ nodes t, f <- S.toList $ formulas n, isAU f] in
				let to_delete0 = filter (\(m,g) -> not (checkAU t m g)) aus in
					let to_delete1 = map fst to_delete0 in 
						foldl (flip delete_node) t to_delete1



deletion_rules :: Tableaux -> Tableaux
deletion_rules = delete_EU . delete_AU . delete_or . delete_unreachable . delete_inconsistent 


refine_tableaux :: Tableaux -> Tableaux
refine_tableaux t = let t' = deletion_rules t in
					if t' == t then t else deletion_rules t'










-- Tableaux Aux
succesors :: Tableaux -> Node -> Set Node
succesors t@(_, nodes, rel) n = case R.lookupDom n rel of
									Just s -> s
									Nothing -> S.empty

-- Tableaux Aux
predecesors :: Tableaux -> Node -> Set Node
predecesors t@(_, nodes, rel) n = case R.lookupRan n rel of
									Just s -> s
									Nothing -> S.empty



{-------------------------


		Debugging


--------------------------}	



init0 :: String -> Tableaux
init0 = make_tableaux . parseFormula 

init1 :: String -> Tableaux
init1 = do_tableaux . init0

test :: String -> String -> [Tableaux -> Tableaux] -> IO ()
test path fl fs = let res = foldl (flip ($)) (init1 fl) fs in
					writeFile path (tab2dot res)



test2 :: String -> [Action] -> IO Tableaux
test2 fl fs = do_actions 0 fs (return $ init1 fl) 

type Action = (Int, Tableaux -> Tableaux)

do_actions ::  Int -> [Action] -> IO Tableaux -> IO Tableaux
do_actions i [] t = t
do_actions i ((0, f):fs) t = do_actions i fs t
do_actions i (((k+1), f):fs) t = do
								tab <- t
								writeFile ("output/out" ++ show i ++ ".dot") (tab2dot (f tab))
								do_actions (i+1) ((k, f):fs) (return (f tab))






{-------------------------


		PRINTING


--------------------------}	




numberNodes :: Tableaux -> Map Node Int
numberNodes (_, nodes, _) = M.fromList (zip (S.toList nodes) [1..])
 
(+++) :: String -> String -> String
(+++) = (\x y -> x ++ ("\n" ++ y))

tab2dot :: Tableaux -> String
tab2dot t@(r, nodes, rel) =  let num = numberNodes t in
								"digraph {\n" ++ 
								(S.fold (+++) "" (S.map (renderNode num) nodes)) ++ 
								"\n" ++ 
								renderArcs num t
								++ "\n}"

order_flas :: Set Formula -> [String]
order_flas s = reverse $ sortBy (comparing length) (S.toList (S.map show selection))

	where selection = S.filter elementary s 	

renderNode :: Map Node Int -> Node -> String
renderNode num n@(OrNode s) = let label = foldr (+++) "" (order_flas s) in
										"n" ++ show (num M.! n) ++ " [shape=circle, label=\"" ++ label ++ "\"];" 
renderNode num n@(AndNode s) = let label = foldr (+++) "" (order_flas s) in
										"n" ++ show (num M.! n) ++ " [shape=square, label=\"" ++ label ++ "\"];" 





renderArcs :: Map Node Int -> Tableaux -> String
renderArcs num t@(r, nodes, rel) = foldl (+++) "" (map (uncurry (renderOneArc num)) (R.toList rel))

renderOneArc :: Map Node Int -> Node -> Node -> String
renderOneArc num n n' = "n" ++ show (num M.! n) ++ " -> " ++ "n" ++ show (num M.! n') 






