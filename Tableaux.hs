{-# LANGUAGE DeriveGeneric #-}
module Tableaux where

import GHC.Generics (Generic)
import Data.Hashable

import Parser
import BDD as B

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
import Data.List as L	
import Data.List (sortBy, (\\))
import Data.Ord

import Debug.Trace

import Control.Monad
import Control.Monad.Fix

import qualified Model as Model
import Model (Model)


-- NODE
--
--
--
--


data Node 	= 	OrNode {formulas :: Set Formula} 
			|	AndNode {formulas :: Set Formula} 
			deriving (Eq, Ord, Generic)

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
data Tableaux = Tableaux {
					root :: Node, 						-- root  
					nodes :: Set Node,					-- nodes 
					rel :: Relation Node Node			-- relation
				} deriving (Show, Eq,Generic)


make_tableaux :: Set Formula -> Tableaux
make_tableaux s = let root = OrNode s in 
					Tableaux root (S.singleton root) R.empty

frontier :: Tableaux -> Set Node
frontier t = nodes t S.\\ (R.dom . rel) t


blocks :: Node -> Set Node
blocks (OrNode s) = S.map (\f -> AndNode (S.fromList f)) (closure s) 
			--let forms = (closure s) in
			--			let lit_forms = S.map (L.filter isLiteral) forms in
			--			--let cons_lit_forms = S.filter (\l -> not $ inconsistent (S.fromList l)) lit_forms in
			--				let branch_cond = \f ->  B.reduce_CNF_formula (S.union (S.singleton [make_and f]) (S.map (L.map Dctl.negate) (S.delete f lit_forms))) in
			--					let and_nodes =	S.map (\f -> (AndNode (S.fromList f), branch_cond (L.filter isLiteral f))) forms in
			--					--(trace ("lit_forms = " ++ (show lit_forms)))
			--					--(trace ("and_nodes = " ++ (show and_nodes)))
			--					and_nodes
			

tiles :: Node -> Set Node
tiles (AndNode s) = let ex = S.map chopEX (S.filter isEX s) ;
						ax = S.map chopAX (S.filter isAX s) 
					in
						if (S.null ex) && (S.null ax) then
							S.empty
						else
							if (S.null ex) && not (S.null ax) then
								S.singleton (OrNode ax)
							else
								let new_ex = (if not (S.null ex) then ex else S.singleton (E(X T))) in
									(\ex -> S.map OrNode (S.map (`S.insert` ax) ex)) new_ex



expand_node :: Node -> Tableaux -> (Tableaux, Set Node)
expand_node n t@(Tableaux root nodes rel) = case n of
												OrNode _ ->	(Tableaux root nodes' rel', S.empty)
																where
																	succs = S.toList (blocks n)
																	nodes' = nodes `S.union` S.fromList succs
																	rel' = rel `R.union` R.fromList [(n,succ) | succ <- succs]

												AndNode s -> case succs of
																[] ->	(Tableaux root nodes' rel', S.singleton dummy)
																			where
																			dummy = (OrNode s)
																			nodes' = dummy `S.insert` nodes
																			rel' = rel `R.union` R.fromList [(n,dummy), (dummy,n)]
																x:_ -> (Tableaux root nodes' rel', S.empty)
																			where 
																				nodes' = nodes `S.union` S.fromList succs
																				rel' = rel `R.union` R.fromList [(n,succ) | succ <- succs]
																where succs = S.toList (tiles n)



do_tableaux_impl :: Set Node -> Tableaux -> Tableaux
do_tableaux_impl used t = case S.pick $ nodes t S.\\ used of
							(Just n) -> let (t',s) = expand_node n t in 
											do_tableaux_impl (used S.+ s S.<+ n) $  t'
							Nothing -> t



do_tableaux :: Tableaux -> Tableaux
do_tableaux t = do_tableaux_impl S.empty t



{-------------------------


		DELETION


--------------------------}			

delete_node :: Node -> Tableaux -> Tableaux
delete_node n t@(Tableaux root nodes rel) = case n of
										(AndNode _) -> Tableaux root nodes' rel'
										(OrNode _) -> S.fold delete_node (Tableaux root nodes' rel') (predecesors t n)

		where
			rel' = nodes' R.<| rel R.|> nodes'
			nodes' = nodes S.\\ nn			
			nn = S.singleton n 


delete_nodes :: Set Node -> Tableaux -> Tableaux
delete_nodes s t = S.fold delete_node t s

delete_inconsistent :: Tableaux -> Tableaux
delete_inconsistent t = let inc = S.filter inconsistent_node $ nodes t in
												S.fold delete_node t inc


inconsistent_node :: Node -> Bool
inconsistent_node (AndNode s) = inconsistent s
inconsistent_node (OrNode s) = inconsistent s



delete_unreachable :: Tableaux -> Tableaux
delete_unreachable t@(Tableaux root nodes rel) =let lookup = R.lookupDom root (R.closure rel) ;
													reach = if isJust lookup then fromJust lookup else S.empty 
												in 
													S.fold delete_node t (nodes S.\\ reach)


delete_or :: Tableaux -> Tableaux
delete_or t = let to_delete = S.filter (\n -> isOr n && S.null (succesors t n)) (nodes t) in
					S.fold delete_node t to_delete




checkEU :: Tableaux -> Node -> Formula -> Bool
checkEU t n f = let val = fromJust $ M.lookup n (tagmap t f) in
					val /= pinf && val /= ninf-- checkEU_impl t n f S.empty


checkEU_impl :: Tableaux -> Node -> Formula -> Set Node -> Bool
checkEU_impl t n@(OrNode s) f@(E (U g h)) v = S.some (\m -> checkEU_impl t m f v) ((succesors t n) `S.difference` v)
checkEU_impl t n@(AndNode s) f@(E (U g h)) v = if S.member h s then 
													True
												else
													S.member g s && S.some (\m -> checkEU_impl t m f (n `S.insert` v)) ((succesors t n) `S.difference` v)


delete_EU :: Tableaux -> Tableaux
delete_EU t = 	let eus = [(n,f) | n <- S.toList $ nodes t, f <- S.toList $ formulas n, isEU f] ;
					to_delete0 = filter (\(m,g) -> not (checkEU t m g)) eus ;
					to_delete1 = map fst to_delete0
				in 
					foldl (flip delete_node) t to_delete1




checkAU :: Tableaux -> Node -> Formula -> Bool
checkAU t n f = let tag = (tagmap t f) ;
--(trace ("tagAU = " ++ show n ++ show (M.lookup n tag)))
					val = fromJust $ M.lookup n tag 
				in
					val /= pinf && val /= ninf --checkAU_impl t n f S.empty


checkAU_impl :: Tableaux -> Node -> Formula -> Set Node -> Bool
checkAU_impl t n@(OrNode s) f@(A (U g h)) v = S.some (\m -> checkAU_impl t m f (n `S.insert` v)) ((succesors t n) `S.difference` v)
checkAU_impl t n@(AndNode s) f@(A (U g h)) v = if S.member h s then 
													True
												else
													S.member g s && S.all (\m -> checkAU_impl t m f (n `S.insert` v)) ((succesors t n) `S.difference` v)

delete_AU :: Tableaux -> Tableaux
delete_AU t = 	let aus = [(n,f) | n <- S.toList $ nodes t, f <- S.toList $ formulas n, isAU f] ;
					to_delete0 = {-(trace ("aus = " ++ show aus)) -} filter (\(m,g) -> not (checkAU t m g)) aus ;
					to_delete1 = map fst to_delete0
				in 
					--(trace ("to_delete1 = " ++ show to_delete1))
					foldl (flip delete_node) t to_delete1



deletion_rules :: Tableaux -> Tableaux
deletion_rules = delete_EU . delete_AU . delete_or . delete_unreachable . delete_inconsistent 


refine_tableaux :: Tableaux -> Tableaux
refine_tableaux t = let t' = deletion_rules t in
					if t' == t then t else deletion_rules t'


{-------------------------


Tableaux Navigation functions 


--------------------------}	

succesors :: Tableaux -> Node -> Set Node
succesors t n = case R.lookupDom n $ rel t of
									Just s -> s
									Nothing -> S.empty


predecesors :: Tableaux -> Node -> Set Node
predecesors t n = case R.lookupRan n $ rel t of
									Just s -> s
									Nothing -> S.empty

reachables :: Tableaux -> Node -> Set Node
reachables t n = let lookup = R.lookupDom (root t) (R.closure (rel t)) in
					let reach = if isJust lookup then fromJust lookup else S.empty in 
						reach

unreachables :: Tableaux -> Node -> Set Node
unreachables t n = (nodes t) S.\\ (reachables t n)

isReachable :: Tableaux -> Node -> Node -> Bool
isReachable t n n' = n' `S.member` (reachables t n)


{-
paths_from :: Tableaux -> Node -> [[Node]]
paths_from t n = let succs = S.toList (succesors t n) in
					let sons = concat(map (\x -> paths_from t x) succs) in
						map (\xxs -> n:xxs) sons
-}

pathsBFS :: Tableaux -> [[Node]]
pathsBFS t = pathsBFSaux t (root t) []

pathsBFSaux :: Tableaux -> Node -> [Node] -> [[Node]]
pathsBFSaux t n visited = let succs = (S.toList (succesors t n)) \\ visited in
							let visited' = visited ++ succs in
								let sons = concat (map (\x -> pathsBFSaux t x (visited')) succs) in
									map (\xxs -> n:xxs) sons

paths_from_to :: Tableaux -> Node -> Node -> [[Node]]
paths_from_to t n n' | not (isReachable t n n') = []
paths_from_to t n n' | otherwise = paths_from_to_aux t n n' []

-- precondition: n' is reachable from n
paths_from_to_aux :: Tableaux -> Node -> Node -> [Node] -> [[Node]]
paths_from_to_aux t n n' visited | (n == n') = [] 
paths_from_to_aux t n n' visited | otherwise = let succs = (S.toList (succesors t n)) \\ visited in
													let visited' = visited ++ succs in
														let sons = concat (map (\x -> pathsBFSaux t x (visited')) succs) in
															map (\xxs -> n:xxs) sons

{-toListBFS :: Tableaux -> [Node]
toListBFS t = toListBFSaux t S.empty (S.singleton (root t))

toListBFSaux :: Tableaux -> Set Node -> Set Node -> [Node]
toListBFSaux t visited _ 		 | (nodes t) == visited = []
toListBFSaux t visited currNodes | otherwise = let visited' = visited S.++ currNodes in
												let succs = S.unions $ S.map (succesors t) currNodes in
													let no_duplicated_succs = S.filter (\e -> not $ (S.member e visited')) succs in
														(S.toList currNodes) ++ (toListBFSaux t visited' no_duplicated_succs)
-}

{-------------------------


		Model Extraction


--------------------------}	



{-------------------------  TAGGING  ---------------------------}

-- AUX
pinf :: Int
pinf = 2^29-1

ninf :: Int
ninf = -2^29
-------

init_tag :: Tableaux -> Formula -> Map Node Int
init_tag t g@(A (U f h)) = M.fromList $ l0 ++ linf
	
	where
		l0 = [(n,0) | n <- goal_nodes]
		linf = [(n,pinf) | n <- (S.toList $ nodes t) \\ goal_nodes]
		--goal_nodes = [n | n <- S.toList $ nodes t, S.member h $ formulas n]
		--agregue la parte de inconsistent_node
		goal_nodes = [n | n <- S.toList $ nodes t, not $ inconsistent_node n, S.member h $ formulas n] 

init_tag t g@(E (U f h)) = M.fromList $ l0 ++ linf
	
	where
		l0 = [(n,0) | n <- goal_nodes]
		linf = [(n,pinf) | n <- (S.toList $ nodes t) \\ goal_nodes]
		--goal_nodes = [n | n <- S.toList $ nodes t, S.member h $ formulas n]		
		--agregue la parte de inconsistent_node
		goal_nodes = [n | n <- S.toList $ nodes t, not $ inconsistent_node n, S.member h $ formulas n]		

init_tag t f = error ("init_tag case not considered: " ++ (show f))

evolve_tag :: Tableaux -> Formula -> Map Node Int -> Map Node Int
evolve_tag t g m = foldl (new_tag t g) m $ M.keys m


new_tag :: Tableaux -> Formula -> Map Node Int -> Node -> Map Node Int
--particular case when f is True
new_tag t g@(A (U T h)) m n@(AndNode s) = 	if (not $ inconsistent_node n) && S.member g s && fromJust (M.lookup n m) == pinf && S.all (\x -> fromJust (M.lookup x m) < pinf) (succesors t n) then
												M.insert n (1 + (S.findMax $ S.map (\x -> fromJust (M.lookup x m)) (succesors t n))) m
											else
												m
new_tag t g@(A (U f h)) m n@(AndNode s) = 	if (not $ inconsistent_node n) && S.member g s && S.member f s && fromJust (M.lookup n m) == pinf && S.all (\x -> fromJust (M.lookup x m) < pinf) (succesors t n) then
												M.insert n (1 + (S.findMax $ S.map (\x -> fromJust (M.lookup x m)) (succesors t n))) m
											else
												m
new_tag t g@(A (U f h)) m n@(OrNode s) = 	if (not $ inconsistent_node n) && S.member g s && fromJust (M.lookup n m) == pinf && S.some (\x -> fromJust (M.lookup x m) < pinf) (succesors t n) then
												M.insert n (S.findMin $ S.map (\x -> fromJust (M.lookup x m)) (succesors t n)) m
											else
												m
--particular case when f is True
new_tag t g@(E (U T h)) m n@(AndNode s) = 	if (not $ inconsistent_node n) && S.member g s && fromJust (M.lookup n m) == pinf && S.some (\x -> fromJust (M.lookup x m) < pinf) (succesors t n) then
												M.insert n (1 + (S.findMin $ S.map (\x -> fromJust (M.lookup x m)) (succesors t n))) m
											else
												m
new_tag t g@(E (U f h)) m n@(AndNode s) = 	if (not $ inconsistent_node n) && S.member g s && S.member f s && fromJust (M.lookup n m) == pinf && S.some (\x -> fromJust (M.lookup x m) < pinf) (succesors t n) then
												M.insert n (1 + (S.findMin $ S.map (\x -> fromJust (M.lookup x m)) (succesors t n))) m
											else
												m
new_tag t g@(E (U f h)) m n@(OrNode s) = 	if (not $ inconsistent_node n) && S.member g s && fromJust (M.lookup n m) == pinf && S.some (\x -> fromJust (M.lookup x m) < pinf) (succesors t n) then
												M.insert n (S.findMin $ S.map (\x -> fromJust (M.lookup x m)) (succesors t n)) m
											else
												m

compute_tag ::  Tableaux -> Formula -> Map Node Int -> Map Node Int
compute_tag t g m = let m' = evolve_tag t g m in 
						if m' == m then
							m
						else
							compute_tag t g m'	  


tagmap ::  Tableaux -> Formula -> Map Node Int
tagmap t g = let mapn = iterate (compute_tag t g) (init_tag t g) in
				mapn !! (S.size . nodes $ t)



--tag :: Tableaux -> Node -> Formula -> Int
--tag t n g = fromJust $ M.lookup n (tagmap t g)




{-------------------------  DAGS  ---------------------------}

dag :: Tableaux -> Node -> Formula -> Tableaux
dag t n@(AndNode _) f@(A (U g h)) = build_dagAU t (tagmap t f) $ init_dag n
dag t n@(AndNode _) f@(E (U g h)) = build_dagEU t (tagmap t f) $ init_dag n
dag t n@(OrNode _) f = error ("dag called with OrNode : " ++ (show n) ++ "and formula f : " ++ (show f)) 

init_dag = \n -> Tableaux n (S.singleton n) R.empty


build_dagAU :: Tableaux -> Map Node Int -> Tableaux -> Tableaux
build_dagAU t m dag  = 	if stop then 
							dag 
						else
							build_dagAU t m $ S.fold (flip $ treat_dag_node t m) dag (frontier dag)

	where stop = S.all (\x -> fromJust (M.lookup x m) == 0 && isAnd x) $ frontier dag


build_dagEU :: Tableaux -> Map Node Int -> Tableaux -> Tableaux
build_dagEU t m dag  = 	if stop then 
							dag 
						else
							build_dagEU t m $ treat_dag_node t m dag pick

	where 
		stop = S.some (\x -> fromJust (M.lookup x m) == 0 && isAnd x) $ frontier dag
		pick = fst . head $ sortBy (comparing snd) (filter (\p -> S.member (fst p) (frontier dag)) (M.toList m))


treat_dag_node :: Tableaux -> Map Node Int -> Tableaux -> Node -> Tableaux
treat_dag_node t@(Tableaux r ns rel) m dag@(Tableaux dr dns drel) n@(OrNode _) = let c = fst . head $ candidates in
																					Tableaux dr (dns S.<+ c) (R.insert n c drel)
	where 
		candidates = sortBy (comparing snd) (filter (\p -> S.member (fst p) (succesors t n)) (M.toList m))

treat_dag_node t@(Tableaux r ns rel) m dag@(Tableaux dr dns drel) n@(AndNode _) = Tableaux dr ns' rel'
																					where
																						succs = S.toList (succesors t n)
																						ns' = dns `S.union` S.fromList succs
																						rel' = drel `R.union` R.fromList [(n,succ) | succ <- succs]





tab_to_model :: Int -> Tableaux -> Model
tab_to_model k t@(Tableaux r ns rel) = Model.Model (trans r) (S.fromList mnodes) new_rel

	where
		new_rel = (R.map trans ((S.fromList) tnodes R.<| (rel R.* rel) R.|> (S.fromList tnodes))) 
		trans = \tn -> fromJust $ M.lookup tn tmmap
		tmmap = M.fromList $ zip tnodes mnodes 	
		mnodes = map (\p -> Model.Node (fst p) (formulas $ snd p)) (zip [k..] tnodes)
		tnodes = S.toList $ S.filter isAnd $ nodes t


{-------------------------  FRAG  ---------------------------}




frag :: Int -> Tableaux -> Node -> Model
frag k t n@(AndNode _) = 	if null eventualities then 
					tab_to_model k $ build_frag_noeven t n
				else	
					build_frag  (k+k') t (tail eventualities) initm 

	where 
		k' = Model.size initm
		initm = tab_to_model k $ (dag t n (head eventualities))
		eventualities = S.toList $ S.filter (\f -> isAU f || isEU f) (formulas n)



build_frag_noeven :: Tableaux -> Node -> Tableaux
build_frag_noeven t n@(AndNode _) = result

	where
		result = Tableaux n new_nodes new_rel
		new_rel = R.fromList $ [(n,l1) | l1 <- S.toList $ level1] ++ [(l1,l2) | l1 <- S.toList $ level1, l2 <- S.toList $ level2, R.member l1 l2 (rel t)] --new_nodes R.<| (rel t) R.|> new_nodes
		new_nodes = level1 S.+ level2 S.<+ n	
		level2 = S.map (fromJust . S.pick) $ S.map (succesors t) level1
		level1 = succesors t n



build_frag :: Int -> Tableaux -> [Formula] -> Model -> Model
build_frag k t [] mres = mres
build_frag k t (f:fs) mres = build_frag (k+k') t fs mres

	where 
		k' = Model.size dg
		mres3 = Model.paste mres2 mn dg (Model.root dg)
		dg = tab_to_model k $ (dag t c f)
		c = find_and t mn
		mn = fromJust $ S.pick $ Model.frontier mres2 ---((trace $ "mres2 --------------- \n\n " ++ show mres2)  mres2)
		mres2 = Model.identifyFrontier mres ---((trace $ "mres -------------------- \n\n " ++ show mres)  mres)


find_and :: Tableaux -> Model.Node -> Node
find_and t nm = fromJust $ S.pick $ S.filter (\n -> isAnd n && formulas n == Model.formulas nm) (nodes t)






{-------------------   MODEL  -----------------------}




model :: Tableaux -> Model
model t = build_model k fr (S.toList $ Model.frontier $ init_model) t init_model	

	where
		fr = S.singleton (choose_and, Model.root init_model)
		k = Model.size init_model
		init_model = frag 0 t choose_and
		choose_and = fromJust $ S.pick $ succesors t (root t) 


build_model :: Int -> Set (Node, Model.Node) -> [Model.Node] -> Tableaux -> Model -> Model
build_model k froots [] t mres = mres
build_model k froots (mn:mns) t mres = case da_one of
										(Just pair) -> build_model k froots (mns) t  new_model_just
										Nothing -> build_model (k'+1) (froots S.<+ (c,mn)) new_front t new_model_noth						

	where
		new_front = S.toList $  Model.frontier $ new_model_noth
		k' = k + Model.size da_frag
		new_model_noth = Model.paste mres mn da_frag (Model.root da_frag) 
		da_frag = frag (k+1) t c
		c = (find_and t mn)
		new_model_just = let p = (mn, snd $ fromJust $ da_one) in Model.identify mres p --- (trace ("p = " ++ (show p) ++ " " ++ (show $ fst p == snd p)) p)
		da_one = S.pick $ S.filter (\p -> fst p == find_and t mn {-&& notElem (snd p) (mn:mns)-}) froots 
		---trrr = trace $ "Current model ----------------------\n" ++ show mres




























{-------------------------


		Debugging


--------------------------}



init0 :: String -> Tableaux
init0 = make_tableaux . parseSpecification 

init1 :: String -> Tableaux
init1 = do_tableaux . init0

init2 :: String -> IO Tableaux
init2 path = do
				str <- readFile path
				return $ init1 str

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
numberNodes t = M.fromList (zip (S.toList $ nodes t) [1..])

-- Auxiliary function
flipMap :: (Ord a, Ord b) => Map a b -> Map b a
flipMap x = M.fromList (map (\p -> (snd p, fst p)) (M.toList x))

 
(+++) :: String -> String -> String
(+++) = (\x y -> x ++ ("\n" ++ y))

tab2dot :: Tableaux -> String
tab2dot t@(Tableaux r nodes rel) =  let num = numberNodes t in
								"digraph {\n" ++ 
								(S.fold (+++) "" (S.map (renderNode num) nodes)) ++ 
								"\n" ++ 
								renderArcs num t
								++ "\n}"

order_flas :: Set Formula -> [String]
order_flas s = reverse $ sortBy (comparing length) (S.toList (S.map show selection))

	where selection = s --S.filter elementary s 	

renderNode :: Map Node Int -> Node -> String
renderNode num n@(OrNode s) = let label = foldr (+++) "" (order_flas s) in
									"n" ++ show (num M.! n) ++ " [shape=circle, label=\"" ++ label ++ "\"];" 
renderNode num n@(AndNode s) = let label = foldr (+++) "" (order_flas s) in
									"n" ++ show (num M.! n) ++ " [shape=square, label=\"" ++ label ++ "\"];" 





renderArcs :: Map Node Int -> Tableaux -> String
renderArcs num t@(Tableaux r nodes rel) = foldl (+++) "" (map (uncurry (renderOneArc num)) (R.toList rel))

renderOneArc :: Map Node Int -> Node -> Node -> String
renderOneArc num n@(OrNode s) n' = "n" ++ show (num M.! n) ++ " -> " ++ "n" ++ show (num M.! n')-- ++ "[label=\"" ++ (show (l M.! (n,n'))) ++ "\"]"
renderOneArc num n n' = "n" ++ show (num M.! n) ++ " -> " ++ "n" ++ show (num M.! n')




tag2dot :: Tableaux -> String
tag2dot t = let f = S.filter Dctl.isF (formulas (root t)) in
				if not $ S.null f then
					let g = S.findMin f ;
						mapn = tagmap t g 
					in
						--(trace ("isF = " ++ (show f)))
						tab2dotWithTags t mapn 
				else
					let gf = S.filter Dctl.isGF (formulas (root t)) in
					if not $ S.null gf then
						let g_subs = L.concat $ break_rule (chopG (S.findMin gf)) ;
							g = (L.filter Dctl.isF g_subs) L.!! 0 ;
						 	mapn = tagmap t g 
						 in
							--(trace ("isF g= " ++ (show g)))
							tab2dotWithTags t mapn
					else
						tab2dot t


tab2dotWithTags :: (Show a) => Tableaux -> Map Node a -> String
tab2dotWithTags t@(Tableaux r nodes rel) m =  let num = numberNodes t in
								"digraph {\n" ++ 
								(S.fold (+++) "" (S.map (renderNodeWithTags num m) nodes)) ++ 
								"\n" ++ 
								renderArcs num t
								++ "\n}"

renderNodeWithTags :: (Show a) => Map Node Int -> Map Node a -> Node -> String
renderNodeWithTags num tag n@(OrNode s) = let label = \str -> "tag = " ++ str ++ "\n" ++ foldr (+++) "" (order_flas s) in
											if (show $ tag M.! n) == show pinf then
												"n" ++ show (num M.! n) ++ " [shape=circle, label=\"" ++ (label "INF") ++ "\"];" 
											else
												"n" ++ show (num M.! n) ++ " [shape=circle, label=\"" ++ (label (show $ tag M.! n)) ++ "\"];" 
renderNodeWithTags num tag n@(AndNode s) = let label = \str -> "tag = " ++ str ++ "\n" ++ foldr (+++) "" (order_flas s) in
											if (show $ tag M.! n) == show pinf then
												"n" ++ show (num M.! n) ++ " [shape=square, label=\"" ++ (label "INF") ++ "\"];" 
											else
												"n" ++ show (num M.! n) ++ " [shape=square, label=\"" ++ (label (show $ tag M.! n)) ++ "\"];" 



