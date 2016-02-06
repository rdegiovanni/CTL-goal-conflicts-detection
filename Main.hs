#!/opt/local/bin/runhugs

import System.Environment
import Dctl
import Parser
import ParseLib
import Tableaux

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import qualified Relation as R
import Relation (Relation)

import Debug.Trace

import qualified Model as Model
import Model (Model)

import Conflict

main = do {
	args <- getArgs;
	run_tableaux $ head args
}


run_tableaux = \path -> do {
	str <- readFile path;
	(dom,goals) <- return $ parseDOMandGOALS str;
	spec <- return $ S.union dom goals;
	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
	putStr ("Tableaux .. ");
	t <- return $ do_tableaux $ make_tableaux spec;
	putStrLn ("done.");
	print_Tableaux_info t;
	writeFile "output/tableaux_raw.dot" (tab2dot t);
	putStr ("Refining tableaux .. ");
	t2 <- return $ refine_tableaux t;
	putStrLn ("done.");
	if not $ S.null $ nodes t2 then 
		do {
			print_Tableaux_info t2;
			writeFile "output/tableaux.dot" (tab2dot t2);
			putStrLn ("Extracting model.");
			model <- return $ Model.model2dot $ Model.flatten $ model t2;
			writeFile "output/model.dot" (model);

			--putStrLn ("SAT");
			run_conflicts_detection dom goals t t2;
			--return ()
		}
	else
		--putStrLn ("UNSAT.");
		putStrLn ("STRONG conflict detected. The specification is inconsistent.");

	return t
}

run_conflicts_detection = \dom -> \goals -> \t -> \t2 -> do {
	spec <- return $ S.union dom goals;
	potential_conflict_set <- potential_conflicts spec t t2;
	if S.null potential_conflict_set then 
			putStrLn ("No WEAK conflict detected.");
	else
		do {
			putStrLn ("Potential conflicts detected:");
			putStrLn (show potential_conflict_set);
			putStrLn ("Filtering WEAK conflicts...");
			weak_conflicts_set <- return $ weak_conflicts dom goals potential_conflict_set;
			putStrLn (show weak_conflicts_set)
		}
}

print_Tableaux_info = \t -> do {
	size <- return $ S.size (nodes t);
	putStrLn ("#nodes= " ++ show (size) ++ "\t");
	putStrLn ("#trans= " ++ show (R.size (rel t)) )
}
