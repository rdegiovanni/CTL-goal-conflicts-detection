#!/opt/local/bin/runhugs

import System.Environment
import Dctl
import Parser
import ParseLib
import Tableaux

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

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
	spec <- return $ parseSpecification str;
	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
	putStr ("Tableaux .. ");
	t <- return $ do_tableaux $ make_tableaux spec;
	putStrLn ("done.");
	writeFile "output/tableaux_raw.dot" (tab2dot t);
	putStr ("Refining tableaux .. ");
	t2 <- return $ refine_tableaux t;
	putStrLn ("done.");
	if not $ S.null $ nodes t2 then 
		do {
			writeFile "output/tableaux.dot" (tab2dot t2);
			putStrLn ("Extracting model.");
			writeFile "output/model.dot" (Model.model2dot $ Model.flatten $ model t2);

			putStr ("Computing conflicts .. ");
			run_conflicts_detection spec t2;
			--return ()
		}
	else
		putStrLn ("STRONG conflict detected. The specification is inconsistent.");

	return t
}

run_conflicts_detection = \spec -> \t -> do {
	potential_conflict_set <- return $ potential_conflicts t;
	if S.null potential_conflict_set then 
			putStrLn ("No WEAK conflict detected.");
	else
		do {
			putStrLn ("Potential conflicts detected:");
			potential_conflicts_forms <- return $ make_safety_conflicts potential_conflict_set;
			putStrLn (show potential_conflicts_forms);
			putStrLn ("Computing WEAK conflicts...");
			weak_conflicts_set <- return $ weak_conflicts spec potential_conflicts_forms;
			putStrLn (show weak_conflicts_set)
		}
}

