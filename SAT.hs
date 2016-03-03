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
	spec <- return $ parseSpecification (remove_comments str);
	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
	putStr ("Tableaux .. ");
	t <- return $ do_tableaux $ make_tableaux spec;
	print_Tableaux_info t;
	putStrLn ("done.");
	writeFile "output/tableaux_raw.dot" (tag2dot t);
	putStr ("Refining tableaux .. ");
	t2 <- return $ refine_tableaux t;
	print_Tableaux_info t2;
	putStrLn ("done.");
	if not $ S.null $ nodes t2 then 
		do {
			writeFile "output/tableaux.dot" (tag2dot t2);
			putStrLn ("Extracting model.");
			model <- return $ Model.model2dot $ Model.flatten $ model t2;
			writeFile "output/model.dot" (model);

			putStrLn ("SAT");
			
			--return ()
		}
	else
		putStrLn ("UNSAT.");
	return t
}

print_Tableaux_info = \t -> do {
	size <- return $ S.size (nodes t);
	putStr ("(#nodes= " ++ show (size) ++ ", ");
	putStr ("#trans= " ++ show (R.size (rel t)) ++ ") ")
}

