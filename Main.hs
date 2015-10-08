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
			writeFile "output/model.dot" (Model.model2dot $ Model.flatten $ model t2)
		}
	else
		putStrLn ("The specification is inconsistent.")
}

