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

--main = do {
--	args <- getArgs;
--	str <- readFile (head args);
--	spec <- return $ parseSpecification str;
--	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
--	mdo_tableaux (return $ make_tableaux spec);
--	putStrLn ("Tableaux done.");
--}


main = do {
	args <- getArgs;
	str <- readFile (head args);
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


{-

mparse :: IO String -> IO (Set Formula)
mparse = fmap parseSpecification

minit :: IO (Set Formula) -> IO Tableaux
minit = fmap make_tableaux

mexpand :: IO Tableaux -> IO Tableaux
mexpand = fmap expand

mdump :: Int -> IO Tableaux -> IO Tableaux
mdump i t = do
			tab <- t
			writeFile ("output/out" ++ show i ++ ".dot") (tab2dot tab)
			t

mdo_tableaux = (mdo_tableaux_imp 0)

mdo_tableaux_imp :: Int -> IO Tableaux -> IO Tableaux
mdo_tableaux_imp i t = do
					t1 <- t	
					mdump i t
					t2 <- mexpand t
					if t1 == t2 then t else mdo_tableaux_imp (i+1) (return t2)
				
-}