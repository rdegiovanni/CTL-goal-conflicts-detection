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


main = do {
	args <- getArgs;
	str <- readFile (head args);
	spec <- return $ parseSpecification str;
	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
	mdo_tableaux (return $ make_tableaux_spec spec);
	putStrLn ("Tableaux done.");
}


main2 = do {
	args <- getArgs;
	str <- readFile (head args);
	spec <- return $ parseSpecification str;
	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
	t <- return $ do_tableaux $ make_tableaux_spec spec;
	writeFile "output/tab_pre_refine.dot" (tab2dot t);
	putStrLn ("Tableaux done.");
	t2 <- return $ refine_tableaux t;
	writeFile "output/out.dot" (tab2dot t2)
}




mparse :: IO String -> IO (Set Formula)
mparse = fmap parseSpecification

minit :: IO (Set Formula) -> IO Tableaux
minit = fmap make_tableaux_spec

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
				
