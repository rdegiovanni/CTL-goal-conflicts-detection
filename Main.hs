#!/opt/local/bin/runhugs

import System.Environment
import Dctl
import Parser
import ParseLib
import Tableaux

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import Hugs.Observe
import Data.HashTable
import Debug.Trace



main = do {
	args <- getArgs;
	str <- readFile (head args);
	spec <- return $ parseSpecification str;
	t <- return $ refine_tableaux $ do_tableaux $ make_tableaux_spec spec;
	writeFile "output/out.dot" (tab2dot t)
}

