module ModuleDeps where
import System.Environment
import qualified Data.Map as M

type Tree = M.Map String [String]

mrgTree = M.unionWith (++)

main 
 = do args <- getArgs
      let (lhsLog,importLog,importTree) = parse args
      lhs <- fmap lines $ readFile lhsLog
      imports <- fmap lines $ readFile importLog
      let tree = buildTree lhs imports
      writeFile importTree $ treeShow tree
      putStrLn "NYI"

{- Parsing -}

-- ignore arguments for now
parse args = ("_lhs.log","_import.log","_importTree.log")


-- look for longest suffix of form  <base>.lhs and return <base>
-- where <base> does not contain '/'
-- e.g.,  ../src/XXXX.lhs  -->  XXXX
parseLHS = pLHS . reverse
 where
  pLHS ('s':'h':'l':'.':rest) = reverse $ takeWhile (/='/') rest
  pLHS _ = ""

parseLHSs = M.fromList . map addNull . filter (/="") . map parseLHS
addNull str= (str,[""])


-- ../src/DataText.lhs:19:import Text.ParserCombinators.Parsec.Token as P
parseImport :: String -> Tree
parseImport = pImp . words
 where
  pImp (w1:w2:_) 
   = case pImp' w1 w2 of
      Nothing -> M.empty
      Just (m1,m2) -> M.singleton m1 [m2]
  pImp _ = M.empty

  pImp' :: String -> String -> Maybe (String, String)
  pImp' w1 w2
   = do parentMod <- parseParent w1
        childMod <- parseChild w2
        return (parentMod,childMod)

-- ../src/DataText.lhs:19:import
parseParent w1 = return w1

-- Text.ParserCombinators.Parsec.Token as P
parseChild w2 = return w2

parseImports = foldl mrgTree M.empty . map parseImport

buildTree lhs imports 
  = parseLHSs lhs `mrgTree` parseImports imports

treeShow = show


