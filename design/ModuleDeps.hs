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

pLHS ('s':'h':'l':'.':rest) = reverse $ takeWhile (/='/') rest
pLHS _ = ""

parseLHSs = M.fromList . map addNull . filter (/="") . map parseLHS
addNull str= (str,[""])


-- ../src/DataText.lhs:19:import Text.ParserCombinators.Parsec.Token as P
parseImport :: String -> Tree
parseImport = pImp . words
 where
  pImp (w1:w2:_) 
   = case parseParent w1 of
      Nothing -> M.empty
      Just m1 -> M.singleton m1 [w2]
  pImp _ = M.empty

-- ../src/DataText.lhs:19:import
parseParent w1 
  | null p1  =  fail ""
  | otherwise  = return p1
  where p1 = pLHS $ dropWhile (/='s') $ reverse w1


parseImports = foldl mrgTree M.empty . map parseImport

buildTree lhs imports 
  = parseLHSs lhs `mrgTree` parseImports imports

treeShow tree
 = unlines $ concat $ map depShow $ M.toList tree

depShow (parent,children)
 = (parent ++ " <-") : split 0 [] (map (' ':) children) 
 where
   split _ rss [] = reverse rss
   split _ [] (s:ss) = split (length s) [s] ss
   split n (rs:rss) (s:ss)
    | n >= 72  =  split len (s:rs:rss) ss
    | otherwise  =  split (n+len) ((s++rs):rss) ss
    where len = length s

