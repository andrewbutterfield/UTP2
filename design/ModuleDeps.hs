module ModuleDeps where
import System.Environment
import qualified Data.Map as M

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

-- ../src/DataText.lhs:19:import Text.ParserCombinators.Parsec.Token as P
parseImport = pImp . words
 where
  pImp (w1:w2:_) = M.singleton w1 [w2]
  pImp _ = M.empty

type Tree = M.Map String [String]

parseLHSs = M.fromList . map addNull . filter (/="") . map parseLHS
addNull str= (str,"")


buildTree lhs imports 
  = parseLHSs lhs

treeShow = show


