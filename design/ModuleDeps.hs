{- Copyright (c) 2016 Andrew Butterfield, TCD -}

module Main where
import qualified Data.Map as M
import Data.List

type Tree = M.Map String [String]

mrgTree = M.unionWith (++)

lhsLog     =  "_lhs.log"
importLog  =  "_import.log"
treeLog    =  "_hierarchy.log"
cyclesLog  =  "_cycles.log"
wxLog      =  "_wxTree.log"

main 
 = do lhs <- fmap (parseLHSs . lines) $ readFile lhsLog
      putStrLn ("Read "++lhsLog)

      imports <- fmap (parseImports . lines) $ readFile importLog
      putStrLn ("Read "++importLog)

      let tree = lhs `mrgTree` imports
      writeFile treeLog $ treeShow tree
      putStrLn ("Written "++treeLog)

      let lhsKeys = M.keys lhs

      -- we don't report this at the moment
      let extern = nub (concat (M.elems imports)) \\ lhsKeys
      let reached = reachable tree "UTP2"
      let used = reached `intersect` lhsKeys
      let unused = reached \\ lhsKeys

      -- we know the hierarchy has a cycle !
      let cycs = cycles tree "UTP2"
      writeFile cyclesLog $  unlines ("Cycles": take 10 (map show cycs))
      putStrLn ("Written "++cyclesLog)

      let wxusers = M.map (filter isWX) $ M.filter (any isWX) tree
      writeFile wxLog $ treeShow wxusers
      let wxusage = M.map (filter (`elem` lhsKeys)) $ M.filterWithKey (fkey isWX) tree
      appendFile wxLog $ '\n':treeShow wxusage
      putStrLn ("Written "++wxLog)


isWX name = take 2 name == "Wx"
fkey w k a = w k

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

cycles :: Tree -> String -> [[String]] -- does not terminate!
-- sample using take/drop
cycles tree name
 = cyc [] name
 where
   cyc :: [String] -> String -> [[String]]
   cyc seen nm
    | nm `elem` seen  =  [nm:seen]
    | otherwise
      = case M.lookup nm tree of
         Nothing  ->  [] -- no cycle here, at least
         Just children
          -> concat $ map (cyc (nm:seen)) children

reachable tree name
 = case M.lookup name tree of
     Nothing -> []
     (Just children) 
       ->  nub (children ++ concat (map (reachable tree) children))


