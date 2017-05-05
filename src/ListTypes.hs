module Main where

main
 = do blines <- fmap lines $ readFile "browse.log"
      let typeDecls = findTypeDecls blines
      putStrLn $ displayDecls typeDecls

type Decl = [String]

findTypeDecls :: [String] ->[Decl]
findTypeDecls [] = []
findTypeDecls (ln:lns)
  | isTypeDecl ln = collectDecl [ln] lns
  | otherwise  =  findTypeDecls lns

isTypeDecl ln
 = take 5 ln == "data " || take 5 ln == "type " || take 8 ln == "newtype "

collectDecl :: Decl -> [String] -> [Decl]
collectDecl dcl [] = [dcl]
collectDecl dcl all@(ln:lns)
 | isIndented ln  = collectDecl (dcl++[ln]) lns
 | otherwise  = dcl : findTypeDecls all

isIndented ln = length (takeWhile (==' ') ln) > 1

displayDecls :: [Decl] -> String
displayDecls = unlines . concat . map dispDecl

dispDecl :: Decl -> [String]
dispDecl dcl = "":dcl
