module UnicodeFun where
import System.IO
import Test.QuickCheck

-- get/write/read raw
raw
 = do putStr "Enter string: "
      str <- getLine
      putStrLn ("str is '"++str++"'")
      writeFile "raw.txt" str
      str' <- readFile "raw.txt"
      putStrLn ("str' is '"++str'++"'")


cook :: String -> String
cook str = read ("\""++str++"\"")

freeze :: String -> String
freeze str = show str

prop_cook_freeze str = cook (freeze str) == str

prop_freeze_cook str = freeze (cook str) == str

prop_read_freeze str = read (freeze str) == str

prop_freeze_read str = freeze (read str) == str


cookit
 = do putStr "Enter string: "
      str <- getLine
      putStrLn ("str    is '"++str++"'")
      let cooked = cook str
      putStrLn ("cooked is '"++cooked++"'")
      writeFile "cooked.txt" cooked
      str' <- readFile "cooked.txt"
      putStrLn ("str' is '"++str'++"'")
 
hcookit
 = do putStr "Enter string: "
      str <- getLine
      putStrLn ("str    is '"++str++"'")
      let cooked = cook str
      putStrLn ("cooked is '"++cooked++"'")
      writeFile "cooked.txt" cooked
      h <- openFile "cooked.txt" ReadMode
      str' <- hGetContents h
      putStrLn ("str' is '"++str'++"'")
      hClose h

freezeit
 = do putStr "Enter string: "
      str <- getLine
      putStrLn ("str    is '"++str++"'")
      let frozen = freeze str
      putStrLn ("frozen is '"++frozen++"'")
      writeFile "frozen.txt" frozen
      str' <- readFile "frozen.txt"
      putStrLn ("str' is '"++str'++"'")

