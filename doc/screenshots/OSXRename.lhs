\section{Mac OS X ScreenShot Renaming}

This is standalone code,
intended for use on Mac OS X to rename screenshots
from that platform.


\begin{code}
module OSXRename where
import Data.Char
import System.IO
import System.Directory
import System.FilePath.Posix

what = putStrLn "doit :: IO ()"
doit = ssRenameFiles isOSXNewScreenShot

isOSXNewScreenShot path
               = takeExtension path == ".png" && take 11 path == "Screen Shot"

ssRenameFiles :: (FilePath -> Bool) -> IO ()
ssRenameFiles newShot
 = do paths <- getDirectoryContents "."
      putStrLn "\nBEFORE:"
      putStrLn $ unlines paths
      putStr "Starting Number ? (negative to abort) : "
      txt <- getLine
      let firstNo = (read txt) :: Int
      if firstNo < 0
       then putStrLn "No files renamed"
       else do putStr "Screenshot Series Title (filename characters only) : "
               title <- getLine
               createDirectoryIfMissing True title
               mapM_ (doRename title) $ zip [firstNo..] $ filter newShot paths
               putStrLn ("Files renamed")
               paths' <- getDirectoryContents ("./"++title)
               putStrLn "\nAFTER:"
               putStrLn $ unlines paths'

doRename :: String -> (Int, FilePath) -> IO ()
doRename title (n,oldpath)  =  renameFile oldpath (title++"/"++title++display 4 n++".png")

display w n =  replicate (w - length s) '0' ++ s where s = show n
\end{code}
