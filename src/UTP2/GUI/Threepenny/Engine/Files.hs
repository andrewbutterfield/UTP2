module UTP2.GUI.Threepenny.Engine.Files where

import           Control.Monad (void)
import           GIFiles       (Args (..))
import qualified GIFiles       as GI

-- |Arguments for Threepenny-gui implementation of GIFiles.hs.
args :: String -> String -> Args () ()
args appUserDir currentFileSpace = Args {
    aW                   = ()
  , aState               = ()
  , aAppUserDir          = const $ appUserDir
  , aCurrentFileSpace    = const $ currentFileSpace
  , aDisplayError        = \x y -> putStrLn $ concat [x, "\n", y]
  , aOnAppUserDirError   = const $ return ()
  , aFSDirOpenDialog     = return Nothing
  , aFSNameDialog        = const $ return ""
  , aNewFS               = const $ const ()
  , aReadFSPFileNewState = const $ const ()
  , aWriteFSPFileFSPs    = const $ []
  }

startupFileHandling :: String -> String -> IO ()
startupFileHandling appUserDir currentFileSpace = void $
  GI.startupFileHandling_GI $ args appUserDir currentFileSpace

