module UTP2.GUI.Threepenny.Engine.Files where

import           Control.Monad             (void)
import           Control.Monad.IO.Class    (liftIO)
import           GIFiles                   (Args (..))
import qualified GIFiles                   as GI
import           UTP2.GUI.Threepenny.Types
import           WxState                   (FileState)

-- |Arguments for Threepenny-gui implementation of GIFiles.hs.
args :: String -> FileState -> Args ()
args appUserDir fstate = Args {
    aW                   = ()
  , aFstate              = fstate
  , aDisplayError        = \x y -> putStrLn $ concat [x, "\n", y]
  , aFSDirOpenDialog     = return $ Just appUserDir
  , aFSNameDialog        = const $ return "UTP2"
  }

-- |UTP2 version of 'startupFileHandling', 'fstate' is stored in the monad.
startupFileHandling :: String -> UTP2 ()
startupFileHandling appUserDir = void $ do
  fstate <- readFileState
  liftIO $ GI.startupFileHandling_GI $ args appUserDir fstate
