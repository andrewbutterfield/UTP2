module UTP2.GUI.Threepenny.Warn where

import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types

-- | Display on-screen warning for a short time.

timeout = 10 -- seconds

warn :: String -> UTP2 ()
warn s = do
  liftIO $ putStrLn "TODO warning mechanism."
