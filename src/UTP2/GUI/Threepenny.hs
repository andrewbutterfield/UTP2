module UTP2.GUI.Threepenny (start) where

import           Control.Monad                   (void)
import           Control.Monad.Trans.Class       (lift)
import qualified Graphics.UI.Threepenny          as UI
import           Graphics.UI.Threepenny.Core
import           Paths_UTP2                      (getDataDir)
import           System.FilePath                 ((</>))
import           UTP2.GUI.Threepenny.Dom
import           UTP2.GUI.Threepenny.Home
import qualified UTP2.GUI.Threepenny.Materialize as Mat
import           UTP2.GUI.Threepenny.Types

-- |Runs the UTP2 Threepenny app.
start :: Int -> IO ()
start port = do
    env        <- initialEnv
    htmlPath   <- (</> "index.html") <$> getDataDir
    staticPath <- (</> "static")     <$> getDataDir
    startGUI defaultConfig {
        jsCustomHTML = Just htmlPath,  -- Custom HTML file
        jsPort       = Just port,      -- Port on which to run
        jsStatic     = Just staticPath -- Directory of static content
    } $ \w -> runUTP2 (app w) env

-- |The Threepenny app.
app :: Window -> UTP2 ()
app window = do
    lift $ return window # set UI.title "UTP²"
    lift $ UI.addStyleSheet window "materialize.css"
    home <- mkHome
    tabs <- Mat.tabs [
        ("Home",     element home)
      , ("Laws",     UI.div # set UI.text "todo")
      , ("OBS.",     UI.div # set UI.text "todo")
      , ("Language", UI.div # set UI.text "todo")
      ]
    lift $ appendToBody [element tabs]
    lift $ Mat.initTabs
