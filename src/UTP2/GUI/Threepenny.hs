module UTP2.GUI.Threepenny (start) where

import           Control.Monad               (void)
import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Home
import           UTP2.GUI.Threepenny.Types

-- |Runs the UTP2 Threepenny app.
start :: Int -> String -> IO ()
start port static = do
    env <- initialEnv
    startGUI defaultConfig {
        jsPort   = Just port,  -- Port on which to run
        jsStatic = Just static -- Directory path for static content
    } $ \w -> runApp (app w) env

-- |The initial environement.
initialEnv :: IO Env
initialEnv = return Env { eWorkspace = "foo/bar" }

-- |The Threepenny app.
app :: Window -> UTP2 ()
app window = do
    lift $ return window # set UI.title "UTP²"
    lift $ UI.addStyleSheet window "materialize.css"
    home  <- mkHome
    void $ lift $ getBody window #+ [element home]
