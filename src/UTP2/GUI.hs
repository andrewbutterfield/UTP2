module UTP2.GUI where

import           Control.Monad.Reader
import           Graphics.UI.Abstract
import           Graphics.UI.Abstract.Threepenny
import qualified Graphics.UI.Threepenny          as UI
import           Graphics.UI.Threepenny.Core     hiding (Config)

type Config = (Int, Int) -- Placeholder

-- |Monad in which we run our app.
type App = ReaderT Config

-- |Run the App monad.
runApp :: App m a -> Config -> m a
runApp = runReaderT

-- |Example app that adds a "foo" button to a window.
exampleApp :: (GUI m w e) => w -> App m ()
exampleApp w = void $ do
    button <- lift $ gButton "foo"
    body   <- lift $ gGetBody w
    lift $ gAdd body [button]

-- |Runs an app with the threepenny GUI.
runThreepenny :: Int -> String -> (Window -> App UI ()) -> Config -> IO ()
runThreepenny port staticPath app config = do
    startGUI defaultConfig {
        jsPort   = Just port,      -- Port on which to run
        jsStatic = Just staticPath -- Directory path for static content
    } $ \w -> runApp (app w) config
