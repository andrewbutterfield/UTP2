{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module UTP2.Abstract where

import           Control.Monad.Reader
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core hiding (Config)

-- |A GUI consists of a collection of types and operations between them. These
-- types include the monad in which the GUI is built and things like windows.
-- Type variables:
--     m: monad in which a GUI runs
--     w: a window
--     e: an element
class Monad m => GUI m w e | m -> w e where
    gButton  :: String -> m e
    gAdd     :: e -> [e] -> m e
    gGetBody :: w -> m e
    gLift    :: e -> m e
    gRunIn   :: w -> m a -> IO a

-- |Theepenny instance of abstract GUI.
instance GUI UI Window Element where
    gButton   = \t -> UI.button # set UI.text t
    gAdd e es = (element e) #+ map element es
    gGetBody  = getBody
    gLift     = element
    gRunIn    = runUI

type Config = (Int, Int) -- TBD
type App    = ReaderT Config

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
    } (\w -> runApp (app w) config)
