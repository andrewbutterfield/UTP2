{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module UTP2.Abstract where

import           Control.Monad.Reader
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core hiding (Config)

-- |A collection of types define our abstract GUI. GUI libraries typically
-- provide their own types representing windows or the monad the GUI runs in.
class Monad m => AG m w e | m -> w e where
    gButton  :: String -> m e
    gAdd     :: m e -> [m e] -> m e
    gGetBody :: w -> m e
    gLift    :: e -> m e
    gRunIn   :: w -> m a -> IO a

-- |Theepenny instance of abstract GUI.
instance AG UI Window Element where
    gButton  = \t -> UI.button # set UI.text t
    gAdd     = (#+)
    gGetBody = getBody
    gLift    = element
    gRunIn   = runUI

type Config = (Int, Int) -- TBD
type App    = ReaderT Config

setup :: AG m w e => w -> App m ()
setup w = void $ do
    button <- lift $ gButton "foo"
    body   <- lift $ gGetBody w
    lift $ gAdd (gLift body) [gLift button]

-- start :: Int -> String -> IO ()
-- start port staticPath = startGUI defaultConfig {
--         jsPort   = Just port,      -- Port on which to run.
--         jsStatic = Just staticPath -- Directory path for static content.
--     } setup
