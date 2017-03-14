module UTP2.GUI.Threepenny.Types where

import           Control.Concurrent.MVar (MVar)
import qualified Control.Concurrent.MVar as MV
import           Control.Monad           (void)
import           Control.Monad.Reader    (ReaderT, ask, runReaderT)
import           Graphics.UI.Threepenny
import           Reactive.Threepenny
import           System.FilePath

-- |Enironment/config the app requires.
data Env = Env {
    eId               :: MVar Int
  , eWorkspace        :: MVar (Maybe String)
  , eWorkspaceB       :: Behavior (Maybe String)
  , eWorkspaceH       :: Handler  (Maybe String) 
  , eWorkspaceModalId :: MVar (Maybe String)
  }

-- |The initial environement.
initialEnv :: IO Env
initialEnv = do
  mId                               <- MV.newMVar 0
  mWorkspace                        <- MV.newMVar Nothing
  (eWorkspaceEvent, eWorkspaceEmit) <- newEvent
  eWorkspaceBehavior                <- stepper Nothing eWorkspaceEvent
  mWorkspaceModalId                 <- MV.newMVar Nothing
  return Env {
      eId               = mId
    , eWorkspace        = mWorkspace
    , eWorkspaceB       = eWorkspaceBehavior
    , eWorkspaceH       = eWorkspaceEmit
    , eWorkspaceModalId = mWorkspaceModalId
    }

-- |Return a unique ID.
uniqueId :: UTP2 String
uniqueId = do
  mId <- eId <$> ask
  id_ <- liftIO $ MV.modifyMVar mId (\i -> return (i + 1, i))
  return $ "UTP2-id-" ++ show id_

currentWorkspace :: UTP2 (Maybe String)
currentWorkspace = eWorkspaceB <$> ask >>= currentValue

emitWorkspace :: UTP2 (Handler (Maybe String))
emitWorkspace = eWorkspaceH <$> ask

-- |Read current workspace.
readWorkspace :: UTP2 (Maybe String)
readWorkspace = do
  mvar <- eWorkspace <$> ask
  liftIO $ MV.readMVar mvar

-- |Set current workspace.
setWorkspace :: String -> UTP2 ()
setWorkspace workspace = do
  mvar <- eWorkspace <$> ask
  liftIO $ MV.modifyMVar_ mvar $ const $ return $ Just workspace

-- |Read workspace modal ID.
readWorkspaceModalId :: UTP2 (Maybe String)
readWorkspaceModalId = do
  mvar <- eWorkspaceModalId <$> ask
  liftIO $ MV.readMVar mvar

-- |Set current workspace modal ID.
setWorkspaceModalId :: String -> UTP2 ()
setWorkspaceModalId modalId = do
  mvar <- eWorkspaceModalId <$> ask
  liftIO $ MV.modifyMVar_ mvar $ const $ return $ Just modalId

-- |Monad the app runs in.
type UTP2 a = ReaderT Env UI a

-- |Run the UTP2 monad.
runApp :: UTP2 a -> Env -> UI a
runApp = runReaderT

