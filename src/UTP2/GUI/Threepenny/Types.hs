module UTP2.GUI.Threepenny.Types where

-- |Types and functions relating to the UTP2 monad.

import           Control.Concurrent.MVar (MVar)
import qualified Control.Concurrent.MVar as MV
import           Control.Monad           (void)
import           Control.Monad.Reader    (ReaderT, ask, runReaderT)
import           GIFiles
import           Graphics.UI.Threepenny
import           Reactive.Threepenny
import           System.FilePath
import           WxState                 (FileState)

-- |Enironment/config the app requires.
data Env = Env {
    eId                :: MVar Int
  , eWorkspaceBehavior :: Behavior (Maybe String)
  , eWorkspaceEmit     :: Handler  (Maybe String)
  , eWorkspaceModalId  :: MVar (Maybe String)
  , eFstate            :: MVar FileState
  }

-- |The initial environement.
initialEnv :: IO Env
initialEnv = do
  mId                               <- MV.newMVar 0
  (eWorkspaceEvent, eWorkspaceEmit) <- newEvent
  eWorkspaceBehavior                <- stepper Nothing eWorkspaceEvent
  mWorkspaceModalId                 <- MV.newMVar Nothing
  (_uname, fstate)                  <- GIFiles.systemFilePaths
  fstateMV                          <- MV.newMVar fstate
  return Env {
      eId                = mId
    , eWorkspaceBehavior = eWorkspaceBehavior
    , eWorkspaceEmit     = eWorkspaceEmit
    , eWorkspaceModalId  = mWorkspaceModalId
    , eFstate            = fstateMV
    }

-- |Return a unique ID.
uniqueId :: UTP2 String
uniqueId = do
  mId <- eId <$> ask
  id' <- liftIO $ MV.modifyMVar mId (\i -> return (i + 1, i))
  return $ "UTP2-id-" ++ show id'

-- |The current workspace.
currentWorkspace :: UTP2 (Maybe String)
currentWorkspace = eWorkspaceBehavior <$> ask >>= currentValue

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

-- |Read the current FileState.
readFileState :: UTP2 FileState
readFileState = do
  mvar <- eFstate <$> ask
  liftIO $ MV.readMVar mvar

-- |Monad the app runs in.
type UTP2 a = ReaderT Env UI a

-- |Run the UTP2 monad.
runUTP2 :: UTP2 a -> Env -> UI a
runUTP2 = runReaderT

