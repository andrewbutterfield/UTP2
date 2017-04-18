module UTP2.GUI.Threepenny.Types where

-- | Types and functions relating to the UTP2 monad.

-- To help avoid import cycles some other types are also defined here.

import           Control.Concurrent.MVar     (MVar)
import qualified Control.Concurrent.MVar     as MV
import           Control.Monad               (void)
import           Control.Monad.Reader        (ReaderT, ask, runReaderT)
import           Control.Monad.Trans.Class   (lift)
import           Data.Tree
import           GIFiles
import           Graphics.UI.Threepenny.Core
import           Reactive.Threepenny
import           System.FilePath
import           WxState                     (FileState)

-- | Monad the app runs in.
type UTP2 a = ReaderT Env UI a

-- | Run the UTP2 monad.
runUTP2 :: UTP2 a -> Env -> UI a
runUTP2 = runReaderT

instance MonadUI (ReaderT Env UI) where
  liftUI = lift

-- | A unique ID string.
--
-- We keep track of a mutable int I. Whenever an ID is requested we use a
-- combination of a predefined string and I's current value, and increment I.
uniqueId :: UTP2 String
uniqueId = do
  mId <- eId <$> ask
  id' <- liftIO $ MV.modifyMVar mId (\i -> return (i + 1, i))
  return $ "UTP2-id-" ++ show id'

-- | Environment/config data for the app. Everything should be mutable data.
--
-- Behaviors represent a dynamic value which can change over time. The Handlers
-- or eXEmit functions can be used to "emit" a new value for a Behavior.
data Env = Env {
    eId                  :: MVar Int
  , eTheoryGraphBehavior :: Behavior (Maybe TGTree)
  , eTheoryGraphEmit     :: Handler  (Maybe TGTree)
  , eWorkspaceBehavior   :: Behavior (Maybe String)
  , eWorkspaceEmit       :: Handler  (Maybe String)
  , eWorkspaceModalId    :: MVar (Maybe String)
  , eFstate              :: MVar FileState
  }

-- Non-core types --------------------------------------------------------------

-- | Theory graph tree node.
type TGNode = (String, UI ())

-- | Theory graph tree.
type TGTree = Tree TGNode

-- Initial data ----------------------------------------------------------------

-- | The initial environment.
initialEnv :: IO Env
initialEnv = do
  mId                                   <- MV.newMVar 0
  (eTheoryGraphEvent, eTheoryGraphEmit) <- newEvent
  eTheoryGraphBehavior                  <- stepper mockInitTheoryGraph eTheoryGraphEvent
  (eWorkspaceEvent, eWorkspaceEmit)     <- newEvent
  eWorkspaceBehavior                    <- stepper Nothing eWorkspaceEvent
  mWorkspaceModalId                     <- MV.newMVar Nothing
  (_, fstate)                           <- GIFiles.systemFilePaths
  fstateMV                              <- MV.newMVar fstate
  return Env {
      eId                  = mId
    , eTheoryGraphBehavior = eTheoryGraphBehavior
    , eTheoryGraphEmit     = eTheoryGraphEmit
    , eWorkspaceBehavior   = eWorkspaceBehavior
    , eWorkspaceEmit       = eWorkspaceEmit
    , eWorkspaceModalId    = mWorkspaceModalId
    , eFstate              = fstateMV
    }

-- | Initial MOCK data for theory graph, consists of a single root node.
mockInitTheoryGraph :: Maybe TGTree
mockInitTheoryGraph = Just $ Node ("_ROOT$0", pure ()) []

-- Helpers for reading/setting from ENV ----------------------------------------

-- | The current theory graph tree.
currentTGTree :: UTP2 (Maybe TGTree)
currentTGTree = eTheoryGraphBehavior <$> ask >>= currentValue

-- | The current workspace.
currentWorkspace :: UTP2 (Maybe String)
currentWorkspace = eWorkspaceBehavior <$> ask >>= currentValue

-- | Read workspace modal ID.
readWorkspaceModalId :: UTP2 (Maybe String)
readWorkspaceModalId = do
  mvar <- eWorkspaceModalId <$> ask
  liftIO $ MV.readMVar mvar

-- | Set current workspace modal ID.
setWorkspaceModalId :: String -> UTP2 ()
setWorkspaceModalId modalId = do
  mvar <- eWorkspaceModalId <$> ask
  liftIO $ MV.modifyMVar_ mvar $ const $ return $ Just modalId

-- | Read the current FileState.
readFileState :: UTP2 FileState
readFileState = do
  mvar <- eFstate <$> ask
  liftIO $ MV.readMVar mvar

