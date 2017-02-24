module UTP2.GUI.Threepenny.Types where

import           Control.Concurrent.MVar (MVar)
import qualified Control.Concurrent.MVar as MV
import           Control.Monad           (void)
import           Control.Monad.Reader
import           Graphics.UI.Threepenny

-- |Enironment/config the app requires.
data Env = Env { eId :: MVar Int }

-- |The initial environement.
initialEnv :: IO Env
initialEnv = do
  mId <- MV.newMVar 0
  return Env { eId = mId }

-- |Returns a unique ID.
uniqueId :: UTP2 String
uniqueId = do
  mId <- eId <$> ask
  id_ <- liftIO $ MV.modifyMVar mId (\i -> return (i + 1, i))
  return $ "UTP2-id-" ++ show id_

-- |Monad the app runs in.
type UTP2 a = ReaderT Env UI a

-- |Run the UTP2 monad.
runApp :: UTP2 a -> Env -> UI a
runApp = runReaderT
