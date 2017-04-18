module UTP2.GUI.Threepenny.Monad where

import           Control.Monad.Reader        (ReaderT, runReaderT)
import           Control.Monad.Trans.Class   (lift)
import           Graphics.UI.Threepenny.Core

-- | Monad the app runs in.
type UTP2 a = ReaderT Env UI a

-- | Run the UTP2 monad.
runUTP2 :: UTP2 a -> Env -> UI a
runUTP2 = runReaderT

instance MonadUI (ReaderT Env UI) where
  liftUI = lift
