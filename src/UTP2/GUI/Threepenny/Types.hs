module UTP2.GUI.Threepenny.Types where

import           Control.Monad          (void)
import           Control.Monad.Reader
import           Graphics.UI.Threepenny

-- |Enironment/config the app requires.
data Env = Env { eWorkspace :: FilePath }

-- |Monad the app runs in.
type UTP2 a = ReaderT Env UI a

-- |Run the UTP2 monad.
runApp :: UTP2 a -> Env -> UI a
runApp = runReaderT
