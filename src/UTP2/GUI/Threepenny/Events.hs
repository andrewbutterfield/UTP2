module UTP2.GUI.Threepenny.Events where

-- |Events not provided by the Threepenny library.

import           Control.Monad               (void)
import           Control.Monad.Reader        (ask)
import           Control.Monad.Trans.Class   (lift)
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types

-- |change event.
change :: Element -> Event ()
change = void . domEvent "change"

-- |Wrapper around Threepenny's 'on' that runs in the UTP2 monad.
on_ :: (element -> Event a) -> element -> (a -> UTP2 ()) -> UTP2 ()
on_ event el run = do
  env <- ask
  lift $ on event el $ \a ->
    runUTP2 (run a) env
