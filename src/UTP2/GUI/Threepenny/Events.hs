module UTP2.GUI.Threepenny.Events where

-- |Events not provided by the Threepenny library.

import           Control.Monad (void)
import           Graphics.UI.Threepenny.Core

-- |change event.
change :: Element -> Event ()
change = void . domEvent "change"
