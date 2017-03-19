module UTP2.GUI.Threepenny.Dom where

-- |DOM query or manipulation functions.

import           Control.Monad               (void)
import           Graphics.UI.Threepenny.Core

-- |Return the body of the current window.
getBody_ :: UI Element
getBody_ = askWindow >>= getBody

-- |Append the given elements to the body.
appendToBody :: [UI Element] -> UI ()
appendToBody els = void $ do
  body <- getBody_
  element body #+ els
