module UTP2.GUI.Threepenny.Style where

-- |Utility functions for styling elements, including layout.

import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core

padding :: Int -> UI Element -> UI Element
padding n = set UI.style [("padding", show n ++ "px")]

smlPadding = padding 8
