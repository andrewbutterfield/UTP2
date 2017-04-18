module UTP2.GUI.Threepenny.Style where

-- | Utility functions for styling elements, including layout.

import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core

sml = 8
med = sml * 2
lrg = med * 2

setPadding :: (Num a, Show a) => a -> UI Element -> UI Element
setPadding x = set UI.style [("padding", px x)]

-- | Convert to pixel string.
px :: (Num a, Show a) => a -> String
px x = show x ++ "px" 

-- | A div with black border and padding. 
-- box :: UI Element
-- box = padding smlPadding
