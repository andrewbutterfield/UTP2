module UTP2.GUI.Threepenny.Style where

-- | Utility functions for styling elements, including layout.

import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core

sml = 4
med = sml * 2
lrg = med * 2

setBorder :: UI Element -> UI Element
setBorder = set UI.style [
    ("border"        , "1px solid black")
  , ("border-radius" , px sml           )
  ]

setPadding :: (Num a, Show a) => a -> UI Element -> UI Element
setPadding x = set UI.style [("padding", px x)]

-- | Convert to pixel string.
px :: (Num a, Show a) => a -> String
px x = show x ++ "px"

-- | A div with black border and padding.
box :: UI Element
box = UI.div # setPadding sml # setBorder
