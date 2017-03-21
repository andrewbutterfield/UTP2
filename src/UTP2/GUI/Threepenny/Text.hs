module UTP2.GUI.Threepenny.Text where

-- |Elements for displaying text.

import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core

-- |Element with given text and style.
styledText :: [(String, String)] -> String -> UI Element
styledText style text = UI.div # set UI.text  text
                               # set UI.style style

-- |Italics text.
textI :: String -> UI Element
textI = styledText [("font-style", "italic")]

-- |Bold text.
textB :: String -> UI Element
textB = styledText [("font-style", "bold")]
