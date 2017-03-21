module UTP2.GUI.Threepenny.Text where

-- |Elements for displaying text.

import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types

-- |Element with given text and style.
styledText :: [(String, String)] -> String -> UTP2 Element
styledText style text = lift $ UI.div # set UI.text  text
                                      # set UI.style style

-- |Italics text.
textI :: String -> UTP2 Element
textI = styledText [("font-style", "italic")]

-- |Bold text.
textB :: String -> UTP2 Element
textB = styledText [("font-style", "bold")]
