module UTP2.GUI.Threepenny.Util where

import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types

-- Text ------------------------------------------------------------------------

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

-- Buttons ---------------------------------------------------------------------

-- |Materialize-styled button with given text.
mkButton :: String -> UTP2 Element
mkButton text =
  lift $ UI.button # set UI.class_ "waves-effect waves-light btn"
                   # set UI.text text
