module UTP2.GUI.Threepenny.Util where

import           Control.Monad               (void)
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
mkButton text = lift $ UI.button # set UI.class_ "waves-effect waves-light btn"
                                 # set UI.text text

-- File Selection --------------------------------------------------------------

-- |Returns a file selector element that executes the given action on value
-- change of the file selector.
fileSelector :: String -> [String -> UI a] -> UTP2 Element
fileSelector text actions = do
    let id = "fileSelectorId"
    selector <- lift $ UI.input # set UI.type_ "file"
                                # set UI.text text
                                # set UI.id_ id
    lift $ on UI.valueChange selector $ const $ void $ do
      filepath <- selectorPath id
      liftIO $ putStrLn "File selected"
      liftIO $ putStrLn filepath
      mapM ($ filepath) actions
    return selector

selectorPath :: String -> UI String
selectorPath id = callFunction $
    ffi "document.getElementById(%1).files[0].path" id

