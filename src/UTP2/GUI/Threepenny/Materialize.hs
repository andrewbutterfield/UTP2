module UTP2.GUI.Threepenny.Materialize where

import           Control.Monad               (void)
import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types
import           UTP2.GUI.Threepenny.Util

-- |Materialize-styled button with given text.
button :: String -> UTP2 Element
button text = lift $ UI.button # set UI.class_ "waves-effect waves-light btn"
                               # set UI.text text

type ModalId = String

-- |Create a materialize-styled modal with given content. Can be opened by
-- passing the resulting ID to `openModal`.
modal :: [UI Element] -> UTP2 ModalId
modal els = do
    modalId <- uniqueId
    modal   <- lift $ UI.div # set UI.class_ "modal"
                             # set UI.id_    modalId
    content <- lift $ UI.div # set UI.class_ "modal-content"
    lift $ element content #+ els
    lift $ element modal   #+ [element content]
    lift $ appendToBody [element modal]
    lift $ initModal modalId
    return modalId

-- |Iniitialize a modal. Must be attached to the body.
initModal :: ModalId -> UI ()
initModal modalId = runFunction $
    ffi "$(%1).modal()" $ "#" ++ modalId

-- |Open the modal of given ID.
openModal :: ModalId -> UI ()
openModal modalId = runFunction $
    ffi "$(%1).modal(%2)" ("#" ++ modalId) "open"
