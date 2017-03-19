module UTP2.GUI.Threepenny.Materialize where

-- |Elements provided by the Materialize CSS library.

import           Control.Monad               (void)
import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Dom
import           UTP2.GUI.Threepenny.Types
import           UTP2.GUI.Threepenny.Util

-- Button ----------------------------------------------------------------------

-- |Materialize-styled button with given text.
button :: String -> UTP2 Element
button text = lift $ UI.button # set UI.class_ "waves-effect waves-light btn"
                               # set UI.text text

-- Modal -----------------------------------------------------------------------

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

-- Tabs ------------------------------------------------------------------------

-- |Materialize-styled tabs with given titles and content.
tabs :: [(String, UI Element)] -> UTP2 Element
tabs els = do
  els'       <- mapM addId els
  tabEls     <- lift $ mapM tab els'
  tabsEl     <- lift $ UI.div # set UI.class_ "row" #+ [
      UI.div # set UI.class_ "col s12" #+ [
        UI.ul # set UI.class_ "tabs" #+ map element tabEls
      ]
    ]
  contentEls <- lift $ mapM content els'
  lift $ UI.div #+ (map element $ [tabsEl] ++ contentEls)
  -- Create unique "id" for each tab content.
  where addId (title, el) = uniqueId >>= \id' -> return (title, el, id')
  -- Create each tab.
        tab (title, el, id') = do
          a <- UI.a  # set UI.href  ("#" ++ id')
                     # set UI.text  title
          UI.li # set UI.class_ "tab" #+ [element a]
  -- Create each content page.
        content (_, el, id') = UI.div # set UI.id_ id' #+ [el]

-- |Initialize tabs. Must be attached to the body.
initTabs :: UI ()
initTabs = runFunction $ ffi "$(%1).tabs()" "ul.tabs"
