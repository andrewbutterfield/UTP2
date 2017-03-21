module UTP2.GUI.Threepenny.Home where

import qualified ContextMenu                     as CM
import           Control.Monad.Trans.Class       (lift)
import qualified Graphics.UI.Threepenny          as UI
import           Graphics.UI.Threepenny.Core
import qualified UTP2.GUI.Threepenny.Materialize as Mat
import           UTP2.GUI.Threepenny.Text
import           UTP2.GUI.Threepenny.Types
import qualified UTP2.GUI.Threepenny.Workspace   as W

-- |Home window.
mkHome :: UTP2 Element
mkHome = do
  W.currentWorkspace'
  topEl       <- lift $ UI.div
  workspaceEl <- W.workspace
  theoriesEl  <- mkTheories
  proofsEl    <- mkProofs
  lift $ element topEl #+ map element [workspaceEl, theoriesEl, proofsEl]

-- |Theories in the home window.
mkTheories :: UTP2 Element
mkTheories = do
  top  <- lift $ UI.div
  text <- textI "Theories"
  box  <- lift $ UI.div # set UI.style [("border", "1px solid black")]
                        # set UI.style [("width", "100vw"), ("min-height", "100px")]
  lift $ element top #+ map element [top, text, box]

-- |Proofs in the home window.
mkProofs :: UTP2 Element
mkProofs = do
  top    <- lift $ UI.div
  text   <- textI "Proofs"
  lift $ CM.contextMenu [
      CM.actionMenuItem "Create new theory"          []
    , CM.actionMenuItem "Save all modified theories" []
    ] text
  button <- Mat.button "."
  lift $ element top #+ map element [text, button]
