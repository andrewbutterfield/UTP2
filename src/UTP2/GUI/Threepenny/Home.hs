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
  workspace <- W.workspace
  theories  <- mkTheories
  proofs    <- mkProofs
  lift $ UI.div #+ map element [workspace, theories, proofs]

-- |Theories in the home window.
mkTheories :: UTP2 Element
mkTheories = do
  top  <- lift $ UI.div
  text <- lift $ textI "Theories"
  box  <- lift $ UI.div # set UI.style [("border", "1px solid black")]
                        # set UI.style [("width", "80vw"), ("min-height", "100px")]
  lift $ element top #+ map element [top, text, box]

-- |Proofs in the home window.
mkProofs :: UTP2 Element
mkProofs = do
  button <- Mat.button "."
  lift $ CM.contextMenu [
      CM.actionMenuItem "Create new theory"          []
    , CM.actionMenuItem "Save all modified theories" []
    ] button
  lift $ UI.div #+ [element button]
