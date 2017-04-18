module UTP2.GUI.Threepenny.Home where

import           Control.Monad.Reader                   (ask)
import qualified Graphics.UI.Threepenny                 as UI
import           Graphics.UI.Threepenny.Core
import qualified Graphics.UI.Threepenny.Ext.Contextmenu as CM
import           UTP2.GUI.Threepenny.Events
import qualified UTP2.GUI.Threepenny.Materialize        as Mat
import qualified UTP2.GUI.Threepenny.Style              as Style
import           UTP2.GUI.Threepenny.Text
import qualified UTP2.GUI.Threepenny.TheoryGraph        as TG
import           UTP2.GUI.Threepenny.Types
import qualified UTP2.GUI.Threepenny.Workspace          as W

-- |Home window.
mkHome :: UTP2 Element
mkHome = do
  W.currentWorkspace'
  workspace <- W.workspace
  theories  <- mkTheories
  proofs    <- mkProofs
  liftUI $ UI.div #+ map element [workspace, theories, proofs]

-- |Theories in the home window.
mkTheories :: UTP2 Element
mkTheories = do
  top   <- liftUI $ UI.div
  text  <- liftUI $ textI "Theories"
  box   <- liftUI $ Style.box #
    set UI.style [("width", "90vw"), ("min-height", "100px")]
  theoryGraphBehavior <- eTheoryGraphBehavior <$> ask
  -- If the tree is not set display a message saying so.
  let treeBehavior = maybe (textB "No Theory Graph") (TG.tree)
                     <$> theoryGraphBehavior
  -- Add the current tree to 'box' now, and whenever the tree changes.
  liftUI $ nowAndOnChange treeBehavior $ \uiEl -> do
    uiEl >>= \el -> element box # set children [el]
  liftUI $ element top #+ map element [text, box]

-- |Proofs in the home window.
mkProofs :: UTP2 Element
mkProofs = do
  button <- Mat.button "."
  liftUI $ CM.contextMenu [
      CM.actionMenuItem "Create new theory"          []
    , CM.actionMenuItem "Save all modified theories" []
    ] button
  liftUI $ UI.div #+ [element button]
