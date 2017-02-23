module UTP2.GUI.Threepenny.Home where

import           Control.Monad.Reader        (ask)
import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types
import           UTP2.GUI.Threepenny.Util

-- |Home window.
mkHome :: UTP2 Element
mkHome = do
    top       <- lift $ UI.div
    workspace <- eWorkspace <$> ask
    text      <- textB $ "Workspace " ++ workspace
    theories  <- mkTheories
    proofs    <- mkProofs
    selector  <- fileSelector "Selector"
    lift $ element top #+ map element [text, theories, proofs, selector]

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
    button <- mkButton "."
    lift $ element top #+ map element [text, button]

