module UTP2.GUI.Threepenny.Home where

import           ContextMenu                     (MenuItem)
import qualified ContextMenu                     as CM
import           Control.Monad.Reader            (ask)
import           Control.Monad.Trans.Class       (lift)
import qualified Graphics.UI.Threepenny          as UI
import           Graphics.UI.Threepenny.Core
import qualified UTP2.GUI.Threepenny.Materialize as Mat
import           UTP2.GUI.Threepenny.Types
import           UTP2.GUI.Threepenny.Util

-- |Home window.
mkHome :: UTP2 Element
mkHome = do
  liftIO $ putStrLn "Workspace not yet selected"
  top       <- lift $ UI.div
  workspace <- currentWorkspace'
  text      <- workspaceText
  theories  <- mkTheories
  proofs    <- mkProofs
  selector  <- fileSelector "Selector" []
  lift $ element top #+ map element [text, theories, proofs, selector]

workspaceText :: UTP2 Element
workspaceText = do
  textEl     <- textB "No workspace selected"
  workspaceB <- eWorkspaceB <$> ask
  let textB =
        fmap (maybe ("no workspace") (\w -> "Workspace: " ++ show w)) workspaceB
  lift $ element textEl # sink UI.text textB
  return textEl

-- |Description of current workspace, if selected.
currentWorkspace' :: UTP2 (Maybe String)
currentWorkspace' = do
  mayWorkspace <- currentWorkspace
  liftIO $ putStrLn $ "Current workspace: " ++ show mayWorkspace
  case mayWorkspace of
    Just workspace -> return mayWorkspace
    Nothing        -> do
      openWorkspaceSelector
      return Nothing

-- |Opens the modal for selecting a workspace.
openWorkspaceSelector :: UTP2 ()
openWorkspaceSelector = do
  modalId <- readWorkspaceModalId
  liftIO $ putStrLn $ "modalId"
  case modalId of
    Just modalId -> lift $ Mat.openModal modalId
    Nothing      -> do
      h4       <- lift $ UI.h4 # set UI.text "Select a workspace"
      selector <- fileSelector "select" [
        ]
      modalId  <- Mat.modal $ map element [h4, selector]
      setWorkspaceModalId modalId
      openWorkspaceSelector

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

