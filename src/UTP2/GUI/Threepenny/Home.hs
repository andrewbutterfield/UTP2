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
  currentWorkspace'
  top       <- lift $ UI.div
  text      <- workspaceText
  theories  <- mkTheories
  proofs    <- mkProofs
  lift $ element top #+ map element [text, theories, proofs]

-- |Element that displays the current workspace.
workspaceText :: UTP2 Element
workspaceText = do
  textEl            <- textB ""
  workspaceBehavior <- eWorkspaceBehavior <$> ask
  let textBehavior =
        maybe "No workspace selected" (\w -> "Workspace: " ++ show w)
        <$> workspaceBehavior
  lift $ element textEl # sink UI.text textBehavior
  return textEl

-- |Wrapper around `currentWorkspace` which open the workspace selector if no
-- workspace is selected.
currentWorkspace' :: UTP2 (Maybe String)
currentWorkspace' = do
  mayWorkspace <- currentWorkspace
  liftIO $ putStrLn $ "Current workspace: " ++ show mayWorkspace
  case mayWorkspace of
    Just workspace -> return mayWorkspace
    Nothing        -> openWorkspaceSelector >> return Nothing

-- |Opens the modal for selecting a workspace.
openWorkspaceSelector :: UTP2 ()
openWorkspaceSelector = do
  modalId <- readWorkspaceModalId
  liftIO $ putStrLn $ "modalId"
  case modalId of
    Just modalId -> lift $ Mat.openModal modalId
    Nothing      -> do
      h4       <- lift $ UI.h4 # set UI.text "Select a workspace"
      selector <- dirSelector "select" $ eWorkspaceEmit <$> ask
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

