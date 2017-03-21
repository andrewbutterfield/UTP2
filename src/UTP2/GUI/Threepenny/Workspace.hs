module UTP2.GUI.Threepenny.Workspace where

import           Control.Monad                   (void)
import           Control.Monad.Reader            (ask)
import           Control.Monad.Trans.Class       (lift)
import qualified Graphics.UI.Threepenny          as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Events
import           UTP2.GUI.Threepenny.FileSystem
import qualified UTP2.GUI.Threepenny.Materialize as Mat
import           UTP2.GUI.Threepenny.Text
import           UTP2.GUI.Threepenny.Types

-- |Element that displays the current workspace.
workspace :: UTP2 Element
workspace = do
  textEl            <- textB "" -- Text from behavior.
  workspaceBehavior <- eWorkspaceBehavior <$> ask
  -- Text based on current value of workspace.
  let textBehavior =
        maybe "No workspace selected" (\w -> "Workspace: " ++ show w)
        <$> workspaceBehavior
  -- Button to select workspace.
  buttonEl <- Mat.button "Select workspace"
  on_ UI.click buttonEl $ const openWorkspaceSelector
  lift $ element textEl # sink UI.text textBehavior
  lift $ UI.div #+ map element [textEl, buttonEl]

-- |Returns the current workspace, opening the workspace selector if no
-- workspace is selected.
currentWorkspace' :: UTP2 (Maybe String)
currentWorkspace' = do
  mayWorkspace <- currentWorkspace
  case mayWorkspace of
    Just workspace -> return mayWorkspace
    Nothing        -> openWorkspaceSelector >> return Nothing

-- |Opens the modal for selecting a workspace.
openWorkspaceSelector :: UTP2 ()
openWorkspaceSelector = do
  modalId <- readWorkspaceModalId
  case modalId of
    Just modalId -> lift $ Mat.openModal modalId
    Nothing      -> do
      h4       <- lift $ UI.h4 # set UI.text "Select a workspace"
      selector <- dirSelector "select" $ eWorkspaceEmit <$> ask
      modalId  <- Mat.modal $ map element [h4, selector]
      setWorkspaceModalId modalId
      openWorkspaceSelector
