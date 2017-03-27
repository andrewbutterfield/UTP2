module UTP2.GUI.Threepenny.Workspace where

import           Clay                               (center, inlineFlex)
import           Control.Monad                      (void)
import           Control.Monad.Reader               (ask)
import           Control.Monad.Trans.Class          (lift)
import qualified Graphics.UI.Threepenny             as UI
import           Graphics.UI.Threepenny.Core
import           Graphics.UI.Threepenny.Ext.Flexbox as Flex
import qualified UTP2.GUI.Threepenny.Engine.Files   as EF
import           UTP2.GUI.Threepenny.Events
import           UTP2.GUI.Threepenny.FileSystem
import           UTP2.GUI.Threepenny.Materialize    (ModalId)
import qualified UTP2.GUI.Threepenny.Materialize    as Mat
import           UTP2.GUI.Threepenny.Text
import           UTP2.GUI.Threepenny.Types

-- |Element that displays the current workspace.
workspace :: UTP2 Element
workspace = do
  -- Text for the text element is taken from the workspace behavior.
  textEl            <- lift $ textB "" #
    set UI.style [("padding-right", "16px")]
  workspaceBehavior <- eWorkspaceBehavior <$> ask
  -- Text based on current value of workspace.
  let textBehavior =
        maybe "No workspace selected" (\w -> "Workspace: " ++ show w)
        <$> workspaceBehavior
  -- Button to select workspace.
  buttonEl <- Mat.button "Select workspace"
  on_ UI.click buttonEl $ const openWorkspaceSelector
  lift $ element textEl # sink UI.text textBehavior
  lift $ Flex.flex_c UI.div ((display inlineFlex) { pAlignItems = center }) $
    map element [textEl, buttonEl]

-- |Returns the current workspace, opening the workspace selector if no
-- workspace is selected.
currentWorkspace' :: UTP2 (Maybe String)
currentWorkspace' = do
  mayWorkspace <- currentWorkspace
  case mayWorkspace of
    Just workspace -> return mayWorkspace
    Nothing        -> openWorkspaceSelector >> return Nothing

-- |Opens the modal for selecting a workspace. If no modal element has yet been
-- created, we create one.
openWorkspaceSelector :: UTP2 ()
openWorkspaceSelector = do
  modalId <- readWorkspaceModalId
  case modalId of
    Just modalId -> lift $ Mat.openModal modalId
    -- |If a workspace selector element hasn't been created yet.
    Nothing      -> do
      modalId <- workspaceSelector
      setWorkspaceModalId modalId
      openWorkspaceSelector

-- |Create a workspace selector which resides in a modal. The modal is attached
-- to the document body.
workspaceSelector :: UTP2 ModalId
workspaceSelector = do
  h4       <- lift $ UI.h4 # set UI.text "Select a workspace"
  selector <- dirSelector "select" $ eWorkspaceEmit <$> ask
  workspaceBehavior <- eWorkspaceBehavior <$> ask
  -- |Run startup file handling once a workspace is selected.
  onChanges_ workspaceBehavior $ \mayWorkspace -> do
    case mayWorkspace of
      Nothing        -> liftIO $ putStrLn "No workspace selected"
      Just workspace -> EF.startupFileHandling workspace
  Mat.modal $ map element [h4, selector]
