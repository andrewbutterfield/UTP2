module UTP2.GUI.Threepenny.TheoryGraph where

import qualified Clay
import           Control.Monad.Reader                   (ask)
import           Data.Tree
import qualified Graphics.UI.Threepenny                 as UI
import           Graphics.UI.Threepenny.Core
import           Graphics.UI.Threepenny.Ext.Contextmenu
import           Graphics.UI.Threepenny.Ext.Flexbox
import qualified UTP2.GUI.Threepenny.Style              as Style
import           UTP2.GUI.Threepenny.Types
import           UTP2.GUI.Threepenny.Warn

-- | TGTree and TGNode are defined in Types.

-- | An element representing the given tree.
tree :: TGTree -> UI Element
tree tree' = do
  -- Map each level of the tree to a row of elements.
  let rows = map row' (levels tree')
  flex_c UI.div (flexDirection Clay.column) rows

-- | An element representing a row of the tree.
row' :: [TGNode] -> UI Element
row' nodes =
  flex_c UI.div (justifyContent Clay.spaceAround) $ map node nodes

-- | An element representing a node of the tree.
node :: TGNode -> UI Element
node (text, action) = Style.box # set UI.text text

-- | Create a new theory, attached to the root theory, which is displayed in the
-- theory graph.
createNewTheoryFromRoot :: String -> UTP2 ()
createNewTheoryFromRoot text = do
  currentTree <- currentTGTree
  warn "TODO Creating a new theory should be hooked into backend."
  case currentTree of
    Nothing                 -> warn "No Theory Tree to add to."
    Just (Node root ts) -> do
      emit <- eTheoryGraphEmit <$> ask
      liftIO $ emit $ Just $ Node root $ Node (text, pure ()) [] : ts
