module UTP2.GUI.Threepenny.TheoryGraph where

import qualified Clay
import           Data.Tree
import qualified Graphics.UI.Threepenny                 as UI
import           Graphics.UI.Threepenny.Core
import           Graphics.UI.Threepenny.Ext.Contextmenu
import           Graphics.UI.Threepenny.Ext.Flexbox
import           UTP2.GUI.Threepenny.Types

nodeStyle = [
    ("border"       , "1px solid black" )
  , ("border-radius", "2px"             )
  , ("padding"      , "5px"             )
  ]

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
node (text, action) =
  UI.div # set UI.style nodeStyle
         # set UI.text text
