module UTP2.GUI.Threepenny.FileSystem where

-- |Elements and functions for interacting with the file system.

import           Control.Monad.Trans.Class      (lift)
import qualified Graphics.UI.Threepenny         as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Attributes
import           UTP2.GUI.Threepenny.Events
import           UTP2.GUI.Threepenny.Types

-- |Returns a file selector element that emits the updated value on change.
fileSelector :: String -> UTP2 (Handler (Maybe String)) -> UTP2 Element
fileSelector text emitter = do
  id_      <- uniqueId
  selector <- lift $ UI.input # set UI.type_ "file"
                              # set UI.text  text
                              # set UI.id_   id_
  emit <- emitter
  path <- lift $ on change selector $ const $ do
    filepath <- selectorPath id_
    liftIO $ emit $ Just filepath
  return selector

-- |Given the ID of a file selector, returns its current value.
selectorPath :: String -> UI String
selectorPath id = callFunction $
  ffi "$(%1)[0].files[0].path" $ "#" ++ id

-- sffi :: (Show a, FFI b) => a -> String -> b
-- sffi other = ffi . safe
--   where safe s = concat [
--             "var result = " ++ show s
--           , "if (result === null || result == undefined)"
--           ,   "return " ++ show other
--           , "return result"
--           ]

-- |Variant of 'fileSelector' that only allows the selection of directories.
dirSelector :: String -> UTP2 (Handler (Maybe String)) -> UTP2 Element
dirSelector text emitter = do
  selector <- fileSelector text emitter
  lift $ element selector # set webkitdirectory True
  return selector
