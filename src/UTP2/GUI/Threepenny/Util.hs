module UTP2.GUI.Threepenny.Util where

import           Control.Monad               (void)
import           Control.Monad.Trans.Class   (lift)
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core
import           UTP2.GUI.Threepenny.Types

-- Text ------------------------------------------------------------------------

-- |Element with given text and style.
styledText :: [(String, String)] -> String -> UTP2 Element
styledText style text = lift $ UI.div # set UI.text  text
                                      # set UI.style style

-- |Italics text.
textI :: String -> UTP2 Element
textI = styledText [("font-style", "italic")]

-- |Bold text.
textB :: String -> UTP2 Element
textB = styledText [("font-style", "bold")]


-- File Selection --------------------------------------------------------------

-- |Returns a file selector element that emits the updated value on change.
fileSelector :: String -> UTP2 (Handler (Maybe String)) -> UTP2 Element
fileSelector text emitter = do
  id_      <- uniqueId
  selector <- lift $ UI.input # set UI.type_ "file"
                              # set UI.text  text
                              # set UI.id_   id_
  emit <- emitter
  path <- lift $ on UI.valueChange selector $ const $ do
    filepath <- selectorPath id_
    liftIO $ emit $ Just filepath
    liftIO $ putStrLn $ "Emitted path: " ++ show (Just filepath)
  return selector

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

webkitdirectory = UI.emptyAttr "webkitdirectory"

dirSelector :: String -> UTP2 (Handler (Maybe String)) -> UTP2 Element
dirSelector text emitter = do
  selector <- fileSelector text emitter
  lift $ element selector # set webkitdirectory True
  return selector

-- DOM -------------------------------------------------------------------------

-- |Return the body of the current window.
getBody_ :: UI Element
getBody_ = askWindow >>= getBody

-- |Append the given elements to the body.
appendToBody :: [UI Element] -> UI ()
appendToBody els = void $ do
  body <- getBody_
  element body #+ els

