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

-- |Returns a file selector element that executes the given action on value
-- change of the file selector.
fileSelector :: String -> [String -> UI a] -> UTP2 Element
fileSelector text actions = do
  let id = "fileSelectorId"
  selector <- lift $ UI.input # set UI.type_ "file"
                              # set UI.text  text
                              # set UI.id_   id
  lift $ on UI.valueChange selector $ const $ void $ do
    filepath <- selectorPath id
    liftIO $ putStrLn "File selected"
    liftIO $ putStrLn filepath
    mapM ($ filepath) actions
  return selector

selectorPath :: String -> UI String
selectorPath id = callFunction $
    ffi "$(%1).files[0].path" $ "#" ++ id

dirSelector :: String -> [String -> UI a] -> UTP2 Element
dirSelector text actions = do
  selector <- fileSelector text actions
  -- lift $ element selector # set UI.
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

-- Tabs ------------------------------------------------------------------------

-- |Attach tabs to the body. An "id" will be set on each of the given elements.
tabs :: [(String, UI Element)] -> UTP2 ()
tabs els = do
  els'       <- mapM addId els
  tabEls     <- lift $ mapM tab     els'
  tabsEl     <- lift $ UI.div # set UI.class_ "row" #+ [
      UI.div # set UI.class_ "col s12" #+ [
        UI.ul # set UI.class_ "tabs" #+ map element tabEls    
      ]
    ]
  contentEls <- lift $ mapM content els'
  lift $ appendToBody $ map element $ [tabsEl] ++ contentEls
  return ()
  -- Create unique "id" for each tab content.
  where addId (title, el) = do
          id' <- uniqueId
          return (title, el, id')
  -- Create each tab.
        tab (title, el, id') = do
          a <- UI.a  # set UI.href  ("#" ++ id')
                     # set UI.text  title
          UI.li # set UI.class_ "tab" #+ [element a]
  -- Create each content page.
        content (title, el, id') = UI.div # set UI.id_ id' #+ [el] 
  
