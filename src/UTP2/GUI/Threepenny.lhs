\begin{code}

module UTP2.GUI.Threepenny (start) where

import           Control.Concurrent.MVar
import           Control.Monad                (void)
import           Control.Monad.Reader
import qualified Graphics.UI.Threepenny       as UI
import           Graphics.UI.Threepenny.Core

start :: Int -> String -> IO ()
start port staticPath = startGUI defaultConfig {
        jsPort   = Just port,      -- Port on which to run.
        jsStatic = Just staticPath -- Directory path for static content.
    } setup

-- |Initial setup of the webpage.
setup :: Window -> UI ()
setup window = do
    return window # set UI.title "UTP²"
    UI.addStyleSheet window "materialize.css"
    threepennyGui window

-- |Entry point for core GUI logic, assumes initial window setup.
threepennyGui :: Window -> UI ()
threepennyGui window = void $ do
    top    <- mkTop
    button <- mkButton "hello"
    getBody window #+ map element [top, button]

mkTop :: UI Element
mkTop = UI.div # set UI.style [("border", "1px black")]

-- |Returns a materialize-styled button with given text.
mkButton :: String -> UI Element
mkButton text = UI.button # set UI.class_ "waves-effect waves-light btn"
                          # set UI.text text
\end{code}
