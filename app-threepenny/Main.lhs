\begin{code}
module Main where

import Control.Concurrent  (forkIO, threadDelay)
import Control.Monad       (void)
import Paths_UTP2          (getDataFileName)
import System.Environment  (getArgs)
import System.Process      (spawnProcess)
import UTP2.GUI.Threepenny (start)

main :: IO ()
main = do
    [portArg] <- getArgs
    let port = read portArg
    forkIO $ void $ do
        threadDelay $ 1 * 1000000 -- 1 second
        electronMain <- getDataFileName "electron.js"
        spawnProcess "./node_modules/.bin/electron" [electronMain, portArg]
    start port
\end{code}
