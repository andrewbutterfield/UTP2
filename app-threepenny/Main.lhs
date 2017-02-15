\begin{code}
module Main where

import Control.Concurrent  (forkIO, threadDelay)
import Control.Monad       (void)
import System.Environment  (getArgs)
import System.Process      (spawnCommand)
import UTP2.GUI.Threepenny (start)

main :: IO ()
main = do
    [port, static] <- getArgs
    forkIO $ void $ do
        threadDelay $ 1 * 1000000 -- 1 second
        spawnCommand $ "electron electron.js " ++ port
    start (read port) static
\end{code}
