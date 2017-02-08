\begin{code}
module Main where

import UTP2.GUI
import System.Environment (getArgs)

main :: IO ()
main = do
    [port, static] <- getArgs
    runThreepenny (read port) static exampleApp (0, 0)
\end{code}
