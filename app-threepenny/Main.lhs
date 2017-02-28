\begin{code}
module Main where

import System.Environment  (getArgs)
import UTP2.GUI.Threepenny (start)

main :: IO ()
main = do
    [port] <- getArgs
    start (read port)
\end{code}
