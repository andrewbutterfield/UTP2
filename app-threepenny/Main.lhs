\begin{code}
module Main where

import System.Environment (getArgs)
import UTP2.Threepenny

main :: IO ()
main = do
    [port, static] <- getArgs
    start (read port) static
\end{code}
