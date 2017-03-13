\begin{code}
module Main where

import System.Environment  (getArgs)
import System.IO
import UTP2.GUI.Threepenny (start)

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  [port] <- getArgs
  start (read port)
\end{code}
