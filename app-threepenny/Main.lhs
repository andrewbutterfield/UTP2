\begin{code}
module Main where

import System.Environment  (getArgs)
import System.IO
import UTP2.GUI.Threepenny (start)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  [port] <- getArgs
  start (read port)
\end{code}
