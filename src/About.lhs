\section{About \UTP2}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
{-# LANGUAGE CPP #-}
module About where
import DataText
import Data.List
import System.Info
import Data.Version
\end{code}

\subsection{Program Name \& Version}

\textbf{v0.99$\alpha$3, from 18th Mar 2017}
\begin{code}
version = "0.99a3(2017-03-18+)"
\end{code}

\begin{code}
#ifndef mingw32_HOST_OS
progname = "U\xb7(TP)\178"
#endif
#ifdef mingw32_HOST_OS
progname = "U(TP)^2"
#endif
fullname = progname ++ " v" ++ version
\end{code}


\subsection{About Text}

\begin{code}
aboutText
  = unlines [fullname
            ,"(UTP2 for short)"
            ,""
            ,"2nd-order Equational-Reasoning Proof-Assistant"
            ,"for Unifying Theories of Programming (UTP)"
            ,""
            ,"(c) 2007-17 Andrew Butterfield"
            ," with thanks to :"
            ,"  Andrew Anderson, Colm Bhandal, Simon Dardis,"
            ,"  Ian Fitzpatrick, Karen Forde, Luke McGuinness"
            ,""
            ,"Licensed under BSD-3-Clause - see licence/BSD3.txt"
            ,""
            ,"built ("++build++") using:"
            ,"  wxHaskell"
            ,"  Parsec"
            ]
 where
   build = arch +-+ os +-+ compilerName +-+ cv
   cv = concat
        $ intersperse "."
        $ map show
        $ versionBranch System.Info.compilerVersion
   s +-+ t = s ++ "-" ++ t
\end{code}
