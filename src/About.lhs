\section{About \UTP2}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module About where
import DataText
import Data.List
import System.Info
import Data.Version
\end{code}

\subsection{Program Name \& Version}

\begin{code}
progname = "U(TP)^2"
fullname = progname ++ " v" ++ version
\end{code}

\textbf{v0.98$\alpha$8, from 18th Feb 2015}
\begin{code}
version = "0.98a8(2015-02-18+)"
\end{code}

\subsection{About Text}

\begin{code}
aboutText
  = unlines [fullname
            ,"    a.k.a. Saoith\237n ('See-heen')"
            ,""
            ,"2nd-order Equational-Reasoning Proof-Assistant"
            ,"for Unifying Theories of Programming (UTP)"
            ,""
            ,"(c) 2007-15 Andrew Butterfield"
            ," with thanks to :"
            ,"  Andrew Anderson, Colm Bhandal, Simon Dardis,"
            ,"  Ian Fitzpatrick, Karen Forde, Luke McGuinness"
            ,""
            ,"Licensed under GPL v2 - see COPYING.txt"
            ,""
            ,"built ("++build++") using:"
            ,"  wxHaskell"
            ,"  Parsec"
            ,"  Jaza"
            ,""
            ,[ pFocusStart, eFocusStart, eFocusEnd, pFocusEnd
             , ' '
             , beginPFocus, beginEFocus, deepFocus, endEFocus, endPFocus
             ]
            ]
 where
   build = arch +-+ os +-+ compilerName +-+ cv
   cv = concat
        $ intersperse "."
        $ map show
        $ versionBranch System.Info.compilerVersion
   s +-+ t = s ++ "-" ++ t
\end{code}
