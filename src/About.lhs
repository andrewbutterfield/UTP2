\section{About \UTP2}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
{-# LANGUAGE CPP #-}
module About where
import DataText
import Data.List
import System.Info
import Data.Version
import NiceSymbols
\end{code}

\subsection{Program Name \& Version}

\textbf{v0.99$\alpha$4, from 23rd Mar 2017}
\begin{code}
version = "0.99a4(2017-03-23+)"
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
            ,""
            ,"Effects Tests"
            ,"x "++_in++" S "++_implies++" "++_lnot++"( y "++_in++" T)"
            , mathBold "mathBold"
            , mathSansBold "mathSansBold"
            , _mathcal "MATHCAL"
            , _mathbb "MATHBB"
            ]
 where
   build = arch +-+ os +-+ compilerName +-+ cv
   cv = concat
        $ intersperse "."
        $ map show
        $ versionBranch System.Info.compilerVersion
   s +-+ t = s ++ "-" ++ t
\end{code}
