\section{\LaTeX\ Testing}

\begin{code}
module LaTeXTest where
import Tables
import Datatypes
import Heuristics
import DataText
import Manipulation
import Proof
import Theories
import DSL hiding (ii)
import LaTeXSetup
\end{code}

We build a theory simply to test the \LaTeX\ export/import facilitiies.


\subsection{\texttt{thryName,thrySeqNo :: String,Int}}
\begin{code}
ltx_thryName = "LaTeX-Test"
ltx_thrySeqNo = 99
\end{code}

\subsection{\texttt{typedefs :: Trie Type}}
\begin{code}
ltx_typedefs
 = lbuild
    [ ("Char",Z)
    , ("String",mkTseq (Tvar "Char"))
    ]
\end{code}

\subsection{\texttt{consts :: Trie Expr}}
\begin{code}
ltx_consts
 = lbuild
    [ ("k",Num 99)
    , ("nil",Seq [])
    ]
\end{code}

\subsection{\texttt{exprs :: Trie Expr}}
\begin{code}

ltx_exprs
 = lbuild
    [ ("applic",App "f" (Evar $ preVar "a"))
    , ("single",Set [Evar $ preVar "x"])
    ]


\end{code}

\subsection{\texttt{preds :: Trie Pred}}
\begin{code}

ltx_preds
 = lbuild
    [ ("P1",Obs (Var $ preVar "b"))
    , ("P2",Defd (Evar $ preVar "f"))
    , ("P3",Not (Pvar $ Std "P1"))
    ]


\end{code}

\subsection{\texttt{obs :: Trie Type}}
\begin{code}

ltx_obs
 = lbuild
    [
    ]

\end{code}

\subsection{\texttt{precs :: Trie Precs}}
\begin{code}

ltx_precs
 = lbuild
    [
    ]

\end{code}

\subsection{\texttt{types :: Trie Type}}
\begin{code}

ltx_types
 = lbuild
    [ ("++",Tfun (mkTprod [ts,ts]) ts)
    , ("len",Tfun ts Z)
    , ("k",Z)
    , ("nil",ts)
    ]
 where
   t = Tvar "t"
   ts = mkTseq t



\end{code}

\subsection{\texttt{laws :: LawTable}}
\begin{code}

ltx_laws
 = [
   ]

\end{code}

\subsection{\texttt{conjectures :: Trie Law}}
\begin{code}

ltx_conjectures
 = lbuild
    [
    ]

\end{code}

\subsection{\texttt{theorems :: [Proof]}}
\begin{code}

ltx_theorems
 = [
   ]

\end{code}

\subsection{Final Assembly}
\begin{code}

ltxTestTheory
  = markTheoryDeps ((nmdNullPrfCtxt ltx_thryName)
                       { thrySeqNo = ltx_thrySeqNo
                       , typedefs = ltx_typedefs
                       , consts = ltx_consts
                       , exprs = ltx_exprs
                       , preds = ltx_preds
                       , obs = ltx_obs
                       , precs = ltx_precs
                       , types = ltx_types
                       , laws = ltx_laws
                       , conjectures = ltx_conjectures
                       , theorems = ltx_theorems
                       })

\end{code}
