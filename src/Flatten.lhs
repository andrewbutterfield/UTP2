\section{Conjunctive/Disjunctive Flattening}

\begin{code}
module Flatten where
import Datatypes
import Data.List
\end{code}

WE USE A TEMPORARY HACK HERE, with explicit use of names
from \texttt{Datatypes.lhs} that should be moved to a special "builtins" module.

Flattening nested $\land$s and $\lor$s can be useful (e.g.:)
$$
  \bigwedge\setof{\bigwedge\setof{x_1,\ldots,x_m}
                 ,\bigwedge\setof{y_1,\ldots,y_n}
                 ,\ldots
                 }
  =
  \bigwedge\setof{x_1,\ldots,x_m,y_1,\ldots,y_n,\ldots}
$$

The top-level-only flatteners have been replaced by
deep ones.
\begin{code}
predConjTidy False = sort . conjDeepFlatten
predConjTidy True  = removeDupPreds . sort . conjDeepFlatten

conjFlatten acc [] = reverse acc
conjFlatten acc (TRUE:prs) = conjFlatten acc prs
conjFlatten acc ((PApp nm tprs):prs)
 | nm == n_And  =  conjFlatten (tprs++acc) prs
conjFlatten acc (pr:prs) = conjFlatten (pr:acc) prs
\end{code}

For a disjunction list, tidy elements,
flatten, remove \texttt{FALSE} and duplicate \texttt{Pvar}s:
\begin{code}
predDisjTidy False = sort . disjFlatten []
predDisjTidy True  = removeDupPreds . sort . disjDeepFlatten

disjFlatten acc [] = reverse acc
disjFlatten acc (FALSE:prs) = disjFlatten acc prs
disjFlatten acc ((PApp nm tprs):prs)
 | nm == n_Or  =  disjFlatten (tprs++acc) prs
disjFlatten acc (pr:prs) = disjFlatten (pr:acc) prs
\end{code}

Given a sorted predicate-list,
we want to remove duplicates.
\begin{code}
removeDupPreds [] = []
removeDupPreds (pr:prs) = skipDupPreds pr [pr] prs

skipDupPreds _ acc [] = reverse acc

skipDupPreds cpr acc (pr:prs)
 | cpr == pr  =  skipDupPreds cpr acc prs
 | otherwise  =  skipDupPreds pr (pr:acc) prs
\end{code}

We also provide deep-flattening variants:
\begin{code}
conjDeepFlatten []         = []
conjDeepFlatten (TRUE:prs) = conjDeepFlatten prs
conjDeepFlatten ((PApp nm subprs):prs)
 | nm == n_And  =  conjDeepFlatten subprs ++ conjDeepFlatten prs
conjDeepFlatten (pr:prs)   = pr : conjDeepFlatten prs

disjDeepFlatten []         = []
disjDeepFlatten (FALSE:prs) = disjDeepFlatten prs
disjDeepFlatten ((PApp nm subprs):prs)
 | nm == n_Or  =  disjDeepFlatten subprs ++ disjDeepFlatten prs
disjDeepFlatten (pr:prs)   = pr : disjDeepFlatten prs
\end{code}
