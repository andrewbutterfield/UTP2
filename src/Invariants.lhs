\section{Invariants}

\begin{code}
module Invariants where
import Tables
import Utilities
import Datatypes
import MatchTypes

import Data.List
\end{code}

How could we possibly \emph{not} have these ?

We try to build an invariant fixer
to go with each checker.

\newpage
\subsection{\texttt{QVar} usage}

We have a well-formedness condition for the use of
\texttt{QVars} in quantifiers: given $\quant~ xs  @ P$,
the \texttt{Lst} variables in $xs$ can only appear
in \texttt{QVars} in deeper quantifiers, \emph{and nowhere
else}.
The variables in $xs$ must also be unique.
Note that this also applies in substitutions.
\begin{code}
checkPredQVars pr
 | null dups  =  (True,[])
 | otherwise  =  (False,dups)
 where
   (xs,dups) = wfp pr

   wfp = predRec mrg pspc pbas
   mrg [] = ([],[])
   mrg ((xs,dups):rest)
    = (xs `union` xs',dups `union` dups')
    where (xs',dups') = mrg rest
   pbas = ([],[])

   pspc (PExpr e) = Just $ wfe e
   pspc (PAbs nm  tt xs bps) = Just $ mrg ((xs,dupsOf xs):map wfp bps)
   pspc _ = Nothing

   wfe = exprRec mrg espc ebas
   ebas = ([],[])

   espc (ESub ex (Substn ssub))
     = Just $ mrg ((xs,dupsOf xs):(map wfe (ex:exs)))
     where
       xs = map fst ssub
       exs = map snd ssub
   espc _ = Nothing

checkExprQVars e = checkPredQVars (PExpr e)
\end{code}

For now we don't fix this:
\begin{code}
fixPredQVars pr = error "fixPredQVars NYI"
\end{code}
