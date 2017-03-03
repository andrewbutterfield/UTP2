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

\newpage
\subsection{\texttt{Lang} usage}

First, we have a restriction on the use of the \texttt{LElem}-list
in the Lang construct: A \texttt{LList}
or \texttt{LCount} element's list may only
contain non-\texttt{LList} \texttt{LElems} of the same type:
\begin{code}
checkLList [] = True
checkLList (LList _:_) = False
checkLList (LCount _:_) = False
checkLList (le:les) = chkLL le les
 where
   chkLL le [] = True
   chkLL le (le':les) = chkLE le le' && chkLL le les
   chkLE (LVar  _) (LVar  _) = True
   chkLE (LType _) (LType _) = True
   chkLE (LExpr _) (LExpr _) = True
   chkLE (LPred _) (LPred _) = True
   chkLE        _         _  = False
\end{code}

Next we have a correspondence between the LElem-list (\texttt{les})
and the SynSpec-list (\texttt{ss}) as follows:
\begin{itemize}
  \item
    If the length of \texttt{les} is $n$, then the ``base'' length
    of \texttt{ss} is $n+1$.
  \item
    The ``base''-list identifies the tokens occurring before, after
    and between each element of the language construct:
    \\
    \begin{tikzpicture}
       \matrix [matrix of math nodes] {
         & le_1 && le_2 && \ldots && le_i && \ldots && le_n \\
         ss_1 && ss_2 && ss_3 & \ldots & ss_i && ss_{i+1} & \ldots & ss_n && s_{n+1} \\
       } ;
    \end{tikzpicture}
    \\
    It contains only \texttt{SSNull} and \texttt{SSTok} entries, and ideally only
    the first and last should be \texttt{SNull}%
    \footnote{
      In general, for ease of parsing, the only safe place
      for a \texttt{SSNull} entry will be immediately after a \texttt{LVar},
      since the parser knows an \texttt{LVar} is a single token.
    }%
    .
  \item In addition, if an \texttt{LElem} is an \texttt{LList}/\texttt{LCount},
    then there needs to be a \texttt{SSSep} token to identify the separator
    in use at that point:
    \\
    \begin{tikzpicture}
       \matrix [matrix of math nodes] {
          \ldots &      & \mathtt{LList}_i &          & \ldots \\
          \ldots & ss_i & \mathtt{SSSep}_i & ss_{i+1} & \ldots \\
       } ;
    \end{tikzpicture}
  \item
    In the pathological case where \texttt{les} is empty,
    then \texttt{ss} must be a singleton containing an \texttt{SSTok}.
\end{itemize}
\begin{code}
checkLang [] [SSTok _] = True
checkLang [] [_]       = False
checkLang les ss = chkL les ss
 where

   chkL [] [s] = nonSep s
   chkL (LList _:les) (s:ss)
    | nonSep s  = chkLL les ss
    | otherwise = False
   chkL (LCount _:les) (s:ss)
    | nonSep s  = chkLL les ss
    | otherwise = False
   chkL (_:les) (s:ss)
    | nonSep s  = chkL les ss
    | otherwise = False
   chkL _ _ = False

   chkLL les (s:ss)
    | nonSep s = False
    | otherwise = chkL les ss
   chkLL _ _ = False

   nonSep SSNull    = True
   nonSep (SSTok _) = True
   nonSep (SSSep _) = False

checkLangSpec (LangSpec les ss) = checkLang les ss
\end{code}

\newpage
\subsection{\texttt{Focus} usage}
