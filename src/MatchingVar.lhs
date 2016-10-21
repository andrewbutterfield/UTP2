\section{Variable Matching}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module MatchingVar where
import Utilities
import Tables
import Datatypes
import DataText
import MatchTypes
\end{code}


A standard variable pattern can only match
a standard variable whose type
is compatible with its own.
It can only match a
different variable if it is not ``known''.
If the pattern variable is bound higher up,
then the same must hold for the test variable.

\begin{eqnarray*}
   \MRKnownVN   && \MRKnownV
\\ \MRUnknownVN && \MRUnknownV
\end{eqnarray*}

A general list variable pattern matches anything,
binding to a singleton sequence.
A reserved variable matches itself.

We need to support decoration matching,
in that a subscript matches any other subscript,
and \texttt{Pre} matches anything.
\begin{code}
vMatch :: Monad m
       => LocalContext -> MatchResult
       -> Variable -> Variable
       -> m MatchResult

vMatch here mres
       tv@(Rsv tr tsub,td,_) pv@(Rsv pr psub,pd,_)
 | tr == pr && tsub == psub && td `dMatch` pd
              =  mres `mrgRMR` (okBindV pv tv)
 | otherwise  =  fail "Nothing"
vMatch here mres tv (Rsv _ _,_,_) = fail "Nothing"

vMatch here mres tv pv@(Gen (Lst _),_,_) = mres `mrgRMR` (okBindV pv tv)

vMatch here mres tv pv
 | isLstV pv                    =  fail "Nothing"
 | not (ttype `tlequiv` ptype)  =  fail "Nothing"
 | tv `elem` (tbvs here)
   && pv `elem` (pbvs here)     =  okbind
 | otherwise = vMatch' here mres tv pv
 where
   okbind =  mres `mrgRMR` (okBindV pv tv)
   ttype = mttsLookup (ttts here) tv (ttags here)
   ptype = mttsLookup (ptts here) pv (ptags here)

vMatch' here mres tv pv
 = case tsvlookup (knownObs mctxt) pv of
    Just _  ->  if tv == pv
                then return mres
                else fail "Nothing"
    Nothing
     -> case tsvlookup (knownConsts mctxt) pv of
       Nothing  ->  dvMatch mres tv pv
       _        ->  fail "Nothing"
 where mctxt = mctx here
\end{code}

We also capture these rules using \texttt{dvMatch}
which assumes \texttt{pv} is not known nor a list variable:
\begin{code}
dvMatch :: Monad m
        => MatchResult
        -> Variable      -- tv : test variable
        -> Variable      -- pv : pattern variable
        -> m MatchResult
\end{code}

$\MRAbstractPreCons$
\begin{code}
dvMatch mres tv pv@(_,Pre,_)                =  mres `mrgRMR` okBindV pv tv
\end{code}

$\MRAbstractPostCons$
\begin{code}
dvMatch mres tv@(_,Post,_) pv@(_,Post,_)    =  mres `mrgRMR` okBindV pv tv
\end{code}

$\MRAbstractScrptCons$
\begin{code}
dvMatch mres tv@(_,Scrpt,_) pv@(_,Scrpt,_)  =  mres `mrgRMR` okBindV pv tv
\end{code}

$\MRAbstractSbscrCons$
\begin{code}
dvMatch mres tv pv@(_,Subscript _,_)        =  mres `mrgRMR` okBindV pv tv

dvMatch _ _ _                               =  fail "Nothing"
\end{code}

\newpage
\subsubsection{Decoration Matching}

The decoration matching rules:
\input{doc/formal/Matching-Decoration}

Basically, \emph{if not known},
dashed variable-patterns match dashed test variables,
script variables match script variables,
while other pattern variables, (undashed, or subscripted)
match any test variable.

\begin{code}
dMatch :: Decor  --  test decoration
       -> Decor  --  pattern decoration
       -> Bool
dMatch td            Pre            =  True
dMatch (Subscript _) (Subscript _)  =  True
dMatch Scrpt         Scrpt          =  True
dMatch td            pd             =  td == pd

vdMatch :: Variable -> Variable -> Bool
vdMatch (_,td,_) (_,pd,_) = dMatch td pd
\end{code}
