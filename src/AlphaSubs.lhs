\section{Alpha Substitutions}

\begin{code}
module AlphaSubs where
import Tables
import Datatypes
import Utilities
import DataText
import MatchTypes
import Focus
import FreeBound

import Data.List
import Data.Char
\end{code}



\subsection{Free/Bound Partitioning --- Theory}

For some applications (e.g. type-checking),
we want to $\alpha$-rename all bound variables so they do not
clash with any free ones, or each other
 --- this allows these other applications to be kept simple.

We simply extract all the free variables,
and then use this as an accumulator, renaming any binding that
clashes and adding it in as a name to be avoided.

We illustrate the algorithm
on a simple predicate language (with substitution):
\begin{eqnarray*}
   A \in Atomic
\\ V \in VarList
\\ P \in Pred &::=& A | P \land P | \forall V @ P | P[P_i/v_i],
i \in 1 \ldots n
\end{eqnarray*}
The free/bound partition ($fbpart$) of predicate $P$
is computed by determining the
free variables of $P$, to initialise the used variable list
($U$)
and then using this with an initially empty substitution
function ($\sigma$)
to recursively perform the partition:
\begin{eqnarray*}
   fbpart(P) &\defs& fbp(FV(P),\theta)
\end{eqnarray*}
A key invariant for $(U,\sigma)$ is that all variables in both
domain and range of the substitution are in the used variable
set:
\begin{eqnarray*}
  inv(U,\sigma) &\defs& \dom~\sigma \cup \ran~\sigma \subseteq
  U
\end{eqnarray*}
Given an atomic predicate, we simply apply the current
substitution:
\begin{eqnarray*}
  fbp(U,\sigma) A &\defs& A\sigma
\end{eqnarray*}
Given a composite predicate, we simply map down all
sub-components:
\begin{eqnarray*}
  fbp(U,\sigma)(P_1 \land P_2)
  &\defs&
  fbp(U,\sigma)(P_1) \land fbp(U,\sigma)(P_2)
\end{eqnarray*}
With a quantifier, we first identify the conflict set $C$,
then generate new variables ($N$) for each conflict,
and the corresponding substitution ($\sigma'$).
The bound variables are replaced using $\sigma'$,
and the body is processed with updated used variable set
(all bound and new variables)
($U' = U \cup X \cup N$) and substitution ($\sigma \oplus
\sigma'$)
\begin{eqnarray*}
   fbp(U,\sigma) (\forall X @ P)
   &\defs&
   \LET
\\&&~~C = U \cap X
\\&&~~N = new~C
\\&&~~\sigma' = C \mapsto N
\\&& \IN~\forall X\sigma' @ fbp(U \cup X \cup
N,\sigma\oplus\sigma')P
\end{eqnarray*}
Substitution is treated like a general composite,
except that we also have to substitute the target variables:
\begin{eqnarray*}
   fbp(U,\sigma) (P[P_i/v_i])
   &\defs& (fbp(U,\sigma)P)[(fbp(U,\sigma)P_i)/(v_i\sigma)]
\end{eqnarray*}

\subsection{Generating Fresh Variables}

Generating new variables, given currently used variable roots
and those that clash, returning a substitution association list
and the extended list of variables in use.
The renaming is done at the root level.
\begin{code}
genNewV :: [Root]          -- currently used variable roots (to be avoided)
        -> Trie Root       -- current substitution (Root -+-> Variable)
        -> [Variable]      -- variables to be renamed
        -> ( [Root]        -- resulting used variables
           , Trie Root     -- resulting substitution
           )

genNewV usedr subf [] = (usedr,subf)

genNewV usedr subf (v:vs)
 = genNewV (insnorm r' usedr) (trupdate r r' subf) vs
 where

   r = varRoot v
   r' = case r of
         (Gen (Std s)) -> gennew (Gen . Std) usedr 1 s
         (Gen (Lst s)) -> gennew (Gen . Lst) usedr 1 s
         r             -> gennew (Gen . Lst) usedr 1 $ rootString r


   gennew mkR usedr n s
     | r' `elem` usedr  =  gennew mkR usedr (n+1) s
     | otherwise        =  r'
     where
       s' = remTrailingDigits s++show n
       r' = mkR s'

remTrailingDigits = reverse . dropWhile isDigit . reverse
\end{code}

Code to update and lookup a trie indexed by \texttt{Root}:
\begin{code}
trupdate :: Root -> a -> Trie a -> Trie a
trupdate (Gen (Std s)) x trie = tupdate s x trie
trupdate (Gen (Lst s)) x trie = tupdate ('$':s) x trie
trupdate (Rsv OBS _)   x trie = tupdate ('$':strOBS) x trie
trupdate (Rsv MDL _)   x trie = tupdate ('$':strMDL) x trie
trupdate (Rsv SCR _)   x trie = tupdate ('$':strSCR) x trie

trlookup :: Trie t -> Root -> Maybe t
trlookup trie (Gen (Std s)) = tlookup trie s
trlookup trie (Gen (Lst s)) = tlookup trie ('$':s)
trlookup trie (Rsv OBS _)   = tlookup trie ('$':strOBS)
trlookup trie (Rsv MDL _)   = tlookup trie ('$':strMDL)
trlookup trie (Rsv SCR _)   = tlookup trie ('$':strSCR)
\end{code}



\subsection{Free/Bound Partitioning --- Implementation}

Our implementation
has to work with both \texttt{Pred} and \texttt{Expr}.
\begin{code}
freeBoundPartition :: MatchContext -> Pred -> Pred
freeBoundPartition mctxt pr
 = fbPpred (map varRoot $ predFreeOVars mctxt pr) tnil pr
 where
\end{code}

For \texttt{Pred},
we use special handling for the quantifiers,
and then rely on \texttt{mapP} to handle the rest.
\begin{code}
  fbPpred usedr subf (Forall tt qs pr)
    = fbPpquant usedr subf mkForall qs pr

  fbPpred usedr subf (Exists tt qs pr)
    = fbPpquant usedr subf mkExists qs pr

  fbPpred usedr subf (Exists1 tt qs pr)
    = fbPpquant usedr subf mkExists1 qs pr
\end{code}
\begin{eqnarray*}
   fbp(U,\sigma) (P[P_i/v_i])
   &\defs& (fbp(U,\sigma)P)[(fbp(U,\sigma)P_i)/(v_i\sigma)]
\end{eqnarray*}
\begin{code}
  fbPpred usedr subf (Sub pr (Substn sub))
    = Sub (fbPpred usedr subf pr)
          (Substn (zip vs' ses'))
    where
     (vs,ses) = unzip sub
     ses' = map (fbPexpr usedr subf) ses
     vs' = map (xsub subf) vs

  fbPpred usedr subf pr
    = mapP (fbPpred usedr subf,fbPexpr usedr subf) pr
\end{code}

Quantified predicate handling:
\begin{eqnarray*}
   fbp(U,\sigma) (\forall X @ P)
   &\defs&
   \LET
\\&&~~C = U \cap X
\\&&~~N = new~C
\\&&~~\sigma' = C \mapsto N
\\&& \IN~\forall X\sigma' @ fbp(U \cup X \cup
N,\sigma\oplus\sigma')P
\end{eqnarray*}
\begin{code}
  fbPpquant usedr subf quant qs pr
     = quant (qsub subf' qs)
             (fbPpred usedr' subf' pr)
   where
     (usedr',subf') = fbpPart usedr subf qs

  fbpPart usedr subf qs
    = (usedr' `mrgnorm` rs,subf')
   where
     qvs = outQ qs
     rs = lnorm $ map varRoot qvs
     clashes = usedr `rintersect` qvs
     (usedr',subf') = genNewV usedr subf clashes

  rintersect usedr [] = []
  rintersect usedr (v:vs)
   | varRoot v `elem` usedr  =  v : rest'
   | otherwise               =      rest'
   where rest' = rintersect usedr vs

  qsub subf (Q qs) = Q $ map (xsub subf) qs

  xsub subf v@(r@(Gen _),d,_)
    = case trlookup subf r of
       Nothing    ->  v
       (Just r')  ->  mkVar r' d []
  xsub subf v@(r@(Rsv _ s),d,_)
    = case trlookup subf r of
       Nothing    ->  v
       (Just r')  ->  mkVar r' d s
\end{code}

For \texttt{Expr}, we use special handling for particular atomic
cases,
and the quantifiers, and then rely on \texttt{mapE} to handle
the rest.
\begin{code}
  fbPexpr usedr subf (Var v) = Var (xsub subf v)

  fbPexpr usedr subf (The tt v pr)
    = The 0 (xsub subf' v)
          (fbPpred usedr' subf' pr)
   where
     (usedr',subf') = fbpPart usedr subf $ Q [v]

  fbPexpr usedr subf (Eabs tt qs e)
    = Eabs 0 (qsub subf' qs) (fbPexpr usedr' subf' e)
   where
     (usedr',subf') = fbpPart usedr subf qs

  fbPexpr usedr subf (Esub e (Substn sub))
    = Esub (fbPexpr usedr subf e)
           (Substn (zip vs' ses'))
    where
     (vs,ses) = unzip sub
     ses' = map (fbPexpr usedr subf) ses
     vs' = map (xsub subf) vs

  fbPexpr usedr subf e
    = mapE (fbPpred usedr subf,fbPexpr usedr subf) e
\end{code}
