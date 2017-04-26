\section{Top-Level Matching}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module Matching where
import Tables
import Datatypes
import DataText
import Flatten
import Utilities
import MatchTypes
import MatchingType

import Data.List
\end{code}

Here matching is the activity of taking a
\emph{test} predicate \texttt{tpr}
(usually a sub-part of a proof goal)
and comparing it against a
\emph{pattern} predicate \texttt{ppr}
(typically part of a law)
to see if they match.
A successful match then returns a binding from variables
in the pattern to corresponding parts of the test.
Basic matching is simply the process of performing structural matching,
without any consideration of side-conditions.
However, even basic matching needs to take type information into account,
to avoid excessive spurious matches.

The statement
$$
  p \matches t | \beta
$$
asserts that test object $t$ matches
pattern object  $p$,
producing binding $\beta : Name \pfun Object$.
A binding is either empty ($\theta$) or a set of ``maplets'':
$$
\mapof{x \to a, y \to b, \cdots}
$$
We also have a partial  binder combiner
$$
  \beta_1 \uplus \beta_2
$$
that merges two bindings, provided they agree
on overlapping entries,
and use the notation
$$
\beta_1 \cong \beta_2
$$
to assert that such an agreement exists.

In practise, matching requires extra information about
pattern variables (e.g. are they ``known''?).
We use the notation $\Gamma$ to refer to a collection of all
such information ($\Gamma : Name \pfun Info$),
so many of our matching statements have the form:
$$
 \Gamma \vdash p \matches t | \beta
$$

Note that in most code below, the test argument
appears before the pattern argument, which is usually last,
as we pattern match predominately by pattern, and Haskell
code performs best with its pattern%
\footnote{%
Exercise: work out what precisely is
the referent of each instance of
the word ``pattern'' in this sentence.
}
matching on the last argument.

As a general principle, a binding matches a name
to an object of the relevant kind.
However, a list-variable name is always bound to a list of
objects of the relevant kind.
$$
  \maplet {\lst x} {\seqof{e_1,e_2,\ldots}}
$$

\newpage
\subsection{Matching Strategy}

As we match a test predicate taken from the current focus on a proof goal
against all the laws in scope,
we expect the vast majority of these matches to fail.
Therefore a key feature that contributes to matching performance
is that we should detect failure as soon as possible, so we can move on.
By contrast, there is no real cost to extra effort being spent
on completing successful matches.

At the top-level we start a match by passing in an empty \texttt{MatchResult}.
This is incrementally updated as matching progresses,
primarily to ensure that any matching failure is caught early.
Typically these failures will either be gross structural mismatches,
detected very quickly,
or they will result because matching is trying to force inconsistent bindings.

Every time we successfully update the bindings,
we will immediately use them to check all current deferred matches,
in order to (i) find any new inconsistency so we can fail (now!),
or (ii) simplify the deferred match by removing elements that have already been
bound.

This is implemented by the intelligent \texttt{MatchResult} builder
called \texttt{mkMR}.
It is defined here, rather than in \texttt{MatchTypes},
because checking deferred substitution matches itself requires
recursively doing a match on substitution expressions.



We shall build \texttt{mkMR} out of two key components:
\begin{code}
cleanQVarsToDo
 :: Monad m => VEBind -> [QVarMatchToDo] -> m [QVarMatchToDo]

cleanESubstToDo
 :: Monad m => VEBind -> [ESubstMatchToDo]
 -> m ( VEBind
      , [ESubstMatchToDo]
      , [QVarMatchToDo]
      , [ESubstMatchToDo] )
\end{code}


\subsubsection{Cleaning Deferred \texttt{QVars}}

This function checks every variable in the pattern
to see if it occurs in the binding.
If so, it searches the test to see if it can
find the variables to which it is bound.
If not, we fail, otherwise the pattern variable and its binding are removed.
Once all pattern variables have been treated this way
we do a final well-formedness check.

\input{doc/Manipulation-RuleOut-Qvar}

\begin{code}
cleanQVarsToDo (obnd,osbnd) qvms
 = sequence
   ( map (clnVarToDo $ flattenTrie obnd) qvms
     ++
     map (clnLVarToDo $ flattenTrie osbnd) qvms )

clnVarToDo
 :: Monad m
 => [(String,BObj Variable Expr)] -> QVarMatchToDo -> m QVarMatchToDo
clnVarToDo [] qvm  = return qvm
clnVarToDo ((pv,bobj):pairs) (tvs, pvs)
 = case extractWrapped varKey pv pvs of
    (Just v',pvs') ->  clnStdToDo pairs pvs' tvs bobj
    (Nothing,_)    ->  clnVarToDo pairs (tvs, pvs)

clnLVarToDo
 :: Monad m
 => [(String,BObj Variable Expr)] -> QVarMatchToDo -> m QVarMatchToDo
clnLVarToDo [] qvm  = return qvm
clnLVarToDo ((pv,bobjs):pairs) (tvs, pvs)
 = case extractWrapped gvarKey pv pvs of
    (Just v',pvs') ->  clnLstToDo pairs pvs' tvs bobjs
    (Nothing,_)    ->  clnLVarToDo pairs (tvs, pvs)

-- expect std v mapping to VO(std)
clnStdToDo pairs pvs' tvs (VO tv)
 = case extractWrapped id tv tvs of
     (Nothing,_)    ->  fail "std var bound to something else"
     (Just _,tvs')  ->  clnVarToDo pairs (tvs', pvs')
clnStdToDo _ _ _ _   =  fail "std var not bound to std var"

-- expect non-std v mapping to VSO
clnLstToDo pairs pvs' tvs (VSO vs)
 | issubset vs tvs  =  clnLVarToDo pairs (tvs\\vs, pvs')
clnLstToDo _ _ _ _ = fail "lst var not bound to var-list"
\end{code}

\subsubsection{Cleaning Deferred \texttt{Substn}}

\input{doc/Manipulation-RuleOut-Subst}

\begin{code}
cleanESubstToDo vebind esubtodo = return (vebind, esubtodo, [], [])
\end{code}

\subsubsection{Smart \texttt{MatchResult} Builder}

We shall now formally describe some key properties that hold
for the cleaning functions above,
 calling them $clnQ$ and $clnS$ for short.
\begin{eqnarray*}
   \beta \in  B && \texttt{VEBind}
\\ q \in Q && \texttt{[QVarMatchToDo]}
\\ s \in S && \texttt{[ESubstMatchToDo]}
\\
\\ clnQ &:& B \fun Q \fun Q_\bot
\\ clnS &:& B \fun S \fun (B \cross S \cross Q \cross S)_\bot
\end{eqnarray*}

We first define two (overloaded) predicates ($\uplus$)
that assert that neither $q$ nor $s$
containing anything that overlaps with bindings in $\beta$,
which we characterise by saying they don't change their arguments in that
case:
\begin{eqnarray*}
   \beta \uplus q &\defs&  clnQ~\beta~q = q
\\ \beta \uplus s &\defs&  clnS~\beta~s = (\beta,s,\nil,\nil)
\\ \beta \uplus \nil &\equiv& \True
\\ \beta \uplus q_1 \land \beta \uplus q_2
   &\equiv&
   \beta \uplus (q_1\cat q_2)
\\ \beta \uplus s_1 \land \beta \uplus s_2
   &\equiv&
   \beta \uplus (s_1\cat s_2)
\end{eqnarray*}
We can then assert when these predicates hold
for usage of the above two functions:
\begin{eqnarray*}
   clnQ~\beta~q = q' &\implies& \beta \uplus q'
\\ clnS~\beta~s = (\beta',s',q'',s'') &\implies& \beta' \uplus s'
\\ clnQ~\beta~\nil &=& \nil
\\ clnS~\beta~\nil &=& (\beta,\nil,\nil,\nil)
\end{eqnarray*}
We can specify the behaviour of \texttt{mkMR} as
\begin{eqnarray*}
   mkMR &:& B \cross Q \cross S \fun B \cross Q \cross S
\\ mkMR (\beta,q,s) = (\beta',q',s')
   &\implies&
   \beta' \uplus q' \land \beta \uplus s'
\end{eqnarray*}
In effect it first calls $clnQ$ and then $clnS$.
If the latter returns non-nil 3rd and 4th components,
then we recursively process those.
\begin{eqnarray*}
\lefteqn{mkMR(\beta,q,s)}
\\&\defs& \textbf{let}
\\&& \quad q' = clnQ(\beta,q)
\\&& \quad (\beta',s',q'',s'') = clnS(\beta,s)
\\&& \textbf{in}
\\&& \textbf{if } q''=\nil \land s''=\nil
\\&& \textbf{then } (\beta',q',s')
\\&& \textbf{else }
\\&& \quad \textbf{let }
\\&& \qquad (\beta'',q''',s''') = mkMR(\beta',q' \cat q'',s'\cat s'')
\\&& \quad \textbf{in } (\beta'',q''',s'\cat s''')
\end{eqnarray*}
Proof of termination looks tricky.


\begin{code}
mkMR :: Monad m => MatchResult -> m MatchResult

mkMR (bnds@(_, vebind, _),qvms,sbms)
 = do qvms' <- cleanQVarsToDo vebind qvms
      return (bnds, qvms, sbms)
\end{code}

\newpage
\subsubsection{Merging Match Results}

When we merge \texttt{MatchResult}s,
we first merge the three components independently.
Then we build the match-result with the partial resolution provided by \texttt{mkMR}.

\begin{code}
mrgMR :: Monad m => MatchResult -> MatchResult -> m MatchResult
mres1 `mrgMR` mres2
  = do mres' <- mres1 `mergeMR` mres2
       mkMR mres'
\end{code}

We then define a number of useful variants:
\begin{code}
mrgRMR :: Monad m => MatchResult -> m MatchResult -> m MatchResult
mrgRMR mres1 moutcome
 = do mres2 <- moutcome
      mres1 `mrgMR` mres2

mrgMO :: Monad m => m MatchResult -> m MatchResult -> m MatchResult
mo1 `mrgMO` mo2
  = do mr1 <- mo1
       mr2 <- mo2
       mr1 `mrgMR` mr2

moMerge :: MatchResult -> [MatchResult] -> [MatchResult]
moMerge mr0 [] = []
moMerge mr0 (mr:mrs)
 = case mr0 `mrgMR` mr of
    Nothing   ->  moMerge mr0 mrs
    Just mr'  ->  mr' : moMerge mr0 mrs
\end{code}


\newpage
\subsection{Structural Matching}

Given the revision of the variable types,
we now expect structural matching to be a form of recursive
invoking one matcher for each of the term and variable types,
plus two specialised matchers for lists of things
(variable-lists and substitutions).

\begin{tabular}{|l|l|}
  \hline
  Type & Matcher
\\\hline
  \texttt{Variable} & \texttt{vMatch}
\\\hline
  \texttt{ListVar} & \texttt{lvMatch}
\\\hline
  \texttt{GenVar} & \texttt{gvMatch}
\\\hline
  \texttt{Expr} & \texttt{eMatch}
\\\hline
  \texttt{Pred} & \texttt{pMatch}
\\\hline
  \texttt{Substn} & \texttt{sMatch}
\\\hline
  \texttt{VarList} & \texttt{vlMatch}
\\\hline
\end{tabular}

\subsubsection{Structural Rules}

Let $\Gamma \vdash P \matches T | \beta$
mean that pattern $P$ matches test $T$ with bindings $\beta$,
given that $\Gamma$ are the ``known'' variables.
The $ | \beta $ suffix is ommitted if $\beta$ is empty.

\input{doc/formal/Matching-Structural}

Structural matching is primarily implemented in
the functions \texttt{pMatch} and \texttt{eMatch} decribed below.

\subsubsection{Bound Variable Handling}

We need to extend bound variable lists
when matching under quantifiers.
\begin{code}
(+<) :: VarList -> VarList -> VarList
vs +< xs = lnorm (vs++xs)

(+<<) :: VarList -> (Substn Variable GenVar a) -> VarList
vs +<< (vas, lvs) = lnorm (vs ++ map (V . fst) vas ++ map fst lvs)
\end{code}

\newpage
\subsection{Basic Predicate Matching}

We do not match the \texttt{PVar} $\_UNINT$ marking an uninterpreted language
construct:
\begin{code}
nameUNINT = "_UNINT"
predUNINT = PVar $ parseVariable nameUNINT
\end{code}

\begin{code}
pMatch :: (Functor m, Monad m)
       => LocalContext
       -> MatchResult
       -> Pred
       -> Pred
       -> m MatchResult
\end{code}


\subsubsection{Matching \texttt{PVar}}

\texttt{PVar} $\_UNINT$ never matches anything.
A \texttt{PVar} that is defined,
matches itself or its definition (\texttt{pNameMatch}).
Otherwise it matches anything, except an \texttt{PExpr} whose type is not \texttt{B}.
\begin{eqnarray*}
   \MRPUnInstN && \MRPUnInst
\\ \MRPKnownN && \MRPKnown
\\ \MRPUnKnownN && \MRPUnKnown
\end{eqnarray*}
\begin{code}
pMatch here mres tpr (PVar p)
 | varKey p == nameUNINT  =  (fail "Nothing")
 | otherwise
    = case tslookup (knownPreds (mctx here)) (varKey p) of
       Just dpr  ->  pNameMatch mres tpr (p,dpr)
       Nothing   ->  freePMatch p tpr
 where
   freePMatch p (PExpr te)
    | not ((evalExprType (ttts here) (ttags here) te) `tlequiv` B)
                     =  (fail "Nothing")
   freePMatch p tpr  =  mres `mrgRMR` okBindP p tpr
\end{code}

\subsubsection{Matching \texttt{XXX}}


\begin{code}
pMatch here mres TRUE TRUE = return mres
pMatch here mres FALSE FALSE = return mres
\end{code}

When matching $\land$
we need also to look for 2-place atomic predicate conjunctions:

\subsubsection{Matching \texttt{XXX}}

\begin{eqnarray*}
   \MRTwoPlaceManyN && \MRTwoPlaceMany
\\
\\ \MRTwoPlaceLessN && \MRTwoPlaceLess
\end{eqnarray*}
\begin{code}
pMatch here mres (PApp tnm tprs) (PApp pnm pprs)
 | tnm==n_And && tnm==pnm  =  pMList here mres tprs pprs
pMatch here mres (PApp tnm tprs) ppr
 | tnm==n_And  =  pM2Place here mres (conjDeepFlatten tprs) ppr
\end{code}

\subsubsection{Matching \texttt{XXX}}


We also need to look for 2-place test
predicates that use meta variables:
\begin{eqnarray*}
   \MRTwoPlaceOneN && \MRTwoPlaceOne
\end{eqnarray*}
\begin{code}
pMatch here mres
       tpr@(P2 tnm  tlv1 tlv2)
       ppr@(P2 pnm  plv1 plv2)
 | tnm==pnm  =  pM1Place here mres tlv1 tlv2 plv1 plv2
\end{code}


\subsubsection{Matching \texttt{XXX}}

Expressions (Atomic Predicates):
We only match expressions whose types are compatible
\begin{code}
pMatch here mres (PExpr te) (PExpr pe)
 | ttype `tlequiv` ptype
    = eMatch here mres te pe
 | otherwise  =  (fail "Nothing")
 where
   ttype = evalExprType (ttts here) (ttags here) te
   ptype = evalExprType (ptts here) (ptags here) pe
\end{code}

\subsubsection{Matching \texttt{TypeOf}}

\begin{code}
pMatch here mres (TypeOf te tt) (TypeOf pe pt)
 | ttype `tlequiv` ptype
   = do tbnds <- tMatch tt pt
        ebnds <- eMatch here mres te pe
        mres `mrgRMR` (injTbind tbnds `mrgMR` ebnds)
 | otherwise  =  (fail "Nothing")
 where
   ttype = evalExprType (ttts here) (ttags here) te
   ptype = evalExprType (ptts here) (ptags here) pe
\end{code}

\subsubsection{Matching \texttt{PApp}}


The next collection of patterns involve simple recursion
into predicate sub-components:
\begin{eqnarray*}
   \MRCompositeN && \MRComposite
\end{eqnarray*}
\begin{code}
pMatch here mres (PApp tnm tprs) (PApp pnm pprs)
 | tnm==pnm = pMList here mres tprs pprs
\end{code}

\newpage

\subsubsection{Matching \texttt{PAbs}}


We permit meta-matching in quantifier variable lists,
and we also support the fact that vector metavariables can
match trivial quantifiers (empty binding list, so effectively no quantifier):
\begin{eqnarray*}
   \MRQuantN && \MRQuant
\\
\\ \MRNullQuantZN && \MRNullQuantZ
\end{eqnarray*}
For now we do not support the following:
\begin{eqnarray*}
   \MRNullQuantON && \MRNullQuantO
\end{eqnarray*}
\begin{code}
pMatch here mres (PAbs tnm ttag tqv tprs) (PAbs pnm ptag pqv pprs)
 | tnm==pnm  =  pQMatch here mres ttag tqv tprs ptag pqv pprs
\end{code}

\subsubsection{Matching \texttt{Univ}}


With universal closure, all pattern variables are bound,
and hence should never be treated as ``known''.
\begin{eqnarray*}
  \MRUnivN && \MRUniv
\end{eqnarray*}
Reminder: A proposed pattern like $[ok \implies ok'] \land ok$
needs to have bound variables made fresh,
and so should become $[f_1 \implies f_2] \land ok$,
where $f_1$ and $f_2$ are fresh,
before its use in matching.
\begin{code}
-- pMatch here mres (Univ ttag tpr) (Univ ptag ppr)
--  = pMatch here' mres tpr ppr
--  where here' = here{ ttags=ttag:(ttags here)
--                    , ptags=ptag:(ptags here)
--                    , tbvs=(tbvs here) -- plus freevars of tpr?
--                    , pbvs=(pbvs here) -- plus freevars of ppr
--                    }
\end{code}

\subsubsection{Matching \texttt{XXX}}


Substitutions:
\begin{eqnarray*}
   \MRPSubstN && \MRPSubst
\end{eqnarray*}
\begin{code}
pMatch here mres (Sub tpr tsub) (Sub ppr psub)
  = do bodymr <- pMatch here mres tpr ppr
       (tsub',psub') <- esMCondition bodymr tsub psub
       esMatch here bodymr tsub' psub'
\end{code}

\subsubsection{Matching Done}

\begin{code}
pMatch _ _ _ _ = (fail "Nothing")
\end{code}

\newpage
\subsubsection{Predicate List Matching}
Code to match lists of things:
\begin{code}
pMList :: (Functor m, Monad m) => LocalContext -> MatchResult
       -> [Pred] -> [Pred] -> m MatchResult

pMList here mres [] [] = return mres
pMList here mres [tpr] [ppr]
  = pMatch here mres tpr ppr
pMList here mres (tpr:tprs) (ppr:pprs)
  = do pmres <- pMatch here mres tpr ppr
       pMList here pmres tprs pprs
pMList _ _ _ _ = fail "Nothing"
\end{code}

\subsubsection{Known PVar Matching}

Here we have matched test predicate \texttt{tpr}
against PVar \texttt{pname}, a known predicate mapped to \texttt{pbody}.
It must either be equal to \texttt{pname}, or \texttt{pbody}.
We give a binding if we match the \texttt{pbody}, so that the replacement,
if the law is applied,
can match the test form.
\begin{eqnarray*}
   \MRPKnownN && \MRPKnown
\end{eqnarray*}
\begin{code}
pNameMatch :: Monad m => MatchResult -> Pred -> (Name,Pred) -> m MatchResult
pNameMatch mres tpr@(PVar tname) (pname,pbody)
  | varKey tname == pname    =  return mres
pNameMatch mres tpr (pname,pbody)
  | tpr == pbody  =  mres `mrgRMR` okBindP pname tpr -- is == too strong here ?
  | otherwise     =  fail "Nothing"
\end{code}

\subsubsection{Predicate Quantifier Matching}

With type-tags
\begin{code}
pQMatch here mres ttag tqv tprs ptag pqv pprs
 = do bodymr <- pMList here' mres tprs pprs
      (tqv',pqv') <- qMCondition bodymr tqv pqv
      qMatch here bodymr tqv' pqv'
 where here' = here{ ttags=ttag:(ttags here)
                   , ptags=ptag:(ptags here)
                   , tbvs=(tbvs here) +< tqv
                   , pbvs=(pbvs here) +< pqv }
\end{code}

Without type-tags
\begin{code}
pPQMatch here mres tqv tpr pqv ppr
 = do bodymr <- pMatch here' mres tpr ppr
      qMatch here bodymr tqv pqv
 where here' = here{ tbvs = (tbvs here) +< tqv
                   , pbvs = (pbvs here) +< pqv }
\end{code}

\newpage
\subsubsection{2-place Predicate (Singleton) Matching}

We match a 2-place predicate pattern against a single 2-place predicate test.
\begin{eqnarray*}
   \MRTwoPlaceOneN && \MRTwoPlaceOne
\\ \MRTwoPlaceOneRsvN && \MRTwoPlaceOneRsv
\end{eqnarray*}
\begin{code}
pM1Place :: Monad m
         => LocalContext
         -> MatchResult
         -> ListVar -> ListVar
         -> ListVar -> ListVar
         -> m MatchResult

pM1Place here mres tlv1 tlv2 plv1@(pv1, prs1) plv2@(pv2, prs2)
 | validRsvPair tlv1 tlv2
    = do bind1 <- pm1bind plv1 tlv1
         bind2 <- pm1bind plv2 tlv2
         bind1 `mrgMR` bind2
 | otherwise  =  (fail "Nothing")
 where
   mctxt = mctx here

   validRsvPair (tv1, _) (tv2,_)
    | isRsvV tv1 && isRsvV tv2  =  tv1 == tv2
   validRsvPair _ _ = True

   pm1bind plv tlv
    | isRsvLV plv  =  pm1place plv tlv
    | otherwise    =  mres `mrgMR` (bindES plv [tlv],[],[])
\end{code}
\newpage
Here we have a reserved list variable pattern $pv$ whose denotation is $V_p \ominus X_p$
and test $tv$ with denotation $V_t \ominus X_t$, where $V_p, V_t \subseteq \sem O$,
are known, while $X_p$ and $X_t$ are not.
We want a binding $pv \to tv$ with, in addition some bindings
from elements of $X_p$  to members
of $V_t \cup X_t$.
In  case where all variables in $X_p$ and $X_t$ are
standard we must have
\[
  \#V_p - \#X_p = \#V_t - \#X_t
\]
and we require the pattern to have no fewer unknowns than the test
\[
  \#X_p \geq \#X_t
\]
The extra bindings are from
each variable in $X_p$ to those in $X_t \cup (V_p\setminus V_t)$.
\begin{code}
-- in pM1Place here mres tlv1 tlv2 (pv1, prs1) (pv2, prs2)

   pm1place pv (Var tv)
    | not (vdMatch tv pv) = fail "Nothing"
    | not (lessOK mctxt pv tv) = fail "Nothing"
    | not (null pXs && null tXs)
       = pm1placeLVs pv tv pV tV pX1 tX1 pXs tXs
    -- null pXs, tXs, so everything must fit together exactly
    | lenpX1 < lentX1  = fail "Nothing"
    | length pV - length tV == lenpX1 - lentX1
       = pm1placeBind pv tv pX1 (map varRoot pVlesstV++tX1)
    | otherwise = (fail "Nothing")
    where
     (pV,pX) = lVarDenote mctxt pv
     (tV,tX) = lVarDenote mctxt tv
     (pX1,pXs) = partition isStdGV pX
     (tX1,tXs) = partition isStdGV tX
     lenpX1 = length pX1
     lentX1 = length tX1
     pVlesstV = pV \\ tV

     lessOK mctxt (pr, pless) (tr, tless)
      | pr == tr  =  True
      | not ((proots \\ troots) `subsetOf` plesss) = False
      | not ((troots \\ proots) `subsetOf` tlesss) = False
      where
        proots = rsvVRoots mctxt pr
        plesss = map varStringRoot pless
        troots = rsvVRoots mctxt tr
        tlesss = map varStringRoot tless
     lessOK mctxt _ _ = True

   pm1place _ _ = (fail "Nothing")
\end{code}

\newpage
We want to construct bindings for a match,
from general roots that appear in reserved list-variable subtraction
lists, so binding root $u$ to root $v$
will result in the following variable bindings:
\[u \to v, u' \to v'
\]
\begin{code}
-- in pM1Place here mres tlv1 tlv2 (pv1, prs1) (pv2, prs2)

   pm1placeBind pv tv pX tX
    | null xS  =  okBindV pv tv
    | otherwise
      = do bind1 <- okBindV pv tv
           binds <- foldl1 mrgMO $ map gRootBind $ zip pX tX
           mres `mrgRMR` (bind1 `mrgMR` binds)
    where xS = zip pX tX

   --gRootBind :: (GenRoot, GenRoot) -> MatchOutcome
   gRootBind (pGR,tGR)
     = okBindV pV tV `mrgMO` okBindV pV' tV'
     where
       pV  = mkObs pGR VPre
       tV  = mkObs tGR VPre
       pV' = mkObs pGR VPost
       tV' = mkObs tGR VPost
\end{code}

\newpage
Here we have a situation where at least one of $X_p$ or $X_t$ has list variables.
The general situation is, in terms of denotations,
that we are trying to match pattern
\[
  V_p \ominus (X1_p \cup XS_p)
\]
against test
\[
  V_t \ominus (X1_t \cup XS_t)
\]
where at least one of $XS_p$ and $XS_t$ is non-empty.
\begin{code}
-- in pM1Place here mres tlv1 tlv2 (pv1, prs1) (pv2, prs2)

--    pm1placeLVs :: Variable -- pv
--                -> Variable -- tv
--                -> [Variable] -- pV
--                -> [Variable] -- tV
--                -> [GenRoot] -- pX1, Std
--                -> [GenRoot] -- tX1, Std
--                -> [GenRoot] -- pXs, Lst
--                -> [GenRoot] -- tXs, Lst
--                -> MatchOutcome
\end{code}

Keep in mind that all variables in the $V$s are known observation variables,
while all those in the $X1$ are unknown standard,
with the $XS$s containing general list variables.
We expect the following inequalities to hold (otherwise a match is not possible):
\begin{eqnarray*}
   |X1_p| ~\leq~ |X1_t| &&
\\ |X1_p| ~=~ |X1_t| &\implies& |XS_t| ~\geq~ 1 ~\implies~ |XS_p| ~\geq~ 1
\\ |X1_p| ~<~ |X1_t| &\implies& |XS_p| ~\geq~ 1
\end{eqnarray*}

Given a denotation of the form $V \ominus (X1 \cup XS)$,
we can give an upper bound for the ``size'' of the denotation as $|V|-|X1|$.
Consideration of this leads to some more inequalities:
\begin{eqnarray*}
   |V_p| - |X1_p| &\leq& |V_p \cap V_t|
%\\ |X1_p| &\leq& |V_p\setminus V_t|
%\\ |X1_p| ~<~ |V_p\setminus V_t| &\implies& |XS_p| ~\geq~ 1
%\\ |X1_t| &\leq& |V_t\setminus V_p|
%\\ |X1_t| ~<~ |V_t\setminus V_p| &\implies& |XS_t| ~\geq~ 1
\end{eqnarray*}

We also note that we cannot rely on any test variable having a convenient
value, so for instance, we cannot allow test $O\less{\lst u}$
match pattern $S\less x$,
because we cannot expect that $\lst u$ will denote a list containing $ok$.
However test $O\less{ok,\lst u}$ is fine. The general rule seems to be,
we are ok if
\[
  V_t \subseteq \sem{R_p}
\]

For now we pick off simple cases.
\begin{code}
-- in pM1Place here mres tlv1 tlv2 (pv1, prs1) (pv2, prs2)

   pm1placeLVs pv@(_, pd, _) tv pV tV [] [] [pX] []
     = do rmatch <- bindO oroots pv tv
          let lbind = bindQL (mkGVar VPre pX) []
          mres `mrgRMR` (rmatch `ovrMR` (lbind, [], []))


   pm1placeLVs pv@(_, pd, _) tv pV tV [] [] [pX] tXs
    = do rmatch <- bindO oroots pv tv
         let lbind = bindQL (mkGVar VPre pX) (map (mkGVar VPre) tXs)
         mres `mrgRMR` (rmatch `ovrMR` (lbind, [], []))

   pm1placeLVs pv tv pV tV pX1 tX1 pXs tXs = fail "Nothing"

   oroots = obsRoots mctxt

   ovrMR ((gpbind1,vebind1,ttbind1),qtodo1,estodo1)
         ((gpbind2,vebind2,ttbind2),qtodo2,estodo2)
    = return (( gpbind1 `toverride` gpbind2
            , vebind1 `toverride` vebind2
            , ttbind1 `toverride` ttbind2 )
           , qtodo1++qtodo2
           , estodo1++estodo2)

-- end pM1Place
\end{code}

\newpage
\subsubsection{2-Place Predicate Matching}

\begin{eqnarray*}
   \MRTwoPlaceManyN && \MRTwoPlaceMany
\\
\\ \MRTwoPlaceLessN && \MRTwoPlaceLess
\end{eqnarray*}
Given a pattern of the form $p(\lst x,\lst y)$,
and a list of test predicates $\seqof{t_1,\ldots,t_n}$,
where $t_i = p(e_i,f_i)$,
can we get a sequences of matches ?
These can only occur as \texttt{P2}.
\begin{code}
pM2Place :: Monad m
         => LocalContext
         -> MatchResult
         -> [Pred] -- And-list (via deepConjFlatten)
         -> Pred
         -> m MatchResult

pM2Place here mres tprs ppr
 = pm2place ppr
 where

   pm2place (P2 pnm plv1 plv2)
     =  pm2place' (pm2name pnm) tprs plv1 plv2

   pm2place _ = fail "Nothing"
\end{code}

The 2-place atomic predicate \texttt{ppr} over meta-variables
is matched against every member of of \texttt{tprs},
by first ensuring that every 2-place test predicate is the same
as the pattern. We get back lists of expressions.
We then check the consistency of the two lists
of the appropriate type.
\begin{code}
   pm2place' pm2 tprs plv1 plv2
    = do epairs <- sequence (map (pm2 plv1 plv2) tprs)
         let (es1,es2) = unzip epairs
         mres1 <- check2PlaceBind (mctx here) mres plv1 es1
         check2PlaceBind (mctx here) mres1 plv2 es2

   pm2name pnm plv1 plv2 (PExpr (App nm [te1,te2]))
    | nm == pnm    =  pm2place'' te1 te2 plv1 plv2
   pm2equal _ _ _  =  fail "Nothing"
\end{code}

Here we now need to match pattern variables against
corresponding expressions.
\begin{code}
   pm2place'' te1 te2 plv1 plv2
    = do e1 <- lvSnglMatch (mctx here) plv1 te1
         e2 <- lvSnglMatch (mctx here) plv2 te2
         return (e1,e2)

-- end pM2PlaceObs
\end{code}

We use \texttt{rlvSnglMatch} to match an
expression that is a reserved list-variable
against an single variable as a possible member of its final list.
\begin{code}
rlvSnglMatch mctxt pv te@(Var v)   =  rlvSnggVarMatch mctxt pv te v
rlvSnglMatch mctxt pv te           =  (fail "Nothing")
\end{code}

We use \texttt{rlvSnggVarMatch} to match a reserved list-variable
against an single variable as a possible member of its final list.
\MRRSVSINGLE
\begin{code}
rlvSnggVarMatch mctxt pv te tv@(Gen (Std _),_,_)
 | tv `elem` fst (gVarDenote mctxt pv)  =  return te
 | otherwise  =  (fail "Nothing")

rlvSnggVarMatch mctxt pv te tv@(Gen (Lst _),_,_)  =  return te

rlvSnggVarMatch mctxt pv te tv -- isRsvV tv

 | tV `subsetOf` pV  =  return te

 where
   (pV,pX) = gVarDenote mctxt pv
   (tV,tX) = gVarDenote mctxt tv

rlvSnggVarMatch _ _ _ _   =  (fail "Nothing")
\end{code}


We have several bindings in which each variable is bound to
a sub-list of the final outcome. This function fuses those
together to give that final version, having checked that the
final outcome is OK.
\begin{eqnarray*}
   \sem{R\less{vs}} &=& V \ominus X,\lst X
\\ T &\subseteq& \sem R
\\ R \matches (T,\lst T) &\withbind& \mapof{R\to T, (X,\lst x) \to ((V\setminus T,\lst T)}
\\ &\textbf{iff}&
\\ T &\subseteq& V
\\ \lst X=\emptyset &\implies& \#(V\setminus T) = \#X
\\ \lst X\neq\emptyset &\implies& \#(V\setminus T) \geq \#X
\end{eqnarray*}
\begin{code}
check2PlaceBind :: Monad m
                => MatchContext -> MatchResult -> Variable -> [Expr]
                -> m MatchResult

check2PlaceBind mctxt mres pv es
 | isGenV pv                    =  mres `mrgRMR` okBindES pv es
 | not (null tTS)               =  fail "Nothing" -- too loose, best not to match
 | not( tT1 `subsetOf` pV)      =  fail "Nothing"
 | null pXS && diff == 0        =  mk2PlaceRsvBind mres pv tT1 pX1 pXS vLessT
 | not (null pXS) && diff >= 0  =  mk2PlaceRsvBind mres pv tT1 pX1 pXS vLessT
 | otherwise                    =  fail "Nothing"
 where
   (tT1,tTS) = partition isStdV $ lnorm $ map getVar es
   vLessT = pV \\ tT1
   diff = length vLessT - length pX1
   (pV,pX) = gVarDenote mctxt pv
   (pX1,pXS) = partition isStdG pX

mk2PlaceRsvBind
 :: Monad m
 => MatchResult
 -> Variable   --  pv     : pattern reserved variable
 -> [Variable] --  tT1    : list of test observation (std) variables
 -> [GenRoot]  --  pX1    : standard variables in X where [[pv]] = V (-) X
 -> [GenRoot]  --  pXS    : list variables in X where [[pv]] = V (-) X
 -> [Variable] --  vLessT :  V \ tT1 where [[pv]] = V (-) X
 -> m MatchResult

mk2PlaceRsvBind mres pv@(_,pd,_) tT1 pX1 pXS vLessT
 = mres
   `mrgRMR`
   (((bindQL pv tT1),[],[])
    `mrgMR`
    ( nullBinds
    , [(vLessT,map (mkGVar pd) (pX1++pXS))]
    ,[] ))
\end{code}

We use \texttt{lvSnglMatch} to match a list-variable
against an expression as a possible member of its final list.
Reserved list variables can only match single variables in their denotation
here, or reserved variables that they can subsume,
while non-reserved ones can match anything.
The bindings produced here are ``raw'', in that we have
a list-variable (\texttt{pv}) bound to a single item directly.
All these bindings get post-processed by \texttt{listVFuse} to generate the
appropriate lists later on.
\begin{code}
lvSnglMatch mctxt pv te
 | isRsvV pv  =  rlvSnglMatch mctxt pv te
 | otherwise  =  return te
\end{code}

\newpage
\subsubsection{Pred-Substitution Matching}

Conditioning:
\begin{code}
psMCondition :: Monad m
             => MatchResult -> PSubst -> PSubst -> m ( PSubst, PSubst )

psMCondition _ tsub psub = return (tsub,psub) -- for now.
\end{code}

\begin{eqnarray*}
   \MRPSubstN && \MRPSubst
\end{eqnarray*}
\begin{code}
psMatch :: (Functor m, Monad m)
        => LocalContext
        -> MatchResult
        -> PSubst -> PSubst
        -> m MatchResult

psMatch here mres (Substn tssub) (Substn pssub)
 = do mres1 <- pMList here mres vs' us'
      pMList here mres1 qs ps
 where
   (us,ps) = unzip pssub
   (vs,qs) = unzip tssub
   us' = map (PVar . genRootAsVar) us
   vs' = map (PVar . genRootAsVar) vs
\end{code}


\newpage
\subsection{Basic Expression Matching}

\begin{code}
eMatch :: (Functor m, Monad m)
       => LocalContext
       -> MatchResult
       -> Expr -> Expr
       -> m MatchResult
\end{code}

\begin{eqnarray*}
   \MRKnownVN   && \MRKnownV
\\ \MRUnknownVN && \MRUnknownV
\end{eqnarray*}
\begin{code}
eMatch here mres (Var tv) (Var pv)
 = vMatch here mres tv pv
\end{code}

\begin{eqnarray*}
   \MRKnownEN   && \MRKnownE
\\ \MRUnknownEN && \MRUnknownE
\end{eqnarray*}
\begin{code}
eMatch here mres te (Var pv)
 -- bound pv can only match bound tv, not general te
 | pv `elem` (pbvs here)        =  fail "Nothing"
 | not (ttype `tlequiv` ptype)  =  fail "Nothing"
 | otherwise                    =  veMatch (mctx here) mres te pv
 where
   ttype = evalExprType (ttts here) (ttags here) te
   ptype = mttsLookup (ptts here) pv (ptags here)
\end{code}

A \texttt{Evar} pattern matches an \texttt{Expr}, but must be equal
if the pattern is a known \texttt{Evar}.
\begin{code}
-- eMatch here mres te (Evar e)
-- = case tsvlookup (knownExprs (mctx here)) e of
--     Nothing  ->  mres `mrgRMR` okBindE e te
--     Just de  ->  eNameMatch mres te (e,de)
\end{code}

In most other cases we recurse down following expression structure
\begin{eqnarray*}
   \MRCompositeN && \MRComposite
\end{eqnarray*}
\begin{code}
eMatch here mres (Num ti) (Num pi)
 = matchIfEq ti pi (return mres)
eMatch here mres (App ts tes) (App ps pes)
 = eMList here mres tes pes

eMatch here mres (Abs tnm ttag tqvs tes) (Abs pnm ptag pqvs pes)
 | tnm==pnm
    = do mres1 <- eMList here' mres tes pes
         qMatch here mres1 tqvs pqvs
    where here' = here{ ttags = ttag:(ttags here)
                      , ptags = ptag:(ptags here)
                      , tbvs = (tbvs here) +< tqvs
                      , pbvs = (pbvs here) +< pqvs }

eMatch here mres (ESub te tsub) (ESub pe psub)
  = do mres1 <- esMatch here mres tsub psub
       eMatch here' mres1 te pe
 where here' = here{ tbvs = (tbvs here) +<< tsub
                   , pbvs = (pbvs here) +<< psub }

eMatch here mres _ _ = fail "Nothing"

matchIfEq x y mok = if x==y then mok else fail "Nothing"

eMList :: (Functor m, Monad m)
       => LocalContext
       -> MatchResult
       -> [Expr] -> [Expr]
       -> m MatchResult

eMList here mres [] [] = return mres
eMList here mres (te:tes) (pe:pes)
  = do mres1 <- eMatch here mres te pe
       eMList here mres1 tes pes
eMList here mres _ _ = fail "Nothing"
\end{code}

We have matched test expression \texttt{te}
against Evar \texttt{ename}, a known predicate mapped to \texttt{ebody}.
It must either be equal to \texttt{ename}, or \texttt{ebody}.
In any case, no binding results, as the replacement, if the law is applied,
will be \texttt{ename} in any case.
\begin{code}
eNameMatch :: Monad m
           => MatchResult -> Expr -> (Variable, Expr) -> m MatchResult

-- eNameMatch mres (Evar t) (ename,ebody)
--  | t == ename    =  return mres
--  | otherwise     =  fail "Nothing"
eNameMatch mres te (ename,ebody)
  | te == ebody  =  return mres
  | otherwise     =  fail "Nothing"
\end{code}


\begin{code}
eQMatch here mres ttag tqvs tpr te ptag pqvs ppr pe
 = do mres1 <- pMatch here' mres tpr ppr
      mres2 <- eMatch here' mres1 te pe
      qMatch here mres2 tqvs pqvs
 where here' = here{ ttags = ttag:(ttags here)
                   , ptags = ptag:(ptags here)
                   , tbvs = (tbvs here) +< tqvs
                   , pbvs = (pbvs here) +< pqvs }
\end{code}

\newpage
\subsection{Infix Matching}\label{ssec:infix-matching}

Infix patterns arise in three ways:
\begin{enumerate}
  \item
    Predicate patterns such as $P \land Q$, $P \implies Q$, etc.
    These only match test predicates of precisely the same form.
  \item
    Expression patterns $e \oplus f$.
    Matching these depends on what we know about $\oplus$.
  \item
    Language patterns with two components and a single infix symbol,
    e.g., $P \oplus P$, $E \oplus E$, $E \oplus P$, $V \oplus E$, etc.
    For now, we only consider patterns $P\oplus P$ and $E \oplus E$
    as ``infix'', with the rest matching structurally in the
    usual ways.
    Note that language patterns $E \oplus E$ are redundant
    in that having a precedence entry for $\oplus$
    autmatically gives us a \texttt{Bin} construct, so there is
    no need to define such notation using the language table.
    Matching the ``infix'' language patterms also depends on what we know about $\oplus$.
\end{enumerate}
In the latter two cases, in order to parse such constructs,
we must have an entry in the \texttt{precs} table asserting that
$\oplus \mapsto p$.


Apart from that obligatory requirement,
we have a number of possibilities:
\begin{itemize}
  \item $\oplus$ is not mentioned anywhere else,
    so must be a \texttt{Bin} variant of an \texttt{Expr}
    \\(Right now such usage will parse but not type-check
    so we can add laws with these patterns, but not enter
    conjectures about them. These patterns are very dangerous!)
  \item $\oplus$ is mentioned in \texttt{lang},
    and so is a Language infix pattern as described above.
    This mention is obligatory for all \texttt{Lang} constructs.
  \item $\oplus$ is mentioned in \texttt{types}.
  \item $\oplus$ is given a DEF-law in \texttt{laws}.
    This is also obligatory for Lang patterns,
    but we treat a definition equal to $\_UNINT$
    as being a non-definition.
\end{itemize}


\newpage
This gives us a range of possibilities
for both expression ($e \oplus f$) and language ($P\oplus P, E \oplus E$)
infix patterns.

\begin{tabular}{|c|c|c|p{2in}|}
  \hline
  \texttt{form} & DEF & \texttt{types} & Description
\\\hline\hline
  $e \oplus f$ & $\_UNINT$ & -
  & Generic, matches any \texttt{Bin}
\\\hline
  $e \oplus f$ & $\_UNINT$ & $T_1 \times T_2 \fun T_3$
  & Typed Generic, matches \texttt{Bin} consistent with type.
\\\hline
  $e \oplus f$ & none & $T_1 \times T_2 \fun T_3$
  & Specific, matches $\oplus$ only
\\\hline
  $P\oplus P$ & $\_UNINT$ & n/a
  & Generic, matches any binary predicate operator
\\\hline
  $P\oplus P$ & yes & n/a
  & Specific, matches $\oplus$ only
\\\hline
  \multicolumn{4}{|l|}{any other combination should not occur}
\\\hline
\end{tabular}

We now further extend $\Gamma$ to
record details about infix operators,
so for operator $\oplus$, $\Gamma(\oplus)$
maps to a set of data items.
If $\Gamma(\oplus) = \emptyset$,
then all we know about $\oplus$ is its precedence%
\footnote{which we always know, otherwise we could not parse it!}.
We present some matching rules for the $P$ and $E$ cases above
(the $\ell$ cases are similar).
\MRBINOP


\newpage
\subsection{Substitution Matching}

\subsubsection{Expr-Substitution Matching}

\input{doc/Expr-Substitution-Matching}


Just like QVars, we first check a substitution match
to see if some has already been resolved via body matching.

\begin{code}
esMCondition :: Monad m
             => MatchResult -> ESubst -> ESubst -> m ( ESubst, ESubst )

esMCondition mres (Substn tsub) (Substn psub) = esMcond [] tsub psub
 where

   esMcond pcs tsub [] = return (Substn tsub, Substn $ reverse pcs)
   esMcond pcs tsub (pex:psub)
    =  esMcond (pex:pcs) tsub psub -- for now
\end{code}


Unlike \texttt{QVars} matching, we do have to distinguish between
known and unknown variables here.

\begin{code}
esMatch :: (Functor m, Monad m)
        => LocalContext
        -> MatchResult
        -> ESubst -> ESubst
        -> m MatchResult

-- singleton pattern, singleton test
esMatch here mres
        ts@(Substn [(tv,te)]) ps@(Substn [(pv,pe)])
 | isStdV pv && (not (isVar pe) || isStdV (getVar pe))
   = do mres1 <- vMatch here mres tv pv
        eMatch here mres1 te pe

-- singleton generic list-variable pattern, general test
esMatch here mres
        ts@(Substn tsubs) ps@(Substn [(pv,pe)])
 | not $ isVar pe  =  fail "Nothing" -- shouldn't happen if invariant holds
 | isGenV pv && isGenV pev
   =  do qb <- okBindQL pv tvs
         eb <- okBindES pev tes
         mres `mrgRMR` (qb `mrgMR` eb)
 where
   pev = getVar pe
   (tvs,tes) = unzip tsubs

-- check a match is possible,
-- do all the reserved list-variable matching,
-- and then defer anything left over.
esMatch here mres ts@(Substn tsub) ps@(Substn psub)
 | n < k                         =  fail "Nothing"
 | ell == 0 && (n > k || m > 0)  =  fail "Nothing"
 | otherwise
     =  do (binds,tsub',psub') <- matchRsvSubs tsub psub
           mres `mrgMR` (binds,[],mkSubstToDo here tsub' psub')
 where
   (stdt,lstt) = vPartition $ map fst tsub
   n = length stdt ; m = length lstt
   (stdp,lstp) = vPartition $ map fst psub
   k = length stdp ; ell = length lstp
   -- need to unify MatchTypes.LocalContext with ThisContext

   matchRsvSubs tsub psub
    | tclean && pclean  =  mRsvVEs nullBinds [] tsub psub
    | otherwise  =  return ( nullBinds, tsub, psub)
    where
      tclean = all (cleanVar (mctx here) . fst) tsub
      pclean = all (cleanVar (mctx here) . fst) psub

   mRsvVEs binds busp tsub []  =  return (binds,tsub,reverse busp)
   mRsvVEs binds busp tsub ((pv,pe):psub)
    | isRsvV pv
        =  if isVar pe
            then do (msub',tsub') <- getDen dpv dpe tsub
                    let vbnds = bindES pv $ map (Var . fst) msub'
                    let ebnds = bindES pev $ map snd msub'
                    nbnds <- vbnds `mrgB` ebnds
                    binds' <- binds `mrgB` nbnds
                    mRsvVEs binds' busp tsub' psub
            else fail ""
    | otherwise  =  mRsvVEs binds ((pv,pe):busp) tsub psub
    where
      (dpv,_) = varExpand (mctx here) pv
      pev = getVar pe
      (dpe,_) = varExpand (mctx here) pev

      -- getDen :: [Variable] -> [Variable] -> [(Variable,Expr)]
      --        -> Maybe ([(Variable,Expr)],[(Variable,Expr)])
      getDen dpv dpe tsub = gD dpv dpe [] [] [] tsub

      gD dpv dpe mdvs busm bust []
        | dpv == mdvs'  =  return (reverse busm, reverse bust)
        | otherwise    =  fail ""
        where mdvs' = lnorm mdvs
      gD dpv dpe mdvs busm bust (ts@(tv,te):tsub)
       | dtv `subsetOf` dpv  =  gD dpv dpe (dtv++mdvs) (ts:busm) bust      tsub
       | otherwise           =  gD dpv dpe mdvs        busm      (ts:bust) tsub
       where
         (dtv,_) = varExpand (mctx here) tv
\end{code}



\newpage
\subsection{Variable Matching}

\input{doc/VariableKinds}


\newpage
\subsubsection{List-Matching}\label{ssec:list-matching}

\input{doc/Matching-List-Motivation}

A representative set of the new meta-matching rules:

\MRLISTVAR

Note, for example, that $PExpr$ can match itself,
the explicit list of its variables, or any combination
of $Mdl$, $Var$ and their explicit variable lists.
The rules regarding decoration matching are, \emph{ceteris paribus},
that same as for standard variables.

\MRTWOPLACE



Matching a (standard, free) variable against an expression
(that is not a variable).
\begin{eqnarray*}
   \MRKnownEN   && \MRKnownE
\\ \MRUnknownEN && \MRUnknownE
\end{eqnarray*}
\begin{code}
veMatch :: Monad m
        => MatchContext
        -> MatchResult
        -> Expr -> Variable
        -> m MatchResult

veMatch mctxt mres te pv
 = case tsvlookup (knownObs mctxt) pv of
    Just _  ->  fail "Nothing" -- obsvars only match self
    Nothing
     -> case tsvlookup (knownConsts mctxt) pv of
       Nothing  ->  okbind
       Just ke  ->  if te==ke  then okbind else fail "Nothing"
 where okbind = mres `mrgRMR` okBindE pv te
\end{code}

\section{Variable Matching}


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

\section{Variable-List Matching}


\subsection{Basic Quantifier Matching}


\subsubsection{Quantifier-Match Conditioning}

Given a quantifier body match,
the first thing we want to do is to check  for compatibility
with the quantifier lists to be matched and effectively remove
any that have already been matched, to simplify what remains.
We call this step ``conditioning'' the quantifier match.

For example, matching test $\forall a,b @ C$ against pattern $\forall x,y @ P$,
first matches $C$ against $P$.  Say this succeeds, binding $y$ to $a$.
Then, instead of trying to match test quantifier list $a,b$
against $x,y$ and hope to get $y$ bound to $a$,
we simply simplify our quantifier matching problem here to matching $b$
against $x$, and so get the final result $\mapof{x \to b, y \to a}$.
Should the $C$ vs $P$ match return a binding of $y$ to $c$ (say),
then the whole match fails, as the quantifier list match forces $y$
to bind to either on of $a$ or $b$, but not $c$, or any other variable that
might be in $C$.

To condition a match, we work through the pattern variables,
see if they have been bound (in \texttt{ebnds}).
If so, we look for their target in the test variables.
If found, we remove both.
If not found, we fail.
\begin{code}
qMCondition :: Monad m
            => MatchResult -> QVars -> QVars -> m ( QVars, QVars )

qMCondition ((_,vebnds,_),_,_) ( tqv) ( pqv)
 = qMcond [] tqv pqv
 where

   qMcond pcv tqv [] = return ( tqv, reverse pcv)
   qMcond pcv tqv (pv:pqv)
    = case tvlookup vebnds pv of
       Nothing    ->  qMcond (pv:pcv) tqv pqv -- not matched, so keep
       Just vobj  ->  qMcheck pcv pqv tqv vobj pv  -- matched, check in tqv
\end{code}
If \texttt{pv} is standard, then \texttt{tve} must be a standard variable, and we need
to find it in \texttt{tqv}:
\begin{code}
   qMcheck pcv pqv tqv (TO (Var tv@(Gen (Std _),_,_))) (Gen (Std _),_,_)
     | tv `elem` tqv  =  qMcond pcv (tqv \\ [tv]) pqv
\end{code}
If \texttt{pv} is a list variable, then \texttt{tve} must be a sequence
of variables, and we need
to find them in \texttt{tqv}:
\begin{code}
   qMcheck pcv pqv tqv (VSO tvvs) (Gen (Lst _),_,_)
     =  qMcond pcv (tqv \\ tvvs) pqv
   qMcheck pcv pqv tqv (TSO tves) (Gen (Lst _),_,_)
     | all (`elem` tqv) tvvs  =  qMcond pcv (tqv \\ tvvs) pqv
     where tvvs = map getVar tves
\end{code}
If \texttt{pv} is a reserved variable, we leave everything as is, and move on
(best dealt with by \texttt{qMatch}):
\begin{code}
   qMcheck pcv pqv tqv _ pv@(Rsv _ _,_,_)  =  qMcond (pv:pcv) tqv pqv
\end{code}
All other cases result in failure.
\begin{code}
   qMcheck _ _ _ _ _ = fail "Nothing"
\end{code}

\newpage
\subsection{Quantifier Matcher}

Quantifier-list matching has two phases:
the first (\texttt{qMatch1}) deals with any pattern reserved variables,
while the second (\texttt{qMatch2}) processes the rest.

Given that all these variables are in quantifier lists,
none are considered to be ``known''.

In amongst the list variables are the reserved ones.
The key thing to keep in mind here is that a reserved
variable like $O$ is a shorthand for a list of observation variables.
So the binding of such a variable has to be of something of potentially
the same length. In fact we expect reserved variables in patterns
to match observation variables in scope,
despite being in a binding position
---this is not necessary for the soundness of the prover,
but helps keep things clear for the user.
This is complicated by the presence of list-variables in reserved subtractions
(e.g., $O\less{\lst x}$, where we need to know the binding of $\lst x$
before we can be definitive about what $O\less{\lst x}$ is bound to).
If $O$ stands for $o_1,\ldots,o_n$, then a binding of $O$ to $x_1,\ldots,x_n$
is equivalent to bindings of $o_i$ to $x_i$, for $i \in 1\ldots n$.

We first look for any reserved variables in the pattern,
and see if these can be matched against test variables.
The remaining  parts of pattern and test are then
subject to a number of heuristics,
before being defferred, if necessary.
\begin{code}
qMatch :: Monad m
       => LocalContext
       -> MatchResult
       -> QVars             -- test QVars
       -> QVars             -- pattern QVars
       -> m MatchResult

qMatch here mres ( tvs) ( pvs)
 = do let (prvs,pgvs) = partition isRsvV pvs
      let (tks,tus,tls,tRs) = classifyVars (isKnownObsVar . mctx) here tvs
      let tRos = concat $ map denotePair tRs
      let kobs = ( sizeMdl  mctxt > 0
                 , sizeScr  mctxt > 0
                 , sizeMdl' mctxt > 0
                 , sizeScr' mctxt > 0 )
      (ctvs',mres1,umrvs)
                     <- qMatch1 here mres [] (tks,tus,tls,tRs) tRos prvs
      let tvs' = cvmerge ctvs'
      qMatch2 here mres1 tvs' (lnorm (pgvs ++ umrvs))
 where
   mctxt = mctx here
   denotePair tR
    = let (obs,subr) = gVarDenote (mctx here) tR
      in map (pairR tR) obs
   pairR tR ob = (ob,tR)
   cvmerge (kvs,uvs,lvs,rvs) = kvs++uvs++lvs++rvs
\end{code}

\subsubsection{Quantifier Matching, Phase 1}

We handle each reserved variable one at a time,
returning bindings and/or defferred \texttt{QVar} matches,or failing:
\begin{code}
qMatch1 :: Monad m
        => LocalContext
        -> MatchResult
        -> [Variable]
        -> ClassedVars
        -> [(Variable, Variable)]  --   std obs -+-> Rsv
        -> [Variable]
        -> m ( ClassedVars, MatchResult, [Variable] )

qMatch1 here mres umrvs ctvs tRos [] = return(ctvs, mres, umrvs)

qMatch1 here mres umrvs ctvs tRos (prv:prvs)
 = do (ctvs',tRos',mres',umrvs') <- rsvMatch (mctx here) mres umrvs ctvs tRos prv
      qMatch1 here mres' umrvs' ctvs' tRos' prvs
\end{code}

\newpage
Given a pattern reserved variable, we look among the test variables
for possible bindings.
\MRULES{
  \Gamma & R & (v_1,\ldots,v_n) & \beta
}
\begin{code}
rsvMatch :: Monad m
         => MatchContext
         -> MatchResult
         -> [Variable]
         -> ClassedVars
         -> [(Variable,Variable)]
         -> Variable
         -> m ( ClassedVars, [(Variable,Variable)], MatchResult, [Variable] )
\end{code}
We subsume a lot of rules with this case:
\MRULES{
   \Gamma & R & (\ldots,R,\ldots)               & \maplet R R
\\ \Gamma & R & (\ldots,\sem{R},\ldots)         & \maplet{R}{\sem{R}}
\\ \Gamma & R_a & (\ldots,R_b,\ldots)           &  \maplet{R_a}{R_b}
\\ \Gamma & O^d & (\ldots,M^d,S^d,\ldots)       & \maplet{O^d}{(M^d,S^d)}
\\ \Gamma & O^d & (\ldots,M^d,\sem{S^d},\ldots) & \maplet{O^d}{(M^d,\sem{S^d})}
}
The code below also works for $R\less{o1,\ldots,o\ell}$,
where $\setof{o1,\ldots,o\ell} \subseteq \sem R$.
\begin{code}
rsvMatch mctxt mres umvrs ctvs@(tks,tus,tls,tRs) tRos prv
 | prv `elem` tRs
   = do mresult <- mres `mrgRMR` bindO oroots prv prv
        return ( (tks,tus,tls,tRs\\[prv])
               , remRv prv tRos
               , mresult
               , umvrs )
 |  null psubr && (fst $ varsDenote mctxt tmatch)
                `eqvsMS`
                (fst $ varsDenote mctxt pRsem)
   = do bind' <-bindOL oroots prv tmatch
        mres' <- mres `mrgMR` (bind', [], [])
        return ( (tksout,tusout,tls,tRs\\(map snd tRosin))
               , tRosout
               , mres'
               , umvrs)
 | null (tks++tus++tls)
   && length tRs == 1 && length psubr == 1 && length tsubr == 1
   && vdMatch prv trv
   = do mres1 <- mres `mrgRMR` bindO oroots prv trv
        let bindSub = nullBinds
        mres' <- mres1 `mrgMR` ( bindSub, [], [])
        return ( ( [], [] ,[], [] )
                 , remRv prv tRos
                 , mres'
                 , umvrs )
 where
   oroots = obsRoots mctxt

   (pRsem,psubr) = gVarDenote mctxt prv
   (tksin,tksout) = partition (flip elem pRsem) tks
   (tusin,tusout) = partition (flip elemMS pRsem) tus
   (tRosin,tRosout) = partition (flip elemMS pRsem . fst) tRos
   tmatch = lnorm (tksin++tusin++map snd tRosin)

   [trv] = tRs
   (tRsem,tsubr) = gVarDenote mctxt trv
   psub1 = head psubr
   tsub1 = head tsubr
\end{code}

If we get here, then matching this reserved variable is deferred.
For now this is all reserved variables of the form $R\less{\ldots,u,\ldots}$
where $u \notin \sem R$.
\begin{code}
rsvMatch mctxt mres umvrs ctvs@(tks,tus,tls,tRs) tRos prv
 = return (ctvs, tRos, mres, prv:umvrs)
\end{code}

Variable equality, modulo subscripts:
\begin{code}
eqVModSubscript :: Variable -> Variable -> Bool
eqVModSubscript (r1,Subscript _,_) (r2,Subscript _,_)  =  r1 == r2
eqVModSubscript v1                 v2                  =  v1 == v2

[]       `eqvsMS` []        =  True
(v1:vs1) `eqvsMS` (v2:vs2)  =  v1 `eqVModSubscript` v2 && vs1 `eqvsMS` vs2
_        `eqvsMS` _         =  False

tRs `intsctMS` pMS = sort $ intersectBy eqVModSubscript tRs pMS

elemMS = elemBy eqVModSubscript

remRv rv tros = filter (not . (==rv) . snd) tros
\end{code}

\newpage
\subsubsection{Quantifier Matching, Phase 2}


We are now trying to match test
$$
a_1,\ldots,a_n , \lst b_1,\ldots,\lst b_m
$$
against pattern
$$
  u_1,\ldots,u_k ,  \lst v_1,\ldots,\lst v_\ell
$$
which will only work if
$$
n \geq k \land ((n \neq k \lor m > 0) \implies \ell > 0)
$$
A match is infeasible if the number of pattern standard variables
is greater than the number of test standard variables.
\begin{code}
qMatch2 :: Monad m
        => LocalContext -> MatchResult
        -> [Variable] -> [Variable] -> m MatchResult
\end{code}
Initially, we try to pick off some common simple cases.

\MRULES{
   \Gamma & s & t & \maplet s t
}
\begin{code}
qMatch2 here mres [tv@(Gen (Std _),_,_)] [pv@(Gen (Std _),_,_)]
 = mres `mrgRMR` (okBindV pv tv)
\end{code}
\MRULES{
   \Gamma & \lst x & (v_1,\ldots,v_n) & \maplet{\lst x}{(v_1,\ldots,v_n)}
\\ \Gamma|_{u\textsf{ not obs.}} & R\less u & \sem{R}\setminus\setof{k}
  & \mapof{ R\less u \to \sem{R}\setminus\setof k, u \to k }
}
\begin{code}
qMatch2 here mres tvs [pv]
 | isGenV pv  =  mres `mrgRMR` (okBindQL pv tvs)
 | isRsvV pv
   =  let (Rsv pr pless,pd,_) = pv
      in  srvMatch (mctx here) mres tvs pv pr pless pd
 | otherwise     =  fail "Nothing"

-- pattern singles must cover all test singles
-- then look at reserved list variables
qMatch2 here mres tvs pvs
 | n < k                         =  (fail "Nothing")
 | ell == 0 && (n > k || m > 0)  =  (fail "Nothing")
 | otherwise
     =  do (vebinds',tvs',pvs') <- matchRsvVs tvs pvs
           mres `mrgMR` ((tnil,vebinds',tnil),mkQVarsToDo tvs' pvs',[])
 where
   mctxt = mctx here
   (stdt,lstt) = vPartition tvs
   (stdp,lstp) = vPartition pvs
   n = length stdt ; m = length lstt
   k = length stdp ; ell = length lstp

   -- if all reserved list variables are 'clean', match them here
   -- matchRsvVs :: [Variable] -> [Variable]
   --            -> m (VEBind, [Variable], [Variable])
   matchRsvVs tvs pvs
    | tclean && pclean = mRsvVs tnil [] tvs pvs
    | otherwise  =  return (tnil,tvs,pvs)
    where
      tclean = all (cleanVar mctxt) tvs
      pclean = all (cleanVar mctxt) pvs

   -- for every (clean) pattern reserved variable,
   -- pull out its denotation from the test variables
   mRsvVs qbind svp tvs []  =  return $ (qbind,tvs,reverse svp)
   mRsvVs qbind svp tvs (pv:pvs)
    | isRsvV pv  =  do (mvs',tvs') <- getDen dvs tvs
                       qbind' <- veupdateVSO pv mvs' qbind
                       mRsvVs qbind' svp tvs' pvs
    | otherwise     =  mRsvVs qbind (pv:svp) tvs pvs
    where
      (dvs,_) = varExpand mctxt pv -- clean, so no subtractions

      -- getDen :: [Variable] -> [Variable] -> Maybe ([Variable],[Variable])
      getDen dvs tvs = gD dvs [] [] [] tvs

      gD dpv mdvs mvs svt []
        | dpv == mdvs'  =  return (lnorm mvs, reverse svt)
        | otherwise    =  fail ""
        where mdvs' = lnorm mdvs
      gD dpv mdvs mvs svt (tv:tvs)
       | dtv `subsetOf` dpv  =  gD dpv (dtv++mdvs) (tv:mvs) svt      tvs
       | otherwise           =  gD dpv mdvs        mvs        (tv:svt) tvs
       where
         (dtv,_) = varExpand mctxt tv
\end{code}

\newpage

Matching a single reserved list-variable (s.r.v.)
of the form $R\less{\ldots,u,\ldots}$ where $u$ might be an
observation variable.
against an arbitrary \texttt{QVar}-list.
\MRULES{
   \Gamma|_{u\textsf{ not obs.}} & R\less u & \sem{R}\setminus\setof{k}
 & \mapof{ R\less u \to \sem{R}\setminus\setof k, u \to k }
}
At this point we can assume that $R\less u$ iteself is not among the test variables
(as it would have been caught in Phase 1).
\begin{code}
srvMatch :: Monad m
         => MatchContext
         -> MatchResult
         -> [Variable] -- arbitrary test variables
         -> Variable   -- Reserved List-Variable (isRsvV)
         -> RsvRoot
         -> [GenRoot]
         -> Decor
         -> m MatchResult
\end{code}

Simplest case --- one of each, with one unknown subtraction each.
\MRULES{
   \Gamma|_{u,v\textsf{ not obs.}} & R\less u &R\less v
 & \mapof{ R\less u \to R\less v, u \to v }
}
\begin{code}
srvMatch mctxt mres [tv@(Rsv tr [v@(Std _)],td,_)] pv pr [u@(Std ustr)] pd
 | tr == pr && td `dMatch` pd
   = do bindU <- bindu u v
        bindR <- bindOL oroots pv [tv]
        bind' <- bindR `mrgB` bindU
        mres `mrgMR` (bind', [], [])
 where
  oroots = obsRoots mctxt
  bindu u v
   | ustr `elem` oroots  =  fail "Nothing" -- prevent known var matching unknown
   | otherwise           =  return $ bindV (genRootAsVar u) (genRootAsVar v)
\end{code}

Case $pv = R\less{ks,us}$
\begin{eqnarray*}
   \sem R &=& k_1,\ldots,k_i,k_{i+1},\ldots,k_n
\\ \sem{R\less{k_{i+1},\ldots,k_n,u_1,\ldots,u_n}}
   &=& k_1,\ldots,k_i \setminus u_1,\ldots,u_n
\end{eqnarray*}
Matching fails if $n > i$.
\begin{code}
srvMatch mctxt mres tvs pv pr pless@(_:_) pd
 | all isStdG pless && length psubg <= length mkvs
   = do bindR <- bindOL oroots pv $ lnorm (mrest++akvs)
        bind' <- bindR `mrgB` (tnil, subbind, tnil)
        mres `mrgMR` (bind', [], [])
 where
   (pkvs,psubg) = gVarDenote mctxt pv -- (Rsv pr [], pd, varKey pv)
   akvs = tvs `intsctMS` pkvs
   mkvs = pkvs \\ akvs
   oroots = obsRoots mctxt
   (subbind,mrest) = pairup [] psubg mkvs

   -- greedy, match in the order in which they occur
   pairup pairs [] mkvs = (lbuild pairs,mkvs)
   pairup pairs (pg:psubg) (mkv:mkvs)
    = pairup ((renderVar (Gen pg) pd, VO mkv):pairs) psubg mkvs
\end{code}

Case $tvs = ks,R_t\less{ks'}$, and $pv = R_p\less{\lst u}$.
Provided $\sem{R_t}\setminus ks' \subseteq \sem{R_p}$:
\begin{eqnarray*}
   \sem{R_p\less{\lst u}} &=& \sem{R_p} \ominus \setof{\lst u}
\\ \sem{ks,R_t\less{ks'}} &=& ks \cup \sem{R_t} \setminus ks' \ominus \emptyset
\\ \lst u &\mapsto& \sem{R_t}\setminus (ks \cup \sem{R_t} \setminus ks')
\end{eqnarray*}
\begin{code}
srvMatch mctxt mres tvs pv pr [us@(Lst ustr)] pd
 | issing pX && null tX && null (tV\\allV)
   = do bindR <- bindOL oroots pv tvs
        bind' <- bindR `mrgB` bindQL (mkGVar pd us) (allV\\tV)
        mres `mrgMR` (bind', [], [])
 where
   (pV,pX) = gVarDenote mctxt pv
   issing [_] = True
   issing _   = False
   (allV,_) = gVarDenote mctxt $ mkRVar pr [] pd
   (tV,tX) = varsDenote mctxt tvs
   oroots = obsRoots mctxt

srvMatch _ _ _ _ _ _ _ = fail "Nothing"
\end{code}


To allow $Q$ to match against $\forall \lst x @ P$
with $\lst x$ bound to nil, we need a special matcher
\begin{eqnarray*}
   \MRNullQuantZN && \MRNullQuantZ
\end{eqnarray*}
\begin{code}
qMatchNull :: Monad m
           => MatchResult
           -> QVars             -- pattern QVars
           -> m MatchResult

qMatchNull mres ( qs)
 | all isGenV qs = mres `mrgMR` (injQLbind $ map bindnull qs)
 | otherwise  =  fail "Nothing"
 where bindnull (_,_,vs) = (vs,[])
\end{code}

\newpage
\subsubsection{Valid reserved list-Variable lists}



\newpage
\section{Formal Stuff Gathered}
\input{doc/formal/Matching-Structural}
\input{doc/formal/Matching-Decoration}
\input{doc/formal/Matching-List}
\input{doc/formal/Matching-Infix}
\input{doc/formal/Matching-Type-Rules}

\newpage
\subsection{Formal Array macros gathered}

MRSTRUCT
\MRSTRUCT

MRDECOR
\MRDECOR

MRLISTVAR
\MRLISTVAR

MRRSVSINGLE
\MRRSVSINGLE

MRTWOPLACE
\MRTWOPLACE

MRBINOP
\MRBINOP

MRTYPE
\MRTYPE
