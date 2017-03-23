\section{Formula Manipulation}

\begin{code}
module Manipulation where
import Tables
import Datatypes
import DataText
import Flatten
import Focus
import MatchTypes
import Matching
import AlphaSubs
import FreeBound
import Types
import SideConditions
import Substitution
import Heuristics
import Utilities
import DSL
import Data.List
import Data.Maybe
import Debug.Trace
\end{code}

Here we collect a variety of built-in manipulations
that can be applied the focus of a goal predicate.

\newpage
\subsection{Application}

We implement $\beta$-reduction for predicate application:
\begin{code}
predBetaReduce mctxt sc pr@( PApp nm1 [PAbs nm2 _ vs [bodyp], argp] )
  | nm1 == n_PVApp && nm2 == n_PVAbs  =  pvBetaR mctxt sc vs bodyp argp
  | nm1 == n_PEApp && nm2 == n_PEAbs  =  peBetaR mctxt sc vs bodyp argp
predBetaReduce mctxt sc pr = pr


pvBetaR mctxt sc [] bodyp arg  =  bodyp
pvBetaR mctxt sc [pv] bodyp argp
  | isStdV pv  =  predPSub argp (varGenRoot pv) bodyp
pvBetaR mctxt sc (pv:qvs) bodyp argp
  | isStdV pv  =  pvAbs qvs $ predPSub argp (varGenRoot pv) bodyp
pvBetaR mctxt sc pvs bodyp argp = pvApp (pvAbs pvs bodyp) argp

peBetaR mctxt sc [] bodyp arge  =  bodyp
peBetaR mctxt sc [ev] bodyp (PExpr arge)
  | isStdV ev  =  predONSub mctxt sc (mkSubs arge ev) bodyp
peBetaR mctxt sc (ev:qvs) bodyp (PExpr arge)
 | isStdV ev  = peAbs qvs $ predONSub mctxt sc (mkSubs arge ev) bodyp
peBetaR mctxt sc pvs bodyp argp = peApp (peAbs pvs bodyp) argp
\end{code}

\newpage
\subsection{Proof Procedures}



\subsubsection{Predicate Tidy-Up}

We do some simple tidying,
eliminating \texttt{TRUE}, \texttt{FALSE}
and $\Defd(v)$
where possible, ordering lists
and deleting (some) duplicate predicates, if requested:
\begin{code}
prTidy (cTdy,dTdy) (PApp nm [PExpr (Var _)])
 | nm == n_Defd  =  TRUE

prTidy (cTdy,dTdy) (PApp nm [pr])
 | nm == n_Not  =  mkNot (prTidy (cTdy,dTdy) pr)

prTidy (cTdy,dTdy) (PApp nm prs)
 | nm == n_And  =  prTidyAnd $ cTdy prs'
 | nm == n_Or   =  prTidyOr  $ dTdy prs'
 | otherwise    =  PApp nm prs'
 where prs' = map (prTidy (cTdy,dTdy)) prs

prTidy (cTdy,dTdy) (PAbs nm _ qvs prs)
  | hasUnorderedQVars nm = PAbs nm 0 (lnorm qvs) prs'
  | otherwise            = PAbs nm 0 qvs prs'
  where prs' = map (prTidy (cTdy,dTdy)) prs

prTidy (cTdy,dTdy) (Sub pr sub) = Sub (prTidy (cTdy,dTdy) pr) sub

-- not inside Lexts
prTidy (cTdy,dTdy) pr = pr

prTidyAnd prs
 | null prs  =  TRUE
 | null (tail prs)  =  head prs
 | otherwise        =  mkAnd prs

prTidyOr prs
 | null prs  =  FALSE
 | null (tail prs)  =  head prs
 | otherwise         =  mkOr prs

hasUnorderedQVars nm
 = nm `elem` [n_Forall,n_Exists]

predTidy nodup = prTidy (predConjTidy nodup, predDisjTidy nodup)

hm_tidyFlat = (
    unlines $ [" : Tidy (flatten)\n",
    "Flattens out expressions of the form:",
    "a*(b*c)",
    "into",
    "a * b * c,",
    "for commutative *."])

predFlatten = prTidy (conjFlatten [], disjFlatten [])
predSort = prTidy (sort, sort)

hm_tidySortDups = (
    unlines $ [" : Tidy (sort, remove duplicates)\n",
    "Does the same as the tidy command \'T\'",
    "only does not flatten any of the expressions."])

predRemDup = prTidy (removeDupPreds . sort, removeDupPreds . sort)

data TidySpec = Tflt | Tsrt | Trdp | Tsf | Tall deriving (Eq,Ord)
instance Show TidySpec where
 show Tflt = "assoc"
 show Tsrt = "comm"
 show Trdp = "comm-idem"
 show Tsf  = "assoc-comm"
 show Tall = "assoc-comm-idem"

hm_tidySort = (
    unlines $ [" : Tidy (sort)\n",
    "Attempts to group like terms in an expression."])

hm_tidyFlatSort = (
    unlines $ [" : Tidy (flatten & sort)\n",
    "A shortcut combination of the two tidy commands \'<\' and \'-\'."])

hm_tidyFlatSortDups = (
    unlines $ [" : Tidy (flatten, sort, remove duplicates)\n",
    "Does the same job as tidy, \'t\',",
    "but also attempts to remove duplicate expressions",
    "e.g. this function will ideally convert",
    "a * a * b * a",
    "to",
    "a * b,",
    "if * is idempotent."])

tidyPred Tsrt = predSort
tidyPred Tflt = predFlatten
tidyPred Trdp = predRemDup
tidyPred Tsf  = predTidy False
tidyPred Tall = predTidy True
\end{code}

\newpage
\subsubsection{Predicate Simplification}

MOST OF THIS NEEDS TO GO TO MODULES TO DO WITH THE "ROOT-THEORY".

Predicate simplification is
essentially recursive constant-folding.
\begin{code}
hm_predSimp = (
    unlines $ [" : Simplify\n",
    "Performs easy simplifications like constant folding, e.g.:",
    " TRUE /\\ P   -->  P",
    " FALSE /\\ P  -->  FALSE",
    " Q \\/ FALSE  -->  Q",
    " Q \\/ TRUE   -->  TRUE"])

predSimp :: Pred -> Pred
\end{code}
\begin{code}
predSimp (PApp nm prs) = predAppSimp nm prs
predSimp (PAbs nm tt qs prs) = predAbsSimp nm qs prs
predSimp (Sub pr sub) = Sub (predSimp pr) sub
predSimp pr = pr
\end{code}

THIS CODE SHOULD LOOKUP '\texttt{nm}' IN A TABLE!
\begin{code}
predAppSimp nm prs
 | nm == n_Defd && length prs == 1  =  predSimpDefd pr
 | nm == n_Not && length prs == 1   =  predSimpNot pr
 | nm == n_And                      =  predSimpAnd prs
 | nm == n_Or                       =  predSimpOr  prs
 | nm == n_Imp && length prs == 2   =  predSimpImp pr1 pr2
 | nm == n_Eqv && length prs == 2   =  predSimpEqv pr1 pr2
 | nm == n_If  && length prs == 3   =  predSimpIf  prc prt pre
 where
   [pr]          = prs
   [pr1,pr2]     = prs
   [prc,prt,pre] = prs
predAppSimp nm prs = PApp nm prs
\end{code}

ALL THIS CODE BELONGS WITH 'ROOT THEORY' STUFF

\begin{code}
predSimpDefd (PApp nm [PExpr (Var _)])
 | nm == n_Defd  =  TRUE              -- Vars always defined
predSimpDefd pr  =  PApp n_Defd [pr]
\end{code}

\begin{code}
predSimpNot TRUE                          = FALSE
predSimpNot FALSE                         = TRUE
predSimpNot (PApp nm [pr]) | nm == n_Not  =  predSimp pr
predSimpNot pr                            = mkNot $predSimp pr
\end{code}

\begin{code}
predSimpAnd prs
 | null prs'          =  TRUE
 | length prs' == 1   =  head prs'
 | FALSE `elem` prs'  =  FALSE
 | otherwise          =  mkAnd prs'
 where prs' = remPred predIsTrue (map predSimp prs)
\end{code}

\begin{code}
predSimpOr prs
 | null prs'          =  FALSE
 | length prs' == 1   =  head prs'
 | TRUE `elem` prs'   =  TRUE
 | otherwise          =  mkOr prs'
 where prs' = remPred predIsFalse (map predSimp prs)
\end{code}

\begin{code}
predSimpImp pr1 TRUE   =  TRUE
predSimpImp FALSE pr2  =  TRUE
predSimpImp TRUE pr2   =  predSimp pr2
predSimpImp pr1 FALSE  =  mkNot (predSimp pr1)
predSimpImp pr1 pr2    =  mkImp (predSimp pr1) (predSimp pr2)
\end{code}

\begin{code}
predSimpEqv TRUE pr2   =  predSimp pr2
predSimpEqv pr1 TRUE   =  predSimp pr1
predSimpEqv FALSE pr2  =  mkNot (predSimp pr2)
predSimpEqv pr1 FALSE  =  mkNot (predSimp pr1)
predSimpEqv pr1 pr2    =  mkEqv (predSimp pr1) (predSimp pr2)
\end{code}

\begin{code}
predSimpIf TRUE prt pre    =  predSimp prt
predSimpIf FALSE prt pre   =  predSimp pre
predSimpIf cond TRUE pre   =  predSimp $ mkOr  [cond, pre]
predSimpIf cond prt TRUE   =  predSimp $ mkOr  [mkNot cond, prt]
predSimpIf cond FALSE pre  =  predSimp $ mkAnd [mkNot cond, pre]
predSimpIf cond prt FALSE  =  predSimp $ mkAnd [cond, prt]
predSimpIf prc prt pre
 = mkIf (predSimp prc) (predSimp prt) (predSimp pre)
\end{code}

THIS CODE SHOULD LOOKUP '\texttt{nm}' IN A TABLE!
\begin{code}
predAbsSimp nm qs [pr]
 | nm == n_Forall   =  predSimpForall  qs pr
 | nm == n_Exists   =  predSimpExists  qs pr
 | nm == n_Exists1  =  predSimpExists1 qs pr
 | nm == n_Univ     =  predSimpUniv       pr
predAbsSimp nm qs prs = PAbs nm 0 qs (map predSimp prs)
\end{code}

ALL THIS CODE BELONGS WITH 'ROOT THEORY' STUFF

Quantification:
\begin{code}
predSimpForall [] pr     =  predSimp pr
predSimpForall _  TRUE   =  TRUE
predSimpForall _  FALSE  =  FALSE
predSimpForall qs pr
 = case predSimp pr of
    TRUE  -> TRUE
    FALSE -> FALSE
    spr   -> mkForall qs spr
\end{code}

\begin{code}
predSimpExists [] pr     =  predSimp pr
predSimpExists qs TRUE   =  TRUE
predSimpExists qs FALSE  =  FALSE
predSimpExists qs pr
 = case predSimp pr of
    TRUE -> TRUE
    FALSE -> FALSE
    spr -> mkExists qs spr
\end{code}

\begin{code}
predSimpExists1 [] pr     =  FALSE
predSimpExists1 qs TRUE   =  FALSE
predSimpExists1 qs FALSE  =  FALSE
predSimpExists1 qs pr
 = case predSimp pr of
    TRUE  -> TRUE
    FALSE -> FALSE
    spr   -> mkExists1 qs spr
\end{code}

\begin{code}
predSimpUniv pr
 = case predSimp pr of
     TRUE   ->  TRUE
     FALSE  ->  FALSE
     spr    ->  mkUniv spr
\end{code}


Various auxiliaries used to define the above.
\begin{code}
predIsTrue TRUE      = True
predIsTrue _         = False

predIsFalse FALSE     = True
predIsFalse _         = False

remPred c [] = []
remPred c (pr:prs) = if c pr then prs' else pr:prs' where prs' = remPred c prs
\end{code}

\newpage
\subsection{Assert Definedness}

This replaces a boolean-value (top-level) expression $e$ by $e \land \Defd(e)$.

\begin{code}
assertDefined pr@(PExpr e) = mkAnd [pr,mkDefd e]
assertDefined pr         = pr
\end{code}


\subsection{Predicate-List Splitting}

Sometimes it is useful to split a predicate list into two parts,
according to some predicate:
\begin{code}
hm_binderSplit = (
    unlines $ [" : Binder Split\n",
    "This splits a quantified expression into bound and unbound variables.",
    "Imagine you had an expression (Q xs | v1 * v2 * ... * vn),",
    "* being an associative, commutative, operator",
    "and Q being some form of quantification (exists or forall).",
    "Then performing a binder split will re-order the inner expression",
    "v1 * v2 * ... * vn",
    "so that all the variables bound by the quantification are grouped together.",
    "In other words, the inner expression is split into bound and unbound terms.",
    "The advantage of this is that the unbound terms can be moved,",
    "all at once, outside the expression."])

splitPred splitp (PApp nm prs)
 | isSplittable nm  = PApp nm (joinsplit (PApp nm) sat notsat)
 where (sat,notsat) = partition splitp prs
splitPred _ pr = pr
\end{code}

For now, we hardcode \texttt{isIndexSplittable},
but eventually this will have to come form a table:
\begin{code}
isSplittable nm
 = nm `elem` [n_And,n_Or]
\end{code}


We need to be careful if either sat or notsat are empty or singleton:
\begin{code}
joinsplit con sat []      = sat
joinsplit con []  notsat  = notsat
joinsplit con sat notsat = [mk con sat,mk con notsat]
 where
   mk con [pr] = pr
   mk con prs  = con prs
\end{code}

\subsubsection{Binder-based Split Predicate}
We can split on the basis of the binding
of free variables
\begin{code}
isFreeUnder bs pr
 = null (lnorm (predFreeOVars nullMatchContext pr) `intersect` (lnorm bs))
\end{code}

\newpage
\subsubsection{Splitting by Indices}

Alternatively, we can use an index list to pull the values apart
(re-ordering to match the index order):
\begin{code}
hm_indexSplit = (
    unlines $
    [ " : Index Split\n",
    "Given a focus of the form:",
    "   v1 * v2 * ... * vn",
    "...where * is associative, commutative operator.",
    "You provide an list of indices in any order.",
    "The corresponding elements are gathered and brought to the front",
    "For example, if you had an expression of the form above",
    "and you typed in \'3, 2\',",
    "you\'d end up with an expression of the form:",
    "  (v3 * v2) * (v1 * v4 * v5 *...*vn)"
    ])

-- And/Or splitting
indicesSplitPred ixs (PApp nm prs)
 | isIndexSplittable nm = PApp nm  (joinsplit mkAnd ixd notixd)
 where (ixd,notixd) = indicesSplit ixs prs

-- Quantifer splitting
indicesSplitPred ixs (PAbs nm _ qvs bdps)
  | isIndexSplittable nm = PAbs nm 0 qixd [PAbs nm 0 qnotixd bdps]
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs

indicesSplitPred _ pr = pr
\end{code}
For now, we hardcode \texttt{isIndexSplittable},
but eventually this will have to come form a table:
\begin{code}
isIndexSplittable nm
 = nm `elem` [n_And,n_Or,n_Forall,n_Exists]
\end{code}


\newpage

The indices-splitting function that does the hard work:
\begin{code}
indicesSplit :: Eq a => [Int] -> [a] -> ([a],[a])
indicesSplit ixs xs
 = (selected,rest)
 where
   len = length xs
   ixs' = filter (inrange len) ixs
   inrange len ix = 1 <= ix && ix <= len
   selected = nub $ map (getfrom xs) ixs'
   rest = remove ixs xs
   getfrom xs ix = xs!!(ix-1)
   remove ixs xs = catMaybes $ markgone ixs 1 xs
   markgone ixs ix [] = []
   markgone ixs ix (x:xs)
    | ix `elem` ixs  =  Nothing : rest
    | otherwise      =  Just x : rest
    where rest = markgone ixs (ix+1) xs
\end{code}

Splitting \texttt{QVars}:
(\emph{Needs re-writing to take account of \texttt{ixs} ordering..}.)
\begin{code}
qvarsIxSplit ixs ( qs)
 = qixSpl qxs [] [] 1 ixs xs
 where
   (xs,qxs) = vPartition qs

   qixSpl qxs dxi dxinot i ixs [] = qixSpl' dxi dxinot [] [] i ixs qxs

   qixSpl qxs dxi dxinot i [] xs = ( dxi, (reverse dxinot++xs++qxs))

   qixSpl qxs dxi dxinot i iixs@(ix:ixs) (x:xs)
    | i <  ix    =  qixSpl qxs dxi     (x:dxinot) i' iixs xs
    | i == ix    =  qixSpl qxs (x:dxi) dxinot     i' ixs  xs
    | otherwise  =  qixSpl qxs dxi     (x:dxinot) i' ixs  xs
    where i'=i+1

   qixSpl' dxi dxinot dxiq dxinotq i ixs []
    = (  (reverse dxi++reverse dxiq)
      ,  (reverse dxinot++reverse dxinotq) )

   qixSpl' dxi dxinot dxiq dxinotq i [] qxs
    = (  (reverse dxi++reverse dxiq)
      ,  (reverse dxinot++reverse dxinotq++qxs) )

   qixSpl' dxi dxinot dxiq dxinotq i iixs@(ix:ixs) (qx:qxs)
    | i <  ix    =  qixSpl' dxi dxinot dxiq      (qx:dxinotq) i' iixs qxs
    | i == ix    =  qixSpl' dxi dxinot (qx:dxiq) dxinotq      i' ixs qxs
    | otherwise  =  qixSpl' dxi dxinot dxiq      (qx:dxinotq) i' ixs qxs
    where i'=i+1
\end{code}


\newpage
\subsection{Predicate Expansion}

Given a predicate-table list, we fully expand all \texttt{PVar}s
in a predicate, descending recursively.
This works even if the table has circular dependencies.
A parameter function (\texttt{pf :: Pred -> Pred}) is used to clean
up each predicate extracted from the table:
\begin{code}
expandPred pf preds pr
 = pf (expand [] pr)
 where
   expand ns pr@(PVar v)
     | v `elem` ns  =  pr
     | otherwise
        = case tslookup preds $ show v of
           Nothing  ->  pr
           (Just prdef)
            -> expand (v:ns) (pf prdef)
   expand ns (PApp nm prs) = PApp nm (map (expand ns) prs)
   expand ns (PAbs nm _ qs prs) = PAbs nm 0 qs (map (expand ns) prs)
   expand ns (Sub pr sub) = Sub (expand ns pr) sub
   expand ns pr = pr
\end{code}
Note that this function does not enter expressions and
so will not expand \texttt{PVar}s inside set/sequence comprehensions at present.
