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
predBetaReduce mctxt sc (Papp (Ppabs (Q []) bodyp) argp)  = bodyp
predBetaReduce mctxt sc (Papp (Ppabs (Q [pv]) bodyp) argp) | isStdV pv
  = predPSub argp (varGenRoot pv) bodyp
predBetaReduce mctxt sc (Papp (Ppabs (Q (pv:qvs)) bodyp) argp) | isStdV pv
  = Ppabs (Q qvs) $ predPSub argp (varGenRoot pv) bodyp

predBetaReduce mctxt sc (Papp (Peabs (Q []) bodyp) (Obs arge))
  = bodyp
predBetaReduce mctxt sc (Papp (Peabs (Q [ev]) bodyp) (Obs arge)) | isStdV ev
  = predONSub mctxt sc (mkSubs arge ev) bodyp
predBetaReduce mctxt sc (Papp (Peabs (Q (ev:qvs)) bodyp) (Obs arge)) | isStdV ev
  = Peabs (Q qvs) $ predONSub mctxt sc (mkSubs arge ev) bodyp

predBetaReduce mctxt sc pr = pr
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
-- not inside Lexts
prTidy (cTdy,dTdy) (Defd (Var _)) = TRUE
prTidy (cTdy,dTdy) (Not pr) = Not (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (And prs)
 | null prs'  =  TRUE
 | null (tail prs')  =  head prs'
 | otherwise         =  mkAnd prs'
 where prs' = cTdy (map (prTidy (cTdy,dTdy)) prs)
prTidy (cTdy,dTdy) (Or prs)
 | null prs'  =  FALSE
 | null (tail prs')  =  head prs'
 | otherwise         =  mkOr prs'
 where prs' = dTdy (map (prTidy (cTdy,dTdy)) prs)
prTidy (cTdy,dTdy) (NDC pr1 pr2)
  = NDC (prTidy (cTdy,dTdy) pr1) (prTidy (cTdy,dTdy) pr2)
prTidy (cTdy,dTdy) (Imp pr1 pr2)
  = Imp (prTidy (cTdy,dTdy) pr1) (prTidy (cTdy,dTdy) pr2)
prTidy (cTdy,dTdy) (Eqv pr1 pr2)
  = Eqv (prTidy (cTdy,dTdy) pr1) (prTidy (cTdy,dTdy) pr2)
prTidy (cTdy,dTdy) (If prc prt pre)
  = If (prTidy (cTdy,dTdy) prc) (prTidy (cTdy,dTdy) prt) (prTidy (cTdy,dTdy) pre)
prTidy (cTdy,dTdy) (Forall tt qvs pr)
  = Forall 0 (lqnorm qvs) (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Exists tt qvs pr)
  = Exists 0 (lqnorm qvs) (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Exists1 tt qvs pr)
  = Exists1 0 (lqnorm qvs) (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Univ tt pr) = Univ 0 (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Sub pr sub) = Sub (prTidy (cTdy,dTdy) pr) sub
prTidy (cTdy,dTdy) (Ppabs s pr) = Ppabs s (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Papp prf pra)
  = Papp (prTidy (cTdy,dTdy) prf) (prTidy (cTdy,dTdy) pra)
prTidy (cTdy,dTdy) (Psapp pr spr) = Psapp (prTidy (cTdy,dTdy) pr) spr
prTidy (cTdy,dTdy) (Psin pr spr) = Psin (prTidy (cTdy,dTdy) pr) spr
prTidy (cTdy,dTdy) (Pforall pvs pr) = Pforall pvs (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Pexists pvs pr) = Pexists pvs (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) (Peabs s pr) = Peabs s (prTidy (cTdy,dTdy) pr)
prTidy (cTdy,dTdy) pr = pr

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
\end{code}

First, casting expression truth values up to predicate level:
\begin{code}
predSimp (Obs T) = TRUE
predSimp (Obs F) = FALSE
\end{code}

For now, we consider that variables always denote
\begin{code}
predSimp (Defd (Var _)) = TRUE
\end{code}

Negation:
\begin{code}
predSimp (Not TRUE) = FALSE
predSimp (Not FALSE) = TRUE
predSimp (Not (Obs T)) = FALSE
predSimp (Not (Obs F)) = TRUE
predSimp (Not (Not pr)) = predSimp pr
predSimp (Not pr) = Not (predSimp pr)
\end{code}

Conjunction and Disjunction are dual so get similar treatment:
\begin{code}
predSimp (And prs)
 | null prs'          =  TRUE
 | length prs' == 1   = head prs'
 | FALSE `elem` prs'  =  FALSE
 | F `oelem` prs'     =  FALSE
 | otherwise          =  mkAnd prs'
 where prs' = remPred predIsTrue (map predSimp prs)

predSimp (Or prs)
 | null prs'          =  FALSE
 | length prs' == 1   = head prs'
 | TRUE `elem` prs'   =  TRUE
 | T `oelem` prs'     =  TRUE
 | otherwise          =  mkOr prs'
 where prs' = remPred predIsFalse (map predSimp prs)
\end{code}

\newpage
Implication, Equivalence and Conditional:
\begin{code}
predSimp (Imp pr1 TRUE) = TRUE
predSimp (Imp FALSE pr2) = TRUE
predSimp (Imp TRUE pr2) = predSimp pr2
predSimp (Imp pr1 FALSE) = Not (predSimp pr1)
predSimp (Imp pr1 (Obs T)) = TRUE
predSimp (Imp (Obs F) pr2) = TRUE
predSimp (Imp (Obs T) pr2) = predSimp pr2
predSimp (Imp pr1 (Obs F)) = Not (predSimp pr1)
predSimp (Imp pr1 pr2) = Imp (predSimp pr1) (predSimp pr2)

predSimp (Eqv TRUE pr2) = predSimp pr2
predSimp (Eqv pr1 TRUE) = predSimp pr1
predSimp (Eqv FALSE pr2) = Not (predSimp pr2)
predSimp (Eqv pr1 FALSE) = Not (predSimp pr1)
predSimp (Eqv (Obs T) pr2) = predSimp pr2
predSimp (Eqv pr1 (Obs T)) = predSimp pr1
predSimp (Eqv (Obs F) pr2) = Not (predSimp pr2)
predSimp (Eqv pr1 (Obs F)) = Not (predSimp pr1)
predSimp (Eqv pr1 pr2) = Eqv (predSimp pr1) (predSimp pr2)

predSimp (If TRUE prt pre) = predSimp prt
predSimp (If FALSE prt pre) = predSimp pre
predSimp (If (Obs T) prt pre) = predSimp prt
predSimp (If (Obs F) prt pre) = predSimp pre
predSimp (If cond TRUE pre) = predSimp $ Or [cond, pre]
predSimp (If cond prt TRUE) = predSimp $ Or [Not cond, prt]
predSimp (If cond FALSE pre) = predSimp $ And [Not cond, pre]
predSimp (If cond prt FALSE) = predSimp $ And [cond, prt]
predSimp (If cond (Obs T) pre) = predSimp $ Or [cond, pre]
predSimp (If cond prt (Obs T)) = predSimp $ Or [Not cond, prt]
predSimp (If cond (Obs F) pre) = predSimp $ And [Not cond, pre]
predSimp (If cond prt (Obs F)) = predSimp $ And [cond, prt]
predSimp (If prc prt pre)
 = If (predSimp prc) (predSimp prt) (predSimp pre)
\end{code}

Quantification:
\begin{code}
predSimp (Forall _ (Q []) pr) = predSimp pr
predSimp (Forall _ qs TRUE) = TRUE
predSimp (Forall _ qs FALSE) = FALSE
predSimp (Forall _ qs (Obs T)) = TRUE
predSimp (Forall _ qs (Obs F)) = FALSE
predSimp (Forall _ qs pr)
 = case (predSimp pr) of
    TRUE -> TRUE
    FALSE -> FALSE
    spr -> Forall 0 qs spr

predSimp (Exists _ (Q []) pr) = predSimp pr
predSimp (Exists _ qs TRUE) = TRUE
predSimp (Exists _ qs FALSE) = FALSE
predSimp (Exists _ qs (Obs T)) = TRUE
predSimp (Exists _ qs (Obs F)) = FALSE
predSimp (Exists _ qs pr)
 = case (predSimp pr) of
    TRUE -> TRUE
    FALSE -> FALSE
    spr -> Exists 0 qs spr

predSimp (Exists1 _ (Q []) pr) = FALSE
predSimp (Exists1 _ qs TRUE) = FALSE
predSimp (Exists1 _ qs FALSE) = FALSE
predSimp (Exists1 _ qs (Obs T)) = FALSE
predSimp (Exists1 _ qs (Obs F)) = FALSE
predSimp (Exists1 _ qs pr)
 = case (predSimp pr) of
    TRUE -> TRUE
    FALSE -> FALSE
    spr -> Exists1 0 qs spr

predSimp (Univ _ pr)
 = case (predSimp pr) of
     TRUE   ->  TRUE
     FALSE  ->  FALSE
     spr    ->  Univ 0 spr
\end{code}

Miscellaneous stuff:
\begin{code}
predSimp (Sub pr sub) = Sub (predSimp pr) sub
predSimp (Ppabs s pr) = Ppabs s (predSimp pr)
predSimp (Papp prf pra) = Papp (predSimp prf) (predSimp pra)
predSimp (Psapp pr spr) = Psapp (predSimp pr) (psetSimp spr)
predSimp (Psin pr spr) = Psin (predSimp pr) (psetSimp spr)
predSimp (Pforall pvs pr) = Pforall pvs (predSimp pr)
predSimp (Pexists pvs pr) = Pexists pvs (predSimp pr)
predSimp (Peabs s pr) = Peabs s (predSimp pr)

predSimp pr = pr
\end{code}

Various auxiliaries used to define the above.
\begin{code}
psetSimp (PSet prs) = PSet (map predSimp prs)
psetSimp (PSetC nms pr1 pr2) = PSetC nms (predSimp pr1) (predSimp pr2)
psetSimp (PSetU s1 s2) = PSetU (psetSimp s1) (psetSimp s2)
psetSimp s = s

_ `oelem` []                 =  False
e `oelem` ((Obs e'):rest)  =  e == e' || e `oelem` rest
e `oelem` (_:rest)          =  e `oelem` rest

predIsTrue TRUE      = True
predIsTrue (Obs T) = True
predIsTrue _         = False

predIsFalse FALSE     = True
predIsFalse (Obs F) = True
predIsFalse _         = False

remPred c [] = []
remPred c (pr:prs) = if c pr then prs' else pr:prs' where prs' = remPred c prs
\end{code}

\newpage
\subsection{Assert Definedness}

This replaces a boolean-value (top-level) expression $e$ by $e \land \Defd(e)$.

\begin{code}
assertDefined pr@(Obs e) = And [pr,Defd e]
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

splitPred splitp (And prs) = mkAnd (joinsplit mkAnd sat notsat)
 where (sat,notsat) = partition splitp prs
splitPred splitp (Or prs) = mkOr (joinsplit mkOr sat notsat)
 where (sat,notsat) = partition splitp prs
splitPred _ pr = pr
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
indicesSplitPred ixs (And prs) = And (joinsplit mkAnd ixd notixd)
 where (ixd,notixd) = indicesSplit ixs prs
indicesSplitPred ixs (Or prs) = Or (joinsplit mkOr ixd notixd)
 where (ixd,notixd) = indicesSplit ixs prs

-- Quantifer splitting
indicesSplitPred ixs (Forall _ qvs bdp)
  = Forall 0 qixd (Forall 0 qnotixd bdp)
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs
indicesSplitPred ixs (Exists _ qvs bdp)
  = Exists 0 qixd (Exists 0 qnotixd bdp)
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs

indicesSplitPred ixs (Pforall qvs pr)
  = Pforall qixd (Pforall qnotixd pr)
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs
indicesSplitPred ixs (Pexists qvs pr)
  = Pexists qixd (Pexists qnotixd pr)
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs

indicesSplitPred ixs (Peabs qvs pr)
  = Peabs qixd (Peabs qnotixd pr)
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs
indicesSplitPred ixs (Ppabs qvs pr)
  = Ppabs qixd (Ppabs qnotixd pr)
  where (qixd,qnotixd) = qvarsIxSplit ixs qvs

indicesSplitPred _ pr = pr
\end{code}

\newpage The indices-splitting function that does the hard work:
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
qvarsIxSplit ixs (Q qs)
 = qixSpl qxs [] [] 1 ixs xs
 where
   (xs,qxs) = vPartition qs

   qixSpl qxs dxi dxinot i ixs [] = qixSpl' dxi dxinot [] [] i ixs qxs

   qixSpl qxs dxi dxinot i [] xs = (Q dxi,Q (reverse dxinot++xs++qxs))

   qixSpl qxs dxi dxinot i iixs@(ix:ixs) (x:xs)
    | i <  ix    =  qixSpl qxs dxi     (x:dxinot) i' iixs xs
    | i == ix    =  qixSpl qxs (x:dxi) dxinot     i' ixs  xs
    | otherwise  =  qixSpl qxs dxi     (x:dxinot) i' ixs  xs
    where i'=i+1

   qixSpl' dxi dxinot dxiq dxinotq i ixs []
    = ( Q (reverse dxi++reverse dxiq)
      , Q (reverse dxinot++reverse dxinotq) )

   qixSpl' dxi dxinot dxiq dxinotq i [] qxs
    = ( Q (reverse dxi++reverse dxiq)
      , Q (reverse dxinot++reverse dxinotq++qxs) )

   qixSpl' dxi dxinot dxiq dxinotq i iixs@(ix:ixs) (qx:qxs)
    | i <  ix    =  qixSpl' dxi dxinot dxiq      (qx:dxinotq) i' iixs qxs
    | i == ix    =  qixSpl' dxi dxinot (qx:dxiq) dxinotq      i' ixs qxs
    | otherwise  =  qixSpl' dxi dxinot dxiq      (qx:dxinotq) i' ixs qxs
    where i'=i+1
\end{code}


\newpage
\subsection{Predicate Expansion}

Given a predicate-table list, we fully expand all \texttt{Pvar}s
in a predicate, descending recursively.
This works even if the table has circular dependencies.
A parameter function (\texttt{pf :: Pred -> Pred}) is used to clean
up each predicate extracted from the table:
\begin{code}
expandPred pf preds pr
 = pf (expand [] pr)
 where
   expand ns pr@(Pvar r)
     | v `elem` ns  =  pr
     | otherwise
        = case tslookup preds $ show r of
           Nothing  ->  pr
           (Just prdef)
            -> expand (v:ns) (pf prdef)
     where v = rootVar $ Gen r
   expand ns (Not pr) = Not (expand ns pr)
   expand ns (And prs) = mkAnd (map (expand ns) prs)
   expand ns (Or prs) = mkOr (map (expand ns) prs)
   expand ns (NDC pr1 pr2) = NDC (expand ns pr1) (expand ns pr2)
   expand ns (Imp pr1 pr2) = Imp (expand ns pr1) (expand ns pr2)
   expand ns (RfdBy pr1 pr2) = RfdBy (expand ns pr1) (expand ns pr2)
   expand ns (Eqv pr1 pr2) = Eqv (expand ns pr1) (expand ns pr2)
   expand ns (If prc prt pre)
    = If (expand ns prc) (expand ns prt) (expand ns pre)
   expand ns (Forall _ qs pr) = Forall 0 qs (expand ns pr)
   expand ns (Exists _ qs pr) = Exists 0 qs (expand ns pr)
   expand ns (Exists1 _ qs pr)  = Exists1 0 qs (expand ns pr)
   expand ns (Univ _ pr) = Univ 0 (expand ns pr)
   expand ns (Sub pr sub) = Sub (expand ns pr) sub
   expand ns (Ppabs qs@(Q pvs) pr) = Ppabs qs (expand (pvs++ns) pr)
   expand ns (Papp prf pra) = Papp (expand ns prf) (expand ns pra)

   expand ns (Psapp pr spr) = Psapp (expand ns pr) (sexpand ns spr)
   expand ns (Psin pr spr) = Psin (expand ns pr) (sexpand ns spr)

   expand ns (Pforall qs@(Q pvs) pr) = Pforall qs (expand (pvs++ns) pr)
   expand ns (Pexists qs@(Q pvs) pr) = Pexists qs (expand (pvs++ns) pr)

   expand ns (Peabs s pr) = Peabs s (expand ns pr)
   expand ns (Pfocus pr) = Pfocus $ expand ns pr
   expand ns pr = pr

   sexpand ns (PSet prs) = PSet (map (expand ns) prs)
   sexpand ns (PSetC qs@(Q pvs) prc pre)
     = PSetC qs (expand ns' prc) (expand ns' pre)
     where ns' = pvs ++ ns
   sexpand ns (PSetU s1 s2) = PSetU (sexpand ns s1) (sexpand ns s2)
   sexpand ns s = s
\end{code}
Note that this function does not enter expressions and
so will not expand \texttt{Pvar}s inside set/sequence comprehensions at present.

\newpage
\subsection{Error as Identity Handling}

\begin{code}
manipErrLaws
 = map mrkELaw
        [emsg_sub_focus
        ]
   ++
   map mrkPLaw
        [pmsg_free_capture
        ,pmsg_sub_focus
        ,pmsg_alphaNYI
        ]

manipErrPreds
 = map mrkPDef
        [pmsg_free_capture
        ,pmsg_sub_focus
        ,pmsg_alphaNYI
        ]
\end{code}
