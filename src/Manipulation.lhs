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
predBetaReduce mctxt sc (Papp (Ppabs ( []) bodyp) argp)  = bodyp
predBetaReduce mctxt sc (Papp (Ppabs ( [pv]) bodyp) argp) | isStdV pv
  = predPSub argp (varGenRoot pv) bodyp
predBetaReduce mctxt sc (Papp (Ppabs ( (pv:qvs)) bodyp) argp) | isStdV pv
  = Ppabs ( qvs) $ predPSub argp (varGenRoot pv) bodyp

predBetaReduce mctxt sc (Papp (PAbs ( []) bodyp) (PExpr arge))
  = bodyp
predBetaReduce mctxt sc (Papp (PAbs ( [ev]) bodyp) (PExpr arge)) | isStdV ev
  = predONSub mctxt sc (mkSubs arge ev) bodyp
predBetaReduce mctxt sc (Papp (PAbs ( (ev:qvs)) bodyp) (PExpr arge)) | isStdV ev
  = PAbs ( qvs) $ predONSub mctxt sc (mkSubs arge ev) bodyp

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
prTidy (cTdy,dTdy) (PAbs s pr) = PAbs s (prTidy (cTdy,dTdy) pr)
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
\end{code}

First, casting expression truth values up to predicate level:
\begin{code}
predSimp (PExpr T) = TRUE
predSimp (PExpr F) = FALSE
\end{code}

For now, we consider that variables always denote
\begin{code}
predSimp (Defd (Var _)) = TRUE
\end{code}

Negation:
\begin{code}
predSimp (Not TRUE) = FALSE
predSimp (Not FALSE) = TRUE
predSimp (Not (PExpr T)) = FALSE
predSimp (Not (PExpr F)) = TRUE
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
predSimp (Imp pr1 (PExpr T)) = TRUE
predSimp (Imp (PExpr F) pr2) = TRUE
predSimp (Imp (PExpr T) pr2) = predSimp pr2
predSimp (Imp pr1 (PExpr F)) = Not (predSimp pr1)
predSimp (Imp pr1 pr2) = Imp (predSimp pr1) (predSimp pr2)

predSimp (Eqv TRUE pr2) = predSimp pr2
predSimp (Eqv pr1 TRUE) = predSimp pr1
predSimp (Eqv FALSE pr2) = Not (predSimp pr2)
predSimp (Eqv pr1 FALSE) = Not (predSimp pr1)
predSimp (Eqv (PExpr T) pr2) = predSimp pr2
predSimp (Eqv pr1 (PExpr T)) = predSimp pr1
predSimp (Eqv (PExpr F) pr2) = Not (predSimp pr2)
predSimp (Eqv pr1 (PExpr F)) = Not (predSimp pr1)
predSimp (Eqv pr1 pr2) = Eqv (predSimp pr1) (predSimp pr2)

predSimp (If TRUE prt pre) = predSimp prt
predSimp (If FALSE prt pre) = predSimp pre
predSimp (If (PExpr T) prt pre) = predSimp prt
predSimp (If (PExpr F) prt pre) = predSimp pre
predSimp (If cond TRUE pre) = predSimp $ Or [cond, pre]
predSimp (If cond prt TRUE) = predSimp $ Or [Not cond, prt]
predSimp (If cond FALSE pre) = predSimp $ And [Not cond, pre]
predSimp (If cond prt FALSE) = predSimp $ And [cond, prt]
predSimp (If cond (PExpr T) pre) = predSimp $ Or [cond, pre]
predSimp (If cond prt (PExpr T)) = predSimp $ Or [Not cond, prt]
predSimp (If cond (PExpr F) pre) = predSimp $ And [Not cond, pre]
predSimp (If cond prt (PExpr F)) = predSimp $ And [cond, prt]
predSimp (If prc prt pre)
 = If (predSimp prc) (predSimp prt) (predSimp pre)
\end{code}

Quantification:
\begin{code}
predSimp (Forall _ ( []) pr) = predSimp pr
predSimp (Forall _ qs TRUE) = TRUE
predSimp (Forall _ qs FALSE) = FALSE
predSimp (Forall _ qs (PExpr T)) = TRUE
predSimp (Forall _ qs (PExpr F)) = FALSE
predSimp (Forall _ qs pr)
 = case (predSimp pr) of
    TRUE -> TRUE
    FALSE -> FALSE
    spr -> Forall 0 qs spr

predSimp (Exists _ ( []) pr) = predSimp pr
predSimp (Exists _ qs TRUE) = TRUE
predSimp (Exists _ qs FALSE) = FALSE
predSimp (Exists _ qs (PExpr T)) = TRUE
predSimp (Exists _ qs (PExpr F)) = FALSE
predSimp (Exists _ qs pr)
 = case (predSimp pr) of
    TRUE -> TRUE
    FALSE -> FALSE
    spr -> Exists 0 qs spr

predSimp (Exists1 _ ( []) pr) = FALSE
predSimp (Exists1 _ qs TRUE) = FALSE
predSimp (Exists1 _ qs FALSE) = FALSE
predSimp (Exists1 _ qs (PExpr T)) = FALSE
predSimp (Exists1 _ qs (PExpr F)) = FALSE
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
predSimp (PAbs s pr) = PAbs s (predSimp pr)

predSimp pr = pr
\end{code}

Various auxiliaries used to define the above.
\begin{code}
_ `oelem` []                 =  False
e `oelem` ((PExpr e'):rest)  =  e == e' || e `oelem` rest
e `oelem` (_:rest)          =  e `oelem` rest

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
  | isIndexSplittable nm = PAbs nm 0 qixd (PAbs nm 0 qnotixd bdps)
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
   expand ns pr@(PVar r)
     | v `elem` ns  =  pr
     | otherwise
        = case tslookup preds $ show r of
           Nothing  ->  pr
           (Just prdef)
            -> expand (v:ns) (pf prdef)
     where v = rootVar $ Gen r
   expand ns (PApp nm prs) = PApp nm (map (expand ns) prs)
   expand ns (PAbs nm _ qs prs) = PAbs nm 0 qs (map (expand ns) prs)
   expand ns (Sub pr sub) = Sub (expand ns pr) sub
   expand ns pr = pr
\end{code}
Note that this function does not enter expressions and
so will not expand \texttt{PVar}s inside set/sequence comprehensions at present.

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
