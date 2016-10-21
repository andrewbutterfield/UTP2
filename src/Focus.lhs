\section{Focus}

\begin{code}
module Focus where
import Data.List
import Datatypes
import Utilities
import MatchTypes
import FreeBound
\end{code}

``Focus'' is the mechanism for restricting attention
to part of a predicate or expression.
The version implemented here is more complicated than that described
in \texttt{proto/ProtoFocus}, because here we have two mutually-recursive types,
\texttt{Expr} and \texttt{Pred}.
We adopt a number of key principles as far as the transition between the two types
is concerned:
\begin{itemize}
  \item
    A single up or down movement ignores the transition
    ---
    we do not count going from a \texttt{Pred} to immediately contained \texttt{Expr}
    as such a step.
  \item
    So, for example, performing a \texttt{down 2} where the current focus is
    \texttt{Eqv p (Obs e)} moves the focus to be on expression \texttt{e},
    rather than on predicate \texttt{(Obs e)}.
    This means that \texttt{Pfocus (Obs e)} should never occur,
    but instead be represented as \texttt{Obs (Efocus e)}.
  \item
    In effect, the focus marker should be pushed in through a transition
    to the deepest possible location.
\end{itemize}
\begin{code}
pFocus :: Pred -> Pred
pFocus (Obs e)  =  Obs $ Efocus e
pFocus pr       =  Pfocus pr

eFocus :: Expr -> Expr
eFocus (EPred pr)  =  EPred $ Pfocus pr
eFocus e           =  Efocus e
\end{code}

\newpage
\subsection{Displaying Focus}

Normally, we display the third component of the quadruple
which shows the whole predicate, with the focus highlighted in context.

However, sometimes it is useful to see the whole tuple:
\begin{code}
showPFocus :: FPred -> String
showPFocus ( fpr, (pol,bnd,tags), toppr, ics )
 = unlines
    [ show fpr
    , show pol
      ++"{"++(concat $ intersperse "," $ map varKey bnd)++"}"
      ++" <"++(concat $ intersperse ";" $map show tags)++">"
    , show toppr
    , show $ map fst ics
    ]
\end{code}

\newpage
\subsection{Setting Focus}

Setting focus is the act of taking a focus-free expression/predicate
and setting it up so the focus is at the top-level.
In the case of top-level \texttt{Obs} expressions, we place the focus on the expression
component, preferring \texttt{Obs (Efocus e)} to \texttt{Pfocus (Obs e)}.
$$
\begin{array}{c}
     pr    \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{set}
\\ \framebox{$pr$} @ \nil \FExprStrut
\end{array}
$$
\begin{code}
setPFocus :: Pred -> FPred

setPFocus pr@(Obs e)
 = ( Obs e', mxdCtxt, Obs $ Efocus e', [] ) where e' = stripEFocus e

setPFocus pr
 = (pr', baseCtxt, Pfocus pr', [] ) where pr' = stripPFocus pr
\end{code}
We need the case split here
(rather than just simply calling \texttt{pFocus}),
because the initial context is different if the top-level is an expression.


\newpage
\subsection{Clearing Focus}

Clearing focus is the act of removing focus
from an expression or predicate:
$$
\begin{array}{c}
     p(\ldots q\ldots)    \FExprStrut
\\ \texttt{clear}\left\uparrow\FExprStrut\right.
\\ p(\ldots\framebox{$q$}\ldots) @ \sigma \FExprStrut
\end{array}
$$
\begin{code}
clearPFocus :: FPred -> Pred

clearPFocus (_, _, toppr, _) = stripPFocus toppr
\end{code}

The following code is used to strip focus markers from expressions
and predicates.
\begin{code}
stripEFocus :: Expr -> Expr

stripEFocus (Efocus e) = mapE (stripPFocus,stripEFocus) e
stripEFocus e          = mapE (stripPFocus,stripEFocus) e

stripPFocus :: Pred -> Pred

stripPFocus (Pfocus pr) = mapP (stripPFocus,stripEFocus) pr
stripPFocus pr          = mapP (stripPFocus,stripEFocus) pr
\end{code}


\newpage
\subsection{Moving focus down}

We provide a number identifying the sub-expression/predicate
to which we wish to descend.
If the argument is not a expression/predicate
with a sub-expression/predicate matching the number supplied,
then no change occurs (exception: if only one sub-part is present,
then the number is ignored).



\subsubsection{Descending into Predicates}

$$
\begin{array}{c}
   p(\ldots \framebox{$q(\ldots,r_i,\ldots)$} \ldots) @ \sigma \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{down i}
\\ p(\ldots q(\ldots,\framebox{$r_i$},\ldots) \ldots) @ \sigma\cat\seqof i
\end{array}
$$
\begin{code}
downPFocus :: Int -> FPred -> FPred

downPFocus i fpr@( cfpr, ctxt, toppr, ics )
 = case downPF i cfpr of
     Nothing        ->  fpr
     Just (npr, cf) ->  let toppr' = rrepPF (pFocus npr) i toppr ics
                        in  ( npr, cf ctxt , toppr', ics++[(i, ctxt)] )
\end{code}

Descending down
\begin{code}
downPF :: Int -> Pred -> Maybe (Pred, FContext -> FContext)

downPF n (Pfocus pr) = downPF n pr

downPF n (Obs e)
 = case downEF n e of
     Nothing  ->  Nothing
     Just (e', ctxt)  ->  Just (Obs e', ctxt . ctxtMxd)

downPF n (Defd e)     = Just(Defd $ Efocus e, ctxtMxd)
downPF n (TypeOf e t) = Just (TypeOf (Efocus e) t, ctxtMxd)

downPF _ (Not pr)  =  Just(pr, ctxtNeg)
downPF _ (Univ tag pr)
 =  Just(pr, ctxtPush (predFreeOVars nullMatchContext pr,tag))

downPF 1 (NDC pr1 pr2) = Just(pr1, ctxtId)
downPF 2 (NDC pr1 pr2) = Just(pr2, ctxtId)
downPF 1 (Imp pr1 pr2) = Just(pr1, ctxtNeg)
downPF 2 (Imp pr1 pr2) = Just(pr2, ctxtId)
downPF 1 (RfdBy pr1 pr2) = Just(pr1, ctxtId)
downPF 2 (RfdBy pr1 pr2) = Just(pr2, ctxtNeg)
downPF 1 (Eqv pr1 pr2) = Just(pr1, ctxtMxd)
downPF 2 (Eqv pr1 pr2) = Just(pr2, ctxtMxd)
-- downPF 1 (Papp pr1 pr2) = Nothing -- for now (matching unsound)
downPF n (Papp _ pr) = Just(pr, ctxtMxd)

downPF n (And prs) = downPFs ctxtId n prs
downPF n (Or prs)  = downPFs ctxtId n prs

-- Remember: renders as  " prt <| prc |> pre "
downPF 1 (If prc prt pre) = Just (prt, ctxtId)
downPF 2 (If prc prt pre) = Just (prc, ctxtMxd)
downPF 3 (If prc prt pre) = Just (pre, ctxtId)

downPF _ (Forall tag qs pr) = Just(pr, ctxtPush (getqovars qs,tag))
downPF _ (Exists tag qs pr) = Just(pr, ctxtPush (getqovars qs,tag))
downPF _ (Exists1 tag qs pr) = Just(pr, ctxtPush (getqovars qs,tag))

downPF _ (Pforall pvs pr) = Just(pr, ctxtId)
downPF _ (Pexists pvs pr) = Just(pr, ctxtId)
downPF _ (Peabs qs pr) = Just(pr, ctxtPPush (getqovars qs))
downPF _ (Ppabs ss pr) = Just(pr, ctxtMxd)

downPF 1 (Psapp pr spr) = Just(pr, ctxtMxd)
downPF 1 (Psin pr spr) = Just(pr, ctxtMxd)

downPF 1 (Sub pr sub) = Just(pr, ctxtId)
-- downPF n pr@(Sub spr (Substn ssub msub))

downPF n (Lang nm p les ss) = downLF n les

downPF _ pr = Nothing
\end{code}

Going down (total, ignores context):
\begin{code}
goDownPF :: Int -> Pred -> Pred
goDown i (Obs (Efocus e)) = goDown i (Obs e)
goDown i (Pfocus pr) = goDown i pr
goDownPF i pr
 = case downPF i pr of
     Nothing       ->  pr
     Just (pr',_)  ->  pr'
\end{code}


Some common (predicate) descent patterns:
\begin{code}
downPFs cf i prs
 | 1 <= i && i <= length prs = Just (prs!!(i-1), cf)
downPFs _ _ _ = Nothing
\end{code}

\newpage
Stepping once down into an expression:
\begin{code}
downEF :: Int -> Expr -> Maybe (Expr, FContext -> FContext)

downEF n (Efocus e) = downEF n e

downEF _ (App s e)        =  Just(e, ctxtMxd)
downEF _ (Eabs tag qs e)
  =  Just(e, ctxtPush (getqovars qs,tag) . ctxtMxd)
downEF 1 (Bin s i e1 e2)  =  Just(e1, ctxtMxd)
downEF 2 (Bin s i e1 e2)  =  Just(e2, ctxtMxd)
downEF 1 (Equal e1 e2)    =  Just(e1, ctxtMxd)
downEF 2 (Equal e1 e2)    =  Just(e2, ctxtMxd)

-- remember, this renders as " et <| pc |> ee "
downEF 1 (Cond pc et ee)  =  Just(et, ctxtMxd)
downEF 2 (Cond pc et ee)  =  Just(ePred pc, ctxtMxd)
downEF 3 (Cond pc et ee)  =  Just(ee, ctxtMxd)

downEF n (Prod es)    = downEFs ctxtMxd n es
downEF n (Set es)     = downEFs ctxtMxd n es
downEF n (Seq es)     = downEFs ctxtMxd n es
downEF n (Build s es) = downEFs ctxtMxd n es

downEF _ (The tag x pr) = Just (ePred pr, ctxtPush ([x],tag) . ctxtMxd)
downEF 1 (Setc tag qs pr e) = Just (ePred pr, ctxtPush (getqovars qs,tag) . ctxtMxd)
downEF 2 (Setc tag qs pr e) = Just (e, ctxtPush (getqovars qs,tag) . ctxtMxd)

downEF 1 (Seqc tag qs pr e) = Just (ePred pr, ctxtPush (getqovars qs,tag) . ctxtMxd)
downEF 2 (Seqc tag qs pr e) = Just (e, ctxtPush (getqovars qs,tag) . ctxtMxd)

downEF _ (Esub e sub)   = Just (e, ctxtMxd)

downEF i (EPred pr)
 = case downPF i pr of
     Nothing  ->  Nothing
     Just (pr', ctxt)  -> Just (ePred pr', ctxt . ctxtMxd)

downEF _ e = Nothing

downEFs cf i es
 | 1 <= i && i <= length es = Just (es!!(i-1), cf)
downEFs _ _ _ = Nothing
\end{code}


\subsubsection{Descending into Language Constructs}

Get the $n$th expression or predicate
from a list of language elements (all others not being focusable at present):
\begin{code}
downLF _ []            =  Nothing
downLF 0 _             =  Nothing
downLF 1 (LPred pr:_)  =  Just (pr, ctxtMxd)
downLF 1 (LExpr e:_)   =  Just (Obs e, ctxtMxd)
downLF 1 _             =  Nothing
downLF n (_:les)       =  downLF (n-1) les

isFocussable (LPred _)  =  True
isFocussable (LExpr _)  =  True
isFocussable _          =  False

leReplace (LPred _) pr        les = LPred pr:les
leReplace (LExpr _) (Obs e)   les = LExpr e:les
leReplace le        _         les = le:les
\end{code}

\newpage
\subsection{Replacing  sub-component}


Replacement (Predicates):
\begin{code}
irepPF :: Pred -> Int -> Pred -> Pred

irepPF npr i (Pfocus pr)       =  irepPF npr i pr       -- drop focus !
irepPF npr i (Obs (Efocus e))  =  irepPF npr i $ Obs e  -- drop focus !

irepPF (Obs ne) i (Obs e)  =  Obs $ irepEF ne          i e
irepPF npr      i (Obs e)  =  Obs $ irepEF (ePred npr) i e

irepPF (Obs ne) _ (Defd e)      =  Defd ne
irepPF (Obs ne) _ (TypeOf e t)  =  TypeOf ne  t

irepPF npr _ (Not pr)     =  Not npr
irepPF npr _ (Univ tt pr) =  Univ 0 npr

irepPF npr 1 (NDC pr1 pr2)     = NDC npr pr2
irepPF npr 2 (NDC pr1 pr2)     = NDC pr1 npr
irepPF npr 1 (Imp pr1 pr2)     = Imp npr pr2
irepPF npr 2 (Imp pr1 pr2)     = Imp pr1 npr
irepPF npr 1 (RfdBy pr1 pr2)   = RfdBy npr pr2
irepPF npr 2 (RfdBy pr1 pr2)   = RfdBy pr1 npr
irepPF npr 1 (Eqv pr1 pr2)     = Eqv npr pr2
irepPF npr 2 (Eqv pr1 pr2)     = Eqv pr1 npr
-- irepPF npr 1 (Papp pr1 pr2) = Papp npr pr2
irepPF npr _ (Papp pr1 pr2)    = Papp pr1 npr

irepPF npr i (And prs) = irepPFs npr i And prs
irepPF npr i (Or prs)  = irepPFs npr i Or prs

-- Remember: renders as  " prt <| prc |> pre "
irepPF npr 1 (If prc prt pre) = If prc npr pre
irepPF npr 2 (If prc prt pre) = If npr prt pre
irepPF npr 3 (If prc prt pre) = If prc prt npr

irepPF npr _ (Forall tt qs pr)  = Forall 0 qs npr
irepPF npr _ (Exists tt qs pr)  = Exists 0 qs npr
irepPF npr _ (Exists1 tt qs pr) = Exists1 0 qs npr

irepPF npr _ (Pforall pvs pr) = Pforall pvs npr
irepPF npr _ (Pexists pvs pr) = Pexists pvs npr
irepPF npr _ (Peabs qs pr)    = Peabs qs npr
irepPF npr _ (Ppabs ss pr)    = Ppabs ss npr

irepPF npr 1 (Psapp pr spr) = Psapp npr spr
irepPF npr 1 (Psin pr spr)  = Psin npr spr

irepPF npr 1 (Sub pr sub) = Sub npr sub

irepPF npr i (Lang nm p les ss) = irepLF nm p ss npr i les

irepPF _ _ pr = pr

irepPFs npr i con prs
 | 1 <= i && i <= length prs  =  con (take (i-1) prs ++ npr:drop i prs)
irepPFs _ _ con prs           =  con prs

irepLF nm p ss npr i les
 = case irep npr i les of
    Nothing  ->  Lang nm p les ss
    Just les' -> Lang nm p les' ss
 where
   irep npr i [] = Nothing
   irep npr 0 les = Nothing
   irep npr 1 (LPred pr:les) = Just (LPred npr:les)
   irep npr 1 (LExpr e:les) = Nothing
   irep npr 1 les = Nothing
   irep npr n (le:les)
    = do les' <- irep npr (n-1) les
         return (le:les')
\end{code}

\newpage
Replacement (Expressions)
\begin{code}
irepEF :: Expr -> Int -> Expr -> Expr

irepEF ne i (Efocus e) = irepEF ne i e  -- we drop the focus !

irepEF ne _ (App s e)       = App s ne
irepEF ne _ (Eabs tt qs e)  = Eabs 0 qs ne
irepEF ne 1 (Bin s i e1 e2) = Bin s i ne e2
irepEF ne 2 (Bin s i e1 e2) = Bin s i e1 ne
irepEF ne 1 (Equal e1 e2)   = Equal ne e2
irepEF ne 2 (Equal e1 e2)   = Equal e1 ne

-- remember, this renders as " et <| pc |> ee "
irepEF ne         1 (Cond pc et ee) = Cond pc ne ee
irepEF ne         2 (Cond pc et ee) = Cond (pExpr ne) ne ee
irepEF ne         3 (Cond pc et ee) = Cond pc et ne

irepEF ne i (Prod es)    = irepEFs ne i Prod      es
irepEF ne i (Set es)     = irepEFs ne i Set       es
irepEF ne i (Seq es)     = irepEFs ne i Seq       es
irepEF ne i (Build s es) = irepEFs ne i (Build s) es

irepEF ne         1 (Setc tt qs pr e) = Setc 0 qs (pExpr ne) e
irepEF ne         2 (Setc tt qs pr e) = Setc 0 qs pr ne

irepEF ne         1 (Seqc tt qs pr e) = Seqc 0 qs (pExpr ne) e
irepEF ne         2 (Seqc tt qs pr e) = Seqc 0 qs pr ne

irepEF ne _ (Esub e sub)    = Esub ne sub

irepEF _ _ e  = e

irepEFs ne i con es
 | 1 <= i && i <= length es  =  con (take (i-1) es ++ ne:drop i es)
irepEFs _ _ con es           =  con es
\end{code}

\begin{code}
rrepPF :: Pred -> Int -> Pred -> FocusPath ->  Pred

rrepPF npr i (Pfocus pr) [] = irepPF npr i pr
rrepPF npr i (Obs (Efocus e)) [] = Obs $ irepEF (ePred npr) i e

rrepPF npr i currpr ((j,_):ics)
 = let
     nxtpr = goDownPF j currpr
     nxtpr' = rrepPF npr i nxtpr ics
   in irepPF nxtpr' j currpr

rrepPF npr i pr [] = pr  -- should never occur
\end{code}



\newpage

\subsection{Moving focus up}

$$
\begin{array}{c}
   p(\ldots \framebox{$q(\ldots,r_i,\ldots)$} \ldots) @ \sigma \FExprStrut
\\ \texttt{up} \left\uparrow\FExprStrut\right.
\\ p(\ldots q(\ldots,\framebox{$r_i$},\ldots) \ldots) @ \sigma\cat\seqof i
\end{array}
$$

\begin{code}
upPFocus :: FPred -> FPred

upPFocus fpr@(_,_,_,[]) = fpr  --- top-level

upPFocus ( cpr, _, toppr, [(i,ctxt)] )
 = ( toppr', ctxt, pFocus toppr', [] )
 where toppr' = irepPF cpr i toppr

upPFocus ( cpr, _, toppr, ics@((i,ctxt):ics') )
 = let
     nxtpr = goDownPF i toppr
     ( cpr', ctxt', nxtpr', _ ) = upPFocus ( cpr, ctxt, nxtpr, ics' )
     toppr' = irepPF nxtpr' i toppr
   in ( cpr', ctxt', toppr', init ics )
\end{code}


\subsection{Replacing Focus}

$$
\begin{array}{c}
   p(\ldots \framebox{$q$} \ldots) @ \sigma \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{rep r}
\\ p(\ldots \framebox{$r$} \ldots) @ \sigma \FExprStrut
\end{array}
$$

We want to replace the focussed predicate by a given one.
\begin{code}
repPFocus :: Pred -> FPred -> FPred

repPFocus npr (_, ctxt, Pfocus _,       []) = (npr, ctxt, pFocus npr, [])
repPFocus npr (_, ctxt, Obs (Efocus _), []) = (npr, ctxt, pFocus npr, [])

repPFocus npr (_, ctxt, toppr, ics@[(i,_)] )
 = (npr, ctxt, irepPF (pFocus npr) i toppr, ics)

repPFocus npr (cpr, ctxt, toppr, ics@((i,ctxt'):ics') )
 = let
     nxtpr = goDownPF i toppr
     ( cpr', _, nxtpr', _) = repPFocus npr (cpr, ctxt', nxtpr, ics')
     toppr' = irepPF nxtpr' i toppr
   in (npr, ctxt, toppr', ics)

repPFf :: (Pred -> Pred) -> FPred -> FPred
repPFf pfun fpr
 = repPFocus (pfun $ getPFocus fpr) fpr
\end{code}


\subsection{Setting Focus with a Path}
Given a focus path and a predicate
we can set the focus according to that path,
noting that it may fail,
in which case the predicate is returned unchanged.
\begin{code}
setPFocusPath :: [Int] -> Pred -> FPred

setPFocusPath ip pr
 = pathset ip $ setPFocus pr
 where
   pathset []     fpr  =  fpr
   pathset (i:is) fpr  =  pathset is $ downPFocus i fpr
\end{code}




\newpage
\subsubsection{Moving Focus Left/Right}

\begin{code}
rightPFocus :: FPred -> FPred

rightPFocus fpr@(_, _, _, []) = fpr

rightPFocus fpr@(_, ctxt, toppr, ics)
 | n < predBranches ppr  =  downPFocus (n+1) $ upPFocus fpr
 where
   n = fst $ last ics
   ppr = getFocusParent fpr

rightPFocus fpr          =  fpr

leftPFocus :: FPred -> FPred

leftPFocus fpr@(_, _, _, []) = fpr

leftPFocus fpr @ (_, ctxt, toppr, ics)
 | n > 1  =  downPFocus (n-1) $ upPFocus fpr
 where n = fst $ last ics

leftPFocus fpr  =  fpr
\end{code}

Getting the focus parent:
\begin{code}
getFocusParent :: FPred -> Pred
getFocusParent (_, _, _, []) = Perror "Top-level focus has no parent"
getFocusParent (_, _, toppr, [_]) = toppr
getFocusParent (fpr, ctxt, toppr, ((i,_):ics))
 = getFocusParent (fpr, ctxt, goDownPF i toppr, ics)
\end{code}


\newpage
Knowing the branching factor can be useful:
\begin{code}
predBranches :: Pred -> Int
predBranches (Obs e) = exprBranches e
predBranches (Defd e)     = 1
predBranches (TypeOf e t) = 1
predBranches (Not pr)  =  1
predBranches (Univ _ pr) =  1
predBranches (NDC pr1 pr2) = 2
predBranches (Imp pr1 pr2) = 2
predBranches (RfdBy pr1 pr2) = 2
predBranches (Eqv pr1 pr2) = 2
predBranches (Papp _ pr) = 1 -- for now
predBranches (And prs) = length prs
predBranches (Or prs)  = length prs
predBranches (If prc prt pre) = 3
predBranches (Forall tt qs pr) = 3
predBranches (Exists tt qs pr) = 3
predBranches (Exists1 tt qs pr) = 3
predBranches (Pforall pvs pr) = 1
predBranches (Pexists pvs pr) = 1
predBranches (Peabs qs pr) = 1
predBranches (Ppabs ss pr) = 1
predBranches (Psapp pr spr) = 1
predBranches (Psin pr spr) = 1
predBranches (Sub _ (Substn sub)) = 1 + length sub
predBranches (Lang nm p les ss) = length $ filter isFocussable les
predBranches (Pfocus pr) = predBranches pr
predBranches _ = 0

exprBranches :: Expr -> Int
exprBranches (App s e)        =  1
exprBranches (Eabs tt qs e)      =  1
exprBranches (Bin s i e1 e2)  =  2
exprBranches (Equal e1 e2)    =  2
exprBranches (Cond pc et ee)  =  3
exprBranches (Prod es)        = length es
exprBranches (Set es)         = length es
exprBranches (Seq es)         = length es
exprBranches (Build s es)     = length es
exprBranches (The tt x pr)    = 1
exprBranches (Setc tt qs pr e)           = 2
exprBranches (Seqc tt qs pr e)           = 2
exprBranches (Esub e (Substn sub)) = 1 + length sub
exprBranches (Efocus e)               = exprBranches e
exprBranches (EPred pr) = predBranches pr
exprBranches _                        = 0
\end{code}



\newpage
\subsection{Getting Focus Information}


These two function get details about the focus:
\begin{code}
getPFocus :: FPred -> Pred
getPFocus (fpr, _, _, _) = stripPFocus fpr

getPFContext :: FPred -> FContext
getPFContext (_, ctxt, _, _) = ctxt
\end{code}

This function returns the top-level predicate containing the focus:
\begin{code}
getPFTop :: FPred -> Pred
getPFTop (_, _, toppr, _) = toppr
\end{code}



Given a focus, we can extract the relevant focus path:
\begin{code}
getPFocusPath :: FPred -> [Int]
getPFocusPath (_, _, _, ics) =  map fst ics
\end{code}


\newpage
\subsection{Local and Global application under focii}

Sometimes we want to apply a function either to the focus,
or else over the whole predicate in a simple transparent
(non structure-changing)
way, with focus management all taken care of.
In the global case, we remember the focus path,
strip the focus, apply the function,
and then re-establish the focus.
\begin{code}
globalPFapp :: (Pred -> Pred) -> FPred -> FPred
globalPFapp f fpr
 = let
     path = getPFocusPath fpr
   in setPFocusPath path $ f $ clearPFocus fpr
\end{code}

Dropping is also useful:
\begin{code}
fDrop :: (FPred -> FPred) -> Pred -> Pred
fDrop ff = clearPFocus . ff . setPFocus
\end{code}
