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
    \texttt{Eqv p (PExpr e)} moves the focus to be on expression \texttt{e},
    rather than on predicate \texttt{(PExpr e)}.
\end{itemize}

The focussing is now going to be done using a proper zipper,
as prototyped in \texttt{proto/PrettyZipper}.

\newpage
\subsection{Focus Datatypes}

We will adopt the type ``derivatives'' as zipper approach
\cite{McBride-et-al-and-Huet}.
First we address additional context information we want track
as we move the focus.




\subsubsection{Focus Context}

Contexts, associated with predicate-focii,
provide useful information about how the focus
is situated within the top-level predicate.
At present we:
\begin{itemize}
    \item indicate the polarity of the focus w.r.t the implication ordering;
    \item list the object variable bindings encountered on the way to the focus.
\end{itemize}

\paragraph{Polarity}~

\begin{code}
data Polarity = Pos | Neg | Mxd deriving (Eq,Ord)

polneg Pos = Neg
polneg Neg = Pos
polneg Mxd = Mxd

instance Show Polarity where
 show Pos = "+ve"
 show Neg = "-ve"
 show Mxd = "mxd"
\end{code}

\paragraph{Bindings on-route}

We record bindings as a variable  list
\begin{code}
type Binders = [Variable]
\end{code}

\paragraph{Focus Context Definition}~


\begin{code}
type FContext = (Polarity,Binders,[TTTag])

nullCtxt, baseCtxt, mxdCtxt :: FContext
nullCtxt = (Pos,[],[])
baseCtxt = (Pos,[],[0])
mxdCtxt = (Mxd,[],[0])
\end{code}

When we move down, the context needs to be updated
to reflect changes in polarity,
as well as any variable bindings that might be encountered.
Also we should track type-table tags.
We provide some context update functions:

\begin{code}
ctxtId,ctxtNeg,ctxtMxd :: FContext -> FContext
ctxtId = id
ctxtNeg (pol,bs,tags) = (polneg pol,bs,tags)
ctxtMxd (pol,bs,tags) = (Mxd,bs,tags)
\end{code}
Note: with the new simplified \texttt{Expr}/\texttt{Pred} datatypes,
we can no longer hardwire polarity changes in this code.
Instead we need to find a principled way to determine positive
and negative positions in a construct from first principles.
For now all we do is set it to ``mixed'' (\texttt{Mxd}).

\paragraph{Binders}~

\begin{code}
ctxtPush :: ([Variable],TTTag) -> FContext -> FContext
ctxtPush (vs,tag) (pol,bs,tags) = (pol,lnorm (vs++bs),tag:tags)
ctxtPPush vs (pol,bs,tags) = (pol,lnorm (vs++bs),tags)
\end{code}

\subsubsection{Zipper Derivatives}

First, the Expression ``derivative'':
\begin{code}
data Expr'
 = App' String [Expr] [Expr]
 | Abs' String TTTag [Variable] [Expr] [Expr]
 | ESub'1 ESubst
 | ESub'2 Expr [Variable] [Expr] [Expr]
 | EPred' Pred'
 deriving (Show)
\end{code}

Next, the Predicate ``derivative'':
\begin{code}
data Pred'
 = PApp' String [Pred] [Pred]
 | PAbs' String TTTag [Variable] [Pred] [Pred]
 | Sub'1  ESubst
 | Sub'2 Pred [Variable] [Expr] [Expr]
 | PExpr' Expr'
 | TypeOf' Type
 -- Language extensions (Lexts) -- NOT SUPPORTED RIGHT NOW
 -- NEED TO ENCODE Invarants.rcheckLangSpec and similar IN DATASTRUCTURE
--  | Lang' String    -- construct name
--         Int       -- precedence, if binary
--         [LElem]   -- Language elements
--         [SynSpec] -- Interleaving Tokens
 deriving (Show)
\end{code}

\subsubsection{Focussed Entities}

A focussed entity is a quadruple,
with the focus predicate, the context, the top-level predicate
and a stack of index-context pairs.
\begin{code}
type FPred = ( Pred       -- Focus Predicate
             , FContext   -- Focus Context
             , [(Pred',FContext)]    -- Route up to top-level
             )
\end{code}


\newpage
\subsection{Displaying Focus}

Normally, we display the whole predicate,
with the focus highlighted in context.

However, sometimes it is useful to see the whole tuple:
\begin{code}
showPFocus :: FPred -> String
showPFocus = show
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
setPFocus pr@(PExpr _) = ( pr, mxdCtxt,  [] )
setPFocus pr           = ( pr, baseCtxt, [] )
\end{code}
We need the case split here
because the initial context is different if the top-level is an expression.



\newpage
\subsection{Moving focus down}

$$
\begin{array}{c}
   p(\ldots \framebox{$q(r_1,r_2,\ldots)$} \ldots) @ \sigma \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{down}
\\ p(\ldots q(\framebox{$r_1$},r_2,\ldots) \ldots) @ \sigma\cat\seqof 1
\end{array}
$$
\begin{code}
downPFocus :: FPred -> FPred

-- predicates
downPFocus (PApp nm (pr:prs), ctxt, wayup)
 = ( pr
   , ctxtId ctxt
   , (PApp' nm [] prs, ctxt) : wayup )
downPFocus (PAbs nm tag qs (pr:prs), ctxt, wayup)
 = ( pr
   , ctxtPush (getqovars qs,tag) ctxt
   , (PAbs' nm tag qs [] prs, ctxt) : wayup )
downPFocus (Sub pr sub, ctxt, wayup)
 = ( pr
   , ctxtId ctxt
   , (Sub'1 sub, ctxt) : wayup )

-- embedded expressions
downPFocus (PExpr (App nm (e:es)), ctxt, wayup)
 = ( pExpr e
   , ctxtMxd
   , (PExpr' (App' nm [] es), ctxt) : wayup )
downPFocus (PExpr (Abs nm tag qs (e:es)), ctxt, wayup)
 = ( pExpr e
   , ctxtMxd
   , (PExpr' (Abs' nm tag qs [] es), ctxt) : wayup )
downPFocus (PExpr (ESub e sub), ctxt, wayup)
 = ( pExpr e
   , ctxtMxd
   , (PExpr' (ESub'1 sub), ctxt) : wayup )

downPFocus (TypeOf e t, ctxt, wayup)
 = ( pExpr e
   , ctxtMxd
   , (TypeOf' t, ctxt) : wayup )

-- need to figure this out !!!
--downPFocus (Lang nm p les ss, ctxt, wayup)

downPFocus pr = pr
\end{code}


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

upPFocus ( pr, _, (PApp' nm before after, ctxt) : wayup )
 = ( PApp nm (reverse before++pr:after), ctxt, wayup )
upPFocus ( pr, _, (PAbs' nm tag qs before after, ctxt) : wayup )
 = ( PAbs nm tag qs (reverse before++pr:after), ctxt, wayup )
upPFocus ( pr, _, (Sub'1 sub, ctxt) : wayup )
 = ( Sub pr sub, ctxt, wayup )
upPFocus ( PExpr e, _, (Sub'2 pr vs before after, ctxt) : wayup )
 = ( Sub pr $ zip vs (reverse before++e:after), ctxt, wayup )
upPFocus fpr = fpr  --- top-level
\end{code}

\newpage
\subsubsection{Moving Focus Left/Right}

\begin{code}
rightPFocus :: FPred -> FPred

rightPFocus fpr = fpr

leftPFocus :: FPred -> FPred


leftPFocus fpr  =  fpr
\end{code}

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

irepEF ne i (App s es)      = irepEFs ne i (App s) es
irepEF ne _ (Eabs tt qs e)  = Eabs 0 qs ne
irepEF ne 1 (Equal e1 e2)   = Equal ne e2
irepEF ne 2 (Equal e1 e2)   = Equal e1 ne

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





Getting the focus parent:
\begin{code}
getFocusParent :: FPred -> Pred
getFocusParent (_, _, _, []) = perror "Top-level focus has no parent"
getFocusParent (_, _, toppr, [_]) = toppr
getFocusParent (fpr, ctxt, toppr, ((i,_):ics))
 = getFocusParent (fpr, ctxt, goDownPF i toppr, ics)
\end{code}


\newpage
Knowing the branching factor can be useful:
\begin{code}
predBranches :: Pred -> Int
predBranches (PExpr e) = exprBranches e
predBranches (TypeOf e t) = 1
predBranches (PApp _ prs) = length prs
predBranches (PAbs _ tt qs prs) = length prs
predBranches (Sub _ (Substn sub)) = 1 + length sub
predBranches (Lang nm p les ss) = length $ filter isFocussable les
predBranches _ = 0

exprBranches :: Expr -> Int
exprBranches (App s es)       = length es
exprBranches (Eabs n tt qs es)   =  length es
exprBranches (ESub e (Substn sub)) = 1 + length sub
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
