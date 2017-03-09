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
   , ctxtMxd ctxt
   , (PExpr' (App' nm [] es), ctxt) : wayup )
downPFocus (PExpr (Abs nm tag qs (e:es)), ctxt, wayup)
 = ( pExpr e
   , ctxtMxd ctxt
   , (PExpr' (Abs' nm tag qs [] es), ctxt) : wayup )
downPFocus (PExpr (ESub e sub), ctxt, wayup)
 = ( pExpr e
   , ctxtMxd ctxt
   , (PExpr' (ESub'1 sub), ctxt) : wayup )

downPFocus (TypeOf e t, ctxt, wayup)
 = ( pExpr e
   , ctxtMxd ctxt
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

upPFocus ( pr, _, above : wayup ) = upPBuild above pr wayup
upPFocus fpr                      = fpr  --- top-level

upPBuild (PApp' nm before after, ctxt) pr  wayup
 = ( PApp nm (reverse before++pr:after)
   , ctxt, wayup )
upPBuild (PAbs' nm tag qs before after, ctxt) pr wayup
 = ( PAbs nm tag qs (reverse before++pr:after)
   , ctxt, wayup )
upPBuild (Sub'1 sub, ctxt) pr wayup
 = ( Sub pr sub
   , ctxt, wayup )
upPBuild (Sub'2 pr' vs before after, ctxt) pr wayup
 = ( Sub pr' $ Substn $ zip vs (reverse before ++ ePred pr : after)
   , ctxt, wayup )
upPBuild (TypeOf' t, ctxt) pr wayup
 = ( TypeOf (ePred pr) t
   , ctxt, wayup )

upPBuild (PExpr' (App' nm before after), ctxt) pr  wayup
 = ( PExpr (App nm (reverse before++ePred pr:after))
   , ctxt, wayup )
upPBuild (PExpr' (Abs' nm tag qs before after), ctxt) pr wayup
 = ( PExpr (Abs nm tag qs (reverse before++ePred pr:after))
   , ctxt, wayup )
upPBuild (PExpr' (ESub'1 sub), ctxt) pr wayup
 = ( PExpr (ESub (ePred pr) sub)
   , ctxt, wayup )
upPBuild (PExpr' (ESub'2 e' vs before after), ctxt) pr wayup
 = ( PExpr (ESub e' $ Substn $ zip vs (reverse before ++ ePred pr : after))
   , ctxt, wayup )
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

clearPFocus ( pr, _, [] ) = pr
clearPFocus fpr = clearPFocus $ upPFocus fpr
\end{code}

\newpage
\subsubsection{Moving Focus Right}

\begin{code}
rightPFocus :: FPred -> FPred

rightPFocus ( pr, ctxt, (PApp' nm before (pr':after), ctxt') : wayup )
 = ( pr'
   , id ctxt -- we need a way to assess polarity here !
   , (PApp' nm (pr:before) after, ctxt') : wayup )
rightPFocus ( pr, ctxt, (PAbs' nm tt vs before (pr':after), ctxt') : wayup )
 = ( pr'
   , id ctxt -- we need a way to assess polarity here !
   , (PAbs' nm tt vs (pr:before) after, ctxt') : wayup )

rightPFocus ( pr, ctxt, (Sub'1 (Substn sub), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (Sub'2 pr vs [] es', ctxt') : wayup )
 where
   (vs,(e':es')) = unzip sub
rightPFocus ( pr, ctxt, (Sub'2 bodypr vs before (e':after), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (Sub'2 bodypr vs (ePred pr:before) after, ctxt') : wayup )

rightPFocus ( pr, ctxt, (PExpr' (App' nm before (e':after)), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (App' nm (ePred pr:before) after), ctxt') : wayup )
rightPFocus ( pr, ctxt
            , (PExpr' (Abs' nm tt vs before (e':after)), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (Abs' nm tt vs (ePred pr:before) after), ctxt') : wayup )

rightPFocus ( pr, ctxt, (PExpr' (ESub'1 (Substn sub)), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (ESub'2 (ePred pr) vs [] es'), ctxt') : wayup )
 where
   (vs,(e':es')) = unzip sub
rightPFocus ( pr, ctxt
            , (PExpr' (ESub'2 bodye vs before (e':after)), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (ESub'2 bodye vs (ePred pr:before) after), ctxt') : wayup )

rightPFocus fpr = fpr
\end{code}

\subsubsection{Moving Focus Left}

\begin{code}
leftPFocus :: FPred -> FPred

leftPFocus ( pr, ctxt, (PApp' nm (pr':before) after, ctxt') : wayup )
 = ( pr'
   , id ctxt -- we need a way to assess polarity here !
   , (PApp' nm before (pr:after), ctxt') : wayup )
leftPFocus ( pr, ctxt, (PAbs' nm tt vs (pr':before) after, ctxt') : wayup )
 = ( pr'
   , id ctxt -- we need a way to assess polarity here !
   , (PAbs' nm tt vs before (pr:after), ctxt') : wayup )

leftPFocus ( pr, ctxt, (Sub'2 bodypr vs (e':before) after, ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (Sub'2 bodypr vs before (ePred pr:after), ctxt') : wayup )
leftPFocus ( pr, ctxt, (Sub'2 bodypr vs [] after, ctxt') : wayup )
 = ( bodypr
   , ctxtMxd ctxt
   , (Sub'1 $ Substn $ zip vs (ePred pr:after), ctxt') : wayup )

leftPFocus ( pr, ctxt, (PExpr' (App' nm (e':before) after), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (App' nm before (ePred pr:after)), ctxt') : wayup )
leftPFocus ( pr, ctxt
           , (PExpr' (Abs' nm tt vs (e':before) after), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (Abs' nm tt vs before (ePred pr:after)), ctxt') : wayup )

leftPFocus ( pr, ctxt
           , (PExpr' (ESub'2 bodypr vs (e':before) after), ctxt') : wayup )
 = ( pExpr e'
   , ctxtMxd ctxt
   , (PExpr' (ESub'2 bodypr vs before (ePred pr:after)), ctxt') : wayup )
leftPFocus ( pr, ctxt, (PExpr' (ESub'2 bodye vs [] after), ctxt') : wayup )
 = ( pExpr bodye
   , ctxtMxd ctxt
   , (PExpr' (ESub'1 $ Substn $ zip vs (ePred pr:after)), ctxt') : wayup )

leftPFocus fpr  =  fpr
\end{code}

\newpage
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
repPFocus pr' ( pr, ctxt, wayup ) = ( pr', ctxt, wayup )

repPFf :: (Pred -> Pred) -> FPred -> FPred
repPFf f ( pr, ctxt, wayup ) = ( f pr, ctxt, wayup )
\end{code}




\newpage
\subsection{Getting Focus Information}


These two function get details about the focus:
\begin{code}
getPFocus :: FPred -> Pred
getPFocus (pr, _, _) = pr

getPFContext :: FPred -> FContext
getPFContext (_, ctxt, _) = ctxt
\end{code}

This function returns the top-level predicate containing the focus:
\begin{code}
getPFTop :: FPred -> Pred
getPFTop = clearPFocus
\end{code}




\subsection{Setting Focus with a Path}


Given a focus, we can extract the relevant focus path:
\begin{code}
getPFocusPath :: FPred -> [Int]
getPFocusPath (_, _, wayup) = reverse $ map (holeIndex . fst) wayup

holeIndex :: Pred' -> Int
holeIndex (PApp' _ before _)             = 1+ length before
holeIndex (PAbs' _ _ _ before _)         = 1 + length before
holeIndex (Sub'1 _)                      = 1
holeIndex (Sub'2 _ _ before _)           = 2 + length before
holeIndex (TypeOf' _)                    = 1
holeIndex (PExpr' (App' _ before _))     = 1 + length before
holeIndex (PExpr' (Abs' _ _ _ before _)) = 1 + length before
holeIndex (PExpr' (ESub'1 _))            = 1
holeIndex (PExpr' (ESub'2 _ _ before _)) = 2 + length before
\end{code}


Given a focus path and a predicate
we can set the focus according to that path,
noting that it may fail,
in which case the focus may be arbitrary
\begin{code}
setPFocusPath :: [Int] -> Pred -> FPred

setPFocusPath ip pr
 =  setpath ip $ setPFocus pr
 where
   setpath [] fpr = fpr
   setpath (i:is) fpr = setpath is $ sp (i-1) $ downPFocus fpr
   sp 0 fpr = fpr
   sp i fpr = sp (i-1) $ rightPFocus fpr
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
