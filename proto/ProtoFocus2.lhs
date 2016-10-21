\section{Focus Prototyping (2)}
\begin{code}
module ProtoFocus2 where
import Data.List
\end{code}

\subsection{Expression Datatype}
This incorporates a focus marker
\begin{code}
data Expr
 = K Int        -- atomic expression
 | Plus [Expr]  -- composite expression
 | Focus Expr   -- explicit focus marker
 deriving Eq
\end{code}
We render expressions in the obvious way, with the focus marked by a box
so the \texttt{Expr} value
\begin{verbatim}
Plus [ K 1, Plus [ K 2, Focus $ K 3 ], K 4 ]
\end{verbatim}
renders as:
$$
  1 + (~ 2 + \framebox{3} ~) + 4
$$


\subsection{Displaying Expressions}
\begin{code}
instance Show Expr where show = showe False

showe _     (K i)     = show i
showe False (Plus es) = concat $ intersperse "+" $ map (showe True) es
showe True  (Plus es) = '(' : (concat $ intersperse "+" $ map (showe True) es) ++ ")"
showe _     (Focus e) = "<|"++showe False e ++ "|>"
\end{code}

\newpage
\subsection{Focus Datatype}

A quadruple:
\begin{code}
type FExpr uctxt = ( Expr    --  focus expression
                   , uctxt   --  current context
                   , Expr    -- top level expression with focus marker
                   , [ ( Int    --  position in parent (next record)
                       , uctxt  --  context
                       )
                     ]
                   )

-- invariant( fe, fctxt, tope, ics )
--   te has one focus marker, that "contains" fe
--   length of ics = depth of focus (no. of "downs")
-- if ics is null, then tope = Focus fe
\end{code}
We show how the \texttt{FExpr} triple  works with an example,
where we show the focus expression in-situ, and ignore contexts, so
  \texttt{(fe,te,s)}
is rendered as $ te(\framebox{fe}) @ s $.
$$
\begin{array}{c}
     a + (~ (~ b + c + e~) + d ~)    \FExprStrut
\\ \texttt{clear} \left\uparrow\FExprStrut\right\downarrow \texttt{set}
\\ \framebox{a + (~ (~ b + c + e~) + d ~)} @ \seqof{} \FExprStrut
\\ \texttt{up} \left\uparrow\FExprStrut\right\downarrow \texttt{down 2}
\\ a + \framebox{~ (~ b + c + e~) + d ~} @ \seqof{2} \FExprStrut
\\ \texttt{up} \left\uparrow\FExprStrut\right\downarrow \texttt{down 1}
\\ a + (~\framebox{~ b + c + e~} + d ~)  @ \seqof{2,1} \FExprStrut
\\ \texttt{up} \left\uparrow\FExprStrut\right\downarrow \texttt{down 3}
\\ a + (~(~ b + c + \framebox{e} ~) + d ~)  @ \seqof{2,1,3} \FExprStrut
\end{array}
$$


\newpage
\subsection{PUBLIC API}

$$
\begin{array}{c}
     e    \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{set}
\\ \framebox{$e$} @ \nil \FExprStrut
\end{array}
$$
\begin{code}
set :: uctxt -> Expr -> FExpr uctxt
set c0 e = ( e', c0, Focus e', [] ) where e' = strip e
\end{code}
$$
\begin{array}{c}
     e(\ldots f\ldots)    \FExprStrut
\\ \texttt{clear}\left\uparrow\FExprStrut\right.
\\ e(\ldots\framebox{$f$}\ldots) @ \sigma \FExprStrut
\end{array}
$$\begin{code}
clear :: FExpr uctxt -> Expr
clear (_,_,tope,_) = strip tope
\end{code}
$$
\begin{array}{c}
   e(\ldots \framebox{$f(\ldots,g_i,\ldots)$} \ldots) @ \sigma \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{down i}
\\ e(\ldots f(\ldots,\framebox{$g_i$},\ldots) \ldots) @ \sigma\cat\seqof i
\end{array}
$$
\begin{code}
down :: (Expr -> Int -> dctxt) -- context fragment relevant to path
     -> (uctxt -> dctxt -> Expr -> uctxt)  -- build new context
     -> Int -> FExpr uctxt -> FExpr uctxt

down fd fu i fe@( cfe, fc, tope, ics )
 = case descend fd i cfe of
    Nothing  ->  fe
    Just (ne, dc)  ->  let (tope',uc) = rrep (Focus ne) i tope fc ics
                       in ( ne, fu uc dc ne, tope', ics++[(i, fc)] )
\end{code}
$$
\begin{array}{c}
   e(\ldots \framebox{$f(\ldots,g_i,\ldots)$} \ldots) @ \sigma \FExprStrut
\\ \texttt{up} \left\uparrow\FExprStrut\right.
\\ e(\ldots f(\ldots,\framebox{$g_i$},\ldots) \ldots) @ \sigma\cat\seqof i
\end{array}
$$
\begin{code}
up :: FExpr uctxt -> FExpr uctxt

up fe@( _, _, _, [] ) = fe -- top level

up ( cfe, fc, tope, [(i,ic)] )
 = ( tope', ic, Focus tope', [] )
 where tope' = irep cfe i tope

up ( cfe, fc, tope, ics@((i,ic):ics') ) -- ics' not null
 = let nxte = godown i tope
       ( cfe', ic', nxte', _ ) = up ( cfe, ic, nxte, ics')
       tope' = irep nxte' i tope
   in ( cfe', ic', tope', init ics )
\end{code}
$$
\begin{array}{c}
   e(\ldots \framebox{$f$} \ldots) @ \sigma \FExprStrut
\\ \left.\FExprStrut\right\downarrow \texttt{rep g}
\\ e(\ldots \framebox{$g$} \ldots) @ \sigma \FExprStrut
\end{array}
$$
\begin{code}
rep :: Expr -> FExpr uctxt -> FExpr uctxt

rep e (_,   fc, Focus tope, [])        =  (e, fc, Focus e,               [])

rep e (cfe, fc, tope, ics@[(i,ic)])  =  (e, fc, irep (Focus e) i tope, ics)

rep e ( cfe, fc, tope, ics@((i,ic):ics') ) -- ics not null
 = let nxte = godown i tope
       ( cfe', _, nxte', _ ) = rep e ( cfe, ic, nxte, ics' )
       tope' = irep nxte' i tope
   in ( e, fc, tope', ics )
\end{code}
\begin{code}
path :: FExpr uctxt -> [Int]

path (_,_,_,ics) = map fst ics
\end{code}
\begin{code}
showFE :: FExpr uctxt -> String

showFE (_,_,tope,_) = show tope
\end{code}

\newpage
\subsection{UNDER THE HOOD}

\begin{code}
strip :: Expr -> Expr

strip (Focus fe) = strip fe

strip (Plus es) = Plus $ map strip es

strip e = e
\end{code}
\begin{code}
godown :: Int -> Expr -> Expr

godown i (Focus e)           = godown i e

godown i (Plus es)
 | 1 <= i && i <= length es  =  es!!(i-1)

godown i e                   =  e
\end{code}
\begin{code}
descend :: (Expr -> Int -> dctxt) ->Int -> Expr -> Maybe (Expr, dctxt)

descend f i e@(Plus es)
  | 1 <= i && i <= length es  =  Just (es!!(i-1), f e i )

descend _ _ _ = Nothing
\end{code}
\begin{code}
irep :: Expr -> Int -> Expr -> Expr

irep ne i (Focus pe)        = irep ne i pe
irep ne i (Plus es)
 | 1 <= i && i <= length es  =  Plus (take (i-1) es ++ ne:drop i es)
irep ne i pe                = pe
\end{code}

The complex bit.
basically, when \texttt{ics=[]}, then \texttt{curre=Focus e},
so we can do the change to propagate back up.
\begin{code}
rrep :: Expr -> Int -> Expr -> uctxt -> [(Int, uctxt)] -> (Expr, uctxt)

rrep nfe i (Focus e) uc []
 = ( irep nfe i e, uc )

rrep ne i curre uc [] -- should never occur.
 = (curre, uc)

rrep ne i curre uc ((j,uc'):ics)
 = let
     nxte = godown j curre
     (nxte',_) = rrep ne i nxte uc' ics
 in (irep nxte' j curre, uc)
\end{code}

\newpage
\subsection{TESTING}
\begin{code}
ex1 = Plus [ K 10
           , Plus [ K 20
                  , K 30
                  , Plus [ K 40
                         , Plus [ K 50
                                , K 60
                                , K 70
                                ]
                         ]
                  ]
           , K 80
           ]

uc0 :: (Int, Bool)
uc0 = (0,True)
dcf :: Expr -> Int -> Bool
dcf  e i = even i
ucf :: (Int,Bool) -> Bool -> Expr -> (Int,Bool)
ucf (uci,_) dc e = (uci+1, dc)

downAndUp :: Expr -> [Int] -> [Bool]
downAndUp e ixs
 = dau (set uc0 e) ixs
 where
   dau _ [] = []
   dau fe (i:ix)
    = let
        fed  = down dcf ucf i fe
        fedu = up fed
     in (fe == fedu) : dau fed ix
\end{code}
