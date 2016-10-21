\section{Focus Prototyping}
\begin{code}
module ProtoFocus where
import List

fst3 (x,_,_)=x
snd3 (_,y,_)=y
\end{code}

\subsection{Expression Datatype}
This incorporates a focus marker
\begin{code}
data Expr
 = K Int        -- atomic expression
 | Plus [Expr]  -- composite expression
 | Focus Expr   -- explicit focus marker
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

A non-empty list of triples
\begin{code}
type FExpr uctxt = [ ( Expr    --  expression at this level
                      , Int    --  position in parent (next record)
                      , uctxt  --  context
                      )
                   ] -- first element is deepest

-- invariant:
--   list non empty
--   Top-level Focus can only appear in last entry
--                         precisely when list is a singleton
--   expr in first element in non-singleton list has no Focus
--   for [..(ce,i,_),(pe,...)..],  descend i pe always succeeds
\end{code}
We show how the \texttt{FExpr} list  works with an example,
where we ignore contexts, so
  \texttt{(e,i,c)}
is rendered as $ e @ i $, and we show the list as a tower, with the first element
on top, with a horizontal line as separator.
$$
\begin{array}{c}
   \begin{array}{c}
     a + (~ (~ b + c ~) + d ~)    \FExprStrut
   \end{array}
\\ \texttt{clear} \left\uparrow\FExprStrut\right\downarrow \texttt{set}
\\ \begin{array}{c@{~~@~~}l}
     \framebox{a + (~ (~ b + c ~) + d ~)} & 0 \FExprStrut
   \end{array}
\\ \texttt{up} \left\uparrow\FExprStrut\right\downarrow \texttt{down 2}
\\ \begin{array}{c@{~~@~~}l}
      (~ b + c ~) + d                     & 2 \FExprStrut
   \\\hline
       a + \framebox{~ (~ b + c ~) + d ~} & 0 \FExprStrut
   \end{array}
\\ \texttt{up} \left\uparrow\FExprStrut\right\downarrow \texttt{down 1}
\\ \begin{array}{c@{~~@~~}l}
      b + c                               & 1 \FExprStrut
   \\\hline
      \framebox{~ b + c ~} + d            & 2 \FExprStrut
   \\\hline
       a + (~\framebox{~ b + c ~} + d ~)  & 0 \FExprStrut
   \end{array}
\\ \texttt{up} \left\uparrow\FExprStrut\right\downarrow \texttt{down 2}
\\ \begin{array}{c@{~~@~~}l}
      c                                   & 2 \FExprStrut
   \\\hline
      b + \framebox{c}                    & 1 \FExprStrut
   \\\hline
      (~ b + \framebox{c} ~) + d            & 2 \FExprStrut
   \\\hline
       a + (~(~ b + \framebox{c} ~) + d ~)  & 0 \FExprStrut
   \end{array}
\end{array}
$$


\newpage
\subsection{PUBLIC API}
\begin{code}
set :: uctxt -> Expr -> FExpr uctxt
set c0 e = [ ( Focus $ strip e, 0, c0 ) ]
\end{code}
\begin{code}
down :: (Expr -> Int -> dctxt) -- context fragment relevant to path
     -> (uctxt -> dctxt -> Expr -> uctxt)  -- build new context
     -> Int -> FExpr uctxt -> FExpr uctxt

down fd fu i fe@[ (Focus te,k,uc) ]
 = case descend fd i te of
    Nothing  ->  fe
    Just (ne, dc)  ->  let (Just te') = irep (Focus ne) i te
                       in [ (ne,i,fu uc dc ne), (te', k, uc) ]
down fd fu i fe@((ce,j,uc):(pe,k,uc'):rest)
 = case descend fd i ce of
    Nothing  ->  fe
    Just (ne, dc)  ->  let
                        Just ce' = irep (Focus ne) i ce
                        Just pe' = irep ce' j pe
                       in (ne,i,fu uc dc ne):(ce',j,uc):(pe',k,uc'):prop pe' k rest
down _ _ _ fe = fe
\end{code}
\begin{code}
up :: FExpr uctxt -> FExpr uctxt

up fe@[_] = fe

up [(ce,j,uc),(te,k,uc')]
 = let Just te' = irep ce j te
   in [(Focus te',k,uc')]

up ((ce,j,uc):(pe,k,uc'):rest)
 = let
     Just pe' = irep ce j pe
   in (pe',k,uc'):prop (Focus pe') k rest
\end{code}
\begin{code}
rep :: Expr -> FExpr uctxt -> FExpr uctxt

rep e [(te,k,uc)] = [(Focus e,k,uc)]

rep e ((ce,i,uc):rest) = (e,i,uc):prop (Focus e) i rest
\end{code}
\begin{code}
path :: FExpr uctxt -> [Int]

path ctxts = tail $ reverse $ map snd3 ctxts
\end{code}
\begin{code}
clear :: FExpr uctxt -> Expr
clear = strip . fst3 . last
\end{code}
\begin{code}
showFE :: FExpr uctxt -> String

showFE fe = show $ fst3 $ last fe
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
descend :: (Expr -> Int -> dctxt) ->Int -> Expr -> Maybe (Expr, dctxt)

descend f i e@(Plus es)
  | 1 <= i && i <= length es  =  Just (es!!(i-1), f e i )

descend _ _ _ = Nothing
\end{code}
\begin{code}
irep :: Expr -> Int -> Expr -> Maybe Expr  -- boilerplate

irep ne i (Plus es)
  | 1 <= i && i <= length es  =  Just $ Plus (take i' es ++ ne:drop i es)
  where i' = i-1

irep _ _ oe = Nothing
\end{code}
\begin{code}
prop :: Expr -> Int -> FExpr uctxt -> FExpr uctxt

prop e i [] = []

prop e i ((pe,j,uc):rest)
 = let
    Just pe' = irep e i pe
   in (pe',j,uc):prop pe' j rest
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
\end{code}
