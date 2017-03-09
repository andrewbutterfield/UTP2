\section{Formula Normalisation}

\begin{code}
module Normalise where
import Datatypes
import Flatten
import Manipulation
import Data.List
\end{code}

This module collects a variety of ways to transform predicates
into some form of standard form.

\subsection{Conjunctive \& Disjunctive Normal Forms}

We compute these forms by converting predicates
to lists of lists of (non-conj/non-disj) predicates,
manipulating them, and then replacing the \texttt{And} and \texttt{Or} constructors
\begin{code}
dnfLists, cnfLists :: Pred -> [[Pred]]

dnfLists (PApp nm [pr])
 | nm == n_Not  =  map (map pnot) (cnfLists pr)
dnfLists pr@(PApp nm prs)
 | nm == n_And  =  map concat (distribute (map dnfLists prs))
 | nm == n_Or   =  concat  (map dnfLists prs)
 | otherwise    =  [[pr]]

cnfLists (PApp nm [pr])
 | nm == n_Not = map (map pnot) (dnfLists pr)
cnfLists pr@(PApp nm prs)
 | nm == n_And   = concat (map cnfLists prs)
 | nm == n_Or   =  map concat (distribute (map cnfLists prs))
 | otherwise    =  [[pr]]
\end{code}
The mutual recursion between \texttt{dnfLists} and \texttt{cnfLists} on \texttt{Not} is a happy consequence
of de-Morgan's law!

We now need to convert the nested lists back into predicates,
tidying up along the way.

First a list gets cleaned of zero and unit predicates:
\begin{code}
cleanList srp zero unit [] = srp
cleanList srp zero unit (pr:prs)
  | pr == zero  =  [zero]
  | pr == unit  =  cleanList     srp  zero unit prs
  | otherwise   =  cleanList (pr:srp) zero unit prs
\end{code}
Then a list is converted to the appropriate predicate
form using the appropriate constructor and unit,
with sorting and duplicate \texttt{Pvar} removal applied in passing:
\begin{code}
listToPred cons unit [] = unit
listToPred cons unit [pr] = pr
listToPred cons unit prs = cons (removeDupPreds (sort prs))
\end{code}

To convert a list-of-lists to a predicate,
we clean the inner lists and convert them to the
inner logic constructor type (And/Or)
and then clean the resulting lists
and convert them to the outer constructor type (Or/And):
\begin{code}
andList, orList :: [Pred] -> Pred

andList prs = listToPred mkAnd TRUE (cleanList [] FALSE TRUE prs)
orList prs  = listToPred mkOr FALSE (cleanList [] TRUE FALSE prs)
\end{code}

Now the appropriate nestings:
\begin{code}
dnfPred, cnfPred :: [[Pred]] -> Pred

dnfPred prss = orList (map andList prss)
cnfPred prss = andList (map orList prss)
\end{code}

Finally we put it all together:
\begin{code}
dnf = dnfPred . dnfLists
cnf = cnfPred . cnfLists
\end{code}





\subsubsection{Pushing Functions through $\lor$--$\land$}

We sometimes need to push a predicate function (typically negation)
through conjunction and disjunction:
\begin{code}
pushPF f (PApp nm prs)
 | nm == n_And  =  mkAnd (map (pushPF f) prs)
 | nm == n_Or   =  mkOr  (map (pushPF f) prs)
pushPF f pr        = f pr
\end{code}

A negation function that automatically cancels another negation is
useful:
\begin{code}
pnot (PApp nm [pr]) | nm == n_Not  =  pr
pnot pr                            = mkNot pr

pushNot = pushPF pnot
\end{code}




\subsection{Utility Code}

SHOULDN'T THIS BE IN \texttt{Utilities.lhs}?

\subsection{List Distribution}

First we use \texttt{listpairs}
to stick a given value in front of each
elements of a list to give a list of doubletons:
\begin{eqnarray*}
   listpairs &:& A \fun A^n \fun (A^2)^n
\\ listpairs(a)\seqof{b_1,\ldots,b_n}
   &=&
   \seqof{\seqof{a,b_1},\ldots,\seqof{a,b_n}}
\end{eqnarray*}
\begin{code}
listpairs :: a -> [a] -> [[a]]
listpairs x [] = []
listpairs x (y:ys) = [x,y]:(listpairs x ys)
\end{code}
Function \texttt{distrpair} creates a list of doubletons
by prefixing every element of 1st first argument to
each element of the second:
\begin{eqnarray*}
   distrpair &:& A^m \fun A^n \fun (A^2)^{m*n}
\\ \lefteqn{distrpair \seqof{a_1,\ldots,a_m}~\seqof{b_1,\ldots,b_n}}
\\ &=& \seqof{\seqof{a_1,b_1},\ldots,\seqof{a_1,b_n},\ldots,\seqof{a_m,b_1},\ldots,\seqof{a_m,b_n}}
\end{eqnarray*}
\begin{code}
distrpair :: [a] -> [a] -> [[a]]
distrpair [] ys = []
distrpair (x:xs) ys = (listpairs x ys) ++ (distrpair xs ys)
\end{code}
Given a list of elements, and a second list of lists,
\texttt{distrlist}
``conses'' each element of the first to every sub-element of the latter:
\begin{eqnarray*}
   distrlist &:& A^m \fun (A^x)^n \fun (A^{x+1})^{m*n}
\\ \lefteqn{distrlist \seqof{a_1,\ldots,a_m}~\seqof{\sigma_1,\ldots,\sigma_n}}
\\ &=& \seqof{a_1:\sigma_1,\ldots,a_1:\sigma_n,\ldots,a_m:\sigma_1,\ldots,a_m:\sigma_n}
\end{eqnarray*}
\begin{code}
distrlist :: [a] -> [[a]] -> [[a]]
distrlist [] yys = []
distrlist [x] yys = map (x:) yys
distrlist (x:xs) yys = (map (x:) yys) ++ (distrlist xs yys)
\end{code}
Finally we get to \texttt{distribute},
which computes a form of product of a list of lists.
This product is  a list of sub-list, each sub-list having
the same length as the original top-level list,
and consisting of one element drawn in order from each sub-list:
\begin{eqnarray*}
   distribute &:& (A^*)^n \fun  (A^n)^*
\\ \lefteqn{distribute\seqof{\sigma_1,\ldots,\sigma_n}}
\\ &=& \seqof{\ldots,\seqof{\sigma_1[i],\ldots,\sigma_n[j]},\ldots}
\end{eqnarray*}
\begin{code}
distribute :: [[a]] -> [[a]]
distribute [] = []
distribute [xs] = [xs]
distribute [xs,ys] = distrpair xs ys
distribute ([]:xxs) = distribute xxs
distribute (xs:xxs) = distrlist xs (distribute xxs)
\end{code}
