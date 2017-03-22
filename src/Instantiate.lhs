\section{Match Instantiation}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module Instantiate where
import Tables
import Datatypes
import DataText
import Utilities
import MatchTypes
import DSL

import Data.List
\end{code}


We need to instantiate predicates and expressions from patterns
using the bindings.


Recurse down through types:
\begin{code}
instantiateType mctxt binds pat
 = bT pat
 where
   bT (Tvar tv) = bevalT mctxt binds tv
   bT (Tfun t1 t2) = Tfun (bT t1) (bT t2)
   bT (TApp nm ts) = TApp nm (map bT ts)
   bT (Tfree nm css) = Tfree nm (map bC css)
   bT t = t

   bC (cnm,ts) = (cnm,map bT ts)
\end{code}

Recurse down through predicates,
taking care to handle binary atomic predicates
using meta-variables:
\begin{code}
instantiatePred :: MatchContext -> Binding -> Pred -> Pred
instantiatePred mctxt bnds@(gpbnds,vebnds,ttbnds) pat
 = bP pat
 where
   bP pv@(PVar v)
    | isStdV v  = bevalP mctxt bnds $ varGenRoot v
    | isLstV v  = bevalP mctxt bnds $ varGenRoot v

   bP (PApp nm prs) = PApp nm (map bP prs)
   bP (PAbs nm tt qs prs)
      = PAbs nm 0  (instantiateQ mctxt bnds qs) (map bP prs)
   bP (Sub pr sub) = mkSub (bP pr) (instantiateESub mctxt bnds sub)

   bP (TypeOf e t) = TypeOf (instantiateExpr mctxt bnds e) (instantiateType mctxt bnds t)

   bP (PExpr (App nm [Var v1, Var v2]))
    | nm == n_Equal = bE2P mkEqual v1 v2
   bP (PExpr e) = PExpr (instantiateExpr mctxt bnds e)

   bP pat = pat
\end{code}

Handling for 2-place atomic predicates (\texttt{binop}) with list-variables.
\begin{code}
   bE2P binop v1 v2
    | not $ isLstV v1           =  std
    | not $ isLstV v2           =  std
    | length es1 /= length es2  =  std'
    | otherwise = mkAnd (map (b2E binop) (zip es1 es2))
    where

     -- v1,v2 non-list, so instantiate a single binop
     e1 = bevalE mctxt bnds v1
     e2 = bevalE mctxt bnds v2
     std = PExpr (binop e1 e2)

     -- v1 and v2 are list-vars, so see if they expand to lists
     es1 = bevalES mctxt bnds v1
     es2 = bevalES mctxt bnds v2

     std' = PExpr (binop (mkSeq es1) (mkSeq es2))
   -- end bE2P

   b2E binop (e1,e2) = PExpr (binop e1 e2)
\end{code}

Other \texttt{instantiatePred mctxt} auxilliaries:
\begin{code}
   bPV pvs = map (stripPvar . bP . PVar . genRootAsVar . Std . psName) pvs

   stripPvar (PVar r) = show r
   stripPvar pr       = "?PredSet-Name-expected?"
\end{code}


Recurse down through expressions:
\begin{code}
instantiateExpr mctxt bnds@(gpbnds,vebnds,ttbnds) pat
 = bE pat
 where

   bE (Var v) = bevalE mctxt bnds v
   bE (App s es) = App s (map bE es)
   bE (Abs s tt qs es) = Abs s tt (instantiateQ mctxt bnds qs) (map bE es)
   bE (ESub e sub)    = mkEsub (bE e) (instantiateESub mctxt bnds sub)
   bE pat = pat

   bE2 (de,re) = (bE de,bE re)
\end{code}

Suspect variables:
\begin{code}
suspectVar :: Variable -> Variable
suspectVar (vroot,decor,key)  = (suspectRoot vroot,decor,'?':key)
suspectRoot :: Root -> Root
suspectRoot (Gen (Std r))  =  Gen $ Std ('?':r)
suspectRoot (Gen (Lst r))  =  Gen $ Lst ('?':r)
suspectRoot (Rsv OBS gs)   =  Gen $ Lst ("?OBS")
suspectRoot (Rsv MDL gs)   =  Gen $ Lst ("?MDL")
suspectRoot (Rsv SCR gs)   =  Gen $ Lst ("?SCR")
\end{code}


\newpage

\textbf{THIS IS ALL OLD HAT !!!!}
Handling substitutions
where we matched pattern:
$$
 [ e_1,\ldots,e_k , \lst f_1,\ldots,\lst f_\ell
 /
   u_1,\ldots,u_k ,  \lst v_1,\ldots,\lst v_\ell ]
 , \quad k+\ell \geq 1
$$
against test ($m \geq k$:
$$
 [ g_1,\ldots,g_m , \lst h_1,\ldots,\lst h_n
 /
   a_1,\ldots,a_m ,  \lst b_1,\ldots,\lst b_n ]
 , \quad m+n \geq 1
$$
and got, for $ i \leq k$:
        $$
          \begin{array}{ccc}
             e_i & \matches & g_i
          \\ u_j & \mapsto & a_j
          \end{array}
        $$
and either ($\ell \geq 2$):
        $$
         \begin{array}{l@{\mapsto}l}
            \lst f_1 & \seqof{g_{k+1},\ldots,g_m}
         \\ \lst f_2 & \seqof{\lst h_1,\ldots,\lst h_n}
         \\ \lst f_i & \nil, i > 2
         \\ \lst v_1 & \seqof{a_{k+1},\ldots,a_m}
         \\ \lst v_2 & \seqof{\lst b_1,\ldots,\lst b_n}
         \\ \lst v_i & \nil, i > 2
         \end{array}
        $$
or ($\ell=1$):
        $$
         \begin{array}{l@{\mapsto}l}
            \lst f_1 & \seqof{g_{k+1},\ldots,g_m ,  \lst h_1,\ldots,\lst h_n}
         \\ \lst v_1 & \seqof{a_{k+1},\ldots,a_m ,  \lst b_1,\ldots,\lst b_n}
         \end{array}
        $$
We represent these bindings in \texttt{ebnds :: Trie Expr} as follows:
\begin{center}
\begin{tabular}{|c|l|}
  \hline
  Binding & Concrete Representation
  \\\hline
  $u_j \mapsto a_j$               & \texttt{uj |-> Var aj}
  \\\hline
  $\lst v_i \mapsto \seqof{as,\lst b}$  & \texttt{vi |-> Seq (map Var (as++bs))}
  \\\hline
  $\lst f_i \mapsto \seqof{gs,\lst h}$  & \texttt{fi |-> Seq (map Var (gs++hs))}
  \\\hline
\end{tabular}
\end{center}
The \texttt{Seq} in the last two rows are always used,
even if the variable maps to nothing or a single expression.
We want a list lookup that unwraps these:
\begin{code}
lstlookup :: Trie Expr -> Variable -> [Expr]
lstlookup ebnds (Gen (Std _), _, key)
 = case tlookup ebnds key of
     Nothing        ->  []
     Just e         ->  [e]
lstlookup ebnds (r, _, key)
 = case tlookup ebnds key of
     Nothing        ->  []
     -- Just (Seq es)  ->  es -- REVIEW
     Just e         ->  error ("lstlookup "++show r++", no Seq ! - "++show e)
\end{code}

Building a substitution:
\begin{code}
instantiateESub :: MatchContext -> Binding -> ESubst -> ESubst
instantiateESub mctxt bnds (Substn sub)
 = Substn $ concat $ map bSub sub
 where

   bSub :: (Variable,Expr) -> [(Variable,Expr)]
   bSub (v,e)
    = case bevalV mctxt bnds v of
        Left u  ->  [( u, bevalE1 mctxt bnds e )]
        Right vs  ->  zip vs $ bevalEE mctxt bnds e

-- end instantiateESub

bevalE1 :: MatchContext -> Binding -> Expr -> Expr
bevalE1 mctxt bind e
  | isVar e    =  bevalVar mctxt bind $ getVar e
  | otherwise  =  instantiateExpr mctxt bind e

instantiatePSub mctxt bnds@(gpbnds,vebnds,_) (Substn sub)
 = Substn (concat $ map instantiate sub)
 where
   instantiate (r,pr)
    | isStdG r = [(instantiatePV gpbnds r, instantiatePred mctxt bnds pr)]
    | otherwise = zip (instantiatePVs gpbnds r) (instantiatePS gpbnds pr)

   instantiatePV gpbnds r
    = case tglookup gpbnds r of
       Just (TO (PVar v'))  ->  varGenRoot v'
       Just (TO pr)         ->  Std $ "?"++show pr++"?"
       _                    ->  r

   instantiatePVs gpbnds r
    = case tglookup gpbnds r of
       Just (VSO rs)  ->  rs
       _              ->  [r]

   instantiatePS gpbnds (PVar v)
    = case tglookup gpbnds r of
       Just (VSO rs)  ->  map (PVar .genRootAsVar) rs
       _              ->  [PVar v]
    where r = varGenRoot v
   instantiatePS _ pr = [PVar $ genRootAsVar (Lst ('?':show pr++"$"))]
\end{code}

Handle quantifier variables.
\begin{code}
instantiateQ mctxt bnds ( xs)
 =  concat $ map brv xs
 where
   brv x = case bevalV mctxt bnds x of
            Left x    ->  [x]
            Right vs  ->  vs
\end{code}
