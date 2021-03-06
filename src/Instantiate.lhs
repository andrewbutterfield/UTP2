\section{Match Instantiation}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module Instantiate where
import Tables
import Datatypes
import DataText
import Utilities
import MatchTypes

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
   bT (Tprod ts) = Tprod (map bT ts)
   bT (Tmap t1 t2) = Tmap (bT t1) (bT t2)
   bT (Tfun t1 t2) = Tfun (bT t1) (bT t2)
   bT (Tpfun t1 t2) = Tpfun (bT t1) (bT t2)
   bT (Tset t) = Tset (bT t)
   bT (Tseq t) = Tseq (bT t)
   bT (Tseqp t) = Tseqp (bT t)
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
   bP pv@(Pvar r@(Std s)) = bevalP mctxt bnds r
   bP pv@(Pvar r@(Lst s)) = bevalP mctxt bnds r

   bP (Obs (Equal (Var v1) (Var v2))) = bE2P Equal v1 v2
   bP (Obs (Bin op p (Var v1) (Var v2))) = bE2P (Bin op p) v1 v2
   bP (Obs e) = Obs (instantiateExpr mctxt bnds e)

   bP (Defd e) = Defd (instantiateExpr mctxt bnds e)
   bP (TypeOf e t) = TypeOf (instantiateExpr mctxt bnds e) (instantiateType mctxt bnds t)
   bP (Not pr) = Not (bP pr)
   bP (And prs) = mkAnd (map bP prs)
   bP (Or prs) = mkOr (map bP prs)
   bP (NDC pr1 pr2) = NDC (bP pr1) (bP pr2)
   bP (Imp pr1 pr2) = Imp (bP pr1) (bP pr2)
   bP (RfdBy pr1 pr2) = RfdBy (bP pr1) (bP pr2)
   bP (Eqv pr1 pr2) = Eqv (bP pr1) (bP pr2)

   bP (If prc prt pre) = If (bP prc) (bP prt) (bP pre)
   bP (Forall tt qs pr) = mkForall (instantiateQ mctxt bnds qs) (bP pr)
   bP (Exists tt qs pr) = mkExists (instantiateQ mctxt bnds qs) (bP pr)
   bP (Exists1 tt qs pr) = mkExists1 (instantiateQ mctxt bnds qs) (bP pr)
   bP (Univ tt pr) = Univ 0 (bP pr)
   bP (Sub pr sub) = mkSub (bP pr) (instantiateESub mctxt bnds sub)
   bP (Ppabs qs pr) = mkPpabs (instantiateQ mctxt bnds qs) (bP pr)
   bP (Papp prf pra) = Papp (bP prf) (bP pra)
   bP (Psapp pr spr) = Psapp (bP pr) (bPS spr)
   bP (Psin pr spr) = Psin (bP pr) (bPS spr)
   bP (Pforall qs pr) = mkPforall (instantiateQ mctxt bnds qs) (bP pr)
   bP (Pexists qs pr) = mkPexists (instantiateQ mctxt bnds qs) (bP pr)
   bP (Psub pr sub) = mkPsub (bP pr) (instantiatePSub mctxt bnds sub)
   bP (Peabs qs pr) = mkPeabs (instantiateQ mctxt bnds qs) (bP pr)

   bP (Lang nm p [le1,le2] ss) = bL2P nm p ss le1 le2
   bP (Lang nm p les ss) = Lang nm p (bLES les) ss

   bP (Pfocus fpr) = Pfocus $ bP fpr

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
     std = Obs (binop e1 e2)

     -- v1 and v2 are list-vars, so see if they expand to lists
     es1 = bevalES mctxt bnds v1
     es2 = bevalES mctxt bnds v2

     std' = Obs (binop (Seq es1) (Seq es2))
   -- end bE2P

   b2E binop (e1,e2) = Obs (binop e1 e2)
\end{code}

Doing it all for languages:
\begin{code}
   bL2P nm p ss le1 le2
    | not $ isLELstV le1     =  std
    | not $ isLELstV le2     =  std
    | length es1 /= length es2  =  std
    | otherwise = mkAnd (map (b2L nm p ss) (zip es1 es2))
    where

     std = Lang nm p (bLES [le1,le2]) ss

     es1 = bevalES mctxt bnds $ theLEVar le1
     es2 = bevalES mctxt bnds $ theLEVar le2

     vof (LVar g) = mkGVar Scrpt g
     vof (LExpr (Var v)) = v
     v1 = vof le1
     v2 = vof le2

   -- end bL2P

   b2L nm p ss (e1,e2) = Lang nm p [LExpr e1,LExpr e2] ss
\end{code}

Other \texttt{instantiatePred mctxt} auxilliaries:
\begin{code}
   bPS (PSName n)
    = case bevalP mctxt bnds $ Std $ psName n of
        (Pvar (Std n'))  ->  PSName n'
        pr               ->  PSName ('?':show pr)
   bPS (PSet prs) = PSet (map bP prs)
   bPS (PSetC qs pr1 pr2) = PSetC (instantiateQ mctxt bnds qs) (bP pr1) (bP pr2)
   bPS (PSetU s1 s2) = PSetU (bPS s1) (bPS s2)

   bLES = map bLE

   bLE (LVar g)
     = case bevalV mctxt bnds $ mkGVar Scrpt g of
        Left (Gen f,_,_)    ->  LVar f
        Left u    ->  LVar $ Std ('?':show u)
        Right vs  ->  LVar $ Lst ('?':show vs)

   bLE (LType t)    = LType  $ instantiateType mctxt bnds t
   bLE (LExpr e)    = LExpr  $ instantiateExpr mctxt bnds e
   bLE (LPred pr)   = LPred  $ bP pr
   bLE (LList les)  = LList  $ map bLE les
   bLE (LCount les) = LCount $ map bLE les

   bPV pvs = map (stripPvar . bP . Pvar . Std . psName) pvs

   stripPvar (Pvar r) = show r
   stripPvar pr       = "?PredSet-Name-expected?"
\end{code}


Recurse down through expressions:
\begin{code}
instantiateExpr mctxt bnds@(gpbnds,vebnds,ttbnds) pat
 = bE pat
 where

   bE (Var v) = bevalE mctxt bnds v
   bE (Evar e) = bevalE mctxt bnds e
   bE (Prod es) = mkProd (map bE es)
   bE (App s e) = App s (bE e)
   bE (Bin s i e1 e2) = Bin s i (bE e1) (bE e2)
   bE (Equal e1 e2) = Equal (bE e1) (bE e2)
   bE (Set es) = Set (map bE es)
   bE (Setc tt qs pr e)  = mkSetc (instantiateQ mctxt bnds qs) (instantiatePred mctxt bnds pr) (bE e)
   bE (Seq es) = Seq (map bE es)
   bE (Seqc tt qs pr e)  = mkSeqc (instantiateQ mctxt bnds qs) (instantiatePred mctxt bnds pr) (bE e)
   bE (Map drs)       = Map (map bE2 drs)
   bE (Cond pcd et ee) = Cond (instantiatePred mctxt bnds pcd) (bE et) (bE ee)
   bE (Build s es)    = Build s (map bE es)
   bE (Eabs tt qs e)     = mkEabs (instantiateQ mctxt bnds qs) (bE e)
   bE (Esub e sub)    = mkEsub (bE e) (instantiateESub mctxt bnds sub)
   bE (Efocus fe) = Efocus $ bE fe
   bE (EPred fp) = EPred $ instantiatePred mctxt bnds fp
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
     Just (Seq es)  ->  es
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
       Just (TO (Pvar r'))  ->  r'
       Just (TO pr)         ->  Std $ "?"++show pr++"?"
       _                    ->  r

   instantiatePVs gpbnds r
    = case tglookup gpbnds r of
       Just (VSO rs)  ->  rs
       _              ->  [r]

   instantiatePS gpbnds (Pvar r)
    = case tglookup gpbnds r of
       Just (VSO rs)  ->  map Pvar rs
       _              ->  [Pvar r]
   instantiatePS _ pr = [Pvar (Lst ('?':show pr++"$"))]
\end{code}

Handle quantifier variables.
\begin{code}
instantiateQ mctxt bnds (Q xs)
 = Q $ concat $ map brv xs
 where
   brv x = case bevalV mctxt bnds x of
            Left x    ->  [x]
            Right vs  ->  vs
\end{code}
