\section{FUNCTION TEMPLATES}

We import \texttt{Datatypes} so we can check these by compiling them
in the event that datatypes are changed.
\begin{code}
--------------------------------- Saoithin Coding Standard Width -------------------------------->|
module TEMPLATES where
import Datatypes
\end{code}

\begin{code}
decorF NoDecor  =  undefined
decorF Pre  =  undefined
decorF Post  =  undefined
decorF (Subscript s)  =  undefined
\end{code}

\begin{code}
qvarF (Std v)  =  undefined
qvarF (Lst r)  =  undefined
\end{code}


\begin{code}
typeF :: Type -> a
typeF (Tarb)  =  undefined
typeF (Tvar tv)  =  undefined
typeF (Tset t)  =  undefined
typeF (Tseq t)  =  undefined
typeF (Tseqp t)  =  undefined
typeF (Tprod typs)  =  undefined
typeF (Tfree str cases)  =  undefined
typeF (Tfun t1 t2)  =  undefined
typeF (Tpfun t1 t2)  =  undefined
typeF (Tmap t1 t2)  =  undefined
typeF (Tenv)  =  undefined
typeF (Z)  =  undefined
typeF (B)  =  undefined
typeF (Terror str t1)  =  undefined
\end{code}

\begin{code}
exprF :: Expr -> a
exprF (T)  =  undefined
exprF (F)  =  undefined
exprF (Num i)  =  undefined
exprF (Var v)  =  undefined
exprF (Prod es)  =  undefined
exprF (App str e)  =  undefined
exprF (Bin str i e1 e2)  =  undefined
exprF (Equal e1 e2)  =  undefined
exprF (Set es)  =  undefined
exprF (Setc tt qvs pr e)  =  undefined
exprF (Seq es)  =  undefined
exprF (Seqc tt qvs pr e)  =  undefined
exprF (Map drs)  =  undefined
exprF (Cond pr e1 e2)  =  undefined
exprF (Build str es)  =  undefined
exprF (The tt str pr)  =  undefined
exprF (Evar str)  =  undefined
exprF (Eabs tt qvs e)  =  undefined
exprF (Esub e esub)  =  undefined
exprF (Eerror str)  =  undefined
exprF (Efocus e)  =  undefined
exprF (FOnP pr)  =  undefined
\end{code}



\begin{code}
predF :: Pred -> a
predF (TRUE)  =  undefined
predF (FALSE)  =  undefined
predF (Obs e)  =  undefined
predF (Defd e)  =  undefined
predF (TypeOf e typ)  =  undefined
predF (Not pr)  =  undefined
predF (And prs)  =  undefined
predF (Or prs)  =  undefined
predF (Imp pr1 pr2)  =  undefined
predF (Eqv pr1 pr2)  =  undefined
predF (Forall tt qvs pr)  =  undefined
predF (Exists tt qvs pr)  =  undefined
predF (Exists1 tt qvs pr)  =  undefined
predF (Univ tt pr)  =  undefined
predF (Sub pr esub)  =  undefined
predF (Pvar str)  =  undefined
predF (If prc prt pre)  =  undefined
predF (NDC pr1 pr2)  =  undefined
predF (RfdBy pr1 pr2)  =  undefined
predF (Lang str i les sss)  =  undefined
predF (Pforall qvs pr)  =  undefined
predF (Pexists qvs pr)  =  undefined
predF (Psub pr psub)  =  undefined
predF (Psapp pr prset)  =  undefined
predF (Psin pr prset)  =  undefined
predF (Peabs qvs pr)  =  undefined
predF (Ppabs qvs pr)  =  undefined
predF (Papp pr1 pr2)  =  undefined
predF (Perror str)  =  undefined
predF (Pfocus pr)  =  undefined
predF (FOnE e)  =  undefined
\end{code}


\begin{code}
predsetF :: PredSet -> a
predsetF (PSName str)  =  undefined
predsetF (PSet prs)  =  undefined
predsetF (PSetC qvs pr1 pr2)  =  undefined
predsetF (PSetU prset1 prset2)  =  undefined
\end{code}

\begin{code}
lelemF :: LElem -> a
lelemF (LVar str)  =  undefined
lelemF (LType typ)  =  undefined
lelemF (LExpr e)  =  undefined
lelemF (LPred pr)  =  undefined
lelemF (LList les)  =  undefined
lelemF (LCount les)  =  undefined
\end{code}

\begin{code}
synspecF :: SynSpec -> a
synspecF (SSNull)  =  undefined
synspecF (SSTok str)  =  undefined
synspecF (SSSep str)  =  undefined
\end{code}

\begin{code}
langspecF :: LangSpec -> a
langspecF (LangSpec les sss)  =  undefined
\end{code}

\begin{code}
sidecondF :: SideCond -> a
sidecondF (SCtrue)  =  undefined
sidecondF (SCisCond mtyp str)  =  undefined
sidecondF (SCnotFreeIn mtyp qs str)  =  undefined
sidecondF (SCareTheFreeOf mtyp qs str)  =  undefined
sidecondF (SCcoverTheFreeOf mtyp qs str)  =  undefined
sidecondF (SCfresh mtyp str)  =  undefined
sidecondF (SCAnd scs)  =  undefined
\end{code}


\begin{code}
provenanceF :: Provenance -> a
provenanceF (FromUSER user)  =  undefined
provenanceF (ViaPROOF provs)  =  undefined
provenanceF (UserDEFN user)  =  undefined
provenanceF (FromSOURCE src)  =  undefined
\end{code}
