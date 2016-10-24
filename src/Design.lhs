\section{Designs}

Experimenting with Designs

\begin{code}
module Design where
import Tables
import Datatypes
import Heuristics
import Manipulation
import Proof
import DSL
-- import Logic
-- import Builtin
-- import RAlg -- just for ok variable.
-- import R -- just for state variable.
import Utilities
\end{code}


\subsection{Observational Variables}

Already covered (we should really have variables classes
defined seperately.


We then build some useful types:

\begin{code}
dObsTable
  = foldr mkentry builtinTypeTable
     [ (ok,B),(ok',B)
     , (state,Tenv),(state',Tenv)
     ]


d_obs = lnorm [ok,state]
d_obs' = lnorm [ok',state']
d_alpha = Qlist (mrgnorm d_obs d_obs')
dPvar p = Pvar p d_alpha


dComp n p q
 = Exists (Qlist obsmid) (And [p',q'])
 where
   obs = [ok,state]
   addn v = v ++ ntxt
   ntxt = show n
   obsmid = map addn obs
   p' = Sub p pre_sub
   q' = Sub q post_sub
   mides = map Var obsmid
   pre_sub = Substn (0,mides,Qlist (map (++"'") obs))
   post_sub = Substn (0,mides,Qlist obs)
\end{code}

\subsection{Healthiness Conditions}

\subsubsection{H1}

\begin{eqnarray*}
   \H1(P) &\defs& ok \implies P
\end{eqnarray*}

\begin{code}
defH1 = Ppabs "P" (ok ==(dPvar "P"))
h1 = Pvar "H1" d_alpha
\end{code}

\subsubsection{H2}

\begin{eqnarray*}
   \H2(P) &\defs& P;(ok \implies ok' \land state'=state)
\end{eqnarray*}

\begin{code}
defH2 = Ppabs "P" (ok ==(dPvar "P"))
h2 = Pvar "H2" d_alpha
\end{code}

\subsubsection{H3}

\begin{eqnarray*}
   \H3(P) &\defs& P;\Skip
\end{eqnarray*}

\begin{code}
defH3 = Ppabs "P" (ok ==(dPvar "P"))
h3 = Pvar "H3" d_alpha
\end{code}

\subsubsection{H4}

\begin{eqnarray*}
   \H4(P) &\defs& P;true = true
\end{eqnarray*}

\begin{code}
defH4 = Ppabs "P" (ok ==(dPvar "P"))
h4 = Pvar "H1" d_alpha
\end{code}

\subsubsection{all of them}


\begin{code}
predH
 = plupdate tnil
    [(h1,defH1)
    ,(h2,defH2)
    ,(h3,defH3)
    ,(h4,defH4)
    ]
\end{code}


\subsection{Healthiness Properties}

Covered generically in R --- should really be treated in a Generic module!
\subsection{Semantics}

\subsubsection{$x:=e$}

\begin{eqnarray*}
  x:=e & \defs&
\end{eqnarray*}

\begin{code}
defCHAOS = Papp r TRUE
chaos = rPvar "CHAOS"

predR6
 = plupdate predR5
    [(chaos,defCHAOS)
    ]
\end{code}



\subsection{And the Theory is \ldots}

\begin{code}
designName = "Design"

designTypeTable
  = lupdate tnil
      [("state",Tenv),("state'",Tenv)
      ,("ok",B),("ok'",B)
      ]

rtt = lupdate predR9
       [(theoryObservables,rPvar (reactiveName++theoryObservables))]

reactiveTheoryTable = rtt
reactiveByName = tlookup reactiveTheoryTable
reactiveByPvar = pVarLookup reactiveTheoryTable
\end{code}

\subsubsection{D-specific laws}

\begin{code}
dCompDef
  = Eqv (Comp p q) (dComp 0 p q)
  where
    p = dPvar " P"
    q = dPvar " Q"

dLawTable
   =   freelaw "DEF-Design-;" dCompDef
\end{code}

\subsection{Design Conjectures}

We include here conjectures that are relevant to the
specific Design theory of \cite[Chp.~3]{UTP-book}.

\begin{code}
designConjectures
 = lupdate tnil
    [("tr0-existence"
      ,(Exists qtr0 ((Obs tTrace2 (tr `pfx` tr0)) /\ (Obs tTrace2 (tr0 `pfx` tr')))) === defGROW)
    ,("R1-idem",Papp r1 (Papp r1 p) === Papp r1 p)
    ,("tr-offset",Obs tTrace (Equal (strdiff `ssub` sv) trdiff))
    ,("offset-pfx",sv `ppfx` strdiff === tr `ppfx` tr')
    ,("r2-sub-sub",(Sub (Sub (rPvar "P") (r2sub t)) (r2sub s)) === (Sub (rPvar "P") (r2sub t)))
    ,("R2-idem",Papp r2 (Papp r2 p) === Papp r2 p)
    ,("R1-R2-comm",(Papp r1 (Papp r2 p)) === (Papp r2 (Papp r1 p)))
    ,("R1-R3-comm",(Papp r1 (Papp r3 p)) === (Papp r3 (Papp r1 p)))
    ,("R2-R3-comm",(Papp r2 (Papp r3 p)) === (Papp r3 (Papp r2 p)))
    ,("gstop-P:eq:gstop",(Papp r3 gstop) >>(Papp r3 p) === (Papp r3 gstop))
    ,("R3-;-close",((Papp r3 p) >>(Papp r3 q )) === (Papp r3 (p >>q)))
    ]
 where qtr0 = Qvar "tr0" ; tr0 = Var "tr0"
       p = rPvar " P"
       s = "s" ; t = "t"
       gstop = And [q,ok',wait'] ; q = rPvar " Q"
       sv = Var s; strdiff = sv `cat` trdiff
\end{code}

\begin{code}
dProofContext
  = ProofContext "Design" 0
     designTypeTable     -- Design types
     tnil                -- no named expressions
     designTheoryTable   -- Reactive predicates
     dLawTable           -- Reactive laws
     designConjectures   -- Reactive conjectures
     tnil                -- no theorems
     False               -- unmodified
\end{code}

