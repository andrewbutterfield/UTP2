\section{Test Repository}
\begin{code}
module TestRepository where
import TestFramework
import AdHocTests
\end{code}

\subsection{Combinatorial Logic Patterns}

\begin{code}
matchAandB@(aandb,_) = ("aandb",
 TDescr "A /\\ B" tstMtch
 [ TLogGet "" "A /\\ B"
 , TLogPut "" "\nPATTERN : A /\\ B\nTEST    : A /\\ B\nA  |->  A\nB  |->  B\nREBUILD  : A /\\ B"
   OK
 , TLogGet "" "C /\\ D"
 , TLogPut "" "\nPATTERN : A /\\ B\nTEST    : C /\\ D\nA  |->  C\nB  |->  D\nREBUILD  : C /\\ D"
   OK
 , TLogGet "" "E \\/ F"
 , TLogPut "" "\nPATTERN : A /\\ B\nTEST    : E \\/ F\n        NO MATCH"
   OK
 , TLogGet "" ""
 ]
 )
\end{code}

\subsection{Quantifier Patterns}

\begin{code}
matchAllXP@(allxp,_) = ("allxp",
 TDescr "forall x @ P" tstMtch
 [ TLogGet "" "forall x @ P"
 , TLogPut "" "\nPATTERN : forall x @ P\nTEST    : forall x @ P\nP  |->  P\nx  |->  (x,,\"x\")\nREBUILD  : forall x @ P"
   OK
 , TLogGet "" "forall y @ Q"
 , TLogPut "" "\nPATTERN : forall x @ P\nTEST    : forall y @ Q\nP  |->  Q\nx  |->  (y,,\"y\")\nREBUILD  : forall y @ Q"
   OK
 , TLogGet "" ""
 ]
 )

matchAllXsP@(allxsp,_) = ("allxsp",
 TDescr "forall x$ @ P" tstMtch
 [ TLogGet "" "forall x$ @ P"
 , TLogPut "" "\nPATTERN : forall x$ @ P\nTEST    : forall x$ @ P\nP   |->  P\nx$  |->  (x$,,\"x$\")\nREBUILD  : forall x$ @ P"
   OK
 , TLogGet "" "forall y$ @ Q"
 , TLogPut "" "\nPATTERN : forall x$ @ P\nTEST    : forall y$ @ Q\nP   |->  Q\nx$  |->  (y$,,\"y$\")\nREBUILD  : forall y$ @ Q"
   OK
 , TLogGet "" "forall x @ P"
 , TLogPut "" "\nPATTERN : forall x$ @ P\nTEST    : forall x @ P\nP   |->  P\nx$  |->  (x,,\"x\")\nREBUILD  : forall x @ P"
   OK
 , TLogGet "" "forall x,y @ P"
 , TLogPut "" "\nPATTERN : forall x$ @ P\nTEST    : forall x,y @ P\nP   |->  P\nx$  |->  (x,,\"x\"),(y,,\"y\")\nREBUILD  : forall x,y @ P"
   OK
 , TLogGet "" "forall y,y$ @ Q"
 , TLogPut "" "\nPATTERN : forall x$ @ P\nTEST    : forall y,y$ @ Q\nP   |->  Q\nx$  |->  (y,,\"y\"),(y$,,\"y$\")\nREBUILD  : forall y,y$ @ Q"
   OK
 , TLogGet "" "forall a$,b$ @ A"
 , TLogPut "" "\nPATTERN : forall x$ @ P\nTEST    : forall a$,b$ @ A\nP   |->  A\nx$  |->  (a$,,\"a$\"),(b$,,\"b$\")\nREBUILD  : forall a$,b$ @ A"
   OK
 , TLogGet "" ""
 ]
 )

matchAllXsYsP@(allxsysp,_) = ("allxsysp",
 TDescr "forall x$,y$ @ P" tstMtch
 [ TLogGet "" "forall x$,y$ @ P"
 , TLogPut "" "\nPATTERN : forall x$,y$ @ P\nTEST    : forall x$,y$ @ P\nP   |->  P\nx$  |->  (x$,,\"x$\")\ny$  |->  (y$,,\"y$\")\nREBUILD  : forall x$,y$ @ P"
   OK
 , TLogGet "" "A"
 , TLogPut "" "\nPATTERN : forall x$,y$ @ P\nTEST    : A\nP   |->  A\nx$  |->  .\ny$  |->  .\nREBUILD  : A"
   OK
 , TLogGet "" "forall x @ Q"
 , TLogPut "" "\nPATTERN : forall x$,y$ @ P\nTEST    : forall x @ Q\nP   |->  Q\nx$  |->  (x,,\"x\")\ny$  |->  .\nREBUILD  : forall x @ Q"
   OK
 , TLogGet "" "forall z$ @ R"
 , TLogPut "" "\nPATTERN : forall x$,y$ @ P\nTEST    : forall z$ @ R\nP   |->  R\nx$  |->  (z$,,\"z$\")\ny$  |->  .\nREBUILD  : forall z$ @ R"
   OK
 , TLogGet "" "forall a$,b$ @ C"
 , TLogPut "" "\nPATTERN : forall x$,y$ @ P\nTEST    : forall a$,b$ @ C\nP   |->  C\nx$  |->  (a$,,\"a$\")\ny$  |->  (b$,,\"b$\")\nREBUILD  : forall a$,b$ @ C"
   OK
 , TLogGet "" "forall a,b,c @ D"
 , TLogPut "" "\nPATTERN : forall x$,y$ @ P\nTEST    : forall a,b,c @ D\nP   |->  D\nx$  |->  (a,,\"a\"),(c,,\"c\")\ny$  |->  (b,,\"b\")\nREBUILD  : forall a,c,b @ D"
   OK
 , TLogGet "" ""
 ]
 )

matchAllXXsP@(allxxsp,_) = ("allxxsp",
 TDescr "forall x,x$ @ P" tstMtch
 [ TLogGet "" "forall x,x$ @ P"
 , TLogPut "" "\nPATTERN : forall x,x$ @ P\nTEST    : forall x,x$ @ P\nP   |->  P\nx   |->  (x,,\"x\")\nx$  |->  (x$,,\"x$\")\nREBUILD  : forall x,x$ @ P"
   OK
 , TLogGet "" "forall y,y$ @ Q"
 , TLogPut "" "\nPATTERN : forall x,x$ @ P\nTEST    : forall y,y$ @ Q\nP   |->  Q\nx   |->  (y,,\"y\")\nx$  |->  (y$,,\"y$\")\nREBUILD  : forall y,y$ @ Q"
   OK
 , TLogGet "" "forall x @ A"
 , TLogPut "" "\nPATTERN : forall x,x$ @ P\nTEST    : forall x @ A\nP   |->  A\nx   |->  (x,,\"x\")\nx$  |->  .\nREBUILD  : forall x @ A"
   OK
 , TLogGet "" "forall a$,a @ B"
 , TLogPut "" "\nPATTERN : forall x,x$ @ P\nTEST    : forall a,a$ @ B\nP   |->  B\nx   |->  (a,,\"a\")\nx$  |->  (a$,,\"a$\")\nREBUILD  : forall a,a$ @ B"
   OK
 , TLogGet "" ""
 ]
 )

matchAnyOaP@(anyoap,_) = ("anyoap",
 TDescr "exists O_a @ P" tstMtch
 [ TLogGet "" "exists O_a @ P"
 , TLogPut "" "\nPATTERN : exists O_a @ P\nTEST    : exists O_a @ P\nP     |->  P\nM_a   |->  (M,_a,\"M_a\")\nO_a   |->  (O,_a,\"O_a\")\nS_a   |->  (S,_a,\"S_a\")\nok_a  |->  (ok,_a,\"ok_a\")\nx_a   |->  (x,_a,\"x_a\")\ny_a   |->  (y,_a,\"y_a\")\nz_a   |->  (z,_a,\"z_a\")\nREBUILD  : exists O_a @ P"
   OK
 , TLogGet "" "exists M_s,S_s @ P"
 , TLogPut "" "\nPATTERN : exists O_a @ P\nTEST    : exists M_s,S_s @ P\nP     |->  P\nM_a   |->  (M,_s,\"M_s\")\nO_a   |->  (M,_s,\"M_s\"),(S,_s,\"S_s\")\nS_a   |->  (S,_s,\"S_s\")\nok_a  |->  (ok,_s,\"ok_s\")\nx_a   |->  (x,_s,\"x_s\")\ny_a   |->  (y,_s,\"y_s\")\nz_a   |->  (z,_s,\"z_s\")\nREBUILD  : exists M_s,S_s @ P"
   OK
 , TLogGet "" "exists S_x,M_x @ C"
 , TLogPut "" "\nPATTERN : exists O_a @ P\nTEST    : exists M_x,S_x @ C\nP     |->  C\nM_a   |->  (M,_x,\"M_x\")\nO_a   |->  (M,_x,\"M_x\"),(S,_x,\"S_x\")\nS_a   |->  (S,_x,\"S_x\")\nok_a  |->  (ok,_x,\"ok_x\")\nx_a   |->  (x,_x,\"x_x\")\ny_a   |->  (y,_x,\"y_x\")\nz_a   |->  (z,_x,\"z_x\")\nREBUILD  : exists M_x,S_x @ C"
   OK
 , TLogGet "" "exists O_b @ A"
 , TLogPut "" "\nPATTERN : exists O_a @ P\nTEST    : exists O_b @ A\nP     |->  A\nM_a   |->  (M,_b,\"M_b\")\nO_a   |->  (O,_b,\"O_b\")\nS_a   |->  (S,_b,\"S_b\")\nok_a  |->  (ok,_b,\"ok_b\")\nx_a   |->  (x,_b,\"x_b\")\ny_a   |->  (y,_b,\"y_b\")\nz_a   |->  (z,_b,\"z_b\")\nREBUILD  : exists O_b @ A"
   OK
 , TLogGet "" "exists M_b,S_b @ Q[S_b//S]"
 , TLogPut "" "\nPATTERN : exists O_a @ P\nTEST    : exists M_b,S_b @ Q[ S_b//S ]\nP     |->  Q[ S_b//S ]\nM_a   |->  (M,_b,\"M_b\")\nO_a   |->  (M,_b,\"M_b\"),(S,_b,\"S_b\")\nS_a   |->  (S,_b,\"S_b\")\nok_a  |->  (ok,_b,\"ok_b\")\nx_a   |->  (x,_b,\"x_b\")\ny_a   |->  (y,_b,\"y_b\")\nz_a   |->  (z,_b,\"z_b\")\nREBUILD  : exists M_b,S_b @ Q[ S_b//S ]"
   OK
 , TLogGet "" ""
 ]
 )


matchAnyOmP@(anyomp,_) = ("anyomp",
 TDescr "exists O_m @ P" tstMtch
 [ TLogGet "" "exists O_m @ P"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists O_m @ P\nP     |->  P\nM_m   |->  (M,_m,\"M_m\")\nO_m   |->  (O,_m,\"O_m\")\nS_m   |->  (S,_m,\"S_m\")\nok_m  |->  (ok,_m,\"ok_m\")\nx_m   |->  (x,_m,\"x_m\")\ny_m   |->  (y,_m,\"y_m\")\nz_m   |->  (z,_m,\"z_m\")\nREBUILD  : exists O_m @ P"
   OK
 , TLogGet "" "exists O_n @ P"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists O_n @ P\nP     |->  P\nM_m   |->  (M,_n,\"M_n\")\nO_m   |->  (O,_n,\"O_n\")\nS_m   |->  (S,_n,\"S_n\")\nok_m  |->  (ok,_n,\"ok_n\")\nx_m   |->  (x,_n,\"x_n\")\ny_m   |->  (y,_n,\"y_n\")\nz_m   |->  (z,_n,\"z_n\")\nREBUILD  : exists O_n @ P"
   OK
 , TLogGet "" "exists O @ P"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists O @ P\n        NO MATCH"
   OK
 , TLogGet "" "exists O' @ Q"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists O' @ Q\n        NO MATCH"
   OK
 , TLogGet "" "exists ok_m,x_m,y_m,z_m @ A"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists ok_m,x_m,y_m,z_m @ A\nP     |->  A\nM_m   |->  (M,_m,\"M_m\")\nO_m   |->  (ok,_m,\"ok_m\"),(x,_m,\"x_m\"),(y,_m,\"y_m\"),(z,_m,\"z_m\")\nS_m   |->  (S,_m,\"S_m\")\nok_m  |->  (ok,_m,\"ok_m\")\nx_m   |->  (x,_m,\"x_m\")\ny_m   |->  (y,_m,\"y_m\")\nz_m   |->  (z,_m,\"z_m\")\nREBUILD  : exists ok_m,x_m,y_m,z_m @ A"
   OK
 , TLogGet "" "exists x_m,ok_m,z_m,y_m @ B"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists ok_m,x_m,y_m,z_m @ B\nP     |->  B\nM_m   |->  (M,_m,\"M_m\")\nO_m   |->  (ok,_m,\"ok_m\"),(x,_m,\"x_m\"),(y,_m,\"y_m\"),(z,_m,\"z_m\")\nS_m   |->  (S,_m,\"S_m\")\nok_m  |->  (ok,_m,\"ok_m\")\nx_m   |->  (x,_m,\"x_m\")\ny_m   |->  (y,_m,\"y_m\")\nz_m   |->  (z,_m,\"z_m\")\nREBUILD  : exists ok_m,x_m,y_m,z_m @ B"
   OK
 , TLogGet "" "exists M_m,S_m @ Q"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists M_m,S_m @ Q\nP     |->  Q\nM_m   |->  (M,_m,\"M_m\")\nO_m   |->  (M,_m,\"M_m\"),(S,_m,\"S_m\")\nS_m   |->  (S,_m,\"S_m\")\nok_m  |->  (ok,_m,\"ok_m\")\nx_m   |->  (x,_m,\"x_m\")\ny_m   |->  (y,_m,\"y_m\")\nz_m   |->  (z,_m,\"z_m\")\nREBUILD  : exists M_m,S_m @ Q"
   OK
 , TLogGet "" "exists M_a,x_a,y_a,z_a @ C"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists x_a,y_a,z_a,M_a @ C\nP     |->  C\nM_m   |->  (M,_a,\"M_a\")\nO_m   |->  (x,_a,\"x_a\"),(y,_a,\"y_a\"),(z,_a,\"z_a\"),(M,_a,\"M_a\")\nS_m   |->  (S,_a,\"S_a\")\nok_m  |->  (ok,_a,\"ok_a\")\nx_m   |->  (x,_a,\"x_a\")\ny_m   |->  (y,_a,\"y_a\")\nz_m   |->  (z,_a,\"z_a\")\nREBUILD  : exists x_a,y_a,z_a,M_a @ C"
   OK
 , TLogGet "" "exists M_a,S_a @ P"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists M_a,S_a @ P\nP     |->  P\nM_m   |->  (M,_a,\"M_a\")\nO_m   |->  (M,_a,\"M_a\"),(S,_a,\"S_a\")\nS_m   |->  (S,_a,\"S_a\")\nok_m  |->  (ok,_a,\"ok_a\")\nx_m   |->  (x,_a,\"x_a\")\ny_m   |->  (y,_a,\"y_a\")\nz_m   |->  (z,_a,\"z_a\")\nREBUILD  : exists M_a,S_a @ P"
   OK
 , TLogGet "" "exists S_a,ok_a @ P"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists ok_a,S_a @ P\nP     |->  P\nM_m   |->  (M,_a,\"M_a\")\nO_m   |->  (ok,_a,\"ok_a\"),(S,_a,\"S_a\")\nS_m   |->  (S,_a,\"S_a\")\nok_m  |->  (ok,_a,\"ok_a\")\nx_m   |->  (x,_a,\"x_a\")\ny_m   |->  (y,_a,\"y_a\")\nz_m   |->  (z,_a,\"z_a\")\nREBUILD  : exists ok_a,S_a @ P"
   OK
 , TLogGet "" "exists S_a,M_b @ D"
 , TLogPut "" "\nPATTERN : exists O_m @ P\nTEST    : exists M_b,S_a @ D\n        NO MATCH"
   OK
 , TLogGet "" ""
 ]
 )



matchAnySvP@(anysvp,_) = ("anysvp",
 TDescr "exists S\\v @ P" tstMtch
 [ TLogGet "" "exists S\\v @ P"
 , TLogPut "" "\nPATTERN : exists S\\v @ P\nTEST    : exists S\\v @ P\nP    |->  P\nS\\v  |->  (S\\v,,\"S\\\\v\")\nv    |->  (v,,\"v\")\nREBUILD  : exists S\\v @ P"
   OK
 , TLogGet "" "exists S\\x @ P"
 , TLogPut "" "\nPATTERN : exists S\\v @ P\nTEST    : exists S\\x @ P\nP    |->  P\nS\\v  |->  (S\\x,,\"S\\\\x\")\nv    |->  (x,,\"x\")\nREBUILD  : exists S\\x @ P"
   OK
 , TLogGet "" "exists S\\u @ P"
 , TLogPut "" "\nPATTERN : exists S\\v @ P\nTEST    : exists S\\u @ P\nP    |->  P\nS\\v  |->  (S\\u,,\"S\\\\u\")\nv    |->  (u,,\"u\")\nREBUILD  : exists S\\u @ P"
   OK
 , TLogGet "" "exists x,y @ P"
 , TLogPut "" "\nPATTERN : exists S\\v @ P\nTEST    : exists x,y @ P\nP    |->  P\nS\\v  |->  (x,,\"x\"),(y,,\"y\")\nv    |->  (z,,\"z\")\nREBUILD  : exists x,y @ P"
   OK
 , TLogGet "" ""
 ]
 )

matchAnySvsP@(anysvsp,_) = ("anysvsp",
 TDescr "exists S\\v$ @ P" tstMtch
 [ TLogGet "" "exists S\\v$ @ P"
 , TLogPut "" "\nPATTERN : exists S\\v$ @ P\nTEST    : exists S\\v$ @ P\nP     |->  P\nS\\v$  |->  (S\\v$,,\"S\\\\v$\")\nv$    |->  (v$,,\"v$\")\nREBUILD  : exists S\\v$ @ P"
   OK
 , TLogGet "" "exists S\\u$ @ Q"
 , TLogPut "" "\nPATTERN : exists S\\v$ @ P\nTEST    : exists S\\u$ @ Q\nP     |->  Q\nS\\v$  |->  (S\\u$,,\"S\\\\u$\")\nv$    |->  (u$,,\"u$\")\nREBUILD  : exists S\\u$ @ Q"
   OK
 , TLogGet "" "exists S\\x @ Q"
 , TLogPut "" "\nPATTERN : exists S\\v$ @ P\nTEST    : exists S\\x @ Q\nP     |->  Q\nS\\v$  |->  (S\\x,,\"S\\\\x\")\nv$    |->  (x,,\"x\")\nREBUILD  : exists S\\x @ Q"
   OK
 , TLogGet "" "exists x,S\\x @ Q"
 , TLogPut "" "\nPATTERN : exists S\\v$ @ P\nTEST    : exists x,S\\x @ Q\nP     |->  Q\nS\\v$  |->  (x,,\"x\"),(S\\x,,\"S\\\\x\")\nv$    |->  .\nREBUILD  : exists x,S\\x @ Q"
   OK
 , TLogGet "" "exists S\\x:y @ Q"
 , TLogPut "" "\nPATTERN : exists S\\v$ @ P\nTEST    : exists S\\x:y @ Q\nP     |->  Q\nS\\v$  |->  (S\\x:y,,\"S\\\\x:y\")\nv$    |->  (x,,\"x\"),(y,,\"y\")\nREBUILD  : exists S\\x:y @ Q"
   OK
 , TLogGet "" "exists O\\ok:v$ @ Q"
 , TLogPut "" "\nPATTERN : exists S\\v$ @ P\nTEST    : exists O\\ok:v$ @ Q\nP     |->  Q\nS\\v$  |->  (O\\ok:v$,,\"O\\\\ok:v$\")\nv$    |->  (v$,,\"v$\")\nREBUILD  : exists O\\ok:v$ @ Q"
   OK
 , TLogGet "" ""
 ]
 )

matchAnySxP@(anysxp,_) = ("anysxp",
 TDescr "exists S\\x @ P" tstMtch
 [ TLogGet "" "exists S\\x @ P"
 , TLogPut "" "\nPATTERN : exists S\\x @ P\nTEST    : exists S\\x @ P\nP    |->  P\nS\\x  |->  (S\\x,,\"S\\\\x\")\nREBUILD  : exists S\\x @ P"
   OK
 , TLogGet "" "exists y,z @ P"
 , TLogPut "" "\nPATTERN : exists S\\x @ P\nTEST    : exists y,z @ P\nP    |->  P\nS\\x  |->  (y,,\"y\"),(z,,\"z\")\nREBUILD  : exists y,z @ P"
   OK
 , TLogGet "" "exists S\\u @ P"
 , TLogPut "" "\nPATTERN : exists S\\x @ P\nTEST    : exists S\\u @ P\n        NO MATCH"
   OK
 , TLogGet "" "exists x,y @ P"
 , TLogPut "" "\nPATTERN : exists S\\x @ P\nTEST    : exists x,y @ P\nP    |->  P\nS\\x  |->  (y,,\"y\"),(z,,\"z\")\nREBUILD  : exists y,z @ P"
   OK
 , TLogGet "" ""
 ]
 )
\end{code}

\subsection{List-Variable Equality Patterns}

\begin{code}
matchEqSS@(eqss,_) = ("eqss",
 TDescr "S' = S" tstMtch
 [ TLogGet "" "S' = S"
 , TLogPut "" "\nPATTERN : S' = S\nTEST    : S' = S\nS   |->  (S,,\"S\")\nS'  |->  (S,',\"S'\")\nREBUILD  : S' = S"
   OK
 , TLogGet "" "x'=x /\\ y'=y /\\ z'=z"
 , TLogPut "" "\nPATTERN : S' = S\nTEST    : ((x' = x) /\\ (y' = y)) /\\ (z' = z)\nS   |->  (x,,\"x\"),(y,,\"y\"),(z,,\"z\")\nS'  |->  (x,',\"x'\"),(y,',\"y'\"),(z,',\"z'\")\nREBUILD  : (x' = x) /\\ (y' = y) /\\ (z' = z)"
   OK
 , TLogGet "" "O'\\ok = O\\ok"
 , TLogPut "" "\nPATTERN : S' = S\nTEST    : O'\\ok = O\\ok\nS   |->  (O\\ok,,\"O\\\\ok\")\nS'  |->  (O\\ok,',\"O'\\\\ok\")\nREBUILD  : O'\\ok = O\\ok"
   OK
 , TLogGet "" "O'=O"
 , TLogPut "" "\nPATTERN : S' = S\nTEST    : O' = O\n        NO MATCH"
   OK
 , TLogGet "" ""
 ]
 )

matchEqSv@(eqsv,_) = ("eqsv",
 TDescr "S'\\v = S\\v" tstMtch
 [ TLogGet "" "S'\\v = S\\v"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : S'\\v = S\\v\nS'\\v  |->  (S\\v,',\"S'\\\\v\")\nS\\v   |->  (S\\v,,\"S\\\\v\")\nv     |->  (v,,\"v\")\nv'    |->  (v,',\"v'\")\nREBUILD  : S'\\v = S\\v"
   OK
 , TLogGet "" "S'\\u = S\\u"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : S'\\u = S\\u\nS'\\v  |->  (S\\u,',\"S'\\\\u\")\nS\\v   |->  (S\\u,,\"S\\\\u\")\nv     |->  (u,,\"u\")\nv'    |->  (u,',\"u'\")\nREBUILD  : S'\\u = S\\u"
   OK
 , TLogGet "" "x'=x /\\ y'=y"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : (x' = x) /\\ (y' = y)\nS'\\v  |->  (x,',\"x'\"),(y,',\"y'\")\nS\\v   |->  (x,,\"x\"),(y,,\"y\")\nv     |->  (z,,\"z\")\nv'    |->  (z,',\"z'\")\nREBUILD  : (x' = x) /\\ (y' = y)"
   OK
 , TLogGet "" "z'=z /\\ y'=y"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : (z' = z) /\\ (y' = y)\nS'\\v  |->  (y,',\"y'\"),(z,',\"z'\")\nS\\v   |->  (y,,\"y\"),(z,,\"z\")\nv     |->  (x,,\"x\")\nv'    |->  (x,',\"x'\")\nREBUILD  : (y' = y) /\\ (z' = z)"
   OK
 , TLogGet "" "x'=x"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : x' = x\n        NO MATCH"
   OK
 , TLogGet "" "O'\\ok:x = O\\ok:x"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : O'\\ok:x = O\\ok:x\nS'\\v  |->  (O\\ok:x,',\"O'\\\\ok:x\")\nS\\v   |->  (O\\ok:x,,\"O\\\\ok:x\")\nv     |->  (x,,\"x\")\nv'    |->  (x,',\"x'\")\nREBUILD  : O'\\ok:x = O\\ok:x"
   OK
 , TLogGet "" "S'\\x = S\\x"
 , TLogPut "" "\nPATTERN : S'\\v = S\\v\nTEST    : S'\\x = S\\x\nS'\\v  |->  (S\\x,',\"S'\\\\x\")\nS\\v   |->  (S\\x,,\"S\\\\x\")\nv     |->  (x,,\"x\")\nv'    |->  (x,',\"x'\")\nREBUILD  : S'\\x = S\\x"
   OK
 , TLogGet "" ""
 ]
 )

matchEqSx@(eqsx,_) = ("eqsx",
 TDescr "S'\\x = S\\x" tstMtch
 [ TLogGet "" "S'\\x = S\\x"
 , TLogPut "" "\nPATTERN : S'\\x = S\\x\nTEST    : S'\\x = S\\x\nS'\\x  |->  (S\\x,',\"S'\\\\x\")\nS\\x   |->  (S\\x,,\"S\\\\x\")\nREBUILD  : S'\\x = S\\x"
   OK
 , TLogGet "" "S'\\v = S\\v"
 , TLogPut "" "\nPATTERN : S'\\x = S\\x\nTEST    : S'\\v = S\\v\n        NO MATCH"
   OK
 , TLogGet "" "y'=y /\\ z'=z"
 , TLogPut "" "\nPATTERN : S'\\x = S\\x\nTEST    : (y' = y) /\\ (z' = z)\nS'\\x  |->  (y,',\"y'\"),(z,',\"z'\")\nS\\x   |->  (y,,\"y\"),(z,,\"z\")\nREBUILD  : (y' = y) /\\ (z' = z)"
   OK
 , TLogGet "" "x'=x /\\ y' = y"
 , TLogPut "" "\nPATTERN : S'\\x = S\\x\nTEST    : (x' = x) /\\ (y' = y)\n        NO MATCH"
   OK
 , TLogGet "" "x'=x"
 , TLogPut "" "\nPATTERN : S'\\x = S\\x\nTEST    : x' = x\n        NO MATCH"
   OK
 , TLogGet "" "O'\\ok:x = O\\ok:x"
 , TLogPut "" "\nPATTERN : S'\\x = S\\x\nTEST    : O'\\ok:x = O\\ok:x\nS'\\x  |->  (O\\ok:x,',\"O'\\\\ok:x\")\nS\\x   |->  (O\\ok:x,,\"O\\\\ok:x\")\nREBUILD  : O'\\ok:x = O\\ok:x"
   OK
 , TLogGet "" ""
 ]
 )

matchEqXsO@(eqxso,_) = ("eqxso",
 TDescr "x$ = O" tstMtch
 [ TLogGet "" "x$ = O"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : x$ = O\nO   |->  (O,,\"O\")\nx$  |->  (x$,,\"x$\")\nREBUILD  : x$ = O"
   OK
 , TLogGet "" "y$ = O"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : y$ = O\nO   |->  (O,,\"O\")\nx$  |->  (y$,,\"y$\")\nREBUILD  : y$ = O"
   OK
 , TLogGet "" "ok=ok /\\ x=x /\\ y=y /\\ z=z"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : (((ok = ok) /\\ (x = x)) /\\ (y = y)) /\\ (z = z)\nO   |->  (ok,,\"ok\"),(x,,\"x\"),(y,,\"y\"),(z,,\"z\")\nx$  |->  (ok,,\"ok\"),(x,,\"x\"),(y,,\"y\"),(z,,\"z\")\nREBUILD  : (ok = ok) /\\ (x = x) /\\ (y = y) /\\ (z = z)"
   OK
 , TLogGet "" "a=ok /\\ b=x"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : (a = ok) /\\ (b = x)\n        NO MATCH"
   OK
 , TLogGet "" "ok=a /\\ b=x"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : (ok = a) /\\ (b = x)\n        NO MATCH"
   OK
 , TLogGet "" "a=ok /\\ b=x /\\ c=y /\\ d=z"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : (((a = ok) /\\ (b = x)) /\\ (c = y)) /\\ (d = z)\nO   |->  (ok,,\"ok\"),(x,,\"x\"),(y,,\"y\"),(z,,\"z\")\nx$  |->  (a,,\"a\"),(b,,\"b\"),(c,,\"c\"),(d,,\"d\")\nREBUILD  : (a = ok) /\\ (b = x) /\\ (c = y) /\\ (d = z)"
   OK
 , TLogGet "" "ok=a /\\ x=b /\\ y=c /\\ z=d"
 , TLogPut "" "\nPATTERN : x$ = O\nTEST    : (((ok = a) /\\ (x = b)) /\\ (y = c)) /\\ (z = d)\n        NO MATCH"
   OK
 , TLogGet "" ""
 ]
 )

matchEqXsEs@(eqxses,_) = ("eqxses",
 TDescr "x$ = e$" tstMtch
 [ TLogGet "" "v$ = e$"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : v$ = e$\ne$  |->  (e$,,\"e$\")\nv$  |->  (v$,,\"v$\")\nREBUILD  : v$ = e$"
   OK
 , TLogGet "" "v$ = v$"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : v$ = v$\ne$  |->  (v$,,\"v$\")\nv$  |->  (v$,,\"v$\")\nREBUILD  : v$ = v$"
   OK
 , TLogGet "" "O' = O"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : O' = O\ne$  |->  (O,,\"O\")\nv$  |->  (O,',\"O'\")\nREBUILD  : O' = O"
   OK
 , TLogGet "" "v = e"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : v = e\ne$  |->  (e,,\"e\")\nv$  |->  (v,,\"v\")\nREBUILD  : v = e"
   OK
 , TLogGet "" "v = e /\\ u = f"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : (v = e) /\\ (u = f)\ne$  |->  (e,,\"e\"),(f,,\"f\")\nv$  |->  (v,,\"v\"),(u,,\"u\")\nREBUILD  : (v = e) /\\ (u = f)"
   OK
 , TLogGet "" "u = v+1 /\\ v' = u-2"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : (u = v + 1) /\\ (v' = u -2)\ne$  |->  v + 1,u -2\nv$  |->  (u,,\"u\"),(v,',\"v'\")\nREBUILD  : (u = v + 1) /\\ (v' = u -2)"
   OK
 , TLogGet "" "O' = S"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : O' = S\n        NO MATCH"
   OK
 , TLogGet "" "M' = M /\\ S' = S"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : (M' = M) /\\ (S' = S)\ne$  |->  (M,,\"M\"),(S,,\"S\")\nv$  |->  (M,',\"M'\"),(S,',\"S'\")\nREBUILD  : (M' = M) /\\ (S' = S)"
   OK
 , TLogGet "" "x = 42 /\\ u$ = f$"
 , TLogPut "" "\nPATTERN : v$ = e$\nTEST    : (x = 42) /\\ (u$ = f$)\ne$  |->  42,f$\nv$  |->  (x,,\"x\"),(u$,,\"u$\")\nREBUILD  : (x = 42) /\\ (u$ = f$)"
   OK
 , TLogGet "" ""
 ]
 )

matchEqSVs@(eqsvs,_) = ("eqsvs",
 TDescr "S'\\v$ = S\\v$" tstMtch
 [ TLogGet "" "S'\\v$ = S\\v$"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : S'\\v$ = S\\v$\nS'\\v$  |->  (S\\v$,',\"S'\\\\v$\")\nS\\v$   |->  (S\\v$,,\"S\\\\v$\")\nv$     |->  (v$,,\"v$\")\nREBUILD  : S'\\v$ = S\\v$"
   OK
 , TLogGet "" "S'\\v$ = S\\u$"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : S'\\v$ = S\\u$\n        NO MATCH"
   OK
 , TLogGet "" "S'\\u$ = S\\u$"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : S'\\u$ = S\\u$\nS'\\v$  |->  (S\\u$,',\"S'\\\\u$\")\nS\\v$   |->  (S\\u$,,\"S\\\\u$\")\nv$     |->  (u$,,\"u$\")\nREBUILD  : S'\\u$ = S\\u$"
   OK
 , TLogGet "" "S\\v$ = S'\\v$"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : S\\v$ = S'\\v$\n        NO MATCH"
   OK
 , TLogGet "" "O'\\u$ = O\\u$"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : O'\\u$ = O\\u$\n        NO MATCH"
   OK
 , TLogGet "" "O'\\ok:u$ = O\\ok:u$"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : O'\\ok:u$ = O\\ok:u$\nS'\\v$  |->  (O\\ok:u$,',\"O'\\\\ok:u$\")\nS\\v$   |->  (O\\ok:u$,,\"O\\\\ok:u$\")\nv$     |->  (u$,,\"u$\")\nREBUILD  : O'\\ok:u$ = O\\ok:u$"
   OK
 , TLogGet "" "S'\\x = S\\x"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : S'\\x = S\\x\nS'\\v$  |->  (S\\x,',\"S'\\\\x\")\nS\\v$   |->  (S\\x,,\"S\\\\x\")\nv$     |->  .\nREBUILD  : S'\\x = S\\x"
   (FAIL "v$ should bind to x")
 , TLogGet "" "S'\\x:y = S\\x:y"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : S'\\x:y = S\\x:y\nS'\\v$  |->  (S\\x:y,',\"S'\\\\x:y\")\nS\\v$   |->  (S\\x:y,,\"S\\\\x:y\")\nv$     |->  .\nREBUILD  : S'\\x:y = S\\x:y"
   (FAIL "v$ should bind to x,y")
 , TLogGet "" "x'=x /\\ y'=y"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : (x' = x) /\\ (y' = y)\nS'\\v$  |->  (x,',\"x'\"),(y,',\"y'\")\nS\\v$   |->  (x,,\"x\"),(y,,\"y\")\nv$     |->  (z,,\"z\")\nv$'    |->  (z,',\"z'\")\nREBUILD  : (x' = x) /\\ (y' = y)"
   OK
 , TLogGet "" "x'=x"
 , TLogPut "" "\nPATTERN : S'\\v$ = S\\v$\nTEST    : x' = x\nS'\\v$  |->  (x,',\"x'\")\nS\\v$   |->  (x,,\"x\")\nv$     |->  .\nREBUILD  : x' = x"
   (FAIL "v$ should bind to y,z")
 , TLogGet "" ""
 ]
 )

matchEqSUsVs@(eqsusvs,_) = ("eqsusvs",
 TDescr "S'\\u$:v$ = S\\u$:v$" tstMtch
 [ TLogGet "" "S'\\u$:v$ = S\\u$:v$"
 , TLogPut "" "\nPATTERN : S'\\u$:v$ = S\\u$:v$\nTEST    : S'\\u$:v$ = S\\u$:v$\n        NO MATCH"
   (FAIL "both u$ and v$ could map to themselves (or each other !)")
 , TLogGet "" "S'=S"
 , TLogPut "" "\nPATTERN : S'\\u$:v$ = S\\u$:v$\nTEST    : S' = S\n        NO MATCH"
   (FAIL "both u$ and v$ could map to <>")
 , TLogGet "" "S'\\w$ = S\\w$"
 , TLogPut "" "\nPATTERN : S'\\u$:v$ = S\\u$:v$\nTEST    : S'\\w$ = S\\w$\n        NO MATCH"
   (FAIL "one of u$,v$ could bind to w$")
 , TLogGet "" "S'\\v$ = S\\w$"
 , TLogPut "" "\nPATTERN : S'\\u$:v$ = S\\u$:v$\nTEST    : S'\\v$ = S\\w$\n        NO MATCH"
   OK
 , TLogGet "" "S'\\x:y = S\\x:y"
 , TLogPut "" "\nPATTERN : S'\\u$:v$ = S\\u$:v$\nTEST    : S'\\x:y = S\\x:y\n        NO MATCH"
   (FAIL "both u$ and v$ could map to x and y")
 , TLogGet "" ""
 ]
 )

matchEqXSUs@(eqxsus,_) = ("eqxsus",
 TDescr "x$ = S'\\u$" tstMtch

 [ TLogGet "" "x$ = S'\\u$"
 , TLogPut "" "\nPATTERN : x$ = S'\\u$\nTEST    : x$ = S'\\u$\nS'\\u$  |->  (S\\u$,',\"S'\\\\u$\")\nu$     |->  (u$,,\"u$\")\nx$     |->  (x$,,\"x$\")\nREBUILD  : x$ = S'\\u$"
   OK
 , TLogGet "" "y$ = S'\\v$"
 , TLogPut "" "\nPATTERN : x$ = S'\\u$\nTEST    : y$ = S'\\v$\nS'\\u$  |->  (S\\v$,',\"S'\\\\v$\")\nu$     |->  (v$,,\"v$\")\nx$     |->  (y$,,\"y$\")\nREBUILD  : y$ = S'\\v$"
   OK
 , TLogGet "" "x = S'\\y:z"
 , TLogPut "" "\nPATTERN : x$ = S'\\u$\nTEST    : x = S'\\y:z\nS'\\u$  |->  (S\\y:z,',\"S'\\\\y:z\")\nu$     |->  (y,,\"y\"),(z,,\"z\")\nx$     |->  (x,,\"x\")\nREBUILD  : x = S'\\y:z"
   OK
 , TLogGet "" ""
 ]
 )

matchEqUsSX@(equssx,_) = ("equssx",
 TDescr "x$ = S'\\v" tstMtch
 [ TLogGet "" "x$ = S'\\v"
 , TLogPut "" "\nPATTERN : x$ = S'\\v\nTEST    : x$ = S'\\v\nS'\\v  |->  (S\\v,',\"S'\\\\v\")\nv     |->  (v,,\"v\")\nv'    |->  (v,',\"v'\")\nx$    |->  (x$,,\"x$\")\nREBUILD  : x$ = S'\\v"
   OK
 , TLogGet "" "u$ = S'\\u"
 , TLogPut "" "\nPATTERN : x$ = S'\\v\nTEST    : u$ = S'\\u\nS'\\v  |->  (S\\u,',\"S'\\\\u\")\nv     |->  (u,,\"u\")\nv'    |->  (u,',\"u'\")\nx$    |->  (u$,,\"u$\")\nREBUILD  : u$ = S'\\u"
   OK
 , TLogGet "" "u$ = S'\\x"
 , TLogPut "" "\nPATTERN : x$ = S'\\v\nTEST    : u$ = S'\\x\nS'\\v  |->  (S\\x,',\"S'\\\\x\")\nv     |->  (x,,\"x\")\nv'    |->  (x,',\"x'\")\nx$    |->  (u$,,\"u$\")\nREBUILD  : u$ = S'\\x"
   OK
 , TLogGet "" "u$ = S'\\w$"
 , TLogPut "" "\nPATTERN : x$ = S'\\v\nTEST    : u$ = S'\\w$\n        NO MATCH"
   OK
 , TLogGet "" ""
 ]
 )
\end{code}
