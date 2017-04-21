\section{Laws of UTP}

Laws specific to UTP in General

\begin{code}
module UTP where
import Tables
import Utilities
import Datatypes
import DataText
import Heuristics
import MatchTypes
import Laws
import Proof
import Theories
import Precedences
import DSL
import RootTheory
--import Builtin
import Data.List

import Text.ParserCombinators.Parsec.Expr
\end{code}

\subsection{Useful definitions}

\begin{code}
utpProvenance = FromSOURCE "UTP"
mkUTPLaw = mklaw utpProvenance
freeUTPLaw = freelaw utpProvenance
\end{code}


Numbering here refers to sections in the UTP book.
\begin{code}
n_b = "b"
n_c = "c"
n_p = "P"
n_q = "Q"
n_r = "R"
n_s = "S"
n_x = "X"

b = Pvar $ Std n_b
c = Pvar $ Std n_c
p = Pvar $ Std n_p
q = Pvar $ Std n_q
r = Pvar $ Std n_r
s = Pvar $ Std n_s
xx = Pvar $ Std n_x
\end{code}

\subsection{The Logic of Engineering Design (1)}


\subsubsection{Correctness (1.5)}

Definition of universal quantification over all free variables:
$$
[ P ] \equiv (\forall x_1,\ldots,x_n @ P)
      \qquad \{x_1,\ldots,x_n\} = FV(P)
$$
\begin{code}
lUnivDef = (Univ 0 p) === (mkAll qxs p)
flUnivDef = (lUnivDef,SCareTheFreeOf PredM [lstAsGen "x"] n_p)
\end{code}

Disjunction as the least upper bound of the implication ordering:
$$
 [P \lor Q \implies R] \equiv [P \implies R] \land [Q \implies R]
$$
\begin{code}
lDisjLUB = (Univ 0 (p \/ q ==> s))
             === (Univ 0 (p ==> s)) /\ (Univ 0 (q ==> s))
flDisjLUB = (lDisjLUB,SCtrue)
\end{code}

Pulling out the weakest sub-part specification:
$$
 [X \land Q \implies S] \equiv [X \implies (\lnot Q \lor S)]
$$
\begin{code}
lWkSubSpec = (Univ 0 (xx /\ q ==> s)) === (Univ 0 (xx ==> ((Not q) \/ s)))
flWkSubSpec = (lWkSubSpec,SCtrue)
\end{code}

Bring them all together:
\begin{code}
utp_laws_1_5
  = [("DEF-Univ",flUnivDef)
    ,("\\/-lub",flDisjLUB)
    ,("wk-sub-spec",flWkSubSpec)
    ]
\end{code}


\subsubsection{Abstraction (1.6)}

Abstraction:
$$
  [P\implies S] \equiv [(\exists v @ P) \implies S],
  \qquad
  v \notin S
$$
\begin{code}
flHideVar
  = ( (Univ 0 (p ==> s)) === (Univ 0 ((mkAny vs p) ==> s))
    , SCnotFreeIn PredM [lstAsGen "v"] n_s )
  where vs = qvarr "vs"
\end{code}

The residual:
$$
  [X \land Q \implies S] \equiv [X \implies \forall x' @ Q \implies S],
  \qquad
  x \notin X
$$
\begin{code}
flResidual
 = ( (Univ 0 (xx /\ q ==> s)) === (Univ 0 (xx ==> (mkAll xs (q ==> s))))
   , SCnotFreeIn PredM [lstAsGen "x"] n_x )
 where xs = qvarr "xs"
\end{code}

Now, \emph{the} Galois Connection:
$$
 [(\exists c @ D(c) \land L(c,a)) \implies S(a)]
 \equiv
 [D(c) \implies (\forall a @ L(c,a) \implies S(a)) ]
$$
\begin{code}
flTheGC
 = ( left===right, scand [dsc,ssc] )
 where
   a = qvarr "a"
   c = qvarr "c"
   d = Pvar $ Std " D"
   s = Pvar $ Std " S"
   l = Pvar $ Std " L" -- we will have a matching problem to resolve
   left  =  Univ 0 ((mkAny c (d /\ l)) ==> s)
   dsc = SCnotFreeIn PredM [preVar "a"] " D"
   ssc = SCnotFreeIn PredM [preVar "c"] " S"
   right =  Univ 0 (d ==> (mkAll a (l ==> s)))

utp_laws_1_6
  = [("hide-variables",flHideVar)
    ,("residual",flResidual)
    ,("the-Galois-Connection",flTheGC)
    ]
\end{code}


\subsection{Relations (2)}

\subsection{Conditional (2.1)}

Many of these are already included under general logic,
but the following are new:
\begin{eqnarray*}
   P \cond b Q &\equiv& Q \cond{\lnot b} P
\\ P \cond b (Q \cond c R)
   &\equiv&
   P \cond{b \land c} (Q \cond c R)
\\ P \cond b (P \cond c Q)
   &\equiv&
   P \cond{b \lor c} Q
\end{eqnarray*}
\begin{code}
lCondSymm =  p <| b |> q === q <| Not b |> p
lCondAssoc = p <| b |> (q <| c |> r)
             ===
             p <| (b /\ c) |> (q <| c |> r)
lCondMerge = p <| b |> (p <| c |> q) === p <| (b \/ c) |> q
\end{code}

We also need instantiations of the following mutual distribution
law (aka \emph{interchange} or \emph{abides}), for truth-functional
$\odot$:
$$
 (P \odot Q) \cond b (R \odot S)
 \equiv
 (P \cond b R) \odot (Q \cond b S)
$$
\begin{code}
mkAbide odot = ((p `odot` q) <| b |> (r `odot` s))
               ===
               ((p <| b |> r) `odot` (q <| b |> s))
lAndAbides = mkAbide (/\)
lOrAbides = mkAbide (\/)
lImpAbides = mkAbide (==>)
lEqvAbides = mkAbide (===)
\end{code}

All together:
\begin{code}
utp_laws_2_1
  = [("<||>-symm",(lCondSymm,SCtrue))
    ,("<||>-assoc",(lCondAssoc,SCtrue))
    ,("<||>-merge",(lCondMerge,SCtrue))
    ,("/\\-abides",(lAndAbides,SCtrue))
    ,("\\/-abides",(lOrAbides,SCtrue))
    ,("=>-abides",(lImpAbides,SCtrue))
    ,("==-abides",(lEqvAbides,SCtrue))
    ]
\end{code}

\subsection{Sequential Composition (2.2)}

The definition of sequential composition is left to the relevant
theory (imperative, reactive, etc).
Here we simply capture laws common to all uses of it:
\begin{eqnarray*}
   P; (Q; R) &\equiv& (P; Q) ; R
\\ (P \cond C Q );R &\equiv& (P;R) \cond C (Q;R), \qquad C\mbox{ a condition}
\\ (b \land P);Q &\equiv& b \land (P;Q)
\\ (C \land P);Q &\equiv& C \land (P;Q), \qquad C\mbox{ a condition}
\\ P;(Q \land b') &\equiv& (P;Q) \land b'
\\ (P \land b');Q &\equiv& P;(b \land Q)
\end{eqnarray*}
\begin{code}
compSynSpec = [SSNull,SSTok ";",SSNull]
compLangSpec = LangSpec [lPredSpec,lPredSpec] compSynSpec

bpre  = Obs (Var $ preVar "b")
bpost = Obs (Var $ postVar "b")


lCompAssoc  =  (p >>> (q >>> r))
                === ((p >>> q) >>> r)
lCompCondRDistr  =  ((p <| b |> q) >>> r)
                     === ((p >>> r) <| b |> (q >>> r))
lPrePreBoolComp  = ((bpre /\ p) >>> q)  === (bpre /\ (p >>> q))
lPreCondBoolComp  = ((b /\ p) >>> q)  === (b /\ (p >>> q))
lPostPostBoolComp  = (p >>> (q /\ bpost))  === ((p >>> q) /\ bpost)
lPostPreBoolComp  = ((p /\ bpost) >>> q)  === (p >>> (bpre /\ q))


utp_laws_2_2
  = [(";-assoc",(lCompAssoc,SCtrue))
    ,(";-<||>-r-distr",(lCompCondRDistr,isCondP n_b))
    ,("*b-/\\-;",(lPrePreBoolComp,SCtrue))
    ,("pre-/\\-;",(lPreCondBoolComp,isCondP n_b))
    ,(";-/\\-b*",(lPostPostBoolComp,SCtrue))
    ,("post-/\\-;-/\\-pre",(lPostPreBoolComp,SCtrue))
    ]
\end{code}

\subsection{Non-determinism (2.4)}

We don't treat this in a special way, but simply treat it as \texttt{Or ..}.
We have some additional distribution laws w.r.t to conditional
and sequential composition:
\begin{eqnarray*}
   P \cond b  (Q \lor R) &\equiv& (P \cond b Q) \lor (P \cond b R)
\\ P \lor (Q \cond b R) &\equiv& (P \lor Q) \cond b (P \lor R)
\\ P ; (Q \lor R) &\equiv& (P;Q) \lor (P;R)
\\ (P \lor Q) ; R) &\equiv& (P;Q) \lor (Q;R)
\end{eqnarray*}
\begin{code}
lCondOrDistr = (p <| b |> (q \/r)) === (p <| b |> q) \/ (p <| b |> r)
lOrCondDistr = p \/ (q <| b |> r) === (p \/ q) <| b |> (p \/ r)
lCompOrLDistr = p >>> (q \/ r) === (p >>> q) \/ (p >>> r)
lCompOrRDistr = (p \/ q) >>> r === (p >>> r) \/ (q >>> r)

utp_laws_2_4
  = [("<||>-\\/-distr",(lCondOrDistr,SCtrue))
    ,("\\/<||>-distr",(lOrCondDistr,SCtrue))
    ,(";-\\/-l-distr",(lCompOrLDistr,SCtrue))
    ,(";-\\/-r-distr",(lCompOrRDistr,SCtrue))
    ]
\end{code}

\subsection{Strongest Fixed Point (2.7)}

\begin{eqnarray*}
   \FALSE ; P  \quad \equiv & \FALSE &  \equiv \quad P ; \FALSE
\end{eqnarray*}
\begin{code}
lFalseComp =  FALSE >>> p  ===  FALSE
lCompFalse =  p >>> FALSE  ===  FALSE

utp_laws_2_7
  = [("false-;",(lFalseComp,SCtrue))
    ,(";-false",(lCompFalse,SCtrue))
    ]
\end{code}




\subsection{And the Law is \ldots}

\begin{code}
utpLawTable
  = map (wrapProv utpProvenance)
     ( concat -- ltorder [] (ranklist (lawRank []) (concat
        [ utp_laws_1_5
        , utp_laws_1_6
        , utp_laws_2_1
        , utp_laws_2_2
        , utp_laws_2_4
        , utp_laws_2_7
        ] ) -- )


utpName = "UTP"

utpProofContext
  = (buildLangDefinitions . markTheoryDeps)
       ((nmdNullPrfCtxt utpName)
                      { syntaxDeps = [ rootName ]
                      , lang = lbuild [(";",compLangSpec)]
                      , precs = lbuild [ ( ";" , (opPrec 1 ";",AssocRight) ) ]
                      , laws = utpLawTable
                      })
\end{code}


\subsection{A less generic version}

\begin{code}
xyzName = "XYZDesign"

xyzPrec = [ ( ";"   , (opPrec 1 ";",AssocRight) )
          , ( "|-"  , (opPrec 1 "|-",AssocNone) )
          , ( "|="  , (opPrec 1 "|=",AssocNone) )
          , ( ":="  , (60,AssocNone) )
          , ( "::=" , (60,AssocNone) )
          ]

designSynSpec = [SSNull,SSTok "|-",SSNull]
designLangSpec = LangSpec [lPredSpec,lPredSpec] designSynSpec

rfdbySynSpec = [SSNull,SSTok "|=",SSNull]
rfdbyLangSpec = LangSpec [lPredSpec,lPredSpec] rfdbySynSpec

asgSynSpec = [SSNull,SSTok ":=",SSNull]
asgLangSpec = LangSpec [gVarSpec,lExprSpec] asgSynSpec

simAsgSynSpec = [SSNull,SSTok "::=",SSNull]
simAsgLangSpec = LangSpec [gVarSpec,lExprSpec] asgSynSpec

xyzLang = [ (";",compLangSpec)
          , ("|-",designLangSpec)
          , ("|=",rfdbyLangSpec)
          , (":=",asgLangSpec)
          , ("::=",simAsgLangSpec)
          ]

xyz = ["ok","x","y","z"]
xyzbefore = map preVar xyz
xyzmid    = map (subVar "m") xyz
xyzafter = map postVar xyz
xyzobs = lnorm (xyzbefore++xyzafter)
xyzQbefore = Q $ lnorm $ xyzbefore
xyzQmid = Q $ lnorm $ xyzmid
xyzQafter = Q $ lnorm $ xyzafter
xyzQobs = Q xyzobs

xyzObs = map f observations
 where
   f (v,c,t) = (varKey v,(v,c,t))
   observations
    = [ (preVar "ok",Model, B), (postVar "ok",Model, B)
      , (preVar "x", Script,Z), (postVar "x", Script,Z)
      , (preVar "y", Script,Z), (postVar "y", Script,Z)
      , (preVar "z", Script,Z), (postVar "z", Script,Z)
      ]

p `xyzcomp` q = mkBinLang compLangSpec (opPrec 1 ";") (LPred p) (LPred q)
xyzpostsub p = Sub p (Substn (zip xyzafter (map Var xyzmid)))
xyzpresub p  = Sub p (Substn (zip xyzbefore (map Var xyzmid)))

p `xyzdesign` q = Lang "|-" (opPrec 1 "|-") [LPred p,LPred q] designSynSpec

p `xyzrfdby` q = Lang "|=" (opPrec 1 "|=") [LPred p,LPred q] rfdbySynSpec

v `xyzasg` e = Lang ":=" 60 [LVar v,LExpr e] asgSynSpec

v `xyzsasg` e = Lang "::=" 60 [LVar v,LExpr e] simAsgSynSpec

xyzDefs = [ ( ";"
            , (p `xyzcomp` q)
              ===
              Exists 0 xyzQmid
                ( xyzpostsub p /\ xyzpresub q )
            )
          , ( "|-"
            , (p `xyzdesign` q)
               ===
               (ok /\ p ==> ok' /\ q)
            )
          , ( "xyz-univ"
            , Univ 0 p === Forall 0 xyzQobs p
            )
          , ( "|="
            , p `xyzrfdby` q === Univ 0 ( q ==> p )
            )
          , ( ":="
            , Std "v" `xyzasg` e
               === ( ok ==>
                      ok'
                      /\ Obs (Equal (Var $ postVar "v") e)
                      /\ Obs (Equal (Var (scrList' \\\ [Std "v"]))
                                    (Var (scrList \\\ [Std "v"])))
                   )
            )
          , ( "::="
            , Lst "v" `xyzasg` (Var $ lstAsGen "e")
               === ( ok ==>
                      ok'
                      /\ Obs (Equal (Var $ lstAsGen' "v") (Var $ lstAsGen "e"))
                      /\ Obs (Equal (Var (scrList' \\\ [Lst "v"]))
                                    (Var (scrList \\\ [Lst "v"])))
                   )
            )
          , ( "cond"
            , p <| b |> q ===  b /\ p \/ (Not b) /\ q
            )
          ]

mkaxiom (nm,pr) = (nm,(pr,SCtrue))
mkdef (nm,pr) = mkaxiom ("DEF "++nm,pr)

mbefore = obsList
mmid    = lsubVar "m" strOBS
mafter  = obsList'
mQbefore = Q [mbefore]
mQmid    = Q [mmid]
mQafter  = Q [mafter]
mpostsub p = Sub p (Substn [(mafter,Var mmid)])
mpresub p  = Sub p (Substn [(mbefore,Var mmid)])


xyzAxioms = [ ( "3way-absorb" , Or [p /\ q, p /\ r, q /\ (Not r)]
                                ===
                                Or [p /\ r , q /\ (Not r)]
              )
--             , ( "alt-DEF ;" , (p `xyzcomp` q)
--               ===
--               Exists mQmid TRUE
--                 ( mpostsub p /\ mpresub q )
--               )
            ]


xyzLaws = map (wrapProv utpProvenance)
              (map mkaxiom xyzAxioms ++ map mkdef xyzDefs)

p1 = Pvar $ Std "P1"
p2 = Pvar $ Std "P2"
q1 = Pvar $ Std "Q1"
q2 = Pvar $ Std "Q2"
p1q1 = p1 `xyzdesign` q1
p2q2 = p2 `xyzdesign` q2

xyzConjs = [ ( "xyz-univ-TRUE", Univ 0 TRUE )
           , ( "export-pre"
             , ( p `xyzdesign` q )
                 === ( p `xyzdesign` (p /\ q))
             )
           , ( "design-or-distr"
             , (p1q1 \/ p2q2) === ( (p1 /\ p2) `xyzdesign` (q1 \/ q2) )
             )
           , ( "design-cond-distr"
             , p1q1 <| b |> p2q2 === (p1 <| b |> p2) `xyzdesign` (q1 <| b |> q2)
             )
           , ( "ref-refl", p `xyzrfdby` p )
           , ( "ref-antisymm"
             , p `xyzrfdby` q /\ q `xyzrfdby` p ==> Univ 0 (p === q)
             )
           , ( "ref-tran"
             , p `xyzrfdby` q /\ q `xyzrfdby` r ==> p `xyzrfdby` r
             )
           ]

xyzcompassoc = ( "xyz-comp-assoc"
                , ( (p `xyzcomp` (q `xyzcomp` r))
                      === ((p `xyzcomp` q) `xyzcomp` r)
                    ,
                    scand [ SCareTheFreeOf PredM xyzobs n_p
                          , SCareTheFreeOf PredM xyzobs n_q
                          , SCareTheFreeOf PredM xyzobs n_r
                          ]
                  )
               )


mkconj (n,pr) = (n,(pr,SCtrue))

-- known stuff is handy
knownTD = lbuild [("Tknwn",Z),("Tself",Tvar "Tself")]
knownK = lbuild [("Two",Num 2)]
knownE = lbuild [("Eknwn",Num 42),("Eself",Evar $ preVar "Eself")]
knownP = lbuild [("Pknwn",TRUE),("Pself",Pvar $ Std "Pself"),("Pother",Pvar $ Std "Pself")]

xyzDesignTheory
  = (buildLangDefinitions .markTheoryDeps)
        ((nmdNullPrfCtxt xyzName)
                      { syntaxDeps = [ rootName ]
                      , lang = lbuild xyzLang
                      , precs = lbuild xyzPrec
                      , obs = lbuild xyzObs
                      , laws = xyzLaws
                      , conjectures = lbuild (map mkconj xyzConjs)
                      --
                      , typedefs = knownTD
                      , consts = knownK
                      , exprs = knownE
                      , preds = knownP
                      })
\end{code}
