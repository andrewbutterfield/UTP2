\section{Gries/Schneider (Equational) Logic}


\begin{code}
module GS3001 where
import Tables
import Datatypes
import Heuristics
import DataText
import Laws
import Proof
import Theories
import DSL
import RootTheory
import Logic -- for boolOpTypes
import Data.List
\end{code}

\subsection{Useful definitions}

\begin{code}
gs3001Provenance = FromSOURCE "GS3001"
mkGS3001Law = mklaw gs3001Provenance
freeGS3001Law = freelaw gs3001Provenance
\end{code}




\subsection{Laws of Propositional Calculus}

The Law according to Gries \& Schneider (and Dijkstra),
tailored for 3BA31 Formal Methods.



\subsubsection{Equivalence and True}

\begin{code}

gslAxAssocEqv  =  ((pP === pQ) === pR) === (pP === (pQ === pR))  -- 3.1
gslAxSymmEqv   =  (pP === pQ)  === (pQ === pP)                   -- 3.2
gslAxIdEqv     =  TRUE === (pP === pP)                           -- 3.3

gs_laws_1
   =   freeGS3001Law "==-Assoc" gslAxAssocEqv
   ~:~ freeGS3001Law "==-Comm" gslAxSymmEqv
   ~:~ freeGS3001Law "==-Unit" gslAxIdEqv

gsTrue         =  TRUE                                           -- 3.4
gsReflEqv      =  pP === pP                                      -- 3.5

gs_conj_1
 = [( "01 TRUE" , gsTrue )
   ,( "02 ==-refl" , gsReflEqv )
   ]

\end{code}

\subsubsection{Negation, Inequivalence and False}

\begin{code}

gslAxDefFalse  =  FALSE === Not TRUE                      -- 3.8
gslAxDistrNotEqv  =  Not (pP === pQ) === (Not pP === pQ)  -- 3.9

gs_laws_2
   =   freeGS3001Law "False-def" gslAxDefFalse
   ~:~ freeGS3001Law "~-==-Distr" gslAxDistrNotEqv

gslNotEqvComm  =  (Not pP === pQ) === (pP === Not pQ)     -- 3.11
gslNotInvol  =  Not (Not pP) === pP                       -- 3.12
gslNotFalse  =  Not FALSE === TRUE                        -- 3.13
gslNotNEqvFalse  =  (Not pP === pP) === FALSE             -- 3.15
gslSymmNEqv  =  Not (pP === pQ) === Not (pQ === pP)       -- 3.16
gslAssocNEqv                                              -- 3.17
  =  Not (Not (pP === pQ) === pR) === Not (pP === Not (pQ === pR))
gslIXNEqv                                                 -- 3.18
  =  (Not (pP === pQ) === pR) === (pP === Not (pQ === pR))

gs_conj_2
 = [( "03 ~-==-Swap" , gslNotEqvComm )
   ,( "04 ~-Invol" , gslNotInvol )
   ,( "05 False-~" , gslNotFalse )
   ,( "06 =/=-Def" , gslNotNEqvFalse )
   ,( "07 ~-==~Comm" , gslSymmNEqv )
   ,( "08 ~-==-Assoc" , gslAssocNEqv )
   ,( "09 ~-==-Intchg" , gslIXNEqv )
   ]

\end{code}

\subsubsection{Disjunction}

\begin{code}

gslAxSymmOr      =  pP \/ pQ  ===  pQ \/ pP                          -- 3.24
gslAxAssocOr     =  (pP \/ pQ) \/ pR  ===  pP \/ (pQ \/ pR)          -- 3.25
gslAxIdempOr     =  (pP \/ pP)  ===  pP                              -- 3.26
gslAxDistrOrEqv  =  pP \/ (pQ === pR) === ( pP \/ pQ === pP \/ pR )  -- 3.27
gslAxExcMdl      =  pP \/ Not pP                                     -- 3.28

gs_laws_3
   =   freeGS3001Law "\\/-Comm" gslAxSymmOr
   ~:~ freeGS3001Law "\\/-Assoc" gslAxAssocOr
   ~:~ freeGS3001Law "\\/-Idem" gslAxIdempOr
   ~:~ freeGS3001Law "\\/-==-Distr" gslAxDistrOrEqv
   ~:~ freeGS3001Law "Excluded-Middle" gslAxExcMdl

gslZeroOr        =  pP \/ TRUE === TRUE                              -- 3.29
gslIdOr          =  pP \/ FALSE === pP                               -- 3.30
gslDistrOrOr     =  pP \/ (pQ \/ pR) === (pP \/ pQ) \/ (pP \/ pR)    -- 3.31
gsl_3_32         =  (pP \/ pQ === pP \/ Not pQ) === pP               -- 3.32

gs_conj_3
 = [( "10 \\/-Zero" , gslZeroOr )
   ,( "11 \\/-Unit" , gslIdOr )
   ,( "12 \\/-\\/-Distr" , gslDistrOrOr )
   ,( "13 \\/-==-Split" , gsl_3_32 )
   ]

\end{code}

\subsubsection{Conjunction}

\begin{code}

gslAxGoldenRule    =  (pP /\ pQ === pP) === (pQ === pP \/ pQ)        -- 3.35

gs_laws_4
   =   freeGS3001Law "Golden-Rule" gslAxGoldenRule

gslSymmAnd         =  pP /\ pQ  ===  pQ /\ pP                        -- 3.36
gslAssocAnd        =  (pP /\ pQ) /\ pR  ===  pP /\ (pQ /\ pR)        -- 3.37
gslIdempAnd        =  (pP /\ pP)  ===  pP                            -- 3.38
gslIdAnd           =  pP /\ TRUE === pP                              -- 3.39
gslZeroAnd         =  pP /\ FALSE === FALSE                          -- 3.40
gslDistrAndAnd     =  pP /\ (pQ /\ pR) === (pP /\ pQ) /\ (pP /\ pR)  -- 3.41
gslContra          =  pP /\ Not pP  === FALSE                        -- 3.42
gslAbsorbAndOr     =  pP /\ (pP \/ pQ) === pP                        -- 3.43(a)
gslAbsorbOrAnd     =  pP \/ (pP /\ pQ) === pP                        -- 3.43(b)
gslAbsorbAndNotOr  =  pP /\ (Not pP \/ pQ) === pP /\ pQ              -- 3.44(a)
gslAbsorbOrNotAnd  =  pP \/ (Not pP /\ pQ) === pP \/ pQ              -- 3.44(b)
gslDistrOrAnd      =  pP \/ (pQ /\ pR) === (pP \/ pQ) /\ (pP \/ pR)  -- 3.45
gslDistrAndOr      =  pP /\ (pQ \/ pR) === (pP /\ pQ) \/ (pP /\ pR)  -- 3.46
gslDeMorganNand    =  Not ( pP /\ pQ) === Not pP \/ Not pQ           -- 3.47(a)
gslDeMorganNor     =  Not ( pP \/ pQ) === Not pP /\ Not pQ           -- 3.47(b)
gsl_3_48           =  (pP /\ pQ === pP /\ Not pQ) === Not pP         -- 3.48
gsl_3_49                                                             -- 3.49
  =  pP /\ (pQ === pR) === pP /\ pQ === pP /\ pR === pP
gsl_3_50           =  pP /\ (pQ === pP) === pP /\ pQ                 -- 3.50
gslReplacement                                                       -- 3.51
  =  ((pP===pQ)/\(pR===pP)) === ((pP===pQ)/\(pR /\ pQ))
gslEqvDef                                                            -- 3.52
  =  (pP === pQ) === (pP /\ pQ) \/ (Not pP /\ Not pQ)
gslExor                                                              -- 3.53
  =  Not (pP === pQ) === (Not pP /\ pQ) \/ (pP /\ Not pQ)
gsl_3_55                                                             -- 3.55
  = (pP /\ pQ) /\ pR
    ===
    (pP === pQ === pR)
    ===
    (pP \/ pQ === pQ \/ pR === pR \/ pP)
    ===
    pP \/ pQ \/ pR

gs_conj_4
 = [( "14 /\\-Comm" , gslSymmAnd )
   ,( "15 /\\-Assoc" , gslAssocAnd )
   ,( "16 /\\-Idemp" , gslIdempAnd )
   ,( "17 /\\-Zero" , gslZeroAnd )
   ,( "18 /\\-Unit" , gslIdAnd )
   ,( "19 /\\-/\\-Distr" , gslDistrAndAnd )
   ,( "20 Contradiction" , gslContra )
   ,( "21 /\\-\\/-Absorb" , gslAbsorbAndOr )
   ,( "22 \\/-/\\-Absorb" , gslAbsorbOrAnd )
   ,( "23 /\\-~-\\/-Absorb" , gslAbsorbAndNotOr )
   ,( "24 \\/-~-/\\-Absorb" , gslAbsorbOrNotAnd )
   ,( "25 \\/-/\\-Distr" , gslDistrOrAnd )
   ,( "26 /\\-\\/-Distr" , gslDistrAndOr )
   ,( "27 DeMorgan-Nand" , gslDeMorganNand )
   ,( "28 DeMorgan-Nor" , gslDeMorganNor )
   ,( "29 GS3.48" , gsl_3_48 )
   ,( "30 GS3.49" , gsl_3_49 )
   ,( "31 GS3.50" , gsl_3_50 )
   ,( "32 Replacement" , gslReplacement )
   ,( "33 ==-def" , gslEqvDef )
   ,( "34 Exclusive-Or" , gslExor )
   ,( "35 GS3.55" , gsl_3_55 )
   ]

\end{code}

\subsubsection{Implication}

\begin{code}

gslAxDefImp   =  (pP ==> pQ) === (pP \/ pQ === pQ)             -- 3.57

gs_laws_5  =  freeGS3001Law "=>-Join" gslAxDefImp

gslDefImp2    =  (pP ==> pQ) === Not pP \/ pQ                  -- 3.59
gslDefImp3    =  (pP ==> pQ) === (pP /\ pQ === pP)             -- 3.60
gslContraPos  =  (pP ==> pQ) === (Not pQ ==> Not pP)           -- 3.61
gsl_3_62      =  pP ==> (pQ === pR) === pP /\ pQ === pP /\ pR  -- 3.62
gslDistrImpEqv                                                 -- 3.63
  =  pP ==> (pQ === pR) === pP ==> pQ === pP ==> pR
gsl_3_64                                                       -- 3.64
  =  pP ==> (pQ === pR) === (pP ==> pQ) ==> pP ==> pR
gslShunt      =  pP /\ pQ ==> pR === pP ==> (pQ ==> pR)        -- 3.65
gsl_3_66      =  pP /\ (pP ==> pQ) === pP /\ pQ                -- 3.66
gsl_3_67      =  pP /\ (pQ ==> pP) === pP                      -- 3.67
gsl_3_68      =  pP \/ (pP ==> pQ) === TRUE                    -- 3.68
gsl_3_69      =  pP \/ (pQ ==> pP) === pQ ==> pP               -- 3.69
gsl_3_70      =  pP \/ pQ ==> pP /\ pQ === pP === pQ           -- 3.70
gslReflImp    =  pP ==> pP === TRUE                            -- 3.71
gslRZeroImp   =  pP ==> TRUE === TRUE                          -- 3.72
gslLIdImp     =  TRUE ==> pP === pP                            -- 3.73
gslNotImpDef  =  pP ==> FALSE === Not pP                       -- 3.74
gslLNIdImp    =  FALSE ==> pP === TRUE                         -- 3.75
gslWknImp     =  pP ==> pP \/ pQ                               -- 3.76(a)
gslStrImp     =  pP /\ pQ ==> pP                               -- 3.76(b)
gslWknStr     =  pP /\ pQ ==> pP \/ pQ                         -- 3.76(c)
gslStr2       =  pP \/ (pQ /\ pR) ==> pP \/ pQ                 -- 3.76(d)
gslWkn2       =  pP /\ pQ ==> pP /\ (pQ \/ pR)                 -- 3.76(e)
gslMP         =  pP /\ (pP ==> pQ) ==> pQ                      -- 3.77
gsl_3_78                                                       -- 3.78
  =  (pP ==> pR) /\ (pQ ==> pR) === pP \/ pQ ==> pR
gsl_3_79      =  (pP ==> pR) /\ (Not pP ==> pR) === pR         -- 3.79
gslMtlImp     =  (pP ==> pQ) /\ (pQ ==> pP) === (pP === pQ)    -- 3.80
gslASymmImp   =  (pP ==> pQ) /\ (pQ ==> pP) ==> (pP === pQ)    -- 3.81
gslTransImp   =  (pP ==> pQ) /\ (pQ ==> pR) ==> (pP ==> pR)    -- 3.82(a)
gslTransEqvImp  =  (pP === pQ) /\ (pQ ==> pR) ==> (pP ==> pR)  -- 3.82(b)
gslTransImpEqv  =  (pP ==> pQ) /\ (pQ === pR) ==> (pP ==> pR)  -- 3.82(c)

gs_conj_5
 = [( "36 =>-Def" , gslDefImp2 )
   ,( "37 =>-Meet" , gslDefImp3 )
   ,( "38 Contrapositive", gslContraPos )
   ,( "39 GS3.62" , gsl_3_62 )
   ,( "40 =>-==-Distr" , gslDistrImpEqv )
   ,( "41 GS3.64" , gsl_3_64 )
   ,( "42 Shunting" , gslShunt )
   ,( "43 GS3.66" , gsl_3_66 )
   ,( "44 GS3.67" , gsl_3_67 )
   ,( "45 GS3.68" , gsl_3_68 )
   ,( "46 GS3.69" , gsl_3_69 )
   ,( "47 GS3.70" , gsl_3_70 )
   ,( "48 =>-Refl" , gslReflImp )
   ,( "49 =>-R-Zero" , gslRZeroImp )
   ,( "50 =>-L-Unit" , gslLIdImp )
   ,( "51 ~-Def" , gslNotImpDef )
   ,( "52 =>-L-~-Zero" , gslLNIdImp )
   ,( "53 Weaken-Cnsq" , gslWknImp )
   ,( "54 Strengthen-Ante" , gslStrImp )
   ,( "55 =>-Wkn-Str" , gslWknStr )
   ,( "56 =>-Str2" , gslStr2 )
   ,( "57 =>-Wkn2" , gslWkn2 )
   ,( "58 Modus-Ponens" , gslMP )
   ,( "59 Ante-\\/-Distr" , gsl_3_78 )
   ,( "60 Cnsq-/\\-Distr" , gsl_3_79 )
   ,( "61 Mutual-Implication" , gslMtlImp )
   ,( "62 =>-Anti-Symm" , gslASymmImp )
   ,( "63 =>-Trans" , gslTransImp )
   ,( "64 ==-=>-Trans" , gslTransEqvImp )
   ,( "65 =>-==-Trans" , gslTransImpEqv )
   ]

\end{code}

\subsection{Laws of Predicate Calculus}

\subsubsection{General Quantification}


Specialised to $\exists$ and $\forall$.

\begin{code}
gslAllEmpty   =  (rForall qxs FALSE pP) === TRUE               -- 8.13
gslAnyEmpty   =  (rExists qxs FALSE pP) === FALSE              -- 8.13

gslAllOnePt   =  (rForall qxxs (Obs (eqx `Equal` e)) pP)  -- 8.14
                  === rForall qxs TRUE (Sub pP (Substn [(vx,e)]))
gsscAllOnePt  =  x_NotFreeIn_e

gslAnyOnePt   =  (rExists qxxs (Obs (eqx `Equal` e)) pP)  -- 8.14
                  === rExists qxs TRUE (Sub pP (Substn [(vx, e)]))
gsscAnyOnePt  =  x_NotFreeIn_e

gslAllDistr                                                   -- 8.15
  =  (rForall qxs pR pP) /\ (rForall qxs pR pQ) === (rForall qxs pR (pP /\ pQ))
gslAnyDistr                                                   -- 8.15
  =  (rExists qxs pR pP) \/ (rExists qxs pR pQ) === (rExists qxs pR (pP \/ pQ))
gslAllRngSplit                                                -- 8.18
  =  (rForall qxs (pR \/ pS) pP) === (rForall qxs pR pP) /\ (rForall qxs pS pP)
gslAnyRngSplit                                                -- 8.18
  =  (rExists qxs (pR \/ pS) pP) === (rExists qxs pR pP) \/ (rExists qxs pS pP)

gslAllSwap                                                    -- 8.19
  =  (rForall qxs pR (rForall qys pQ pP))
     ===
     (rForall qys pQ (rForall qxs pR pP))
gsscAllSwap   =  scand [lstVar "y" `notPfree` nR,lstVar "x" `notPfree` nQ]

gslAnySwap                                                    -- 8.19
  =  (rExists qxs pR (rExists qys pQ pP))
     ===
     (rExists qys pQ (rExists qxs pR pP))
gsscAnySwap   =  scand [lstVar "y" `notPfree` nR,lstVar "x" `notPfree` nQ]

gslAllNest                                                    -- 8.20
  =  (rForall (Q [lstVar "x",lstVar "y"]) (pR /\ pQ) pP)
     ===
     (rForall (Q[lstVar "x"]) pR (rForall (Q [lstVar "y"]) pQ pP))
gsscAllNest   =  lstVar "y" `notPfree` nR

gslAnyNest                                                    -- 8.20
  =  (rExists (Q [lstVar "x",lstVar "y"]) (pR /\ pQ) pP)
     ===
     (rExists (Q [lstVar "x"]) pR (rExists (Q [lstVar "y"]) pQ pP))
gsscAnyNest   =  lstVar "y" `notPfree` nR

-- we note that 8.21, dummy renaming, is built-in

gs_laws_6
  =     freeGS3001Law "rForall-Empty" gslAllEmpty
    ~:~ freeGS3001Law "rExists-Empty" gslAllEmpty
    ~:~ mkGS3001Law "rForall-1Pt" gslAllOnePt gsscAllOnePt
    ~:~ mkGS3001Law "rExists-1Pt" gslAnyOnePt gsscAnyOnePt
    ~:~ freeGS3001Law "rForall-Distr" gslAllDistr
    ~:~ freeGS3001Law "rExists-Distr" gslAnyDistr
    ~:~ freeGS3001Law "rForall-Rng-Split" gslAllRngSplit
    ~:~ freeGS3001Law "rExists-Rng-Split" gslAnyRngSplit
    ~:~ mkGS3001Law "rForall-Swap" gslAllSwap gsscAllSwap
    ~:~ mkGS3001Law "rExists-Swap" gslAnySwap gsscAnySwap
    ~:~ mkGS3001Law "rForall-Nest" gslAllNest gsscAllNest
    ~:~ mkGS3001Law "rExists-Nest" gslAnyNest gsscAnyNest

tv = Tvar "T"

gslAllSplitOff                                              -- 8.23
  =  (TypeOf e tv) ==>
     ( (rForall qx (TypeOf (Var vx) tv) pP)
        === (rForall qx (TypeOf (Var vx) tv) pP) /\ (Sub pP (Substn [(vx,e)])) )
gslAnySplitOff                                              -- 8.23
  =  (TypeOf e tv) ==>
     ( (rExists qx (TypeOf (Var vx) tv) pP)
        === (rExists qx (TypeOf (Var vx) tv) pP) \/ (Sub pP (Substn [(vx,e)])))

gs_conj_6
  =  [( "66 rForall-SplitOff" , gslAllSplitOff )
     ,( "67 rExists-SplitOff" , gslAnySplitOff )
     ]

\end{code}



\subsubsection{Universal Quantification}

\begin{code}

gslAllTrading                                                        -- 9.2
  =  (rForall qxs pR pP) === (rForall qxs TRUE (pR ==> pP) )

gslDistrOrAll                                                        -- 9.5
  =  pP \/ (rForall qxs pR pQ) === (rForall qxs pR (pP \/ pQ))
gsscDistrOrAll  = lstVar "x" `notPfree` nP

gs_laws_7
  =  freeGS3001Law "rForall-Trading" gslAllTrading
    ~:~ mkGS3001Law "\\/-rForall-Distr" gslDistrOrAll gsscDistrOrAll

gslAllTrading2                                                       -- 9.4
  =  (rForall qxs (pQ /\ pR) pP) === (rForall qxs pQ (pR ==> pP) )

gsl_9_6 = (rForall qxs pR pP) === pP \/ (rForall qxs TRUE (Not pR))    -- 9.6
gssc_9_6 = lstVar "x" `notPfree` nP

gslDistrAndAll                                                       -- 9.7
  =  Not(rForall qxs TRUE (Not pR))
      ==> (pP /\ (rForall qxs pR pQ) === (rForall qxs pR (pP /\ pQ)))
gsscDistrAndAll  = lstVar "x" `notPfree` nP

gslAllTrue = (rForall qxs pR TRUE) === TRUE                           -- 9.8
gslDistrEqvAll                                                       -- 9.9
  = (rForall qxs pR (pP === pQ))
    ==> ((rForall qxs pR pP) === (rForall qxs pR pQ))
gslAllRangeStr  = (rForall qxs (pQ \/ pR) pP) ==> (rForall qxs pQ pP)  -- 9.10
gslAllBodyWkn  = (rForall qxs pR (pQ /\ pP)) ==> (rForall qxs pR pP)   -- 9.11
gslAllMono                                                           -- 9.12
  =  (rForall qxs pR (pQ ==> pP))
      ==> ((rForall qxs pR pQ) ==> (rForall qxs pR pP))
gslAllElim                                                           -- 9.13
  =  (rForall qxxs TRUE pP) ==> (rForall qxs TRUE (Sub pP (Substn [(vx,e)])))

gs_conj_7
 =  [( "68 rForall-Trading2" , (gslAllTrading2,SCtrue) )
    ,( "69 GS9.6" , (gsl_9_6,gssc_9_6) )
    ,( "70 /\\-rForall-Distr" , (gslDistrAndAll,gsscDistrAndAll) )
    ,( "71 rForall-TRUE" , (gslAllTrue,SCtrue) )
    ,( "72 ==-rForall-Distr" , (gslDistrEqvAll,SCtrue) )
    ,( "73 rForall-Range-Strngthn" , (gslAllRangeStr,SCtrue) )
    ,( "74 rForall-Body-Wkn" , (gslAllBodyWkn,SCtrue) )
    ,( "75 rForall-Monotonic" , (gslAllMono,SCtrue) )
    ,( "76 rForall-Instantiation" , (gslAllElim,SCtrue) )
    ]

\end{code}

\subsubsection{Existential Quantification}

\begin{code}

gslAnyDef  = (rExists qxs pR pP) === Not (rForall qxs pR (Not pP))     -- 9.17

gs_laws_8  =  freeGS3001Law "rExists-Def" gslAnyDef

gslGenDeMorgan1                                                      -- 9.18a
  =  Not(rExists qxs pR (Not pP)) === (rForall qxs pR pP)
gslGenDeMorgan2                                                      -- 9.18b
  =  Not(rExists qxs pR pP) === (rForall qxs pR (Not pP))
gslGenDeMorgan3                                                      -- 9.18c
  =  (rExists qxs pR (Not pP)) === Not (rForall qxs pR pP)
gslAnyTrading                                                        -- 9.19
  =  (rExists qxs pR pP) === (rForall qxs TRUE (pR /\ pP) )
gslAnyTrading2                                                       -- 9.20
 =  (rExists qxs (pQ /\pR) pP) === (rForall qxs pQ (pR /\ pP) )

gslDistrAndAny                                                       -- 9.21
  =  pP /\ (rExists qxs pR pQ) === (rExists qxs pR (pP /\ pQ))
gsscDistrAndAny  = lstVar "x" `notPfree` nP

gsl_9_22 = (rExists qxs pR pP) === pP /\ (rExists qxs TRUE pR)         -- 9.22
gssc_9_22 = lstVar "x" `notPfree` nP

gslDistrOrAny                                                        -- 9.23
  =  (rExists qxs TRUE pR)
      ==> (pP \/ (rExists qxs pR pQ) === (rExists qxs pR (pP \/ pQ)))
gsscDistrOrAny  = lstVar "x" `notPfree` nP

gslAnyFalse = (rExists qxs pR FALSE) === FALSE                        -- 9.24
gslAnyRangeWkn  = (rExists qxs pR pP) ==> (rExists qxs (pQ \/ pR) pP)  -- 9.25
gslAnyBodyWkn  = (rExists qxs pR pP) ==>  (rExists qxs pR (pQ \/ pP))  -- 9.26
gslAnyMono                                                           -- 9.27
  =  (rForall qxs pR (pQ ==> pP))
      ==> ((rExists qxs pR pQ) ==> (rExists qxs pR pP))
gslAnyIntro                                                          -- 9.28
  =  (rExists qxs TRUE (Sub pP (Substn [(vx,e)]))) ==> (rExists qxxs TRUE pP)

gslIntchgQuant                                                       -- 9.29
  =  (rExists qxs pR (rForall qys pQ pP))
      ==> (rForall qys pQ (rExists qxs pR pP))
gsscIntchgQuant = scand[lstVar "x" `notPfree` nQ,lstVar "y" `notPfree` nR]

gs_conj_8
  =  [( "77 Gen-DeMorgan-1" , (gslGenDeMorgan1,SCtrue) )
     ,( "78 Gen-DeMorgan-2" , (gslGenDeMorgan2,SCtrue) )
     ,( "79 Gen-DeMorgan-3" , (gslGenDeMorgan3,SCtrue) )
     ,( "80 rExists-Trading" , (gslAnyTrading,SCtrue) )
     ,( "81 rExists-Trading-2" , (gslAnyTrading2,SCtrue) )
     ,( "82 /\\-rExists-Distr" , (gslDistrAndAny,gsscDistrAndAny) )
     ,( "83 GS9.22" , (gsl_9_22,gssc_9_22) )
     ,( "84 \\/-rExists-Distr" , (gslDistrOrAny,gsscDistrOrAny) )
     ,( "85 rExists-FALSE" , (gslAnyFalse,SCtrue) )
    ,( "86 rExists-Range-Wkn" , (gslAnyRangeWkn,SCtrue) )
    ,( "87 rExists-Body-Wkn" , (gslAnyBodyWkn,SCtrue) )
    ,( "88 rExists-Monotonic" , (gslAnyMono,SCtrue) )
    ,( "89 rExists-Introduction" , (gslAnyIntro,SCtrue) )
    ,( "90 Quant-Interchange" , (gslIntchgQuant,gsscIntchgQuant) )
     ]

\end{code}

\subsection{Non-GS Laws}

The following notions are not defined in GS,
but we include them for completeness.

\subsubsection{Unique Quantification}

\begin{code}
gslUniqueExistsDef
  =  (rExists1 qx pR pP)
      ===
      (rExists qx pR pP)
      /\ ( rForall qxy (pR /\ (Sub pR yForx))
                      (pP /\ (Sub pP yForx) ==> x `equal` y) )
  where
   vx = preVar "x"
   vy = preVar "y"
   qxy = Q [vx,vy]
   x = Var vx
   y = Var vy
   yForx = Substn [(vx,y)]
   e1 `equal` e2 = Obs (Equal e1 e2)

gs_laws_9  =  freeGS3001Law "rExists1-Def" gslUniqueExistsDef

gs_conj_9  =  []
\end{code}

\subsubsection{Universal Closure}

\begin{code}

gslUnivDef = Univ 0 pP === rForall qxs TRUE pP
gsscUnivDef = [lstVar "x"] `coverFreeOfP` nP

gs_laws_10  =  mkGS3001Law "Univ-Def" gslUnivDef gsscUnivDef

gs_conj_10  =  []

\end{code}


\subsection{And the Law is \ldots}

\begin{code}

gsLogicLawTable
  =     gs_laws_1
    ~:~ gs_laws_2
    ~:~ gs_laws_3
    ~:~ gs_laws_4
    ~:~ gs_laws_5
    ~:~ gs_laws_6
    ~:~ gs_laws_7
    ~:~ gs_laws_8
    ~:~ gs_laws_9
    ~:~ gs_laws_10

gsConjTable = lbuild (  wrapTrueSC gs_conj_1
                     ++ wrapTrueSC gs_conj_2
                     ++ wrapTrueSC gs_conj_3
                     ++ wrapTrueSC gs_conj_4
                     ++ wrapTrueSC gs_conj_5
                     ++ wrapTrueSC gs_conj_6
                     ++ gs_conj_7
                     ++ gs_conj_8
                     ++ gs_conj_9
                     ++ gs_conj_10
                     )

wrapTrueSC = map wrap
 where wrap (name,pred) = (name,(pred,SCtrue))

gs3001ProofContext
  = markTheoryDeps ((nmdNullPrfCtxt "GS3001")
                      { syntaxDeps = [ rootName ]
                      , types = boolOpTypes
                      , laws = gsLogicLawTable
                      , conjectures = gsConjTable
                      })

gsConjAsLawTable
 = map (wrapProv gs3001Provenance)
       ( wrapTrueSC gs_conj_1
        ++ wrapTrueSC gs_conj_2
        ++ wrapTrueSC gs_conj_3
        ++ wrapTrueSC gs_conj_4
        ++ wrapTrueSC gs_conj_5
        ++ wrapTrueSC gs_conj_6
        ++ gs_conj_7
        ++ gs_conj_8
        ++ gs_conj_9
        ++ gs_conj_10 )


gsFullProofContext
  = markTheoryDeps ((nmdNullPrfCtxt "GSFull")
                      { syntaxDeps = [ rootName ]
                      , types = boolOpTypes
                      , laws = gsLogicLawTable ++ gsConjAsLawTable
                      , conjectures = gsConjTable
                      })

\end{code}
