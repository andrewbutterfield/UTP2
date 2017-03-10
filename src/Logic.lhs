\section{Laws of Logic}

Laws of 2nd order  logic

\begin{code}
module Logic where
import Tables
import Datatypes
import DataText
import Heuristics
import Laws
import Proof
import Theories
import DSL
import RootTheory
import Data.List

import Text.ParserCombinators.Parsec.Expr
\end{code}



\subsection{Useful definitions}

\begin{code}
logicProvenance = FromSOURCE "Logic"
mkLogicLaw = mklaw logicProvenance
freeLogicLaw = freelaw logicProvenance
mkConj nm pr sc = (nm,(pr,sc))
freeConj nm pr = mkConj nm pr SCtrue
\end{code}


\subsection{The Laws}

The parenthesised numbers in inline comments after law definitions
give the the equation number from
``Laws of the Logical Calculi''
by Carroll Morgan and J. W. Sanders,
PRG-78,
September 1989,
Oxford University Computing Laboratory.

\subsubsection{A distributive lattice (2.1)}

\begin{code}
lAndIdem  =  pA /\ pA === pA  -- (1)
lOrIdem   =  pA \/ pA === pA  -- (1)
lAndComm  =  pA /\ pB === pB /\ pA  -- (2)
lOrComm   =  pA \/ pB === pB \/ pA  -- (3)

lAndAssoc = mkEqv (mkAnd [pA,mkAnd[pB,pC]]) (mkAnd [mkAnd [pA,pB],pC])  -- (4)
lOrAssoc = mkEqv (mkOr [pA,mkOr[pB,pC]]) (mkOr [mkOr [pA,pB],pC])  -- (5)

lAndOrAbsR1 = mkEqv (mkAnd [pA,mkOr [pA,pB]]) pA  -- (6)
lAndOrAbsR2 = mkEqv (mkAnd [pA,mkOr [pB,pA]]) pA  -- (6)
lAndOrAbsR3 = mkEqv (mkAnd [mkOr [pA,pB],pA]) pA  -- (6)
lAndOrAbsR4 = mkEqv (mkAnd [mkOr [pB,pA],pA]) pA  -- (6)

lOrAndAbsR1 = mkEqv (mkOr [pA,mkAnd [pA,pB]]) pA -- (6)
lOrAndAbsR2 = mkEqv (mkOr [pA,mkAnd [pB,pA]]) pA -- (6)
lOrAndAbsR3 = mkEqv (mkOr [mkAnd [pA,pB],pA]) pA -- (6)
lOrAndAbsR4 = mkEqv (mkOr [mkAnd [pB,pA],pA]) pA -- (6)

lAndOrDistr1 = mkEqv (mkAnd [pA,mkOr [pB,pC]]) --(7)
                   (mkOr [mkAnd [pA,pB],mkAnd [pA,pC]])
lAndOrDistr2 = mkEqv (mkAnd [mkOr [pB,pC],pA]) --(7)
                   (mkOr [mkAnd [pB,pA],mkAnd [pC,pA]])

lOrAndDistr1 = mkEqv (mkOr [pA,mkAnd [pB,pC]])  -- (8)
                   (mkAnd [mkOr [pA,pB],mkOr [pA,pC]])
lOrAndDistr2 = mkEqv (mkOr [mkAnd [pB,pC],pA])  -- (8)
                   (mkAnd [mkOr [pB,pA],mkOr [pC,pA]])


laws_2_1
   =   freeLogicLaw "/\\-idem" lAndIdem
   ~:~ freeLogicLaw "/\\-comm" lAndComm
   ~:~ freeLogicLaw "/\\-assoc" lAndAssoc
   ~:~ freeLogicLaw "\\/-idem" lOrIdem
   ~:~ freeLogicLaw "\\/-comm" lOrComm
   ~:~ freeLogicLaw "\\/-assoc" lOrAssoc
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.1" lAndOrAbsR1
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.2" lAndOrAbsR2
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.3" lAndOrAbsR3
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.4" lAndOrAbsR4
   ~:~ freeLogicLaw "/\\-\\/-distr.1" lAndOrDistr1
   ~:~ freeLogicLaw "/\\-\\/-distr.1" lAndOrDistr2
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.1" lOrAndAbsR1
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.2" lOrAndAbsR2
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.3" lOrAndAbsR3
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.4" lOrAndAbsR4
   ~:~ freeLogicLaw "\\/-/\\-distr.1" lOrAndDistr1
   ~:~ freeLogicLaw "\\/-/\\-distr.2" lOrAndDistr2

conj_2_1
   = freeConj "/\\-idem" lAndIdem
   : freeConj "/\\-comm" lAndComm
   : freeConj "/\\-assoc" lAndAssoc
   : freeConj "\\/-idem" lOrIdem
   : freeConj "\\/-comm" lOrComm
   : freeConj "\\/-assoc" lOrAssoc
   : freeConj "/\\-\\/-absorb" lAndOrAbsR1
   : freeConj "/\\-\\/-distr" lAndOrDistr1
   : freeConj "\\/-/\\-absorb" lOrAndAbsR1
   : freeConj "\\/-/\\-distr" lOrAndDistr1
   : []

test_2_1 = [ ( "[/\\-idem]", (mkUniv lAndIdem,SCtrue))
           , ( "alphaTest1", (alphaTest1,SCtrue))
           , ( "alphaTest2", (alphaTest2,SCtrue))
           , ( "typeTest1",  (typeTest1,SCtrue))
           ] -- for testing
\end{code}

\subsubsection{A Boolean algebra (2.2)}

\begin{code}
lAndUnit1 = mkEqv (mkAnd [pA,TRUE]) pA  -- (9)
lAndUnit2 = mkEqv (mkAnd [TRUE,pA]) pA  -- (9)
lOrZero1  = mkEqv (mkOr [pA,TRUE]) TRUE  -- (10)
lOrZero2  = mkEqv (mkOr [TRUE,pA]) TRUE  -- (10)
lAndZero1 = mkEqv (mkAnd [pA,FALSE]) FALSE  -- (11)
lAndZero2 = mkEqv (mkAnd [FALSE,pA]) FALSE  -- (11)
lOrUnit1  = mkEqv (mkOr [pA,FALSE]) pA  -- (12)
lOrUnit2  = mkEqv (mkOr [FALSE,pA]) pA  -- (12)

lContradiction1 = mkEqv (mkAnd [pA,mkNot pA]) FALSE  -- (13)
lContradiction2 = mkEqv (mkAnd [mkNot pA,pA]) FALSE  -- (13)
lNoMiddle1      = mkEqv (mkOr [pA,mkNot pA]) TRUE  -- (14)
lNoMiddle2      = mkEqv (mkOr [mkNot pA,pA]) TRUE  -- (14)

lNotNot  = mkEqv (mkNot (mkNot pA)) pA  -- (15)
lAndDeMorgan = mkEqv (mkAnd [mkNot pA,mkNot pB]) (mkNot (mkOr [pA,pB]))  -- (16)
lOrDeMorgan = mkEqv (mkOr [mkNot pA,mkNot pB]) (mkNot (mkAnd [pA,pB]))  -- (17)

lOrAndNotAbs1 = mkEqv (mkOr [pA,mkAnd [mkNot pA,pB]]) (mkOr [pA,pB])  -- (18)
lOrAndNotAbs2 = mkEqv (mkOr [mkAnd [mkNot pA,pB],pA]) (mkOr [pA,pB])  -- (18)
lAndOrNotAbs1 = mkEqv (mkAnd [pA,mkOr [mkNot pA,pB]]) (mkAnd [pA,pB])  -- (19)
lAndOrNotAbs2 = mkEqv (mkAnd [mkOr [mkNot pA,pB],pA]) (mkAnd [pA,pB])  -- (19)

laws_2_2
   =   freeLogicLaw "/\\-unit.1" lAndUnit1
   ~:~ freeLogicLaw "/\\-unit.2" lAndUnit2
   ~:~ freeLogicLaw "/\\-zero.1" lAndZero1
   ~:~ freeLogicLaw "/\\-zero.2" lAndZero2
   ~:~ freeLogicLaw "\\/-unit.1" lOrUnit1
   ~:~ freeLogicLaw "\\/-unit.2" lOrUnit2
   ~:~ freeLogicLaw "\\/-zero.1" lOrZero1
   ~:~ freeLogicLaw "\\/-zero.2" lOrZero2
   ~:~ freeLogicLaw "contradiction.1" lContradiction1
   ~:~ freeLogicLaw "contradiction.2" lContradiction2
   ~:~ freeLogicLaw "excluded-middle.1" lNoMiddle1
   ~:~ freeLogicLaw "excluded-middle.2" lNoMiddle2
   ~:~ freeLogicLaw "~~-idem" lNotNot
   ~:~ freeLogicLaw "/\\-deMorgan" lAndDeMorgan
   ~:~ freeLogicLaw "\\/-deMorgan" lOrDeMorgan
   ~:~ freeLogicLaw "\\/-/\\-~-absorb.1" lOrAndNotAbs1
   ~:~ freeLogicLaw "\\/-/\\-~-absorb.2" lOrAndNotAbs2
   ~:~ freeLogicLaw "/\\-\\/-~-absorb.3" lAndOrNotAbs1
   ~:~ freeLogicLaw "/\\-\\/-~-absorb.4" lAndOrNotAbs2
   ~:~ freeLogicLaw "false" (FALSE === mkNot TRUE)
   ~:~ freeLogicLaw "true" (TRUE === mkNot FALSE)

conj_2_2
   = freeConj "/\\-unit" lAndUnit1
   : freeConj "/\\-zero" lAndZero1
   : freeConj "\\/-unit" lOrUnit1
   : freeConj "\\/-zero" lOrZero1
   : freeConj "contradiction" lContradiction1
   : freeConj "excluded-middle" lNoMiddle1
   : freeConj "~~-idem" lNotNot
   : freeConj "/\\-deMorgan" lAndDeMorgan
   : freeConj "\\/-deMorgan" lOrDeMorgan
   : freeConj "\\/-/\\-~-absorb" lOrAndNotAbs1
   : freeConj "false" (FALSE === mkNot TRUE)
   : freeConj "true" (TRUE === mkNot FALSE)
   : []
\end{code}

\subsubsection{Implication (2.3)}

\begin{code}
lImpDef1 = mkEqv (mkImp pA pB) (mkOr [mkNot pA,pB])  -- (20)
lImpDef2 = mkEqv (mkImp pA pB) (mkOr [pB,mkNot pA])  -- (20)
lImpSelf = mkEqv (mkImp pA pA) TRUE  -- (21)
lImpAlt11 = mkEqv (mkImp pA pB) (mkNot (mkAnd [pA,mkNot pB]))  -- (22)
lImpAlt12 = mkEqv (mkImp pA pB) (mkNot (mkAnd [mkNot pB,pA]))  -- (22)
lNotImp1 = mkEqv (mkNot (mkImp pA pB)) (mkAnd [pA,mkNot pB])  -- (23)
lNotImp2 = mkEqv (mkNot (mkImp pA pB)) (mkAnd [mkNot pB,pA])  -- (23)
lContrapos = mkEqv (mkImp pA pB) (mkImp (mkNot pB) (mkNot pA))  -- (24)

lImpTrue = mkEqv (mkImp pA TRUE) TRUE  -- (25)
lTrueImp = mkEqv (mkImp TRUE pA) pA  -- (26)
lImpFalse = mkEqv (mkImp pA FALSE) (mkNot pA)  -- (27)
lFalseImp = mkEqv (mkImp FALSE pA) TRUE  -- (28)
lImpNeg = mkEqv (mkImp pA (mkNot pA)) (mkNot pA)  -- (29)
lNegImp = mkEqv (mkImp (mkNot pA) pA) pA  -- (30)

lImpAndDistr = mkEqv (mkImp pC (mkAnd [pA,pB])) (mkAnd [mkImp pC pA,mkImp pC pB])  -- (31)
lOrImpDistr = mkEqv (mkImp (mkOr [pA,pB]) pC) (mkAnd [mkImp pA pC,mkImp pB pC])  -- (32)

lBoolMeet1 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv (mkAnd [pA,pB]) pA)
lBoolMeet2 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv (mkAnd [pA,pB]) pA)
lBoolMeet3 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv (mkAnd [pB,pA]) pA)
lBoolMeet4 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv (mkAnd [pB,pA]) pA)
lBoolMeet5 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv pA (mkAnd [pA,pB]))
lBoolMeet6 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv pA (mkAnd [pA,pB]))
lBoolMeet7 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv pA (mkAnd [pB,pA]))
lBoolMeet8 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv pA (mkAnd [pB,pA]))

lBoolJoin1 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv (mkOr [pA,pB]) pB)
lBoolJoin2 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv (mkOr [pA,pB]) pB)
lBoolJoin3 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv (mkOr [pB,pA]) pB)
lBoolJoin4 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv (mkOr [pB,pA]) pB)
lBoolJoin5 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv pB (mkOr [pA,pB]))
lBoolJoin6 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv pB (mkOr [pA,pB]))
lBoolJoin7 = mkEqv (mkOr [mkNot pA,pB])  -- (33)
                 (mkEqv pB (mkOr [pB,pA]))
lBoolJoin8 = mkEqv (mkOr [pB,mkNot pA])  -- (33)
                 (mkEqv pB (mkOr [pB,pA]))

lImpMrg1 = mkEqv (mkImp pA (mkImp pB pC)) (mkImp (mkAnd [pA,pB]) pC)  -- (34)
lImpMrg2 = mkEqv (mkImp pA (mkImp pB pC)) (mkImp pB (mkImp pA pC))  -- (35)

lImpCases1 = mkEqv (mkAnd [mkImp pA pB,mkImp (mkNot pA) pC])  -- (36)
                 (mkOr [mkAnd [pA,pB],mkAnd[mkNot pA,pC]])
lImpCases2 = mkEqv (mkAnd [mkImp (mkNot pA) pC,mkImp pA pB])  -- (36)
                 (mkOr [mkAnd [pA,pB],mkAnd[mkNot pA,pC]])
lImpCases3 = mkEqv (mkAnd [mkImp pA pB,mkImp (mkNot pA) pC])  -- (36)
                 (mkOr [mkAnd[mkNot pA,pC],mkAnd [pA,pB]])
lImpCases4 = mkEqv (mkAnd [mkImp (mkNot pA) pC,mkImp pA pB])  -- (36)
                 (mkOr [mkAnd[mkNot pA,pC],mkAnd [pA,pB]])

laws_2_3
   =   freeLogicLaw "DEF-=>.1" lImpDef1
   ~:~ freeLogicLaw "DEF-=>.2" lImpDef2
   ~:~ freeLogicLaw "=>-self" lImpSelf
   ~:~ freeLogicLaw "=>-alt1" lImpAlt11
   ~:~ freeLogicLaw "=>-alt2" lImpAlt12
   ~:~ freeLogicLaw "=>-neg.1" lNotImp1
   ~:~ freeLogicLaw "=>-neg.2" lNotImp2
   ~:~ freeLogicLaw "contrapositive" lContrapos
   ~:~ freeLogicLaw "=>-true" lImpTrue
   ~:~ freeLogicLaw "true-=>" lTrueImp
   ~:~ freeLogicLaw "=>-false" lImpFalse
   ~:~ freeLogicLaw "false-=>" lFalseImp
   ~:~ freeLogicLaw "=>-neg" lImpNeg
   ~:~ freeLogicLaw "neg-=>" lNegImp
   ~:~ freeLogicLaw "=>-/\\-distr" lImpAndDistr
   ~:~ freeLogicLaw "\\/-=>-distr" lOrImpDistr
   ~:~ freeLogicLaw "bool-meet.1" lBoolMeet1
   ~:~ freeLogicLaw "bool-meet.2" lBoolMeet2
   ~:~ freeLogicLaw "bool-meet.3" lBoolMeet3
   ~:~ freeLogicLaw "bool-meet.4" lBoolMeet4
   ~:~ freeLogicLaw "bool-meet.5" lBoolMeet5
   ~:~ freeLogicLaw "bool-meet.6" lBoolMeet6
   ~:~ freeLogicLaw "bool-meet.7" lBoolMeet7
   ~:~ freeLogicLaw "bool-meet.8" lBoolMeet8
   ~:~ freeLogicLaw "bool-join.1" lBoolJoin1
   ~:~ freeLogicLaw "bool-join.2" lBoolJoin2
   ~:~ freeLogicLaw "bool-join.3" lBoolJoin3
   ~:~ freeLogicLaw "bool-join.4" lBoolJoin4
   ~:~ freeLogicLaw "bool-join.5" lBoolJoin5
   ~:~ freeLogicLaw "bool-join.6" lBoolJoin6
   ~:~ freeLogicLaw "bool-join.7" lBoolJoin7
   ~:~ freeLogicLaw "bool-join.8" lBoolJoin8
   ~:~ freeLogicLaw "=>-merge.1" lImpMrg1
   ~:~ freeLogicLaw "=>-merge.2" lImpMrg2
   ~:~ freeLogicLaw "=>-cases.1" lImpCases1
   ~:~ freeLogicLaw "=>-cases.2" lImpCases2
   ~:~ freeLogicLaw "=>-cases.3" lImpCases3
   ~:~ freeLogicLaw "=>-cases.4" lImpCases4

conj_2_3
   = freeConj "DEF-=>" lImpDef1
   : freeConj "=>-self" lImpSelf
   : freeConj "=>-alt" lImpAlt11
   : freeConj "=>-neg" lNotImp1
   : freeConj "contrapositive" lContrapos
   : freeConj "=>-true" lImpTrue
   : freeConj "true-=>" lTrueImp
   : freeConj "=>-false" lImpFalse
   : freeConj "false-=>" lFalseImp
   : freeConj "=>-neg" lImpNeg
   : freeConj "neg-=>" lNegImp
   : freeConj "=>-/\\-distr" lImpAndDistr
   : freeConj "\\/-=>-distr" lOrImpDistr
   : freeConj "bool-meet" lBoolMeet1
   : freeConj "bool-join" lBoolJoin1
   : freeConj "=>-merge" lImpMrg1
   : freeConj "=>-cases" lImpCases1
   : []
\end{code}

\subsubsection{Other connectives (2.4)}

\begin{code}
lEqvDef  =  mkEqv (mkEqv pA pB) (mkAnd [mkImp pA pB, mkImp pB pA])  -- (37)
lEqvAlt11 =  mkEqv (mkEqv pA pB) (mkOr [mkAnd [pA,pB], mkNot (mkOr [pA,pB])])  -- (38)
lEqvAlt12 =  mkEqv (mkEqv pA pB) (mkOr [mkAnd [pB,pA], mkNot (mkOr [pA,pB])])  -- (38)
lEqvAlt2 =  mkEqv (mkEqv pA pB) (mkEqv (mkNot pA) (mkNot pB))  -- (39)

lEqvSame   =  mkEqv (mkEqv pA pA) TRUE  -- (40)
lEqvDiff1   =  mkEqv (mkEqv pA (mkNot pA)) FALSE  -- (41)
lEqvDiff2   =  mkEqv (mkEqv (mkNot pA) pA) FALSE  -- (41)
lEqvTrue   =  mkEqv (mkEqv pA TRUE) pA  -- (42)
lEqvFalse  =  mkEqv (mkEqv pA FALSE) (mkNot pA)  -- (43)
lImpAlt21   =  mkEqv (mkImp pA pB) (mkEqv pA (mkAnd [pA,pB]))  -- (44)
lImpAlt22   =  mkEqv (mkImp pA pB) (mkEqv pA (mkAnd [pB,pA]))  -- (44)
lImpAlt23   =  mkEqv (mkImp pA pB) (mkEqv (mkAnd [pA,pB]) pA)  -- (44)
lImpAlt24   =  mkEqv (mkImp pA pB) (mkEqv (mkAnd [pB,pA]) pA)  -- (44)
lImpAlt31   =  mkEqv (mkImp pB pA) (mkEqv pA (mkOr [pA,pB]))  -- (45)
lImpAlt32   =  mkEqv (mkImp pB pA) (mkEqv pA (mkOr [pB,pA]))  -- (45)
lImpAlt33   =  mkEqv (mkImp pB pA) (mkEqv (mkOr [pA,pB]) pA)  -- (45)
lImpAlt34   =  mkEqv (mkImp pB pA) (mkEqv (mkOr [pB,pA]) pA)  -- (45)
lOrEqvDistr1  =  mkEqv (mkOr [pA,mkEqv pB pC])  -- (46)
                     (mkEqv (mkOr [pA,pB]) (mkOr [pA,pC]))
lOrEqvDistr2  =  mkEqv (mkOr [mkEqv pB pC,pA])  -- (46)
                     (mkEqv (mkOr [pA,pB]) (mkOr [pA,pC]))
lOrEqvDistr3  =  mkEqv (mkOr [pA,mkEqv pB pC])  -- (46)
                     (mkEqv (mkOr [pB,pA]) (mkOr [pC,pA]))
lOrEqvDistr4  =  mkEqv (mkOr [mkEqv pB pC,pA])  -- (46)
                     (mkEqv (mkOr [pB,pA]) (mkOr [pC,pA]))

lEqvComm  = mkEqv (mkEqv pA pB) (mkEqv pB pA)  -- (47)
lEqvAssoc = mkEqv (mkEqv pA (mkEqv pB pC)) (mkEqv (mkEqv pA pB) pC)  -- (48)

-- The "Golden Rule"

goldenRule1 = mkEqv (mkEqv pA pB)  -- (49)
                  (mkEqv (mkAnd [pA,pB]) (mkOr [pA,pB]))
goldenRule2 = mkEqv (mkEqv pA pB)  -- (49)
                  (mkEqv (mkAnd [pB,pA]) (mkOr [pA,pB]))
goldenRule3 = mkEqv (mkEqv pA pB)  -- (49)
                  (mkEqv (mkOr [pA,pB]) (mkAnd [pA,pB]))
goldenRule4 = mkEqv (mkEqv pA pB)  -- (49)
                  (mkEqv (mkOr [pA,pB]) (mkAnd [pB,pA]))
goldenRule5 = mkEqv (mkEqv pB pA)  -- (49)
                  (mkEqv (mkAnd [pA,pB]) (mkOr [pA,pB]))
goldenRule6 = mkEqv (mkEqv pB pA)  -- (49)
                  (mkEqv (mkAnd [pB,pA]) (mkOr [pA,pB]))
goldenRule7 = mkEqv (mkEqv pB pA)  -- (49)
                  (mkEqv (mkOr [pA,pB]) (mkAnd [pA,pB]))
goldenRule8 = mkEqv (mkEqv pB pA)  -- (49)
                  (mkEqv (mkOr [pA,pB]) (mkAnd [pB,pA]))

-- laws 50 through 59 regarding Exclusive-mkOr are not given here.

lCondDef1  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [pC,pA], mkAnd [mkNot pC,pB]])
lCondDef2 =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [pA,pC], mkAnd [mkNot pC,pB]])
lCondDef3  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [pC,pA], mkAnd [pB,mkNot pC]])
lCondDef4  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [pA,pC], mkAnd [pB,mkNot pC]])
lCondDef5  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [mkNot pC,pB], mkAnd [pC,pA]])
lCondDef6  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [mkNot pC,pB], mkAnd [pA,pC]])
lCondDef7  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [pB,mkNot pC], mkAnd [pC,pA]])
lCondDef8  =  mkEqv (mkIf pC pA pB) (mkOr [mkAnd [pB,mkNot pC], mkAnd [pA,pC]])

lCondAlt1  =  mkEqv (mkIf pC pA pB) (mkAnd [mkImp pC pA, mkImp (mkNot pC) pB])  -- (60)
lCondAlt2  =  mkEqv (mkIf pC pA pB) (mkAnd [mkImp (mkNot pC) pB, mkImp pC pA])  -- (60)

lCondIdem  =  mkEqv  (mkIf pP pA pA) pA  -- (61)
lCondLeftAbs =    mkEqv (mkIf pP pA (mkIf pP pB pC)) (mkIf pP pA pC)  -- (62)
lCondRighttAbs =  mkEqv (mkIf pP (mkIf pP pA pB) pC) (mkIf pP pA pC)  -- (63)
lCondRightDistr  -- (64)
  = mkEqv (mkIf pP pA (mkIf pQ pB pC))
        (mkIf pQ (mkIf pP pA pB) (mkIf pP pA pC))
lCondLeftDistr  -- (65)
  = mkEqv (mkIf pQ (mkIf pP pA pB) pC)
        (mkIf pP (mkIf pQ pA pC) (mkIf pQ pB pC))

lCondTrue = mkEqv  (mkIf TRUE pA pB) pA  -- (66)
lCondFalse = mkEqv (mkIf FALSE pA pB) pB  -- (67)

lAndAsCond1 = mkEqv (mkAnd [pA,pB]) (mkIf pB pA pB)  -- (68)
lAndAsCond2 = mkEqv (mkAnd [pB,pA]) (mkIf pB pA pB)  -- (68)

lOrAsCond1 = mkEqv (mkOr [pA,pB]) (mkIf pA pA pB)  -- (69)
lOrAsCond2 = mkEqv (mkOr [pB,pA]) (mkIf pA pA pB)  -- (69)

lNotAsCond = mkEqv (mkNot pA) (mkIf pA FALSE TRUE)  -- (70)
lPredAsCond = mkEqv (mkIf pA TRUE FALSE) pA  -- (71)
lCondNest  -- (72)
  = mkEqv (mkIf (mkIf pP pB pC) pA pD)
        (mkIf pP (mkIf pB pA pD) (mkIf pC pA pD))

laws_2_4
   =   freeLogicLaw "DEF-==" lEqvDef
   ~:~ freeLogicLaw "==-alt1.1" lEqvAlt11
   ~:~ freeLogicLaw "==-alt1.2" lEqvAlt12
   ~:~ freeLogicLaw "==-alt2" lEqvAlt2
   ~:~ freeLogicLaw "==-same" lEqvSame
   ~:~ freeLogicLaw "==-diff.1" lEqvDiff1
   ~:~ freeLogicLaw "==-diff.2" lEqvDiff2
   ~:~ freeLogicLaw "==-true" lEqvTrue
   ~:~ freeLogicLaw "==-false" lEqvFalse
   ~:~ freeLogicLaw "=>-alt2.1" lImpAlt21
   ~:~ freeLogicLaw "=>-alt2.2" lImpAlt22
   ~:~ freeLogicLaw "=>-alt2.3" lImpAlt23
   ~:~ freeLogicLaw "=>-alt2.4" lImpAlt24
   ~:~ freeLogicLaw "=>-alt3.1" lImpAlt31
   ~:~ freeLogicLaw "=>-alt3.2" lImpAlt32
   ~:~ freeLogicLaw "=>-alt3.3" lImpAlt33
   ~:~ freeLogicLaw "=>-alt3.4" lImpAlt34
   ~:~ freeLogicLaw "\\/-==-distr.1" lOrEqvDistr1
   ~:~ freeLogicLaw "\\/-==-distr.2" lOrEqvDistr2
   ~:~ freeLogicLaw "\\/-==-distr.3" lOrEqvDistr3
   ~:~ freeLogicLaw "\\/-==-distr.4" lOrEqvDistr4
   ~:~ freeLogicLaw "==-comm" lEqvComm
   ~:~ freeLogicLaw "==-assoc" lEqvAssoc
   ~:~ freeLogicLaw "Golden-Rule.1" goldenRule1
   ~:~ freeLogicLaw "Golden-Rule.2" goldenRule2
   ~:~ freeLogicLaw "Golden-Rule.3" goldenRule3
   ~:~ freeLogicLaw "Golden-Rule.4" goldenRule4
   ~:~ freeLogicLaw "Golden-Rule.5" goldenRule5
   ~:~ freeLogicLaw "Golden-Rule.6" goldenRule6
   ~:~ freeLogicLaw "Golden-Rule.7" goldenRule7
   ~:~ freeLogicLaw "Golden-Rule.8" goldenRule8
   ~:~ freeLogicLaw "DEF-<||>.1" lCondDef1
   ~:~ freeLogicLaw "DEF-<||>.2" lCondDef2
   ~:~ freeLogicLaw "DEF-<||>.3" lCondDef3
   ~:~ freeLogicLaw "DEF-<||>.4" lCondDef4
   ~:~ freeLogicLaw "DEF-<||>.5" lCondDef5
   ~:~ freeLogicLaw "DEF-<||>.6" lCondDef6
   ~:~ freeLogicLaw "DEF-<||>.7" lCondDef7
   ~:~ freeLogicLaw "DEF-<||>.8" lCondDef8
   ~:~ freeLogicLaw "<||>-alt.1" lCondAlt1
   ~:~ freeLogicLaw "<||>-alt.2" lCondAlt2
   ~:~ freeLogicLaw "<||>-R-distr" lCondRightDistr
   ~:~ freeLogicLaw "<||>-L-distr" lCondLeftDistr
   ~:~ freeLogicLaw "<|true|>" lCondTrue
   ~:~ freeLogicLaw "<|false|>" lCondFalse
   ~:~ freeLogicLaw "/\\-as-<||>.1" lAndAsCond1
   ~:~ freeLogicLaw "/\\-as-<||>.2" lAndAsCond2
   ~:~ freeLogicLaw "\\/-as-<||>.1" lOrAsCond1
   ~:~ freeLogicLaw "\\/-as-<||>.2" lOrAsCond2
   ~:~ freeLogicLaw "~-as-<||>" lNotAsCond
   ~:~ freeLogicLaw "P-as-<||>" lPredAsCond
   ~:~ freeLogicLaw "<||>-nest" lCondNest

conj_2_4
   = freeConj "DEF-==" lEqvDef
   : freeConj "==-alt1" lEqvAlt11
   : freeConj "==-alt2" lEqvAlt2
   : freeConj "==-same" lEqvSame
   : freeConj "==-diff" lEqvDiff1
   : freeConj "==-true" lEqvTrue
   : freeConj "==-false" lEqvFalse
   : freeConj "=>-alt2" lImpAlt21
   : freeConj "\\/-==-distr" lOrEqvDistr1
   : freeConj "==-comm" lEqvComm
   : freeConj "==-assoc" lEqvAssoc
   : freeConj "Golden-Rule" goldenRule1
   : freeConj "<||>-alt" lCondAlt1
   : freeConj "<||>-R-distr" lCondRightDistr
   : freeConj "<||>-L-distr" lCondLeftDistr
   : freeConj "<|true|>" lCondTrue
   : freeConj "<|false|>" lCondFalse
   : freeConj "/\\-as-<||>" lAndAsCond1
   : freeConj "\\/-as-<||>" lOrAsCond1
   : freeConj "~-as-<||>" lNotAsCond
   : freeConj "P-as-<||>" lPredAsCond
   : freeConj "<||>-nest" lCondNest
   : []
\end{code}

The following isn't worth a sub-section:
\begin{code}
lJoin1 = mkImp pA (mkOr [pA,pB])  -- (73)
lJoin2 = mkImp pB (mkOr [pA,pB])  -- (73)
lMeet1 = mkImp (mkAnd [pA,pB]) pA  -- (74)
lMeet2 = mkImp (mkAnd [pA,pB]) pB  -- (74)

laws_3
   =   freeLogicLaw "=>-\\/-join" lJoin1
   ~:~ freeLogicLaw "=>-\\/-join" lJoin2
   ~:~ freeLogicLaw "/\\-=>-meet" lMeet1
   ~:~ freeLogicLaw "/\\-=>-meet" lMeet2

conj_3
   = freeConj "=>-\\/-join" lJoin1
   : freeConj "/\\-=>-meet" lMeet1
   : []
\end{code}

Laws (75) and (76) in Section 4 are not relevant.

\subsubsection{Some predicate laws (4)}

We generalise the laws to use quantifier list-variables where relevant.

\subsubsection{Eliminating quantifiers (4.3)}


The one-point laws as originally stated are missing a side-condition,
namely that the quantified variable must also not be free in the
term with which it is asserted to be equal.
\begin{eqnarray*}
% \nonumber to remove numbering (before each equation)
  (\forall x \cdot x=t \implies A)
  & \equiv \quad A[t/x] \quad \equiv &
  (\exists x \cdot x=t \land A)
\\ & x \mbox{ not free in } t
\end{eqnarray*}

\begin{code}
lForall1Pt1  -- (77)
  = mkEqv (mkAll qxxs (mkImp (PExpr (eqx `mkEqual` e)) pA))
        (mkAll qxs (Sub pA (Substn [(vx,e)])))
lForall1Pt2  -- (77)
  = mkEqv (mkAll qxxs (mkImp (PExpr (e `mkEqual` eqx)) pA))
        (mkAll qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt1  -- (77)
  = mkEqv (mkAny qxxs (mkAnd [(PExpr (eqx `mkEqual` e)),pA]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt2  -- (77)
  = mkEqv (mkAny qxxs (mkAnd [(PExpr (e `mkEqual` eqx)),pA]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt3  -- (77)
  = mkEqv (mkAny qxxs (mkAnd [pA,(PExpr (eqx `mkEqual` e))]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt4  -- (77)
  = mkEqv (mkAny qxxs (mkAnd [pA,(PExpr (e `mkEqual` eqx))]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))

-- we ignore (78) and (79) at this point.

laws_4_3
   = mkLogicLaw "forall-1-pt.1" lForall1Pt1 x_NotFreeIn_e
   ~:~ mkLogicLaw "forall-1-pt.2" lForall1Pt2 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.1" lEx1Pt1 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.2" lEx1Pt2 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.3" lEx1Pt3 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.4" lEx1Pt4 x_NotFreeIn_e

conj_4_3
   = mkConj "forall-1-pt" lForall1Pt1 x_NotFreeIn_e
   : mkConj "exists-1-pt" lEx1Pt1 x_NotFreeIn_e
   : []
\end{code}

\subsubsection{Quantifiers alone (4.4)}

\begin{code}
lForallIdem = mkEqv (mkAll qxs (mkAll qxs pA)) (mkAll qxs pA)  -- (80)
lExIdem = mkEqv (mkAny qxs (mkAny qxs pA)) (mkAny qxs pA)  -- (81)

lForallDeMorgan = mkEqv (mkNot (mkAll qxs pA)) (mkAny qxs (mkNot pA))  -- (82)
lExDeMorgan   = mkEqv (mkNot (mkAny qxs pA)) (mkAll qxs (mkNot pA))  -- (83)

laws_4_4
   =   freeLogicLaw "forall-idem" lForallIdem
   ~:~ freeLogicLaw "exists-idem" lExIdem
   ~:~ freeLogicLaw "forall-deMorgan" lForallDeMorgan
   ~:~ freeLogicLaw "exists-deMorgan" lExDeMorgan

conj_4_4
   = freeConj "forall-idem" lForallIdem
   : freeConj "exists-idem" lExIdem
   : freeConj "forall-deMorgan" lForallDeMorgan
   : freeConj "exists-deMorgan" lExDeMorgan
   : []
\end{code}


\subsubsection{Extending the commutative laws (4.5)}

\begin{code}
lForallComm = mkEqv (mkAll qxs (mkAll qys pA))  -- (84)
                (mkAll qys (mkAll qxs pA))
lExComm = mkEqv (mkAny qxs (mkAny qys pA))  -- (85)
              (mkAny qys (mkAny qxs pA))

laws_4_5
   = freeLogicLaw "forall-comm" lForallComm
   ~:~ freeLogicLaw "exists-comm" lExComm

conj_4_5
   = freeConj "forall-comm" lForallComm
   : freeConj "exists-comm" lExComm
   : []
\end{code}

\subsubsection{Quantifiers accompanied (4.6)}

\begin{code}
lAndForallDistr1 = mkEqv (mkAll qxs (mkAnd [pA,pB]))  -- (86)
                       (mkAnd [mkAll qxs pA,mkAll qxs pB])
lAndForallDistr2 = mkEqv (mkAll qxs (mkAnd [pB,pA]))  -- (86)
                       (mkAnd [mkAll qxs pA,mkAll qxs pB])

lOrExDistr1 = mkEqv (mkAny qxs (mkOr [pA,pB]))  -- (87)
                  (mkOr [mkAny qxs pA,mkAny qxs pB])
lOrExDistr2 = mkEqv (mkAny qxs (mkOr [pB,pA]))  -- (87)
                  (mkOr [mkAny qxs pA,mkAny qxs pB])

lImpExDistr = mkEqv (mkAny qxs (mkImp pA pB))  -- (88)
                  (mkImp (mkAll qxs pA) (mkAny qxs pB))

lForallImpEx = mkImp (mkAll qxs pA) (mkAny qxs pA)  -- (89)

lOrForallIDistr1 = mkImp (mkOr [mkAll qxs pA,mkAll qxs pB])  -- (90)
                       (mkAll qxs (mkOr [pA,pB]))
lOrForallIDistr2 = mkImp (mkOr [mkAll qxs pA,mkAll qxs pB])  -- (90)
                       (mkAll qxs (mkOr [pB,pA]))

lForallImpImp = mkImp (mkAll qxs (mkImp pA pB))  -- (91)
                    (mkImp (mkAll qxs pA) (mkAll qxs pB))

lAndExIDistr1 = mkImp (mkAny qxs (mkAnd [pA,pB]))  -- (92)
                    (mkAnd [mkAny qxs pA,mkAny qxs pB])
lAndExIDistr2 = mkImp (mkAny qxs (mkAnd [pB,pA]))  -- (92)
                    (mkAnd [mkAny qxs pA,mkAny qxs pB])

lExImpImp = mkImp (mkImp (mkAny qxs pA) (mkAny qxs pB))  -- (93)
                (mkAny qxs (mkImp pA pB))
lExForallSwap = mkImp (mkAny qys (mkAll qxs pA))  -- (94)
                    (mkAll qxs (mkAny qys pA))

laws_4_6
   =   freeLogicLaw "/\\-forall-distr.1" lAndForallDistr1
   ~:~ freeLogicLaw "/\\-forall-distr.2" lAndForallDistr2
   ~:~ freeLogicLaw "\\/-exists-distr.1" lOrExDistr1
   ~:~ freeLogicLaw "\\/-exists-distr.2" lOrExDistr2
   ~:~ freeLogicLaw "=>-exists-distr" lImpExDistr
   ~:~ freeLogicLaw "forall-=>-exists" lForallImpEx
   ~:~ freeLogicLaw "\\/:forall-=>-forall:\\/.1" lOrForallIDistr1
   ~:~ freeLogicLaw "\\/:forall-=>-forall:\\/.2" lOrForallIDistr2
   ~:~ freeLogicLaw "forall:=>-=>-=>:forall" lForallImpImp
   ~:~ freeLogicLaw "exists:/\\-=>-/\\:exists.1" lAndExIDistr1
   ~:~ freeLogicLaw "exists:/\\-=>-/\\:exists.2" lAndExIDistr2
   ~:~ freeLogicLaw "=>:exists-=>-exists:=>" lExImpImp
   ~:~ freeLogicLaw "exists:forall-swap" lExForallSwap

conj_4_6
   = freeConj "/\\-forall-distr" lAndForallDistr1
   : freeConj "\\/-exists-distr" lOrExDistr1
   : freeConj "=>-exists-distr" lImpExDistr
   : freeConj "forall-=>-exists" lForallImpEx
   : freeConj "\\/:forall-=>-forall:\\/" lOrForallIDistr1
   : freeConj "forall:=>-=>-=>:forall" lForallImpImp
   : freeConj "exists:/\\-=>-/\\:exists" lAndExIDistr1
   : freeConj "=>:exists-=>-exists:=>" lExImpImp
   : freeConj "exists:forall-swap" lExForallSwap
   : []
\end{code}

\subsubsection{Manipulation of quantifiers (4.7)}

We now have lots of side-conditions regarding free-variables.
\begin{code}
lForallVac = mkEqv (mkAll qx pA) pA  -- (95)
lExVac = mkEqv (mkAny qx pA) pA  -- (96)
lForallVac' = mkEqv (mkAll qxxs pA) (mkAll qxs pA)
lExVac' = mkEqv (mkAny qxxs pA) (mkAny qxs pA)

lFreeAndForallDistr1 = mkEqv (mkAll qxs (mkAnd[pN,pB]))  -- (97)
                           (mkAnd [pN,mkAll qxs pB])
lFreeAndForallDistr2 = mkEqv (mkAll qxs (mkAnd[pB,pN]))  -- (97)
                           (mkAnd [pN,mkAll qxs pB])

lFreeOrForallDistr1 = mkEqv (mkAll qxs (mkOr[pN,pB]))  -- (98)
                          (mkOr [pN,mkAll qxs pB])
lFreeOrForallDistr2 = mkEqv (mkAll qxs (mkOr[pB,pN]))  -- (98)
                          (mkOr [pN,mkAll qxs pB])

lFreeAnteForallDistr = mkEqv (mkAll qxs (mkImp pN pB))  -- (99)
                         (mkImp pN (mkAll qxs pB))
lFreeCnsqForallDistr = mkEqv (mkAll qxs (mkImp pA pN))  -- (100)
                         (mkImp (mkAny qxs pA) pN)
lFreeCondForallDistr = mkEqv (mkAll qxs (mkIf pN pA pB))  -- (101)
                         (mkIf pN (mkAll qxs pA) (mkAll qxs pB))

lFreeAndExDistr1 = mkEqv (mkAny qxs (mkAnd[pN,pB]))  -- (102)
                       (mkAnd [pN,mkAny qxs pB])
lFreeAndExDistr2 = mkEqv (mkAny qxs (mkAnd[pB,pN]))  -- (102)
                       (mkAnd [pN,mkAny qxs pB])

lFreeOrExDistr1 = mkEqv (mkAny qxs (mkOr[pN,pB]))  -- (103)
                      (mkOr [pN,mkAny qxs pB])
lFreeOrExDistr2 = mkEqv (mkAny qxs (mkOr[pB,pN]))  -- (103)
                      (mkOr [pN,mkAny qxs pB])

lFreeAnteExDistr = mkEqv (mkAny qxs (mkImp pN pB))  -- (104)
                       (mkImp pN (mkAny qxs pB))
lFreeCnsqExDistr = mkEqv (mkAny qxs (mkImp pA pN))  -- (105)
                       (mkImp (mkAll qxs pA) pN)
lFreeCondExDistr = mkEqv (mkAny qxs (mkIf pN pA pB))  -- (106)
                       (mkIf pN (mkAny qxs pA) (mkAny qxs pB))

lForallAlpha = mkEqv (mkAll qxxs pA)  -- (107)
                 (mkAll qyxs (Sub pA (Substn [(vx,eqy)])))
lExAlpha = mkEqv (mkAny qxxs pA)  -- (108)
               (mkAny qyxs (Sub pA (Substn [(vx,eqy)])))
lForallAlpha' = mkEqv (mkAll qxxs (Sub pA (Substn [(vz,eqx)])))  -- (109)
                  (mkAll qyxs (Sub pA (Substn [(vz,eqy)])))
lExAlpha' = mkEqv (mkAny qxxs (Sub pA (Substn [(vz,eqx)])))  -- (110)
                (mkAny qyxs (Sub pA (Substn [(vz,eqy)])))

lForallSpec = mkImp (mkAll qx pA) (Sub pA (Substn [(vx,e)]))  -- (111)
lExGen    = mkImp (Sub pA (Substn [(vx,e)])) (mkAny qx pA)  -- (112)

laws_4_7
   = mkLogicLaw "forall-vac" lForallVac xNFinA
   ~:~ mkLogicLaw "exists-vac" lExVac xNFinA
   ~:~ mkLogicLaw "forall-vac'" lForallVac' xNFinA
   ~:~ mkLogicLaw "exists-vac'" lExVac' xNFinA
   ~:~ mkLogicLaw "free-/\\-forall-distr'.1" lFreeAndForallDistr1 xsNFinN
   ~:~ mkLogicLaw "free-/\\-forall-distr'.2" lFreeAndForallDistr2 xsNFinN
   ~:~ mkLogicLaw "free-\\/-forall-distr'.1" lFreeOrForallDistr1 xsNFinN
   ~:~ mkLogicLaw "free-\\/-forall-distr'.2" lFreeOrForallDistr2 xsNFinN
   ~:~ mkLogicLaw "free-ante-forall-distr'" lFreeAnteForallDistr xsNFinN
   ~:~ mkLogicLaw "free-cnsq-forall-distr'" lFreeCnsqForallDistr xsNFinN
   ~:~ mkLogicLaw "free-cond-forall-distr'" lFreeCondForallDistr xsNFinN
   ~:~ mkLogicLaw "free-/\\-exists-distr'.1" lFreeAndExDistr1 xsNFinN
   ~:~ mkLogicLaw "free-/\\-exists-distr'.2" lFreeAndExDistr2 xsNFinN
   ~:~ mkLogicLaw "free-\\/-exists-distr'.1" lFreeOrExDistr1 xsNFinN
   ~:~ mkLogicLaw "free-\\/-exists-distr'.2" lFreeOrExDistr2 xsNFinN
   ~:~ mkLogicLaw "free-ante-exists-distr'" lFreeAnteExDistr xsNFinN
   ~:~ mkLogicLaw "free-cnsq-exists-distr'" lFreeCnsqExDistr xsNFinN
   ~:~ mkLogicLaw "free-cond-exists-distr'" lFreeCondExDistr xsNFinN
   ~:~ mkLogicLaw "forall-alpha" lForallAlpha yNFinA
   ~:~ mkLogicLaw "exists-alpha" lExAlpha yNFinA
   ~:~ mkLogicLaw "forall-alpha'" lForallAlpha' xyNFinA
   ~:~ freeLogicLaw "forall-spec" lForallSpec
   ~:~ freeLogicLaw "exists-gen" lExGen

conj_4_7
   = mkConj "forall-vac" lForallVac xNFinA
   : mkConj "exists-vac" lExVac xNFinA
   : mkConj "forall-vac'" lForallVac' xNFinA
   : mkConj "exists-vac'" lExVac' xNFinA
   : mkConj "free-/\\-forall-distr'" lFreeAndForallDistr1 xsNFinN
   : mkConj "free-\\/-forall-distr'" lFreeOrForallDistr1 xsNFinN
   : mkConj "free-ante-forall-distr'" lFreeAnteForallDistr xsNFinN
   : mkConj "free-cnsq-forall-distr'" lFreeCnsqForallDistr xsNFinN
   : mkConj "free-cond-forall-distr'" lFreeCondForallDistr xsNFinN
   : mkConj "free-/\\-exists-distr'" lFreeAndExDistr1 xsNFinN
   : mkConj "free-\\/-exists-distr'" lFreeOrExDistr1 xsNFinN
   : mkConj "free-ante-exists-distr'" lFreeAnteExDistr xsNFinN
   : mkConj "free-cnsq-exists-distr'" lFreeCnsqExDistr xsNFinN
   : mkConj "free-cond-exists-distr'" lFreeCondExDistr xsNFinN
   : mkConj "forall-alpha" lForallAlpha yNFinA
   : mkConj "exists-alpha" lExAlpha yNFinA
   : mkConj "forall-alpha'" lForallAlpha' xyNFinA
   : freeConj "forall-spec" lForallSpec
   : freeConj "exists-gen" lExGen
   : []
\end{code}

\subsubsection{Quantifiers over booleans}

Boolean quantification admits the following simplification:
\begin{eqnarray*}
   (\exists b:\Bool @ A) &\equiv& A[True/b] \lor A[False/b]
\\ (\forall b:\Bool @ A) &\equiv& A[True/b] \land A[False/b]
\end{eqnarray*}
Given that we do not yet handle types properly,
we need to use cues from expressions regarding the presence
of booleans, leading to the following laws:
\begin{eqnarray*}
   (\exists b @ A \land b) &\equiv& A[True/b]
\\ (\forall b @ A \land b) &\equiv& False
\\ (\exists b @ A \lor b)  &\equiv& True
\\ (\forall b @ A \lor b)  &\equiv& A[False/b]
\\ (\exists b @ A \implies b) &\equiv& True
\\ (\forall b @ A \implies b) &\equiv& \lnot A[False/b]
\\ (\exists b @ b \implies A) &\equiv& True
\\ (\forall b @ b \implies A) &\equiv& A[True/b]
\\ (\exists b @ b \equiv A) &\equiv& A[True/b] \lor \lnot A[False/b]
\\ (\forall b @ b \equiv A) &\equiv& A[True/b] \land \lnot A[False/b]
\end{eqnarray*}
\begin{code}
lExBoolAnd1  = (mkAny bvxs (bp /\ pA))  === (mkAny qxs (subb pA (EPred TRUE)))
lExBoolAnd2  = (mkAny bvxs (pA /\ bp))  === (mkAny qxs (subb pA (EPred TRUE)))

lAllBoolAnd1 = (mkAll bvxs (bp /\ pA))  === FALSE
lAllBoolAnd2 = (mkAll bvxs (pA /\ bp))  === FALSE

lExBoolOr1   = (mkAny bvxs (bp \/ pA))  === TRUE
lExBoolOr2   = (mkAny bvxs (pA \/ bp))  === TRUE

lAllBoolOr1  = (mkAll bvxs (bp \/ pA))  === (subb pA (EPred FALSE))
lAllBoolOr2  = (mkAll bvxs (pA \/ bp))  === (subb pA (EPred FALSE))

lExBoolPmi   = (mkAny bvxs (pA ==> bp)) === TRUE
lAllBoolPmi  = (mkAll bvxs (pA ==> bp)) === mkNot (subb pA (EPred FALSE))
lExBoolImp   = (mkAny bvxs (bp ==> pA)) === TRUE
lAllBoolImp  = (mkAll bvxs (bp ==> pA)) === (subb pA (EPred TRUE))

lExBoolEqv1  = (mkAny bvxs (bp === pA)) === (subb pA (EPred TRUE)) \/ (mkNot (subb pA (EPred FALSE)))
lExBoolEqv2  = (mkAny bvxs (bp === pA)) === (mkNot (subb pA (EPred FALSE))) \/ (subb pA (EPred TRUE))

lAllBoolEqv1 = (mkAll bvxs (bp === pA)) === (subb pA (EPred TRUE)) /\ (mkNot (subb pA (EPred FALSE)))
lAllBoolEqv2 = (mkAll bvxs (bp === pA)) === (mkNot (subb pA (EPred FALSE))) /\ (subb pA (EPred TRUE))
\end{code}
We also want to handle the cases where the boolean is all that exists:
\begin{eqnarray*}
   (\exists b @ b) &\equiv& True
\\ (\forall b @ b) &\equiv& False
\end{eqnarray*}
\begin{code}
lExBool  = (mkAny bvxs bp)
lAllBool = (mkAll bvxs bp) === FALSE
\end{code}

We can also handle cases where the boolean is negated:
\begin{eqnarray*}
   (\exists b @ A \land \lnot b) &\equiv& A[False/b]
\\ (\forall b @ A \land \lnot b) &\equiv& False
\\ (\exists b @ A \lor \lnot b)  &\equiv& True
\\ (\forall b @ A \lor \lnot b)  &\equiv& A[True/b]
\\ (\exists b @ A \implies \lnot b) &\equiv& True
\\ (\forall b @ A \implies \lnot b) &\equiv& \lnot A[True/b]
\\ (\exists b @ \lnot b \implies A) &\equiv& True
\\ (\forall b @ \lnot b \implies A) &\equiv& A[False/b]
\\ (\exists b @ \lnot b \equiv A) &\equiv& A[False/b] \lor \lnot A[True/b]
\\ (\forall b @ \lnot b \equiv A) &\equiv& A[False/b] \land \lnot A[True/b]
\end{eqnarray*}
\begin{code}
lExNBoolAnd1  = (mkAny bvxs (nbp /\ pA))  === (mkAny qxs (subb pA (EPred FALSE)))
lExNBoolAnd2  = (mkAny bvxs (pA /\ nbp))  === (mkAny qxs (subb pA (EPred FALSE)))

lAllNBoolAnd1 = (mkAll bvxs (nbp /\ pA))  === FALSE
lAllNBoolAnd2 = (mkAll bvxs (pA /\ nbp))  === FALSE

lExNBoolOr1   = (mkAny bvxs (nbp \/ pA))  === TRUE
lExNBoolOr2   = (mkAny bvxs (pA \/ nbp))  === TRUE

lAllNBoolOr1  = (mkAll bvxs (nbp \/ pA))  === (subb pA (EPred TRUE))
lAllNBoolOr2  = (mkAll bvxs (pA \/ nbp))  === (subb pA (EPred TRUE))

lExNBoolPmi   = (mkAny bvxs (pA ==> nbp)) === TRUE
lAllNBoolPmi  = (mkAll bvxs (pA ==> nbp)) === mkNot (subb pA (EPred TRUE))
lExNBoolImp   = (mkAny bvxs (nbp ==> pA)) === TRUE
lAllNBoolImp  = (mkAll bvxs (nbp ==> pA)) === (subb pA (EPred FALSE))

lExNBoolEqv1  = (mkAny bvxs (nbp === pA)) === (subb pA (EPred FALSE)) \/ (mkNot (subb pA (EPred TRUE)))
lExNBoolEqv2  = (mkAny bvxs (nbp === pA)) === (mkNot (subb pA (EPred TRUE))) \/ (subb pA (EPred FALSE))

lAllNBoolEqv1 = (mkAll bvxs (nbp === pA)) === (subb pA (EPred FALSE)) /\ (mkNot (subb pA (EPred TRUE)))
lAllNBoolEqv2 = (mkAll bvxs (nbp === pA)) === (mkNot (subb pA (EPred TRUE))) /\ (subb pA (EPred FALSE))
\end{code}
and when the boolean is all we have got:
\begin{eqnarray*}
   (\exists b @ \lnot b) &\equiv& True
\\ (\forall b @ \lnot b) &\equiv& False
\end{eqnarray*}
\begin{code}
lExNBool  = (mkAny bvxs nbp)
lAllNBool = (mkAll bvxs nbp) === FALSE
\end{code}

Putting it all together:
\begin{code}
laws_boolvar
 =   freeLogicLaw "exist-bv" lExBool
 ~:~ freeLogicLaw "exist-nbv" lExNBool
 ~:~ freeLogicLaw "forall-bv" lAllBool
 ~:~ freeLogicLaw "forall-nbv" lAllNBool
 ~:~ freeLogicLaw "exists-bv-/\\.2" lExBoolAnd2
 ~:~ freeLogicLaw "forall-bv-/\\.1" lAllBoolAnd1
 ~:~ freeLogicLaw "forall-bv-/\\.2" lAllBoolAnd2
 ~:~ freeLogicLaw "exists-bv-\\/.1" lExBoolOr1
 ~:~ freeLogicLaw "exists-bv-\\/.2" lExBoolOr2
 ~:~ freeLogicLaw "forall-bv-\\/.1" lAllBoolOr1
 ~:~ freeLogicLaw "forall-bv-\\/.2" lAllBoolOr2
 ~:~ freeLogicLaw "exists-bv-<==" lExBoolPmi
 ~:~ freeLogicLaw "forall-bv-<==" lAllBoolPmi
 ~:~ freeLogicLaw "exists-bv-==>" lExBoolImp
 ~:~ freeLogicLaw "forall-bv-==>" lAllBoolImp
 ~:~ freeLogicLaw "exists-bv-===.1" lExBoolEqv1
 ~:~ freeLogicLaw "exists-bv-===.2" lExBoolEqv2
 ~:~ freeLogicLaw "forall-bv-===.1" lAllBoolEqv1
 ~:~ freeLogicLaw "forall-bv-===.2" lAllBoolEqv2
 ~:~ freeLogicLaw "exists-nbv-/\\.1" lExNBoolAnd1
 ~:~ freeLogicLaw "exists-nbv-/\\.2" lExNBoolAnd2
 ~:~ freeLogicLaw "forall-nbv-/\\.1" lAllNBoolAnd1
 ~:~ freeLogicLaw "forall-nbv-/\\.2" lAllNBoolAnd2
 ~:~ freeLogicLaw "exists-nbv-\\/.1" lExNBoolOr1
 ~:~ freeLogicLaw "exists-nbv-\\/.2" lExNBoolOr2
 ~:~ freeLogicLaw "forall-nbv-\\/.1" lAllNBoolOr1
 ~:~ freeLogicLaw "forall-nbv-\\/.2" lAllNBoolOr2
 ~:~ freeLogicLaw "exists-nbv-<==" lExNBoolPmi
 ~:~ freeLogicLaw "forall-nbv-<==" lAllNBoolPmi
 ~:~ freeLogicLaw "exists-nbv-==>" lExNBoolImp
 ~:~ freeLogicLaw "forall-nbv-==>" lAllNBoolImp
 ~:~ freeLogicLaw "exists-nbv-===.1" lExNBoolEqv1
 ~:~ freeLogicLaw "exists-nbv-===.2" lExNBoolEqv2
 ~:~ freeLogicLaw "forall-nbv-===.1" lAllNBoolEqv1
 ~:~ freeLogicLaw "forall-nbv-===.2" lAllNBoolEqv2

conj_boolvar
 =   freeConj "exist-bv" lExBool
 : freeConj "exist-nbv" lExNBool
 : freeConj "forall-bv" lAllBool
 : freeConj "forall-nbv" lAllNBool
 : freeConj "exists-bv-/\\.2" lExBoolAnd2
 : freeConj "forall-bv-/\\.1" lAllBoolAnd1
 : freeConj "forall-bv-/\\.2" lAllBoolAnd2
 : freeConj "exists-bv-\\/.1" lExBoolOr1
 : freeConj "exists-bv-\\/.2" lExBoolOr2
 : freeConj "forall-bv-\\/.1" lAllBoolOr1
 : freeConj "forall-bv-\\/.2" lAllBoolOr2
 : freeConj "exists-bv-<==" lExBoolPmi
 : freeConj "forall-bv-<==" lAllBoolPmi
 : freeConj "exists-bv-==>" lExBoolImp
 : freeConj "forall-bv-==>" lAllBoolImp
 : freeConj "exists-bv-===.1" lExBoolEqv1
 : freeConj "exists-bv-===.2" lExBoolEqv2
 : freeConj "forall-bv-===.1" lAllBoolEqv1
 : freeConj "forall-bv-===.2" lAllBoolEqv2
 : freeConj "exists-nbv-/\\.1" lExNBoolAnd1
 : freeConj "exists-nbv-/\\.2" lExNBoolAnd2
 : freeConj "forall-nbv-/\\.1" lAllNBoolAnd1
 : freeConj "forall-nbv-/\\.2" lAllNBoolAnd2
 : freeConj "exists-nbv-\\/.1" lExNBoolOr1
 : freeConj "exists-nbv-\\/.2" lExNBoolOr2
 : freeConj "forall-nbv-\\/.1" lAllNBoolOr1
 : freeConj "forall-nbv-\\/.2" lAllNBoolOr2
 : freeConj "exists-nbv-<==" lExNBoolPmi
 : freeConj "forall-nbv-<==" lAllNBoolPmi
 : freeConj "exists-nbv-==>" lExNBoolImp
 : freeConj "forall-nbv-==>" lAllNBoolImp
 : freeConj "exists-nbv-===.1" lExNBoolEqv1
 : freeConj "exists-nbv-===.2" lExNBoolEqv2
 : freeConj "forall-nbv-===.1" lAllNBoolEqv1
 : freeConj "forall-nbv-===.2" lAllNBoolEqv2
 : []
\end{code}

\subsection{mkAnd the Law is \ldots}

\begin{code}

logicLawTable
  = laws_2_1
  ~:~ laws_2_2
  ~:~ laws_2_3
  ~:~ laws_2_4
  ~:~ laws_3
  ~:~ laws_4_3
  ~:~ laws_4_4
  ~:~ laws_4_5
  ~:~ laws_4_6
  ~:~ laws_4_7
  ~:~ laws_boolvar

logicConjectures
  = conj_2_1
  ++ conj_2_2
  ++ conj_2_3
  ++ conj_2_4
  ++ conj_3
  ++ conj_4_3
  ++ conj_4_4
  ++ conj_4_5
  ++ conj_4_6
  ++ conj_4_7
  ++ conj_boolvar

logicProofContext
 = markTheoryDeps ((nmdNullPrfCtxt "Logic")
                     { syntaxDeps = [ rootName ]
                     , types = boolOpTypes
                     , laws = logicLawTable
                     })
logicLawsTheory
 = markTheoryDeps ((nmdNullPrfCtxt "LogicLaws")
                     { syntaxDeps = [ rootName ]
                     , types = boolOpTypes
                     , laws = freeLogicLaw "DEF-<||>.1" lCondDef1
                     , conjectures = lbuild logicConjectures
                     })
\end{code}
Now some testers:
\begin{code}

alphaTest1 -- forall x @ x = 3 /\ exists x @ x /\ TRUE
 = mkForall qx
    (mkAnd [ PExpr (mkEqual ex (Num 3))
         , mkExists qx (mkAnd [ PExpr ex
                                  , TRUE
                                  ])
         ])
 where ex = Var vx

alphaTest2 -- x /\ forall x @ x = 3 /\ exists x @ x
 = mkAnd [ PExpr ex
       , mkForall qx
                (mkAnd [ PExpr (mkEqual ex (Num 3))
                     , mkExists qx (PExpr ex)
                     ])
       ]
 where ex = Var vx

typeTest1 = PExpr (mkEqual (Var vx) (Var vy))
\end{code}
