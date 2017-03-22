\section{Proof/Theory Synchronisation}

\begin{code}
module Synchronise where
import Tables
import Precedences
import Datatypes
import DataText
import Laws
import Proof
import Theories
import Utilities
import DSL
import MatchTypes
\end{code}


This module provides facilities to allow the entire internal state
of \Saoithin\ to be synchronised with changes made in theory tables.
Examples of such synchronisations include:
\begin{itemize}
  \item
    Modifying the hardwired precedences of \texttt{Bin}
    or infix \texttt{Lang} expressions
    when a precedence table entry has changed.
    \\
    THIS WILL BECOME COMPLETELY REDUNDANT
    AS WE WILL NO LONGER HAVE HARDWIRED PRECEDENCES
\end{itemize}


The top level function pulls out the theory/proof state,
applies a pair of synchronisation functions,
both of which take a theory stack as first argument:
\begin{code}
type SyncFun a = TheoryStack -> a -> a
\end{code}
The first argument is the theories in scope for the particular instance
of type \texttt{a} being synchronised.

To synchronise a theory graph,
we take each theory and synchronise it against
its ``hard stack'' w.r.t. the theory graph.
\begin{code}
syncTheoryGraph :: SyncFun Theory -> TheoryGraph -> TheoryGraph
syncTheoryGraph thsyncf thg@(rdag,trie)
 = (rdag, tmap (syncTheory thg) trie)
 where
   syncTheory thg thry
    = thsyncf (hardGraphToStack (thryName thry) thg) thry
\end{code}

To synchronise a theory stack,
we use a function that takes a theory-stack,
and returns a theory modifier:
\begin{code}
syncTheories :: SyncFun Theory -> TheoryStack -> TheoryStack
syncTheories thsyncf [] = []
syncTheories thsyncf thstk@(th:ths)
 = (thsyncf thstk th):syncTheories thsyncf ths
\end{code}

Synchronising a proof stack means copying the revised
theories from the main-stack,
and then updating the special theories accordingly.
\begin{code}
syncProofStack :: SyncFun Theory -> TheoryGraph -> Proof -> Proof
syncProofStack thsyncf thgf proof
 = let thstk = hardGraphToStack (thname proof) thgf
       spcThs = takeWhile (isSPTName . thryName) (context proof)
       spcThs' = map (thsyncf thstk) spcThs
       thstk' = spcThs' ++ thstk
       mctxts' = mkMatchContexts thstk'
   in proof{ context=thstk', mtchCtxt=mctxts' }
\end{code}


So a synchroniser is defined by two functions,
along with a text description, and name:
\begin{code}
type Synchroniser
 = ( String  -- a short name
   , String  -- a longer descriptor
   , SyncFun Theory  -- how to synchronise a Theory
   , SyncFun Proof   -- how to synchronise a Proof
   )
\end{code}


\newpage
\subsection{The Precedence Synchroniser}

The precedence synchroniser looks for every occurrence
of the \texttt{Expr Bin} variant
and the \texttt{Pred Lang} variant,
and sets their precedence values to those found by looking
at the \texttt{precs} tables in all the theories.
\begin{code}
precsSynchroniser :: Synchroniser
precsSynchroniser
 = ( "Precedence"
   , "Sets all hardwired precedences to match current precedence tables"
   , precsTheorySync
   , precsProofSync
   )
\end{code}
The Theory precedence synchroniser

The idea behind this is to pull out the information from the Predicates and
Expressions contained within the Theory and check them against the Precedences
\begin{code}
precsTheorySync :: SyncFun Theory
precsTheorySync thstk theory
 = theory{
     consts=constants',
     exprs=expressions',
     preds=predicates',
     lang=language',
     laws=laws',
     conjectures=conjectures',
     theorems=theorems',
     langDefs=langDefs'
   }
 where
   constants'    = syncConsts theory precList
   expressions'  = syncExpr theory precList
   predicates'   = syncPreds theory precList
   language'     = syncLang theory precList
   laws'         = syncLaws theory precList
   conjectures'  = syncConj theory precList
   theorems'     = syncTheorems thstk theory
   langDefs'     = syncLanD theory precList

   precList      = map precs thstk
\end{code}

\begin{code}
-- Pull consts out ->  flatten -> map change pred
syncConsts ::  Theory ->  [Trie Precedences.Precs] -> Trie Expr
syncConsts theory precs
 = tmap (changePrecedenceE precs) constants
 where constants = consts theory
\end{code}

\subsection{Several Methods to change the different aspects of Theory}


\begin{code}
syncPreds   :: Theory -> [Trie Precedences.Precs] -> Trie Pred
syncPreds theory precs
 = tmap (changePrecedenceP precs) predicates
 where predicates = preds theory
\end{code}

\begin{code}
syncExpr :: Theory ->  [Trie Precedences.Precs] -> Trie Expr
syncExpr theory precs
 = tmap (changePrecedenceE precs) expression
 where expression = consts theory
\end{code}

\begin{code}
syncLang ::  Theory -> [Trie Precedences.Precs] -> Trie LangSpec
syncLang theory precs = tnil -- for now
\end{code}


\begin{code}
syncLaws :: Theory -> [Trie Precedences.Precs] -> LawTable
syncLaws theory precs
 = map changeLaws lawTable
   where
         changeLaws (string, ((pred,sideCond),provenance,ttbl))
            = (string, ((changePrecedenceP precs pred,sideCond),provenance,ttbl))
         lawTable = laws theory
\end{code}

\begin{code}
syncTheorems :: TheoryStack -> Theory -> [Proof]
syncTheorems thstk theory
    = map (precsProofSync thstk) proofs
    where proofs = theorems theory
\end{code}

\begin{code}
syncConj :: Theory -> [Trie Precedences.Precs] -> Trie Assertion
syncConj theory precs
 = tmap changeConj conjecture
 where
    changeConj (pred, sideCond) = (changePrecedenceP precs pred,sideCond)
    conjecture =  conjectures theory
\end{code}

\begin{code}
syncLanD :: Theory -> [Trie Precedences.Precs] -> Trie [LangDefn]
syncLanD theory precs
 = tmap (map changeLanD) langDef
 where
  changeLanD (pred, predic) = ( changePrecedenceP precs pred
                              , changePrecedenceP precs predic)
  langDef = langDefs theory
\end{code}

Unusual calling pattern here for \texttt{mapE} !
\begin{code}
changePrecedenceE :: [Trie Precedences.Precs] -> Expr -> Expr
changePrecedenceE precs expression
 = mapE ((changePrecedenceP precs), (changePrecedenceE precs))
        (changePrecE precs expression)

changePrecedenceP :: [Trie Precedences.Precs] -> Pred -> Pred
changePrecedenceP precs predicate
 = mapP ((changePrecedenceP precs), (changePrecedenceE precs))
        (changePrecP precs predicate)

changePrecP _ p = p

changePrecE :: [Trie Precedences.Precs] -> Expr ->  Expr
--changePrecE precs expr@(Bin s i e1 e2)
changePrecE precs expr@(App nm [e1,e2])
 | isBin nm
   = let (op,i) = getBin nm
         mres = tslookup precs op
         i' = case mres of
                Nothing    -> i
                Just (r,_) -> r
     in mkBin op i' e1 e2

changePrecE _ e =  e
\end{code}

The Proof precedence synchroniser
\begin{code}
precsProofSync :: SyncFun Proof
precsProofSync thstk proof
 = proof'
 where proof' = proof{
                goal=goal',
                plan=plan',
                context=context',
                mtchCtxt=mtchCtxt'}
       goal' = syncGoal proof precList
       plan' = syncPlan thstk proof precList
       context' = syncContext proof thstk
       mtchCtxt' = syncMatchContext proof precList
       precList= map precs thstk


\end{code}

\subsection{Methods to Sync Proof}

\begin{code}
syncGoal :: Proof -> [Trie Precs] -> Pred
syncGoal proof precs = changePrecedenceP precs goal'
    where goal' = goal proof
\end{code}
\begin{code}
syncPlan :: TheoryStack -> Proof -> [Trie Precs] -> Strategy
syncPlan thstk proof precs
 = syncStrategy thstk precs plan'
 where plan' = plan proof

syncStrategy  thstk precs NoStrategy = NoStrategy
syncStrategy  thstk precs (Reduce  prfSctn)
 = Reduce  (syncProofSection thstk precs prfSctn)
syncStrategy  thstk precs (Lhs2Rhs prfSctn)
 = Lhs2Rhs (syncProofSection thstk precs prfSctn)
syncStrategy  thstk precs (Rhs2Lhs prfSctn)
 = Rhs2Lhs (syncProofSection thstk precs prfSctn)
syncStrategy  thstk precs (RedBoth int prfSctn prfSctn')
 = RedBoth int (syncProofSection thstk precs prfSctn)
               (syncProofSection thstk precs prfSctn')
syncStrategy  thstk precs (LawReduce str sc prfSctn)
 = LawReduce str sc (syncProofSection thstk precs prfSctn)
syncStrategy  thstk precs (Assume pred strat)
 = Assume (changePrecedenceP precs pred) (syncStrategy thstk precs strat)

syncProofSection :: TheoryStack -> [Trie Precs] ->  ProofSection -> ProofSection
syncProofSection thstk precs (fpred, fvset, ttbl, arg)
 = ( syncFPred precs fpred, fvset, ttbl, ( map (syncProofStep precs) arg))

syncFPred precs (pr, ctxt, wayup)
 = (changePrecedenceP precs pr, ctxt, wayup)

-- deprecated
syncArgument :: TheoryStack -> [Trie Precs] -> Argument -> Argument
syncArgument thstk precs (Justify prfStp) =  Justify (syncProofStep precs prfStp)
syncArgument thstk precs (CaseAnalysis bool (prfCse, prfCse'))
 = (CaseAnalysis bool ((map (syncProofCase thstk precs) prfCse),
   (map (syncProofCase thstk precs) prfCse')))

syncProofStep :: [Trie Precs] -> ProofStep -> ProofStep
syncProofStep precs (jstfctn, pred)
 = ((syncJustification precs jstfctn), (changePrecedenceP precs pred))

syncJustification precs (prfrl, fcsPth, infrnc, bndng)
 = (prfrl, fcsPth, (syncInference precs infrnc), (syncBinding precs bndng))

syncInference precs (AlphaSubs esub) = AlphaSubs (syncEsub precs esub)
syncInference precs (Witness esub)   = Witness   (syncEsub precs esub)
syncInference _ infer = infer

syncEsub :: [Trie Precs] -> ESubst -> ESubst
syncEsub precs (Substn list)
 = Substn (map (syncLists precs) list)


syncLists precs (var, expr) = (var, changePrecedenceE precs expr)

syncBinding precs (gpbind, vebind, ttbind)
 = ( tmapT (changePrecedenceP precs) gpbind
   , tmapT (changePrecedenceE precs) vebind
   , ttbind
   )

syncProofCase :: TheoryStack -> [Trie Precs] -> ProofCase -> ProofCase
syncProofCase thstk precs (pred, prfsctn, thryStk)
 = ((changePrecedenceP precs pred), (syncProofSection thstk precs prfsctn),
    (map (precsTheorySync thstk) thryStk))
\end{code}




\begin{code}
syncContext :: Proof -> TheoryStack -> TheoryStack
syncContext proof thystk = map (precsTheorySync thystk) context'
    where context' = context proof
\end{code}

--Synching MatchContext is almost synching a mini Proof or Theory
\begin{code}
syncMatchContext :: Proof -> [Trie Precedences.Precs] -> [MatchContext]
syncMatchContext proof precs = map (changeMatchContext precs) match
    where match =  mtchCtxt proof

changeMatchContext :: [Trie Precedences.Precs] -> MatchContext -> MatchContext
changeMatchContext precs mtchCtxt  = mtchCtxt'
    where mtchCtxt' = mtchCtxt{knownConsts=knownConsts',
                      knownExprs=knownExprs',
                      knownPreds=knownPreds',
                      langDefns=langDefns',
                      mdlObs=(mdlObs mtchCtxt),
                      srcObs=(srcObs mtchCtxt),
                      mdlObs'=(mdlObs' mtchCtxt),
                      srcObs'=(srcObs' mtchCtxt)}
          knownConsts' = syncKnownConsts mtchCtxt precs
          knownExprs'  = syncKnownExprs  mtchCtxt precs
          knownPreds'  = syncKnownPreds  mtchCtxt precs
          langDefns'   = syncKnownLangs  mtchCtxt precs
-- MatchContext Functions
syncKnownConsts :: MatchContext -> [Trie Precedences.Precs] -> [Trie Expr]
syncKnownConsts mtchCtxt precs
    =  map (tmap $ changePrecedenceE precs) knownConsts'
     where knownConsts' = knownConsts mtchCtxt

syncKnownExprs :: MatchContext -> [Trie Precedences.Precs] -> [Trie Expr]
syncKnownExprs mtchCtxt precs
 = map (tmap $ changePrecedenceE precs) knownExprs'
    where knownExprs' = knownExprs mtchCtxt

syncKnownPreds :: MatchContext -> [Trie Precedences.Precs] -> [Trie Pred]
syncKnownPreds mtchCtxt precs
 = map (tmap $ changePrecedenceP precs) knownPreds'
    where knownPreds' = knownPreds mtchCtxt

syncKnownLangs :: MatchContext -> [Trie Precedences.Precs] -> [Trie [LangDefn]]
syncKnownLangs mtchCtxt precs
    = map (tmap (map changeLanD)) langDef
    where
        changeLanD (pred, predic)
          = (changePrecedenceP precs pred, changePrecedenceP precs predic)
        langDef = langDefns mtchCtxt

\end{code}

\newpage
\subsection{The Null (Identity?) Synchroniser}

A place holder:
\begin{code}
nullSynchroniser :: Synchroniser
nullSynchroniser
 = ( "Null"
   , "Leaves everything unchanged"
   , \_ -> id
   , \_ -> id
   )
\end{code}

All known synchronisers:
\begin{code}
availableSynchronisers
 = [  nullSynchroniser
   ,  precsSynchroniser
   ]
\end{code}
