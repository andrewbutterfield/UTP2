\section{Theory Bookkeeping}

\begin{code}
module Theories where
import Tables
import Datatypes
import Utilities
import Types
import FreeBound
import MatchTypes
import Proof
import SideConditions
import Laws

import Data.List
import Data.Maybe
\end{code}
We are going to maintain theories as a stack, with theories
above those on which they depend.
All proofs are done w.r.t. the top theory on the stack.
When no proof is underway we allow the stack to be manipulated in a variety
of ways.

A theory is identified by a name-number pair,
while a law within a theory is simply given a name.
A proof cites a given law by specifying the theory-d (name,number)
and the law-name:
\begin{eqnarray*}
   \ell,m,n &\in& Name
\\ u,v \in Version &=& \nat
\\ s,t,n.v \in ThryId &=& Name \times Version
\\ c,n.v.\ell \in Citation &=& ThryId \times Name
\end{eqnarray*}
\begin{code}
type ThryId = (String,Int)
type Citation = (ThryId,String)
\end{code}

With any theory we can associate sets of names of the laws it contains,
as well as the citations it makes:
\begin{eqnarray*}
   LawNames &:& ThryId \fun \power Name
\\ Citations &:& ThryId \fun \power Citation
\end{eqnarray*}
\begin{code}
lawNames :: Theory -> [String]
lawNames = sort . map fst . laws

citations :: Theory -> [Citation]
citations thry
 = (sort. concat . map (proofCites (thryName thry)) . theorems) thry

proofCites :: String -> Proof -> [Citation]
proofCites thisth = (stratCites thisth) . plan

stratCites :: String -> Strategy -> [Citation]
stratCites thisth NoStrategy           = []
stratCites thisth (Reduce ps)          = prfSecCites thisth ps
stratCites thisth (Lhs2Rhs ps)         = prfSecCites thisth ps
stratCites thisth (Rhs2Lhs ps)         = prfSecCites thisth ps
stratCites thisth (RedBoth _ ps1 ps2)
  = prfSecCites thisth ps1 ++ prfSecCites thisth ps2
stratCites thisth (LawReduce ln sc ps) = mkCitation thisth ln ++ prfSecCites thisth ps
stratCites thisth (Assume _ str)       = stratCites thisth str

prfSecCites :: String -> ProofSection -> [Citation]
prfSecCites thisth (_,_,_,args) = concat (map (stepCites thisth) args)

stepCites :: String -> ProofStep -> [Citation]
stepCites thisth ((_,_,inf,_),_) = inferCite thisth inf

argCites :: String -> Argument -> [Citation]
argCites thisth (Justify ((_,_,inf,_),_)) = inferCite thisth inf
argCites thisth (CaseAnalysis _ pcs)
  = concat (map (proofCaseCites thisth) (fst(ringToList pcs)))

proofCaseCites :: String -> ProofCase -> [Citation]
proofCaseCites thisth (_,ps,_) = prfSecCites thisth ps

inferCite :: String -> Inference -> [Citation]
inferCite thisth (NamedLaw _ cite _) = mkCitation thisth cite
inferCite _  _ = []

-- we do not cite ourselves
-- -- BUG - the assumption that thry was non-null here proved
-- --       to be false.

mkCitation :: String -> String -> [Citation]
mkCitation thisth cite
 | null thry       =  [(("???",vno),lname)]
 | isHYPName thry  =  []
 | thry == thisth  =  [] -- temp
 | otherwise       =  [((thry,vno),lname)]
 where (thry,vno,lname)= qparse cite
\end{code}
Version numbers are used to track the addition of new laws
to theories --- a theory of higher version number
always contains strictly more laws than one with a lower
version number:
\begin{eqnarray*}
  v > u \implies LawNames(n.v) \supset LawNames(n.u)
\end{eqnarray*}
Theory $t$ is \emph{version-dependent} on theory $s$
($ t \vdepends s $)
if any of its proofs
cite a law from $s$, where we take version numbers into account.
\begin{eqnarray*}
   \_ \vdepends \_ &:& ThryId \rel ThryId
\\ t \vdepends s &\defs& s \in \power\pi_1 (Citations~t)
\end{eqnarray*}
Theory $t$ is \emph{name-dependent} on theory $s$
($ t \ndepends s $)
if any of its proofs
cite a law from $s$, where we ignore version numbers.
\begin{eqnarray*}
   \_ \ndepends \_ &:& ThryId \rel ThryId
\\ t \ndepends s &\defs& \pi_1~s \in \power(\pi_1 \circ \pi_1)(Citations~t)
\end{eqnarray*}
For now we simply use name-dependence%
\footnote{It's not clear if version dependence is useful.}%
.
It is useful to be able to extract a theories proofDeps:
\begin{eqnarray*}
   Dependencies &:& ThryId \fun \power Name
\\ Dependencies~t &\defs& \power(\pi_1 \circ \pi_1)(Citations~t)
\end{eqnarray*}
\begin{code}
theoryDependencies :: Theory -> [String]
theoryDependencies = nub . sort . map (fst . fst) . citations
\end{code}

It should be stressed that neither version- nor name-dependence
are transitive relations, in general (though they may often be in practice).
Also, we consider them as irreflexive, so $t \not\ndepends t$.

We want to be able to update a Theory to record its
\texttt{proofDeps}:
\begin{code}
markTheoryDeps :: Theory -> Theory
markTheoryDeps thry
 = thry{ proofDeps = theoryDependencies thry }

thisTheory `dependsOn` thatTheory
 = thryName thatTheory `elem` proofDeps thisTheory

depsOf th = syntaxDeps th ++ proofDeps th
\end{code}


We now consider a system consisting of a single theory-stack,
satisfying the invariant that no theory in the stack
occurs more than once or
depends on one above (before) it:
\begin{eqnarray*}
   \tau \in ThryStack &=& ThryId^*
\\ \Inv{ThryStack}~\nil &\defs& True
\\ \Inv{ThryStack}((n.v)\lcons \tau)
   &\defs&
   \Inv{ThryStack}~\tau
\\ && {} \land
   n.v \notin \elems~\tau
\\ && {} \land
   n \notin \bigcup (\power Dependencies (\elems~\tau))
\end{eqnarray*}
\begin{code}
invTheoryStack :: TheoryStack -> Bool
invTheoryStack [] = True
invTheoryStack (theory:theories)
 = not (thname `elem` (map thryName theories))
   &&  not (thname `elem` concat (map theoryDependencies theories))
   && invTheoryStack theories
 where thname = thryName theory
\end{code}
We define a theory-stack to be complete, if for every theory present,
its \texttt{proofDeps} are also present below (after) it:
\begin{eqnarray*}
   Complete &:& ThryId^* \fun \Bool
\\ Complete~\nil &\defs& True
\\ Complete(t\lcons \tau)
   &\defs&
   Complete~\tau
\\&& {} \land
   Dependencies~t \subseteq \power \pi_1 (\elems~\tau)
\end{eqnarray*}
\begin{code}
completeStack :: TheoryStack -> Bool
completeStack [] = True
completeStack (theory:theories)
 = theoryDependencies theory `subseteq` sort (map thryName theories)
   && completeStack theories

-- this function assumes ordered arguments
[] `subseteq` _       =  True
(x:xs) `subseteq` []  =  False
s1@(x:xs) `subseteq` (y:ys)
     | x  < y     =  False
     | x == y     =  xs `subseteq` ys
     | otherwise  =  s1 `subseteq` ys
\end{code}

We want to define an operation to push a new theory onto a stack,
with two pre-conditions: a hard one that requires it not to be one
that is already present or with existing theories that refer to it
(so preserving the invariant),
and a soft one requiring that all the new theories
proofDeps are already present (ensuring completness).
The operation fails if the hard pre-condition is not met,
succeeds with a warning if the soft condition fails,
and succeeds with no warning if both are met.
\begin{eqnarray*}
   pushTheory &:& ThryId \fun ThryStack \pfun ThryStack \times \Bool
\\ \Pre{pushTheory}~(n.v)~\tau
   &\defs&
   n.v \notin \elems~\tau
\\ && {} \land
   n \notin \bigcup (\power Dependencies (\elems~\tau))
\\ pushTheory~t_\tau
   &\defs& (t\lcons\tau,Dependencies~t \subseteq \power \pi_1 (\elems~\tau))
\end{eqnarray*}
%We want to implement the construction of a stack from a list
%of theories in an incremental fashion,
%in order to avoid re-computing pre-conditions and warnings in full
%for every push.
%Our implementation will simply pair the growing stack with the
%set of theory names already present and the set of theories
%upon which the current stack depends.
\begin{code}
pushTheory :: Theory -> TheoryStack -> Maybe (TheoryStack,Bool)
pushTheory thry stack
 | hardfail   =  Nothing
 | softfail   =  Just (thry:stack,False)
 | otherwise  =  Just (thry:stack,True)
 where
   stknames = (nub . sort . map thryName) stack
   stkdeps =  (nub . sort . concat . map proofDeps) stack
   newname = thryName thry
   newdeps = proofDeps thry
   hardfail =  newname `elem` (stknames++stkdeps)
   softfail = not (newdeps `subseteq` stknames)
\end{code}
NOW OBSOLETE:
(Next, a variant, given a main and  reserve stack (inverted)
that identifies, based on dependencies where the theory should
be located, and then rotates the stacks to the theory will end
up on main top. If a theory of the same name is present, then
we rotate to bring it to main top but leave the original theory
in-situ and flag this.)
\begin{code}

insertTheory thry' main
 | alreadyPresent = (False,main)
 | otherwise      = (True,thry':main)
 where
   thname' = thryName thry'

   alreadyPresent = thname' `elem` map thryName main

--    mainAP = locate main []
--    locate main@(thry:mrest) reserve
--     | thname' == thryName thry  =  (main,reserve)
--     | otherwise                 =  locate mrest (thry:reserve)
--    locate [] reserve         =  ([],reserve)
--
--    (mainD,reserveD) = rotatePastDeps sstk []
--    rotatePastDeps [] reserve = ([],reserve)
--    rotatePastDeps main@(mhd:mtl) reserve
--      | dependOnMe main  = rotatePastDeps mtl (mhd:reserve)
--      | otherwise        = (main,reserve)
--    dependOnMe [] = False
--    dependOnMe (thry:thrys)
--     | thname' `elem` proofDeps thry  =  True
--     | otherwise                      =  dependOnMe thrys

\end{code}

Now, something that removes all ``special'' theories from the top of the main stack
(which is the only place any other than ``\_ROOT'' should appear):
\begin{code}
popSPCTheories []  = []
popSPCTheories main@(thry:rest)
 | isSPC thry  =  popSPCTheories rest
 | otherwise   =  main
\end{code}

\subsubsection{Special Theories}

\subsubsection{Proof Local Theory}

When a proof is started, a proof-context (theory)
local to that proof is pushed on top of the proof current stack,
and used for proof-local definitions (e.g. the \texttt{defnPVar} function).
It is discarded once a proof is completed or abandoned.
It and any assumption theories produced by the Assume strategies are known
as ``special'' theories and are saved and restored with the proof.
\begin{code}
pltPrefix = sptName "PLT_"
isPLT thry = pltPrefix `isPrefixOf` (thryName thry)

pltName name = pltPrefix++name

newPLT pnm = nmdNullPrfCtxt (pltName pnm)
\end{code}

Placing a new predicate definition into the topmost PLT theory:
\begin{code}
notePLTPred name pred [] = ("",[]) -- should scream !!!!

notePLTPred name pred (thry:rest)
 | isPLT thry
    =  (thryName thry ,thry{preds=tupdate name pred (preds thry)} : rest)
 | otherwise
   =  (thn', thry:rest')
 where
   (thn',rest') = notePLTPred name pred rest
\end{code}

Making a proof brings all this together:
\begin{code}
makeProof thname cjname pred sc penv uid
 = let penv' = dropTopLaw cjname penv
       pid = cjname
       penv'' = newPLT pid:penv'
       mctxt' = mkMatchContexts penv''
   in Proof thname cjname pred sc NoStrategy False penv'' [] uid mctxt'
\end{code}


\subsection{Adding/Removing Conjectures}

\begin{code}
addConjecture name law thry
 = thry{conjectures=tupdate name law (conjectures thry)}

remConjecture name thry
 = thry{conjectures=tblank name (conjectures thry)}
\end{code}

\subsection{Derived Theory Fixes}

Some values in a theory are derived, i.e., computed from others.

For now, using a \texttt{MatchContext},
we determine the type-tables relevant for each law.
\begin{code}
fixupTheory :: MatchContext -> Theory -> Theory
fixupTheory mctxt thry = thry{ laws = fixupLawTable mctxt $ laws thry }
\end{code}

Fixing up lawtables:
\begin{code}
fixupLawTable :: MatchContext -> LawTable -> LawTable
fixupLawTable mctxt laws = mapsnd (fixupLaw mctxt) laws
\end{code}

Fixing up laws:
\begin{code}
fixupLaw :: MatchContext -> Law -> Law
fixupLaw mctxt ((pr,sc),prov,_)
 | null msgs  =  ((pr',sc),prov,tts)
 | otherwise  =  ((pr',sc),prov,btupdate (-1) (tsingle "!" terrs) tts)
 where
   (pr',tts,msgs) = setPredTypes mctxt pr
   terrs = Tprod $ map terr msgs
   terr msg = Terror msg Tarb
\end{code}



\subsection{Full Law Lookup}

We want to search for a law by name through theory stacks,
returning the law, along with information about the theory
in which it was found:
\begin{code}
fullLawLookup :: String -> [Theory] -> [MatchContext]
                 -> Maybe (Law, String, Int, MatchContext)
fullLawLookup lname (thry:thries) (mctxt:mctxts)
 = case lwlookup (laws thry) lname of
     Nothing  ->  fullLawLookup lname thries mctxts
     (Just law)  ->  Just (law,thryName thry,thrySeqNo thry,mctxt)
fullLawLookup _ _ _ = Nothing
\end{code}

\subsection{Assertion Conditioning}

We want to condition assertions, with respect to a stack of theories,
so that the use of \texttt{Var} and \texttt{Evar} satisfy
the following guidelines:
\begin{description}
  \item[Var v]
    if $v$ is known (\texttt{obs},\texttt{consts}),
    or bound.
  \item[Evar v]
    if $v$ is known (\texttt{exprs}) or cited in the side-condition.
\end{description}
\begin{code}
conditionAsn :: [Theory] -> Assertion -> Assertion
conditionAsn theories (lawpred,sc)
 = (mapP (condPred [],condExpr []) lawpred,sc)
 where

   known sel = foldl mrgnorm [] (map (trieDom . sel) theories)
   knownVars = known obs `mrgnorm` known consts
   knownEVars = known exprs `mrgnorm` (trieDom . fst . partitionSC) sc

   condPred bvs (Forall _ qvs bpr)
    = Forall 0 qvs (condPred bvs' bpr)
    where bvs' = bvs `mrgnorm` lnorm (getqvars qvs)
   condPred bvs (Exists _ qvs bpr)
    = Exists 0 qvs (condPred bvs' bpr)
    where bvs' = bvs `mrgnorm` lnorm (getqvars qvs)
   condPred bvs (Exists1 _ qvs bpr)
    = Exists1 0 qvs (condPred bvs' bpr)
    where bvs' = bvs `mrgnorm` lnorm (getqvars qvs)

   condPred bvs (Sub bpr (Substn sub))
    = Sub (condPred bvs' bpr) $ Substn (ssub' ++ msub)
    where (ssub,msub) = sPartition sub
          bvs' = bvs `mrgnorm` lnorm (map fst ssub)
          ssub' = mapsnd (condExpr bvs) ssub

   condPred bvs pr = mapP (condPred bvs,condExpr bvs) pr
\end{code}

Variables are viewed as \texttt{Var}s unless they are mentioned
in side-conditions or known
as \texttt{Evar}s.
\begin{code}
   condExpr bvs e@(Var v)
    | v `elemn` bvs                =  e
    | varKey v `elemn` knownEVars  =  Evar v
    | otherwise                    =  e

   condExpr bvs e@(Evar v)
    | v `elemn` bvs                =  Var v
    | varKey v `elemn` knownEVars  =  e
    | otherwise                    =  Var v

   condExpr bvs (Setc _ qvs rpr be)
    = Setc 0 qvs (condPred bvs' rpr) (condExpr bvs' be)
    where bvs' = bvs `mrgnorm` lnorm (getqvars qvs)

   condExpr bvs (Seqc _ qvs rpr be)
    = Seqc 0 qvs (condPred bvs' rpr) (condExpr bvs' be)
    where bvs' = bvs `mrgnorm` lnorm (getqvars qvs)

   condExpr bvs (Esub be (Substn sub))
    = Esub (condExpr bvs' be) $ Substn (ssub' ++ msub)
    where (ssub,msub) = sPartition sub
          bvs' = bvs `mrgnorm` lnorm (map fst ssub)
          ssub' = mapsnd (condExpr bvs) ssub


   condExpr bvs e = mapE (condPred bvs,condExpr bvs) e
\end{code}


\subsection{Reconciling Theory Bundles}

OBSOLETE --- SUPERSEDED BY EDIT FACILITY
We have a new theory (without proofs)
and the old (original) theory.
We want to add the old proofs into the new theory,
provided the old laws are present and unchanged in the theory.
If not, we want to know which laws have become invalidated
so we can downgrade the appropriate laws/theorems to conjectures.
\textbf{Todo: }need to check other theory components for changes.

For now, we only handle laws,
as their impact can be accurately measured.
\begin{code}
reconcileBundle newthry oldthry
 = (newthry',lawConflicts,[newImpact])
 where

   lawConflicts = conflictLookup sameLaw lawConflict
                   (sortBy nameOrder (laws newthry))
                   (sortBy nameOrder (laws oldthry))

   (newthry',newImpact)
    = assessConflictImpact lawConflicts
                           newthry{theorems=theorems oldthry}

--    (rstk',rsrvImpact)
--       = unzip (map (assessConflictImpact lawConflicts) [])

-- reconcileBundle newthry oldthry rstk

nameOrder (nm1,_) (nm2,_) = compare nm1 nm2
\end{code}

\subsubsection{Searching for Conflicts}

It'll help to have a conflict datatype:
\begin{code}
data Change = Del | Add | Mod deriving (Eq,Ord,Show)

data Item = TD | CD | ED | PD | OB | PR | LNG | TY | LW
            deriving (Eq,Ord,Show)

data Conflict = Conflict Change Item String deriving (Eq,Ord)

instance Show Conflict where
 show (Conflict chg itm str)
   = show chg ++ "-" ++ show itm ++ "(" ++ str ++")"
\end{code}

So, basically we compare corresponding components
of new and old theories, flagging any changes (additions, deletions
or modifications) that might compromise the soundness of proof steps.
These are then reported back for further handling.

Conflict lookup takes two ordered lists of (name,thing) pairs,
along with a thing-equivalence function
and a function that converts a comparison into a possible conflict.
\begin{code}
conflictLookup :: (t -> t -> Bool)
                     -> (Ordering -> String -> [Conflict])
                     -> [(String,t)] -> [(String,t)]
                     -> [Conflict]

conflictLookup eqv conf newthings oldthings
    = cL newthings oldthings
    where

      cL _ [] = []

      cL [] olds = concat $ map (conf GT . fst) $ olds

      cL newthings@((newnm,newthing):newrest)
         oldthings@((oldnm,oldthing):oldrest)
       = case newnm `compare` oldnm of
          LT  ->   conf LT newnm ++ cL newrest oldthings
          GT  ->   conf GT oldnm ++ cL newthings oldrest
          _   ->   confEQ        ++ cL newrest oldrest
       where confEQ = if newthing `eqv` oldthing
                       then []
                       else conf EQ newnm
-- end conflictLookup
\end{code}

\subsubsection{Conflict Impact Analysis}

Given a conflict list and a theory,
we search to what theorems, if any, have been invalidated.
Invalid theorems are demoted to conjectures,
and removed from the laws component.
\begin{code}
type Impact = ( String   -- theory name
              , [String] -- names of invalidated theorems
              )

assessConflictImpact :: [Conflict] -> Theory -> (Theory,Impact)

assessConflictImpact [] thry  =  (thry,(thryName thry,[]))

assessConflictImpact conflicts thry
 = (thry',(thryName thry,badtheorems))
 where

  thms = theorems thry
  badtheorems = foldl mrgnorm []
                  $ map (assessProofConflicts conflicts) $ thms

  (thms',cnjs') = thremove badtheorems thms
  lws' = lremove badtheorems (laws thry)

  thry' = thry{ laws = lws'
              , theorems = thms'
              , conjectures = conjectures thry `tmerge` lbuild cnjs'
              }

  thremove bad [] = ([],[])
  thremove bad (prf:prest)
   | nm `elemn` bad  =  (prest',(nm,(goal prf,side prf)):cnjs')
   | otherwise       =  (prf:prest',cnjs')
   where
      nm = pname prf
      (prest',cnjs') = thremove bad prest

  lremove bad [] = []
  lremove bad (law@(nm,_):lrest)
   | nm `elemn` bad  =  remrest
   | otherwise       =  law:remrest
   where remrest = lremove bad lrest

-- end assessConflictImpact
\end{code}

We work through the proof sections of a proof
to see if it refers to any conflicted laws.
\begin{code}
assessProofConflicts :: [Conflict] -> Proof -> [String]

assessProofConflicts conflicts proof
 = assess (plan proof)
 where

   nm = pname proof
   assess NoStrategy                            =  []
   assess (Reduce (_,_,_,arg))                  =  assessArgs arg
   assess (Lhs2Rhs (_,_,_,arg))                 =  assessArgs arg
   assess (Rhs2Lhs (_,_,_,arg))                 =  assessArgs arg
   assess (RedBoth brno (_,_,_,la) (_,_,_,ra))  =  assessArgs (la++ra)
   assess (Assume pr strategy)                  =  assess strategy
   assess (LawReduce lnm sc (_,_,_,arg))
    | lnm `lawIn` conflicts  =  [nm]
    | otherwise              =  assessArgs arg

   assessArgs [] = []
   assessArgs (((_,_,inf,_),pr):args)
    | null impact  =  assessArgs args
    | otherwise    =  impact
    where impact = assessInf inf

   assessInf (NamedLaw _ lname _)
    | lname `lawIn` conflicts  =  [nm]
    | otherwise                =  []
   assessInf _ = []

   lname `lawIn`  []  =  False
   lname `lawIn`  ((Conflict _ LW nm):rest)
    | lname == nm  =  True
    | otherwise    =  lname `lawIn` rest
   lname `lawIn` (_:rest) =  lname `lawIn` rest

-- end assessProofConflicts
\end{code}


\subsubsection{Component Conflict Details}

Laws are the same if the predicates are,
modulo liberal type equivalence, and ignoring inferred types,
with logically equivalent side-conditions,
and ignoring provenance
Law conflicts arise if they are changed or missing.
\begin{code}

((pred1,sc1),_,_) `sameLaw` ((pred2,sc2),_,_)
  = pred1 `pequiv` pred2
    && normaliseSC sc1 == normaliseSC sc2

lawConflict GT name = [Conflict Del LW name]
lawConflict EQ name = [Conflict Mod LW name]
lawConflict _ _     = []

\end{code}



\subsection{Theory Summary}


\begin{code}
theoremsSummary thry
 = unlines (
             ( "Theorem Summary for "
              ++ thryName thry
              ++ thrySepS
              ++ show (thrySeqNo thry)
             )
             : ""
             : map proofSummary (theorems thry)
           )
\end{code}

\subsection{Law Template Matching}

Given a template and list of theories
we return a list of those laws that might match that template:
(\textbf{Do we need \texttt{TypeTables} here ?})
\begin{code}
type LawTemplateMatch
 = ( MatchType  --  type of matching
   , String  --  theory name
   , String  --  law name
   , Assertion  --  entire assertion
   )

templateLawMatchTheories :: Pred -> [Theory] -> [LawTemplateMatch]
templateLawMatchTheories tpr theories
 = concat $ map (templateLawMatchTheory (mkMatchContext theories) tpr)
                theories

templateLawMatchTheory mctxt tpr theory
 = concat $ map (templateLawMatch mctxt (thryName theory) tpr)
          $ laws theory

templateLawMatch mctxt thname tpr (lname,law@(ass,prov,_))
 = let patterns = filter notTREqv $ lawMatchPossibilities law
   in catMaybes $ map doMatch patterns
 where

   notTREqv (TREqv, _, _, _, _)  =  False
   notTREqv _                    =  True

   doMatch (mtyp, ppr, _, tts, _)
    = do binds <- lawMatch [] (FVSet []) Bnil mctxt SCtrue ppr (tpr, SCtrue) tts
         -- not reversal of test and pattern here !
         return (mtyp, thname, lname, ass)
-- templateLawMatch
\end{code}


\subsection{Theorems Checking}

We want to check that theorems and laws are consistent:
\begin{code}
theoremCheck :: Theory -> [String]
theoremCheck thry
 = let
    thlaws = sort $ laws thry
    ththeorems = sortBy theoremByName $ theorems thry
   in filter (not . null) $ checkTheorems ththeorems thlaws

theoremByName prf1 prf2 = compare (pname prf1) (pname prf2)

checkTheorems [] _ = []
checkTheorems _ [] = []
checkTheorems prfs@(prf:prfrest) lws@((lnm,law):lwrest)
 = case compare pnm lnm of
    LT  ->  checkTheorems prfrest lws
    GT  ->  checkTheorems prfs lwrest
    EQ  ->  (checkTheorem pnm prf law) : checkTheorems prfrest lwrest
 where
   pnm = pname prf

checkTheorem pnm prf law
 | prfpred /= lawpred  =  pnm ++ thmLawMismatch prfpred lawpred
 | prfsc   /= lawsc    =  pnm ++ thmLawMismatch prfsc lawsc
 | otherwise           =  ""
 where
  prfpred = goal prf
  prfsc   = side prf
  (lawpred, lawsc) = fst3 law
  thmLawMismatch thm law = " - Thm: "++show thm ++ " - Law: " ++ show law
\end{code}
