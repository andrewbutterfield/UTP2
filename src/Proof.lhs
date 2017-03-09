\section{Proof Bookkeeping}

\begin{code}
module Proof where
import Tables
import Datatypes
import Precedences
import MatchTypes
import Matching
import FreeBound
import Utilities
import DataText
import Types
import Focus
import Heuristics
import SideConditions
import Substitution
import Laws
import Manipulation
import DSL
import Files

import Data.List hiding (stripPrefix)
import Data.Char
import Data.Bits
import Data.Int
--import Data.HashTable
import Data.Maybe

import qualified Test.QuickCheck as QC
import Text.ParserCombinators.Parsec.Expr
\end{code}

\subsection{Proof Datatypes}


\subsubsection{Inference}

Identifies the law/inference-rule/transformation that was
used.
\begin{code}
data Inference
  = NamedLaw MatchType String Provenance
  | InstantLaw String Provenance
  | NameReplace
  | NameFold String
  | RecExpand
  | ISubstitute
  | AlphaSubs ESubst
  | ITidy TidySpec
  | ISimplify
  | INorm String -- named normalisation schemes
  | ISplit [Int]
  | IApply
  | UName String
  | Witness ESubst
  | BinderSplit
  | AssertDefined
  | ForallStrip
  | PropagateEq
  deriving (Eq,Ord)

instance Show Inference where
  show (NamedLaw mtype name prov)
    =  name ++ stateMTyp mtype ++ shortProv prov
  show (InstantLaw name prov)
    =  "INSTANTIATE(" ++ name ++")" ++ shortProv prov
  show NameReplace =  "NAME-REPLACE"
  show (NameFold name) =  "NAME-FOLD("++name++")"
  show RecExpand =  "REC-EXPAND"
  show ISubstitute =  "SUBSTITUTE"
  show (AlphaSubs subs) =  "ALPHA-SUBS"++show subs
  show (ITidy tspec) =  "TIDY("++show tspec++")"
  show ISimplify =  "SIMPLIFY"
  show (INorm ns) = "NORMALISE("++ns++")"
  show (ISplit ixs) =  ("SPLIT"++show ixs)
  show IApply =  "APPLY"
  show (UName name) =  ("UNAME="++name)
  show (Witness subs)  =  "WITNESS"++show subs++""
  show BinderSplit = "BINDER-SPLIT"
  show AssertDefined = "ASSERT-DEFINED"
  show ForallStrip = "FORALL-STRIP"
  show PropagateEq = "PROPAGATE-EQ"

\end{code}
When computing the provenance of a proof,
if the inference was a named-law we take the provenance of that law,
otherwise it is given as \texttt{FromSOURCE},
citing the inference data-constructor.
\begin{code}
inferProv :: Inference -> Provenance
inferProv (NamedLaw _ _ prov)  =  prov
inferProv infer =  FromSOURCE (infname infer)

infname NameReplace =   "NameReplace"
infname (NameFold name) =   "NameFold"
infname RecExpand =  "RecExpand"
infname ISubstitute =  "ISubstitute"
infname (AlphaSubs subs) =   "AlphaSubs"
infname (ITidy tspec) =   "ITidy"
infname ISimplify =   "ISimplify"
infname (INorm ns) =  "INorm"
infname (ISplit ixs) =  "ISplit"
infname IApply =  "IApply"
infname (UName name) =  "UName"
infname (Witness subs)  =  "Witness"
infname BinderSplit = "BinderSplit"
infname AssertDefined = "AssertDefined"
infname ForallStrip = "ForallStrip"
infname PropagateEq = "PropagateEq"
infname _ = "unknownInfName"
\end{code}

\subsubsection{Proof-Relation}

The logic-connective connecting successive proof lines
\begin{code}
data ProofRel = IMP | EQV | PMI deriving (Eq,Ord)

instance Show ProofRel where
  show IMP = "==>"
  show EQV = "==="
  show PMI = "<=="
\end{code}

\subsubsection{Justification}

The justification of a proof-step identifies the focus,
the law/transformation applied, and any bindings supplied:
\begin{code}
type Justification = (ProofRel,[Int],Inference,Binding)

justProv :: Justification -> Provenance
justProv (_,_,infer,_) = inferProv infer
\end{code}

\subsubsection{Proof Steps and Sections}

We are defining a structure here that supports proof sections
consisting of predicates separated by justifications,
represented as a pair of the most recent predicate,
coupled with a list of justification-predicate pairs (``proof-steps'')
that work back to the original goal.
So a proof like:
\begin{eqnarray*}
  && Pred_1
\EQV{$just_1$}
\\&& Pred_2
\\&\vdots
\\&& Pred_{n-1}
\EQV{$just_{n-1}$}
\\&& Pred_n
\end{eqnarray*}
would be represented as:
$$
 (Pred_n,\seqof{(just_{n-1},Pred_{n-1}),\ldots,(just_2,Pred_2),(just_1,Pred_1)})
$$
\begin{code}
type ProofStep = (Justification,Pred)
\end{code}

For efficiency, we also store the free-variables of the current
focus in the proof-section --- this is transient information computed
on the fly whenever the predicate part changes,
and is not part of the proof transcript.
\begin{code}
type ProofSection = (FPred,FVSetExpr,TypeTables,[ProofStep])
\end{code}


However, we also like to allow a case-split to occur
wherever a proof-step is possible,
in which case it becomes a list of predicate/proof-section pairs.
The predicate identifies the case condition, and the proof-section
is the justification for that case,
where the case-condition is added as an assumption
(laws) to a new local proof context.
Case-splits end every branch agrees.
The invocation of a case split requires a law that has the form of a
disjunction:
$$
  A_1 \lor A_2 \lor \ldots \lor A_n \equiv True
$$
Given goal $G$ we obtain
$$
 (A_1 \implies G) \land (A_2 \implies G) \land \ldots \land (A_n \implies G)
$$
This is then split into $n$ pieces.
With a case split we need to know when it has closed.
The following was added to support this but in the future
with we integrate it into the justification datatype,
and not the proof-step one.
\begin{code}
data Argument = Justify ProofStep
              | CaseAnalysis Bool (Ring ProofCase)
              deriving (Show)

type ProofCase = (Pred,ProofSection,TheoryStack)
\end{code}


Given a predicate, a strategy might use proof sections to:
\begin{itemize}
  \item Reduce the goal to $True$;
  \item Reduce the lhs of an proof relation to the rhs, or v.v.;
  \item Reduce both lhs and rhs to some common predicate; or
  \item Start with some axiom or pre-existing law and transform that to the goal.
  \item If an implication goal, assume the lhs, and use a strategy
        to handle the rhs.
   This latter case requires careful handling,
   see \S\ref{ssec:Deduction}.
\end{itemize}
\begin{code}
data Strategy = NoStrategy
              | Reduce ProofSection
              | Lhs2Rhs ProofSection
              | Rhs2Lhs ProofSection
              | RedBoth Int ProofSection ProofSection
              | LawReduce String SideCond ProofSection
              | Assume Pred Strategy
              deriving Show
\end{code}
The integer in RedBoth (0,1,2) identifies the active proof section
(1,2) or indicates both are complete (0).

Describing Strategy Details
\begin{code}
strategyHeader NoStrategy  = "No Strategy specified"
strategyHeader (Reduce ps)  = "Reduce to TRUE"
strategyHeader (Lhs2Rhs ps) = "Reduce Left to Right"
strategyHeader (Rhs2Lhs ps) = "Reduce Right to Left"
strategyHeader (RedBoth _ lhs rhs) = "Reduce Both to Same"
strategyHeader (LawReduce ln sc ps)
 = "Reduce from Law '" ++ ln ++ "'" ++ scDispl sc
 where
   scDispl SCtrue = ""
   scDispl sc = ", "++show sc
strategyHeader (Assume cnsq strategy)
 = "Assume, then " ++ strategyHeader strategy
\end{code}

\newpage
\subsubsection{Proof}

A Proof consists of a name, goal predicate
a proof strategy that shows how proof sections
are used to produce the desired outcome,
a boolean flag indicating if the proof is complete,
as well as a list of the contexts (theories) on which the proof depends.
We also provide a field that lists the context names,
to facilitate import/export.
We also note the user responsible for the proof.
\begin{code}
data Proof = Proof{ thname, pname :: String
                  , goal :: Pred
                  , side :: SideCond
                  , plan :: Strategy
                  , done :: Bool
                  , context :: TheoryStack
                  , ctxtNames :: [String]
                  , prover :: String
                  -- derived
                  , mtchCtxt :: [MatchContext]
                  }
             deriving Show

goalSetf f recd = recd{ goal = f $ goal recd }

dummyProof = Proof "-?-" "-dummy-"
               nonsense
               SCtrue
               NoStrategy
               False
               []
               []
               "whodunnit?"
               []

nonsense = PVar $ Std "Nonsense"

proofLaw proof = (pname proof, (goal proof, side proof))

proofHypotheses stk = map laws . filter isHYP $ stk
\end{code}


Given a proof, we often want access to the ``current predicate'':
\begin{code}
currProofState :: Proof -> ((FPred, FVSetExpr), TypeTables)
currProofState proof
 = case (plan proof) of
    NoStrategy  ->  ((setPFocus $ goal proof,fvClosed),Bnil)
    strategy    ->  currStrategyState strategy

currStrategyState :: Strategy -> ((FPred, FVSetExpr), TypeTables)
currStrategyState NoStrategy = error "Proof.currStrategyState NoStrategy"
currStrategyState (Reduce (fpr,fovs,tts,_)) = ((fpr,fovs),tts)
currStrategyState (Lhs2Rhs (fpr,fovs,tts,_)) = ((fpr,fovs),tts)
currStrategyState (Rhs2Lhs (fpr,fovs,tts,_)) = ((fpr,fovs),tts)
currStrategyState (RedBoth 2 _ (fpr,fovs,tts,_)) = ((fpr,fovs),tts)
currStrategyState (RedBoth _ (fpr,fovs,tts,_) _) = ((fpr,fovs),tts)
currStrategyState (LawReduce _ _ (fpr,fovs,tts,_)) = ((fpr,fovs),tts)
currStrategyState (Assume _ strategy) = currStrategyState strategy

currProofGoal :: Proof -> (FPred, FVSetExpr)
currProofGoal = fst . currProofState

setProofGoal :: FPred -> FVSetExpr -> TypeTables -> Proof -> Proof
setProofGoal fpr fovs ttbl proof
 = proof{plan=setStrategyGoal fpr fovs ttbl (plan proof)}

setStrategyGoal :: FPred -> FVSetExpr -> TypeTables -> Strategy -> Strategy
setStrategyGoal fpr fovs ttbl NoStrategy
                      = NoStrategy
setStrategyGoal fpr fovs ttbl (Reduce  (_,_,_,args))
                       = Reduce  (fpr,fovs,ttbl,args)
setStrategyGoal fpr fovs ttbl (Lhs2Rhs (_,_,_,args))
                      = Lhs2Rhs (fpr,fovs,ttbl,args)
setStrategyGoal fpr fovs ttbl (Rhs2Lhs (_,_,_,args))
                       = Rhs2Lhs (fpr,fovs,ttbl,args)
setStrategyGoal fpr fovs ttbl (RedBoth 2 lhs (_,_,_,args))
                       = RedBoth 2 lhs (fpr,fovs,ttbl,args)
setStrategyGoal fpr fovs ttbl (RedBoth brno (_,_,_,args) rhs)
                       = RedBoth brno (fpr,fovs,ttbl,args) rhs
setStrategyGoal fpr fovs ttbl (LawReduce ln sc (_,_,_,args))
                       = LawReduce ln sc (fpr,fovs,ttbl,args)
setStrategyGoal fpr fovs ttbl (Assume cnsq strategy)
                       = Assume cnsq (setStrategyGoal fpr fovs ttbl strategy)


currProofPred :: Proof -> FPred
currProofPred = fst . currProofGoal

setProofPred :: FPred -> TypeTables -> Proof -> Proof
setProofPred fpr tts = setProofGoal fpr fvClosed tts

currProofFVSet :: Proof -> FVSetExpr
currProofFVSet = snd . currProofGoal
\end{code}



Given a proof, we also want the ``target predicate'',
which ends the proof when we transform the current predicate to
be equal to it.
\textbf{(WHY NO CODE HERE ????)}

Pulling out an assertion can be helpful too:
\begin{code}
proofAssertion :: Proof -> Assertion
proofAssertion prf = (goal prf, side prf)
\end{code}



We also want an easy way to add a proof-step:
\begin{code}
addProofStep :: FPred -> Justification -> Proof -> Proof
addProofStep npred just proof
 = proof{plan=addStrategyStep npred just (plan proof)}

addStrategyStep npred just NoStrategy = NoStrategy
addStrategyStep npred just (Reduce (fpr,_,_,args))
                          = Reduce $ addPS npred just fpr args
addStrategyStep npred just (Lhs2Rhs (fpr,_,_,args))
                          = Lhs2Rhs $ addPS npred just fpr args
addStrategyStep npred just (Rhs2Lhs (fpr,_,_,args))
                          = Rhs2Lhs $ addPS npred just fpr args

addStrategyStep npred just (RedBoth 1 (fpr,_,_,args) rhs)
  = RedBoth 1 (addPS npred just fpr args) rhs
addStrategyStep npred just (RedBoth 2 lhs (fpr,_,_,args))
  = RedBoth 2 lhs (addPS npred just fpr args)
addStrategyStep npred just (RedBoth brno lhs rhs)
  = error "addStrategyStep to finished RedBoth !!!"

addStrategyStep npred just (LawReduce ln sc (fpr,_,_,args))
  = LawReduce ln sc $ addPS npred just fpr args

addStrategyStep npred just (Assume cnsq strategy)
  = Assume cnsq (addStrategyStep npred just strategy)

addPS npred just fpr args
 = ( npred
   , fvClosed
   , Bnil
   , (just, clearPFocus fpr):args
   )
\end{code}

Some provenance extraction:
\begin{code}
psProv :: ProofStep -> Provenance
psProv (just,_) = justProv just

argProv :: Argument -> [Provenance]
argProv (Justify ps) = [psProv ps]
argProv (CaseAnalysis _ (pcs1,pcs2)) = concat $ map pcProv $ (pcs1++pcs2)

pcProv :: ProofCase -> [Provenance]
pcProv (_,ps,_) = psecProv ps

psecProv :: ProofSection -> [Provenance]
psecProv (_,_,_,args) = map psProv $ args

strProv :: Strategy -> [Provenance]
strPrv NoStrategy = []
strProv (Reduce ps) = psecProv ps
strProv (Lhs2Rhs ps) = psecProv ps
strProv (Rhs2Lhs ps) = psecProv ps
strProv (RedBoth _ ps1 ps2) = psecProv ps1 ++ psecProv ps2
strProv (LawReduce _ _ ps) = psecProv ps
strProv (Assume _ str) = strProv str

proofProv :: Proof -> Provenance
proofProv prf = viaPROOF $ strProv $  plan prf
\end{code}

Also important is accessing the top-level match context:
\begin{code}
topMtchCtxt :: Proof -> MatchContext
topMtchCtxt prf
 | null mctxts  =  nullMatchContext
 | otherwise    =  head mctxts
 where mctxts = mtchCtxt prf
\end{code}

Sometimes we want to skip any HYP theories on top:
\begin{code}
topNonHYPMtchCtxt :: Proof -> MatchContext
topNonHYPMtchCtxt prf
 | null mctxts  =  nullMatchContext
 | otherwise    =  head mctxts
 where
   mctxts = dropWhile isHYPMatchContext $ mtchCtxt prf
\end{code}

\subsubsection{Proof Display}
We define a level of detail specification
for displaying proofs,
that we call its \emph{verbosity}:
\begin{code}

data Verbosity
 = Verbosity { showThryName
             , showThryNum
             , showLawName
             , showMatchType
             , showProvShort
             , showProvFull
             , showLocation
             , showPBinds
             , showEBinds
             , showTBinds
             , showQBinds
             , focusOnly
             :: Bool }

instance Show Verbosity where
  show vb
    =  "show prel"
    ++ showif (showThryName vb)  ", thry-name "
    ++ showif (showThryNum vb)   ", thry-num "
    ++ showif (showLawName vb)   ", law "
    ++ showif (showMatchType vb) ", match "
    ++ showif (showProvShort vb) ", s-prov "
    ++ showif (showProvFull vb) ", provenance "
    ++ showif (showLocation vb)  ", locn "
    ++ showif (showPBinds vb)    ", pbnds "
    ++ showif (showEBinds vb)    ", ebnds "
    ++ showif (showTBinds vb)    ", tbnds "
    ++ showif (showQBinds vb)    ", qbnds "
    ++ showif (focusOnly vb)    ", focus-only "

showif False _ = ""
showif True  s = s

setThryName f vb     = vb{showThryName = f(showThryName vb)}
setThryNum f vb      = vb{showThryNum = f(showThryNum vb)}
setLawName f vb      = vb{showLawName = f(showLawName vb)}
setMatchType f vb    = vb{showMatchType = f(showMatchType vb)}
setProvShort f vb    = vb{showProvShort = f(showProvShort vb)}
setProvFull f vb    = vb{showProvFull = f(showProvFull vb)}
setLocation f vb     = vb{showLocation = f(showLocation vb)}
setPBinds f vb       = vb{showPBinds = f(showPBinds vb)}
setEBinds f vb       = vb{showEBinds = f(showEBinds vb)}
setTBinds f vb       = vb{showTBinds = f(showTBinds vb)}
setQBinds f vb       = vb{showQBinds = f(showQBinds vb)}
setFocusOnly f vb    = vb{focusOnly = f(focusOnly vb)}

relonly   = Verbosity False False False False False False False False False False False False
terse     = relonly{showLawName=True}
succinct  = terse{showMatchType=True,showLocation=True}
expansive = succinct{showPBinds=True,showEBinds=True,showTBinds=True,showQBinds=True}
showall   = expansive{showThryName=True,showThryNum=True,showProvFull=True}

terseFO     = terse{focusOnly=True}
succinctFO  = succinct{focusOnly=True}
expansiveFO = expansive{focusOnly=True}
showallFO   = showall{focusOnly=True}

\end{code}

We display a proof section's argument list:
\begin{code}
showProofSteps vb [] = ""
showProofSteps vb ((jstfy,pred):rest)
 = showJustification vb jstfy
   ++ "    " ++ show pred ++ "\n"
   ++ showProofSteps vb rest
\end{code}

We now display a justification, with a level of detail
determined by the verbosity argument:
\begin{code}
showJustification vb (prel,fpath,infer,bnds)
 = show prel
   ++ wrapCoz (  showInfer vb infer
              ++ showFPath vb fpath
              ++ showBindings vb bnds )
 where
   wrapCoz "" = ""
   wrapCoz s = "  \""++s++"\"\n"
\end{code}
We show inferences if required,
to the relevant level of detail
\begin{code}
showInfer vb (NamedLaw mt iname prov)
 = showLName vb iname
   ++ showMType (showMatchType vb) mt
   ++ showLProv (showProvShort vb) (showProvFull vb) prov
showInfer vb infer
 | showLawName vb  =  show infer
 | otherwise       =  ""

showLName vb iname
 = concat $ intersperse [qualSep] $ filter (not . null)
   $ [ showif (showThryName vb) thnm
     , showif (showThryNum vb) (show thseq)
     , showif (showLawName vb) lname
     ]
 where (thnm,thseq,lname) = (qparse iname)

showMType False _   =  ""
showMType True  mt  =  stateMTyp mt

showLProv True _ prov  =  shortProv prov
showLProv _ True prov  =  show prov
showLProv _ _   _      =  ""
\end{code}
We show focus paths, if required.
\begin{code}
showFPath vb fpath
 | showLocation vb  =  " @"++(concat $ intersperse "." $ map show fpath)
 | otherwise        =  ""
\end{code}
\begin{code}
showBindings vb (gpbnds,vebnds,ttbnds)
 = showMapLets
     (  showBindTrie showGPObj (showPBinds vb) gpbnds
     ++ showBindTrie showVEObj (showEBinds vb) vebnds
     ++ showBindTrie showTTObj (showTBinds vb) ttbnds
     )

showBindTrie :: (a -> String) -> Bool -> Trie a -> [(String,String)]
showBindTrie _ False trie = []
showBindTrie shObj True trie   = map show2 $ trieFlatten "" trie
 where show2 (str,thing) = (str,shObj thing)

showMapLets [] = ""
showMapLets mlets
 = showMLets " { " mlets ++ " }"
showMLets pre [] = ""
showMLets pre (mlet:mlets)
 = pre ++ showMLet mlet ++ showMLets ", " mlets
showMLet (str,thing) = str ++ " >-> "++thing
\end{code}
We now show a predicate, according to the verbosity specification.
\begin{code}
showPredicate vb fpred
 | focusOnly vb   =  showFOPredicate fpred
 | otherwise      =  show $ getPFTop fpred

showFOPredicate (fpr, _, _, [])  =  show fpr
showFOPredicate (fpr, _, _, [_])  =  ".. "++show fpr++" .."
showFOPredicate (fpr, _, _)  =  "... "++show fpr++" ..."
\end{code}



We produce a textual rendering of a proof script.
First,
the key leader strings, setting up indentations:
\begin{code}
scriptPredLdr           =  "     "
scriptRelLdr prel  =  " "++show prel++"   \" "
scriptBindLdr           =  "         { "
\end{code}

\begin{code}
hm_write = (
    unlines $ [" : Write Current Proof\n",
    "Writes the current proof out to a .txt file or a lateX file."])

proofStateScript vb proof
 = [ (if (done proof) then "C" else "Inc")
     ++ "omplete Proof for '"
     ++ (thname proof) ++ qualSep:(pname proof)
   , ""
   , "Goal : " ++ show (goal proof) ++ showSC (side proof)
   , ""
   , "Strategy: " ++ strategyHeader (plan proof)
   , ""
   ]
   ++ "":(planScript vb (context proof) $ plan proof)

showSC :: SideCond -> String
showSC SCtrue = ""
showSC sc = ", "++show sc

planScript vb _ NoStrategy = ["No Proof Strategy specified"]
planScript vb _ (Reduce (fpr,_,_,args)) = argScript vb (clearPFocus fpr) args
planScript vb _ (Lhs2Rhs (fpr,_,_,args)) = argScript vb (clearPFocus fpr) args
planScript vb _ (Rhs2Lhs (fpr,_,_,args)) = argScript vb (clearPFocus fpr) args
planScript vb _ (RedBoth brno (lfpr,_,_,largs) (rfpr,_,_,rargs))
 = ("LHS:":argScript vb (clearPFocus lfpr) largs) ++ ("RHS:":argScript vb (clearPFocus rfpr) rargs)
planScript vb _ (LawReduce ln sc (fpr,_,_,args)) = argScript vb (clearPFocus fpr) args
planScript vb ctxt (Assume _ subplan)
 = ("Hyps: "++show (length hyps)) : assumeStackScript vb hlaws ++ planScript vb ctxt subplan
 where
  hyps = filter isHYP ctxt
  hlaws = map laws hyps

assumeStackScript :: Verbosity -> [LawTable] -> [String]
assumeStackScript vb [] = []
assumeStackScript vb hypos
 = "Hypotheses: "
    : (intersperse hypline (concat $ map (assumptionScript vb) $ hypos))
 where hypline = " --- "

assumptionScript :: Verbosity -> LawTable -> [String]
assumptionScript vb lawlist = map (lawScript vb) lawlist

lawScript :: Verbosity -> (String,Law) -> String
lawScript vb (lname,((pred,sc),_,_))
 = showLName vb lname ++ " : " ++ show pred ++ showSC sc



argScript :: Verbosity -> Pred -> [ProofStep] -> [String]
argScript vb cpred [] = [scriptPredLdr ++ show cpred]
argScript vb cpred ((jstfy,pred'):rest)
 = argScript vb pred' rest ++ ("":(justifyScript vb jstfy)) ++ ["",scriptPredLdr ++show cpred]

justifyScript vb (prel,fpath,inference,bnds)
  = (   scriptRelLdr prel
     ++ showInfer vb inference
     ++ showFPath vb fpath ++ " \""):(bindScript vb bnds)

bindScript vb (gpbnds,vebnds,ttbnds)
 | null list  =  []
 | otherwise  =  (scriptBindLdr++first):(map (scriptBindLdr++) rest)
 where
   plist = listbinds (showPBinds vb) (flattenTrie gpbnds)
   elist = listbinds (showEBinds vb) (flattenTrie vebnds)
   tlist = listbinds (showTBinds vb) (flattenTrie ttbnds)
   list = plist ++ elist ++ tlist
   (first:rest) = list

listbinds False  _ = []
listbinds True bnds= lbnds bnds
 where
   lbnds [] = []
   lbnds ((k,d):rest) = (k++"-->"++show d):(lbnds rest)
\end{code}

We display a proof section's argument list:
\begin{code}
showArgument vb [] = ""
showArgument vb (Justify (jstfy,pred):rest)
 = showJustification vb jstfy
   ++ "    " ++ show pred ++ "\n"
   ++ showArgument vb rest
showArgument vb ((CaseAnalysis open pcs):rest)
 = (if open then "Open" else "Closed") ++" Case-Split\n"
   ++ showProofCases vb 1 (fst(ringToList pcs))
   ++ showArgument vb rest

showProofCases vb n [] = ""
showProofCases vb n ((casepr,((pr,_,_,_),_,_,arg),_):rest)
  = "Case "++show n++" ("++show casepr++"):\n"
    ++showProofSteps vb arg++"\n"
    ++ show pr++"\n"
    ++ "End Case "++show n
    ++ showProofCases vb (n+1) rest
\end{code}



We also need to be able to undo proof steps:
\begin{code}
hm_undo = (
    unlines $ [" : Undo last proof step\n",
    "Use this if you make a mistake."])

undoStrategy st@(Reduce ps) = (undone,if undone then Reduce ups else st)
  where (undone,ups) = undoProofSec ps
undoStrategy st@(Lhs2Rhs ps) = (undone,if undone then Lhs2Rhs ups else st)
  where (undone,ups) = undoProofSec ps
undoStrategy st@(Rhs2Lhs ps) = (undone,if undone then Rhs2Lhs ups else st)
  where (undone,ups) = undoProofSec ps
undoStrategy st@(RedBoth 1 lhs rhs) = (undone,if undone then RedBoth 1 ulhs rhs else st)
  where (undone,ulhs) = undoProofSec lhs
undoStrategy st@(RedBoth 2 lhs rhs) = (undone,if undone then RedBoth 2 lhs urhs else st)
  where (undone,urhs) = undoProofSec rhs
undoStrategy st@(LawReduce ln sc ps) = (undone,if undone then LawReduce ln sc ups else st)
  where (undone,ups) = undoProofSec ps
undoStrategy (Assume cnsq strategy) = (undone, Assume cnsq strategy')
 where (undone,strategy') = undoStrategy strategy
undoStrategy st = (False,st)
\end{code}

If a proof has been imported, the focus information is lost,
so we need to restore it on an undo:
\begin{code}
undoProofSec ps@(_,_,_,[]) = (False,ps)
undoProofSec ((pr,_,_,_),_,_,((jstfy,pr'):args))
 = (True,(setPFocus pr',fvClosed,Bnil,args))
\end{code}

\newpage
\subsection{Theories}

A \emph{Theory} consists of a series of tables mapping names
to types, expressions, predicates, laws, behaviours, conjectures and theorems,
plus a modification indicator and some derived data (dependencies, etc.)
The tables fall into two classes:
\begin{enumerate}
  \item definition tables, associating constants with names
  \item symbol tables, associating attributes with names
\end{enumerate}
There are four namespaces:
typenames (\texttt{Tvar});
observations variables (\texttt{Var});
expression-names (\texttt{Evar});
and predicate-names (\texttt{PVar}).
Quantified variables do not feature in these tables.
\begin{code}
data Theory
  = Theory { thryName :: String
           , thrySeqNo :: Int
           , syntaxDeps :: [String]        -- String denotes:
           -- definition tables
           , typedefs :: Trie Type         -- TVar
           , consts :: Trie Expr           -- Var
           , exprs  :: Trie Expr           -- Evar
           , preds  :: Trie Pred           -- PVar
           -- symbol tables
           , obs    :: Trie ObsKind        -- Var
           , precs  :: Trie Precs          -- Var
           , lang   :: Trie LangSpec       -- Name
           , types  :: Trie Type           -- Var
           , laws   :: LawTable            -- Name
           , conjectures :: Trie Assertion -- Name
           , theorems :: [Proof]
           -- derived
           , modified :: Modification
           , proofDeps :: [String]
           , langDefs :: Trie [LangDefn]
           }

conjecturesSetf f recd = recd{ conjectures = f $ conjectures recd }
theoremsSetf f recd = recd{ theorems = f $ theorems recd }
\end{code}

We need to track how modified a theory is:
\begin{description}
  \item[Transient]
    Changes not usually worth saving
  \item[Log]
    Changes that need to be saved,
    but don't require a revision increase
  \item[Upgrade]
    Changes worth saving that also warrant a version increase.
\end{description}
\begin{code}
data Modification = Transient | Log | Upgrade deriving (Eq,Ord,Show)
\end{code}

Displaying a theory:
\begin{code}
instance Show Theory where
 show thry = "THEORY "++(fullThryName thry)
           ++ "\n\nType-defs:\n" ++ (show (typedefs thry))
           ++ "\nConstant-defs:\n" ++ (show (consts thry))
           ++ "\nExpression-defs:\n" ++ (show (exprs thry))
           ++ "\nPredicate-defs:\n" ++ (show (preds thry))
           ++ "\nObs:\n" ++ (show (obs thry))
           ++ "\nPrecs:\n" ++ (show (precs thry))
           ++ "\nLanguage:\n" ++ (show (lang thry))
           ++ "\nTypes:\n" ++ (show (types thry))
           ++ "\nLaws:\n" ++ (lawshow (laws thry))
           ++ "\nConjectures:\n" ++ (show (conjectures thry))
           ++ "\nLangDefns:\n"++ (show (langDefs thry))
           ++ "\nTHEORY END"

fullThryName thry = thryName thry ++ qualSep:(show (thrySeqNo thry))
thryNameRoot = takeWhile (not . (==qualSep))

lawshow [] = ""
lawshow ((nm,(law,pv,_)):lws)
 = nm ++ " : " ++ sl law
      ++ " ("++show pv++") "
   ++ '\n':(lawshow lws)
 where
   sl (pr,SCtrue) = show pr
   sl (pr,sc) = show pr ++ ",- " ++ show sc

nmdNullPrfCtxt name = Theory name 0 []
                                   tnil tnil tnil tnil
                                   tnil tnil tnil tnil [] tnil []
                                   Transient [] tnil
nullPrfCtxt         = nmdNullPrfCtxt (sptName "_NULL")
unknownPrfCtxt      = nmdNullPrfCtxt (sptName "_UNKNOWN")
\end{code}

Someties it is useful to display (small) theories
using one entry per line, without headings:
\begin{code}
theoryAsLines :: Theory -> [String]
theoryAsLines thry
 = [ thryName thry ++ qualSep:(show (thrySeqNo thry)) ]
   ++ (lshow show ":"  $ flattenTrie $ obs thry)
   ++ (lshow show "-"  $ flattenTrie $ precs thry)
   ++ (lshow show "^=" $ flattenTrie $ lang thry)
   ++ (lshow show "^=" $ flattenTrie $ typedefs thry)
   ++ (lshow show "^=" $ flattenTrie $ consts thry)
   ++ (lshow show "^=" $ flattenTrie $ exprs thry)
   ++ (lshow show "^=" $ flattenTrie $ preds thry)
   ++ (lshow show ":"  $ flattenTrie $ types thry)
   ++ (lshow id   "="  $ map nmass $ laws thry)
   ++ (lshow assh "?"  $ flattenTrie $ conjectures thry)
 where
   lshow sh _ [] = []
   lshow sh sep ((nm,thing):rest)
     = (nm ++ " " ++ sep ++ " " ++ sh thing) : lshow sh sep rest
   nmass (nm,(ass,pv,_)) = (nm,assh ass)
   assh (pr,SCtrue) = show pr
   assh (pr,sc) = show pr ++ ",- "++show sc
\end{code}


\subsection{Adding/Removing Theory Table entries}

\begin{code}
upd_typedefs nm x th = th{typedefs=tupdate nm x (typedefs th)}
upd_consts nm x th = th{consts=tupdate nm x (consts th)}
upd_exprs nm x th = th{exprs=tupdate nm x (exprs th)}
upd_preds nm x th = th{preds=tupdate nm x (preds th)}
upd_obs nm x th = th{obs=tupdate nm x (obs th)}
upd_precs nm x th = th{precs=tupdate nm x (precs th)}
upd_lang nm x th = th{lang=tupdate nm x (lang th)}
upd_types nm x th = th{types=tupdate nm x (types th)}
upd_laws nm x th = th{laws=lwupdate nm x (laws th)}
upd_conjectures nm x th = th{conjectures=tupdate nm x (conjectures th)}
upd_theorems nm x th
 = th{theorems=thupd x (theorems th)}

thupd x [] = [x]
thupd x (y:ys)
 | pname x == pname y  =  x:ys
 | otherwise           =  y:thupd x ys

rem_typedefs nm th = th{typedefs=tblank nm (typedefs th)}
rem_consts nm th = th{consts=tblank nm (consts th)}
rem_exprs nm th = th{exprs=tblank nm (exprs th)}
rem_preds nm th = th{preds=tblank nm (preds th)}
rem_obs nm th = th{obs=tblank nm (obs th)}
rem_precs nm th = th{precs=tblank nm (precs th)}
rem_lang nm th = th{lang=tblank nm (lang th)}
rem_types nm th = th{types=tblank nm (types th)}
rem_laws nm th = th{laws=lwdelete nm (laws th)}
rem_conjectures nm th = th{conjectures=tblank nm (conjectures th)}
rem_theorems nm th
 = th{theorems=thrmv nm (theorems th)}

thrmv :: String -> [Proof] -> [Proof]
thrmv nm [] = []
thrmv nm (y:ys)
 | nm == pname y  =  ys
 | otherwise      =  y:thrmv nm ys
\end{code}

\subsubsection{Language/Precedence consistency}

Given a list of language specifications,
we will want to ensure that any binary operators so introduced
are included in the precedence table, if not already
present.

The following code sweeps over a whole theory and patches it up
(shouldn't be necessary anymore).
\begin{code}
coverLangBinaryPrec thry
 = thry{precs = precs thry `precDownDate` flattenTrie (lang thry)}

precDownDate :: Trie Precs -> [(String,LangSpec)] -> Trie Precs
precDownDate precs lspecs
 = foldr downdate precs
     (map mkprec . filter (isBinSpec . snd) $ lspecs)   -- $
 where
  p = precTightLang
  mkprec (n,(LangSpec _ ss)) = (fsttok ss,(p,AssocNone))
  fsttok [] = "?????"
  fsttok (SSTok op:_) = op
  fsttok (s:ss) = fsttok ss
  downdate (n,prc) precs = tdowndate n prc precs
\end{code}

\subsection{Definition Laws}

A definition law is a law of the form $lhs \equiv rhs$,
with a lawname prefixed with "DEF ".
The $lhs$ component will be an instance of the construct/concept/function
under definition, whilst the $rhs$ will typically be its expansion
as some predicate.
\begin{code}
defnNamePrefix = "DEF "
isDefnName lawname = defnNamePrefix `isPrefixOf` lawname
getDefnPreds (PApp nm [lhs,rhs]) | nm == n_Eqv  =  Just (lhs,rhs)
getDefnPreds _              =  Nothing
\end{code}

It can useful to pull out such definitions,
removing the prefix on the fly,
as well as partitioning $lhs$ and $rhs$
(and keeping side-conditions along)
\begin{code}
findDefns :: LawTable -> [(String,Pred,Pred,SideCond)]
findDefns lawtable = fd [] lawtable
 where

  fd defns [] = defns

  fd defns ((lname,(((PApp nm [lhs,rhs]),sc),_,_)):rest)
   | nm == n_Eqv
      = case (stripPrefix defnNamePrefix lname) of
          Nothing  ->  fd defns rest
          Just defnm  ->  fd ((defnm,lhs,rhs,sc):defns) rest

  fd defns (_:rest) = fd defns rest
\end{code}

First,
given a complete language construct (name and syntax-spec.)
we generate a conservative definition entry,
as well as a precedence entry.
\begin{code}
genDummyLangDefn user lname lspec
 = (dname,llaw)
 where
   dname = defnNamePrefix++lname
   llaw = ((lass,SCtrue),UserDEFN user,Bnil)
   lass = genDummyLangLHS lname lspec === predUNINT

genDummyLangLHS lname (LangSpec les ss)
 = Lang lname 0 les' ss
 where
   les' = instantiate 0 les

   instantiate _ [] =[]
   instantiate i (le:les) = inst i le : instantiate (i+1) les

   inst i (LVar _)         =  LVar  $ Std  $ "v"++show i
   inst i (LType _)        =  LType $ Tvar $ "t"++show i
   inst i (LExpr _)        =  LExpr $ mkEVar $ preVar $ "e"++show i
   inst i (LPred _)        =  LPred $ PVar $ Std $ "P"++show i
   inst i (LList [])       =  LList []
   inst i (LList (le:_))   =  LList [inst i le]
   inst i (LCount [])      =  LCount []
   inst i (LCount (le:_))  =  LCount [inst i le]
\end{code}


\subsubsection{Language/DEF-laws consistency}
Given a list of language specifications, we will want to ensure
at least one relevant definition is present.
\begin{code}
coverLangDEFs thry = thry
-- DEPRECATED UNTIL LAW EDITS POSSIBLE (at least)
--  = thry{laws = laws thry `defLawCover` flattenTrie (lang thry)}

defLawCover :: LawTable -> [(String,LangSpec)] -> LawTable
defLawCover laws lspecs = genDefLaws laws undefdLang
 where
  nspecs = lnorm lspecs
  lnames = map fst nspecs
  deflaws = lnorm $ catMaybes $ map (defLawLangName . fst)  laws
  undefdLang = deflaws `alrem` nspecs

genDefLaws laws [] = laws
genDefLaws laws ((lname,lspec):lspecs)
 = genDefLaws (genDummyLangDefn "Proof.genDefLaws" lname lspec:laws) lspecs

--genDefLaw (lname,lspec) = ("DEF "++lname,((TRUE,SCtrue),FromSOURCE "Proof.genDefLaw"))
\end{code}



\subsubsection{Language Definitions in Theories}

For every language construct mentioned in the \texttt{lang} component
of a \texttt{Theory},
we expect there to be at least one definition law given in
the \texttt{laws} component.
Given \texttt{(Lang nm \ldots)}
we expect one law named \verb*"DEF nm"
or multiple laws whose names are prefixed by
\verb*"DEF nm ".
\begin{code}
defLawLangName lawname
 = case words lawname of
    ("DEF":langname:_)  ->  Just langname
    _                   ->  Nothing
\end{code}
We want to take these laws and then use them to build the
\texttt{langDefs} component, for use in free/bound variable determination.
We satisfy an invariant that requires any definition list
in the result trie to be non-empty.
A much more important invariant is that these definitions
should not be recursive, as then the free-variable checking will
turn into a potentially non-terminating procedure.
There is nothing preventing other laws giving recursive expansions,
but they cannot be used here.

TODO: RETHINK THIS GIVEN THAT NOT ALL \texttt{Lang} NEED a DEF-law.
\begin{code}
buildLangDefinitions :: Theory -> Theory
buildLangDefinitions thry = thry{ langDefs = lbuild validdefs }
 where
  defns = findDefns (laws thry)
  ldefs = assembleLDefs (lang thry) defns
  validdefs = stripLDefRec ldefs

assembleLDefs langs defns = assLDef [] defns
 where

   assLDef ldefs [] = ldefs
   assLDef ldefs ((nm,lhs,rhs,_):rest)
    | isLang    =  assLDef (alinsnorm (flip(++)) lname [(lhs,rhs)] ldefs) rest
    | otherwise  =  assLDef ldefs rest
    where
     lname = takeWhile (/=' ') nm
     isLang = isJust (tlookup langs lname)

stripLDefRec :: [(String,[LangDefn])] -> [(String,[LangDefn])]
stripLDefRec ldefs
 = filter good ldefs
 where
   defdep (nm,defs) = (nm,lnorm (concat (map (predLang . snd) defs)))
   defdeps = map defdep ldefs
   depclosed = ereltclose defdeps
   baddeps = erelrkernel depclosed
   good (a,_) = not(a `elem` (cdbg (not . null) "Recursive Lang : " baddeps))
\end{code}

\subsection{Theory Stacks}

We will want to manipulate stacks of theories:
\begin{code}
type TheoryStack = [Theory]
\end{code}
The name-space used for \texttt{laws}, \texttt{conjectures}
and \texttt{theorems} is the same, so entries in all three under
the same name must have the same predicate.
A package is \emph{fully verified}, under the above naming convention,
if every law is a theorem.
\begin{code}
isFullyVerified thry
 = lawnames `within` thmnames
 where
   lawnames = sort (map fst (laws thry))
   thmnames = map pname $ theorems thry
\end{code}
Function \texttt{within} assumes both lists are ordered:
\begin{code}
[] `within` bs = True
_  `within` [] = False
as@(a:arest) `within` (b:brest)
 = case compare a b of
     LT -> False
     EQ -> arest `within` brest
     GT -> as `within` brest
\end{code}
We lift lookups at theory component level up to the top-level:
\begin{code}
typedefsLkp nm thry    = tlookup (typedefs thry) nm
constsLkp nm thry      = tlookup (consts thry) nm
exprsLkp nm thry       = tlookup (exprs thry) nm
predsLkp nm thry       = tlookup (preds thry) nm
obsLkp nm thry         = tlookup (obs thry) nm
precsLkp nm thry       = tlookup (precs thry) nm
langLkp nm thry        = tlookup (lang thry) nm
typesLkp nm thry       = tlookup (types thry) nm
lawsLkp nm thry        = lwlookup (laws thry) nm
conjecturesLkp nm thry = tlookup (conjectures thry) nm
theoremsLkp nm thry
 = lkp nm (theorems thry)
 where
   lkp nm [] = Nothing
   lkp nm (p:ps)
    | nm == pname p  =  Just p
    | otherwise      =  lkp nm ps
\end{code}


We allow for a process whereby conjectures with proofs (theorems)
are removed from the table:
\begin{code}
removeTheorems thrms conjs
 = remThms thnames conjs
 where
   thnames = trieDom thrms
   remThms []          conjs = conjs
   remThms (name:rest) conjs
    = case tlookup conjs name of
        Nothing   ->  remThms rest conjs
        (Just _)  ->  remThms rest (tblank name conjs)
\end{code}

\newpage
\subsection{Theory Graphs}

We also need to deal with theories in a graph:
\begin{code}
type TheoryGraph
  = ( RDAG String  -- rooted graph of theory names
    , Trie Theory  -- named theory pool
    )
\end{code}

Pulling a stack w.r.t to a given theory,
from a graph is important.
We have two variants:
\begin{description}
  \item[Hard] The theory stack is only those theories
    actually connected in the graph as descendants of the
    named theory.
  \item[Soft] The theory stack also includes non-Relatives
    of the named theory.
    \\
    \textit{This is dangerous as having two ``soft'' proofs
     on different, initially non-related theories can allow an outcome that requires
     cycles in the graph}
\end{description}
\begin{code}
hardGraphToStack :: String -> TheoryGraph -> TheoryStack
hardGraphToStack thnm (rdag,trie)
 = catMaybes $ map (tlookup trie) (thnm:descs)
 where
   descs = rdDescendants thnm rdag

softGraphToStack :: String -> TheoryGraph -> TheoryStack
softGraphToStack thnm (rdag,trie)
 = catMaybes $ map (tlookup trie) (thnm:(nonrels++descs))
 where
   descs = rdDescendants thnm rdag
   nonrels = rdNonRelatives thnm rdag
\end{code}

Sometimes we want a stack from the whole theory graph:
\begin{code}
graphAsStack :: TheoryGraph -> TheoryStack
graphAsStack (rdag,trie)
 = catMaybes $ map (tlookup trie) thnms
 where
   thnms = rdNamesOf rdag
\end{code}

Given a stack, it is useful to be able to rebuild the trie components
of a graph:
\begin{code}
stackToTrie :: TheoryStack -> Trie Theory
stackToTrie []        =  tnil
stackToTrie (th:ths)  =  tupdate (thryName th) th $ stackToTrie ths
\end{code}

\subsubsection{Qualified Names}

Given a law ``Lname'', qualified as being in version $v$ of proof context ``Pname'',
we build a complete reference string to the law by concatenating the
components, qualifiers first, separated by a special character:

((``Pname'',$v$),``Lname'') becomes ``Pname\$v\$Lname''.

\begin{code}
qualSep = '$'
thrySepS = [qualSep]
\end{code}

We can render such names, given the qualifiers:
\begin{code}
qprint (pcname,vno) = pcname ++ qualSep:(show vno)

qlawprint2 quals lname = (qprint quals) ++ qualSep:lname
qlawprint3 (pcn,v,ln) = (qprint (pcn,v)) ++ qualSep:ln

pcqname thry = qprint (thryName thry,thrySeqNo thry)

mkpid tname lname -- when we don't want theory seqnos
 = tname ++ qualSep:lname
\end{code}
We can parse such  names, giving back the qualifiers and law-name,
and dealing with partial information.
Valid forms of qualified name are:

\begin{tabular}{|l|l|r|l|l|}
  \hline
     Spec & Theory & Seq & Tgt & action
  \\\hline
     \texttt{name} & - & - & \texttt{name} & lookup \texttt{name} in PCs, returning first found
  \\\hline
     \texttt{thry\$name} & \texttt{thry} & - & \texttt{name} & lookup \texttt{name} in PC \texttt{thry}
  \\\hline
     \texttt{thry\$123\$name} & \texttt{thry} & \texttt{000} & \texttt{name} & lookup \texttt{name} in PC \texttt{thry}, version at or after 123
  \\\hline
\end{tabular}

\begin{code}
qparse name
 | qlen == 1  =  (""  ,  (-1),   name)
 | qlen == 2  =  (q2pc,  (-1), q2name)
 | qlen == 3  =  (q3pc, q3seq, q3name)
 | otherwise  =  (""  ,  (-1),     "")
 where
   qs = qualSplit name
   qlen = length qs
   [q2pc,q2name] = qs
   [q3pc,q3ss,q3name] = qs
   q3seq = getint q3ss

qualSplit = qsplit [] ""
 where
  qsplit stilps garf [] = reverse (reverse garf:stilps)
  qsplit stilps garf (c:cs)
    | c == qualSep  =  qsplit (reverse garf:stilps) "" cs
    | otherwise     =  qsplit stilps (c:garf) cs
\end{code}

The correctness of the print/parse relationship here requires
that \texttt{qualSep} does not appear in names%
\footnote{This needs to be enforced by the GUI!}%
.
\begin{code}
validQName name = not (qualSep `elem` name)

prop_qcorrect (pcn,v,ln) =
  validQName (pcn++ln)
   QC.==>  (pcn,v,ln) == qparse (qlawprint3 (pcn,v,ln))
\end{code}


\subsubsection{Proof Environments}

The proof environment is basically the stack of theories
in the proof datatype.
We provide a number of handy access functions for these.
For historical reasons, the theory stack will be referred to below
as ``\texttt{pe}''.
The name in each context entry is derived
from the proof context data
\begin{code}
ctxtEntryFullName root seq = root++qualSep:(show seq)
\end{code}

We define a very flexible search function on proof theory-stacks
that takes a triple,
(the result of doing a ``\texttt{qualSplit}'' on a name,
and then tailors the search appropriately.

\begin{tabular}{|c|c|c|l|}
  \hline
    \texttt{pcname} & \texttt{seq} & \texttt{tgtname} & search
  \\\hline
    ``'' & $v$ & \emph{tgt} & lookup \emph{tgt} in any theory, version ${}>v$
  \\\hline
    \emph{thry} & $v$ & \emph{tgt} & lookup \emph{tgt} in \emph{thry}, version ${}>v$
  \\\hline
\end{tabular}

Its next argument is a function taking a string and looking up one
of the components of a \texttt{Theory}.
\begin{code}
qualLookup (pcname,seq,tgtname) lkpf [] = Nothing
qualLookup (pcname,seq,tgtname) lkpf (pc:pcs)
  | seq <= thrySeqNo pc
    && ( pcname == "" || pcname == thryName pc)
     =   case lkpf tgtname pc of
           result@(Just _)  ->  result
           Nothing          ->  qualLookup (pcname,seq,tgtname) lkpf pcs
  | otherwise  = qualLookup (pcname,seq,tgtname) lkpf pcs
\end{code}

We define some useful builder and access functions:
\begin{code}
setTopConjectures conj mstk = top{ conjectures = conj }:rest
 where (top:rest) =  mstk

setTopTheorems thms mstk = top{ theorems = thms }:rest
 where (top:rest) =  mstk

-- currentTheories = map fst . contexts

lkpProofEnv tbl name mstk = lkpStack name (map tbl mstk)

lkpStack name [] = []
lkpStack name (tr:trs)
 = case tlookup tr name of
     Nothing       ->  lkpStack name trs
     (Just thing)  ->  thing:(lkpStack name trs)
\end{code}

It is useful to be able to get at the named theories
\begin{code}
thlookup n [] = Nothing
thlookup n (th:ths)
     | n == thryName th  =  Just th
     | otherwise         =  thlookup n ths

getTheoryObservables thname mstk
 = case thlookup thname mstk of
     Nothing      ->  tnil
     (Just thry)  ->  sbuild (getObservables thry)

getObservables pc = trieDom (obs pc)
\end{code}

\newpage
\subsubsection{Proof Environment Matching}

Matching needs to be done using context information,
both from the relationship of the current focus to the
overall goal (\texttt{ctxt}) and in terms of the theories
currently in scope (\texttt{mstk}).
\begin{code}
matchInProofEnv :: MatchFilter -> RankHeuristic -> MatchPostProcess
                   -> FContext -> FVSetExpr -> TypeTables
                   -> SideCond -> FPred
                   -> [Theory] -> [MatchContext]
                   -> [(RankedMatch,MatchContext)]
matchInProofEnv f r p fctxt fovs tts sc fpr thrys mctxts
  = rankMatches f r p
    $
    matchInProofContexts fovs fctxt tts sc fpr thrys mctxts
\end{code}

We have to remove any occurrence of a law with the same name as the conjecture
from the top theory (the conjecture's own).
This situation arises when we redo an existing proof.
\begin{code}
dropTopLaw :: String -> [Theory] -> [Theory]
dropTopLaw _ []  =  []
dropTopLaw cjname (topthry:rest) = topthry' : rest
 where
   topthry' = topthry{laws = filter (notcalled cjname) $ laws topthry}
   notcalled nm (lnm,_) =  lnm /= nm
\end{code}


We build a stack of \texttt{MatchContext} from a \texttt{TheoryStack}:
\begin{code}
mkMatchContext thrys
 = deriveMatchContext
     nullMatchContext{
        mcThName = thryName $ head thrys
      , knownObs = envObs thrys
      , knownTypes = envAllTypes thrys
      , knownConsts = envConsts thrys
      , knownExprs = envExprs thrys
      , knownPreds = envPreds thrys
      , langDefns = envLDefs thrys
      , mdlObs = [], mdlObs' = []
      , srcObs = [], srcObs' = []
      }

mkMatchContexts [] = []
mkMatchContexts thrys@(_:rest)
 = mkMatchContext thrys : mkMatchContexts rest
\end{code}
\textbf{Important}: when we upgrade to using rDAGs to connect theories,
then we need to ensure that the match-contexts respect the rDAG,
and not the way in which the theories are stacked in a proof.


Useful accessors:
\begin{code}
envObs      thrys  =  map obs thrys
envTypes    thrys  =  map types thrys
envTypeDefs thrys  =  map typedefs thrys
envAllTypes thrys  =  map alltypes thrys
envConsts   thrys  =  map consts thrys
envExprs    thrys  =  map exprs thrys
envPreds    thrys  =  map preds thrys
envLaws     thrys  =  map laws thrys
envConj     thrys  =  map conjectures thrys
envThms     thrys  =  map theorems thrys
envLDefs    thrys  =  map langDefs thrys

allvars thrys  = (tmap (Var . fst3) $ obs thrys) `tmerge` exprs thrys
alltypes thrys = (tmap thd3         $ obs thrys) `tmerge` types thrys
\end{code}

Finally, we provide a way of taking a proof and synchronising
an updated theory stack with its context:
\begin{code}
synchroniseProofContext :: TheoryStack -> Proof -> Proof
synchroniseProofContext thstk proof
 = let thstk' = merge (context proof) thstk
       mctxts' = mkMatchContexts thstk'
   in proof{ context=thstk', mtchCtxt=mctxts' }
 where
   merge [] thstk = thstk
   merge (th:ths) thstk
    | isSPTName $ thryName th  =  th : merge ths thstk
    | otherwise                =  thstk
\end{code}


\subsubsection{Proof Matching}

\begin{code}
matchInProofContexts :: FVSetExpr -> FContext
                        -> TypeTables -> SideCond -> FPred
                        -> [Theory] -> [MatchContext]
                        -> [(String,MatchContext,[(LawMatch,String)])]

matchInProofContexts fovs fctxt ttts tsc tfpr (thry:thrys) (mctxt:mctxts)
 = (thnm,mctxt,thryMtchs) : matchInProofContexts fovs fctxt ttts tsc tfpr thrys mctxts
 where
   lawsFound = findLaws fctxt fovs ttts mctxt tsc tfpr (laws thry)
   thryMtchs = map matchFixup lawsFound

   thnm = thryName thry
   matchFixup (lmatch,lname) = (lmatch,name'++lname)
   name' = name++[qualSep]
   name = thnm ++ qualSep:(show (thrySeqNo thry))

matchInProofContexts _ _ _ _ _ _ _ = []
\end{code}

Stuff:
\begin{code}
penamed self thry = (thryName thry, self thry)

envNmdCtxtTypes mstk = map (penamed types) mstk
envNmdCtxtExprs mstk = map (penamed exprs) mstk
envNmdCtxtPreds mstk = map (penamed preds) mstk
envNmdCtxtLaws  mstk = map (penamed laws) mstk
envNmdCtxtConj  mstk = map (penamed conjectures) mstk
envNmdCtxtThms  mstk = map (penamed theorems) mstk

addLaw name law@(pred,sc,ttbl) (pc:rest) -- updates the top-most context
 = pc{laws=(name,law):(laws pc),modified=Upgrade} : rest
\end{code}


We will want to post-process any change to the current (goal) predicate
to ensure that the underlying type of any \texttt{PExpr} component is correctly set:
\begin{code}
fixFType :: TheoryStack -> FPred -> (FPred, TypeTables)
fixFType mstk fpr = fpredTypeTables (mkMatchContext mstk) fpr

fixType :: TheoryStack -> Pred -> (Pred, TypeTables)
fixType mstk pr = predTypeTables (mkMatchContext mstk) pr

ushow  = ushow' . clearPFocus
ushow' (PExpr e) = "PExpr("++show e++")"
ushow' pr = fst5 (predParts pr) ++ "(" ++ show pr  ++")"
\end{code}




\subsubsection{Activating a Proof}

When we import a proof we need to make it ``live''
by setting focii on all the current predicates of proof sections.
No Longer required --- proof current goal always has a focus.
\begin{code}
makeLive :: Proof -> Proof

makeLive = id  -- proof = proof{plan=activatePlan (plan proof)}
\end{code}


\subsection{Special Proof Theories}

We have proof-contexts/theores that perform special roles.
They are identified as having names that start with underscores.

\begin{code}
sptPrefix = '_'

sptName = (sptPrefix :)

isSPTName "" = False
isSPTName (c:_) = c == sptPrefix
\end{code}


We also introduce the notion of standard theories
vs. special (internal) ones, the latter whose names
start with an underscore.
\begin{code}
isSTDName "" = False
isSTDName (c:_)
 | c == '_'   =  False
 | otherwise  =  True

isSTD = isSTDName . thryName

isSPCName "" = False
isSPCName (c:_)
 | c == '_'   =  True
 | otherwise  =  False

isSPC = isSPCName . thryName
\end{code}

\subsection{Specifying Proof Strategies}

Initially, when a goal predicate is loaded into a proof,
the strategy set is NoStrategy.
We then pick an appropriate strategy using a strategy-specifier,
and describe when a strategy is compatible:
\begin{code}
data StratSpec
  = SSRed | SSL2R | SSR2L | SSRB | SSLwR | SSInd | SSAss StratSpec
  deriving (Eq,Ord)

instance Show StratSpec where
  show SSRed      = "Reduce"
  show SSL2R      = "Lhs-to-Rhs"
  show SSR2L      = "Rhs-to-Lhs"
  show SSRB       = "Reduce-Both"
  show SSLwR      = "Reduce-Law"
  show SSInd      = "Induction"
  show (SSAss ss) = "Assume, then "++show ss

isSCompatible SSRed         _ = True
isSCompatible SSL2R (PApp nm [_,_]) | nm == n_Eqv  = True
isSCompatible SSR2L (PApp nm [_,_]) | nm == n_Eqv  = True
isSCompatible SSRB  (PApp nm [_,_]) | nm == n_Eqv  = True
isSCompatible SSLwR         _ = True
isSCompatible SSInd         _ = True
isSCompatible (SSAss subs) (PApp nm [_,rhs])
 | nm == n_Imp  = isSCompatible subs rhs
isSCompatible     _        _  = False
\end{code}

This could be broadened in the future to allow L2R/R2L reduction
of implication goals.

Not currently handled is splitting an equivalence into two reductions.

\newpage
\subsection{Setting Proof Strategies}

\begin{code}
setStrategy :: [Theory] -> StratSpec -> Proof -> TypeTables -> (Proof,[Theory])
\end{code}

The reduction strategy (\texttt{SSRed}) simply involves starting
with the entire goal, and reducing it down to TRUE.
\begin{code}
setStrategy penv SSRed proof tts
  = ( proof{ plan=Reduce (setPFocus (goal proof),fvClosed,tts,[])
           , done=False}
    , [] )
\end{code}

The applicability of other strategies depends
on the structure of the goal.
\begin{code}
setStrategy mstk str proof tts
 = case (goal proof) of
\end{code}

If the goal has  the form $P \equiv Q$ or $P = Q$ then three strategies apply:

\begin{tabular}{|l|l|}
   \hline
     \texttt{SSL2R} & take $P$ and transform it into $Q$
   \\\hline
     \texttt{SSR2L} & take $Q$ and transform it into $P$
   \\\hline
     \texttt{SSRB} & transform both $P$ and $Q$ to a third form $R$
   \\\hline
\end{tabular}

\begin{code}
    PApp nm [lhs,rhs] | nm == n_Eqv
     -> case str of
         SSL2R  ->  ( prf'{plan=Lhs2Rhs (setPFocus lhs,fvClosed,tts,[])}, [] )
         SSR2L  ->  ( prf'{plan=Rhs2Lhs (setPFocus rhs,fvClosed,tts,[])}, [] )
         SSRB   ->  ( prf'{plan=RedBoth 1 (setPFocus lhs,fvClosed,tts,[])
                                        (setPFocus rhs,fvClosed,tts,[])}, [] )
         _      ->  ( proof, [] )

    PExpr (App nm [lhs,rhs]) | nm == n_Equal
     -> case str of
         SSL2R  ->  ( prf'{plan=Lhs2Rhs ( setPFocus (PExpr lhs)
                                        , fvClosed, tts, []) }
                    , [] )
         SSR2L  ->  ( prf'{plan=Rhs2Lhs ( setPFocus (PExpr rhs)
                                        , fvClosed, tts, []) }
                    , [] )
         SSRB   ->  ( prf'{plan=RedBoth 1 ( setPFocus (PExpr lhs)
                                          , fvClosed, tts, [])
                                          ( setPFocus (PExpr rhs)
                                          , fvClosed, tts, []) }
                    , [] )
         _      ->  ( proof, [] )
\end{code}

\newpage
If the goal has  the form $P \implies Q$ then one strategy applies

\begin{tabular}{|l|l|}
   \hline
     \texttt{SSAss} & assume $P$, and then prove $Q$
   \\\hline
\end{tabular}

\begin{code}
    imp@(PApp nm [lhs,rhs]) | nm == n_Imp
     -> case str of
        (SSAss subs) ->
         let (hypos,cnsq) = assumptionSplit imp in
         let (assTh,hfv) = mkAssumptionTheory (pname proof) hypos mstk in
         let (subprf,substk) = setStrategy mstk subs
                                   prf'{goal=cnsq,plan=NoStrategy} tts
         in
          ( prf'{ plan=Assume cnsq (plan subprf) }
          , substk++[assTh]
          )
        _ -> ( proof, [] )
\end{code}

For  goals of any other form then no special strategies
are available.
\begin{code}
    _ -> ( proof, [] )
 where
   prf' = proof{done=False}
\end{code}

For the reduce-from-law strategies, we need a law argument.
\begin{code}
setLawReduce (nlaw,(lgoal,sc)) tts proof
 = proof{ plan=LawReduce nlaw sc (setPFocus lgoal,fvClosed,tts,[])
        , done=False}
\end{code}

When a proof using the \texttt{Assume} strategy is imported,
the top element of the \texttt{currStk} component has to be reconstructed.
The code here is similar to the \texttt{(Imp lhs rhs)} case of
\texttt{setStrategy} above,
except that the only component that needs updating is the theory stack.
\begin{code}
addAssumeHyps :: TheoryStack -> Proof -> TheoryStack
addAssumeHyps mstk proof
  = case (plan proof) of
      (Assume _ _)
         -> let (hypos,_) = assumptionSplit (goal proof) in
            let (assTh,_) = mkAssumptionTheory (pname proof) hypos mstk in
            [assTh]
      _  ->  []
\end{code}

\subsection{Proof By Assumption}

First, a function to split an implication into a hypothesis list,
and a consequent, by examining both sides of the implication.
It converts
$$
  \bigwedge_{j=1}^{k_1} H_{1j} \implies
  (\bigwedge_{j=1}^{k_2} H_{2j} \implies
  \ldots
  (\bigwedge_{j=1}^{k_n} H_{nj} \implies C) \ldots )
$$
to
$$
  \bigwedge_{i,j=1,1}^{n,k_i} H_{ij} \implies C
$$
where $C$ is not of the form $A \implies B$,
and preserving the original textual ordering of the $H_{ij}$.

If any $H_{ij}$ is itself an implication ($A_{ij} \implies C_{ij}$),
then we replace it by by two equivalent forms based on the
folowing propositional law:
$$
  (A \equiv A \land C)
  \equiv
  (A \implies C)
  \equiv
  (C \equiv C \lor A)
$$
\begin{code}
assumptionSplit :: Pred -> ([Pred],Pred)
assumptionSplit
 = replaceImplications . splitHypotheses . findConsequent []

findConsequent hyps (PApp nm [hyp,rest])
 | nm == n_Imp  =  findConsequent (hyp:hyps) rest
findConsequent hyps pr             = (reverse hyps,pr)

splitHypotheses (hyps,cnsq)
 = (concat $ map splitHyp hyps, cnsq)
 where
  splitHyp (PApp nm prs) | nm == n_And  =  prs
  splitHyp pr                       = [pr]

replaceImplications (hyps,cnsq)
 = (concat $ map replImpl hyps, cnsq)
 where
   replImpl (PApp nm [ante,cnsq])
     | nm == n_Imp
       = [ mkEqv (mkAnd [ante,cnsq]) ante
         , mkEqv (mkOr  [ante,cnsq]) cnsq ]
   replImpl pr = [pr]
\end{code}

\textbf{The assumption strategy is sound
only if any free variables in the hypotheses match only themselves
when used as a law, and not arbitrary values~!
}
We identify these free variables
and record them in definition tables in the hypotheses theory.

Next, we need to extract all the free variables from the hypotheses:
\begin{code}
hypothesesFreeVars hs
  = ( predsFreeOVars nullMatchContext hs
    , predsFreeEVars nullMatchContext hs
    , predsFreePVars nullMatchContext hs
    )
\end{code}

Given a list of free variables and a theory-stack,
we want to build dummy definitions
of variables not already defined in some theory.
Dummy builders no longer need to do any renaming,
as the matching process now handles known variables
is a much more intelligent fashion.
\begin{code}
dummyOVarDef x = (varKey x,Var x)
dummyEVarDef e = (varKey e,mkEVar e)
dummyPVarDef v = (varKey v,PVar $ varGenRoot v)
\end{code}

We need to supply a generic dummmy-definition build function,
that returns tables as well as lists of the variables so rename
\begin{code}
buildDummyDefs mkdummy vs tabs
 = bdd [] vs
 where
   bdd ddefs [] = lbuild ddefs
   bdd ddefs (v:vs)
    = case tsvlookup tabs v of
        Nothing  ->  bdd ((mkdummy v):ddefs) vs
        (Just _) ->  bdd ddefs vs
\end{code}


Generating hypotheses as named laws:
\begin{code}
genNamedAssumptions pname ths
 = gna 1 [] ths
 where
   gna _ hyps [] = hyps
   gna n hyps ((h,tts):ths)
     = gna (n+1) ((hname n,((h,SCtrue),FromSOURCE "Proof",tts)):hyps) ths
   hname n = pname++".hyp."++(show n)
\end{code}

Bringing it all together:
Given a theory-stack,
we need to create a new (temporary) theory,
to hold our hypotheses (as laws),
and dummy definitions for every free hypothesis variable
without any other definitions,
with all those free variables renamed to avoid clashes with existing
laws.
We use the proof name as a seed to generate names for the theory
and all the laws.
The theory name is tagged with an initial ``assumption-mark''
character, so it is recognisable as such a theory
and not included in theory dependencies.
\begin{code}
hypPrefix = sptName "HYP_"
hypName name = hypPrefix++name
isHYPName name = hypPrefix `isPrefixOf` name
isHYP thry = isHYPName (thryName thry)
isHYPMatchContext = isHYPName . mcThName

mkAssumptionTheory :: String -> [Pred] -> TheoryStack
                   -> (Theory, ([Variable], [Variable], [Variable]))
mkAssumptionTheory pname hs thstk
 = let hfv@(ovs,evs,pvs) = hypothesesFreeVars hs in
   let odfns = buildDummyDefs dummyOVarDef ovs (map consts thstk) in
   let edfns = buildDummyDefs dummyEVarDef evs (map exprs  thstk) in
   let pdfns = buildDummyDefs dummyPVarDef pvs (map preds  thstk) in
   let mctxt = mkMatchContext thstk in
   let ths = map (predTypeTables mctxt) hs in
   let hlaws = genNamedAssumptions pname ths in
   let newth = (nmdNullPrfCtxt (hypName pname)) in
   (newth{consts=odfns,exprs=edfns,preds=pdfns,laws=hlaws},hfv)
\end{code}

\subsection{Case/Branch Switching}

We need to handle the fact we have several branches in a proof and we
may wish to jump between them. At present we simply visit them round-robin.
\begin{code}
hm_switch = (
    unlines $ [" : Case/branch switch (Round Robin)\n",
    "With a left to right (L2R) or right to left (R2L) proof strategy,",
    "use this key to switch from the LHS to the RHS and vice versa."])

caseSwitch prf
  | switched  =   (switched,prf{plan=plan'})
  | otherwise  =  (switched,prf)
  where
    (switched,plan') = caseSSwitch (plan prf)

\end{code}
At present, we only handle branches that arise from a \texttt{RedBoth} strategy.
Case branches in justifications will need heavier machinery.
\begin{code}

caseSSwitch (RedBoth 1 lhs rhs) = (True,RedBoth 2 lhs rhs)
caseSSwitch (RedBoth 2 lhs rhs) = (True,RedBoth 1 lhs rhs)
caseSSwitch (Assume _ strategy)
  | switched  =   (switched,strategy')
  | otherwise  =  (switched,strategy)
  where
    (switched,strategy') = caseSSwitch strategy
caseSSwitch str  = (False,str)

\end{code}

\subsection{Finalising Proofs}

We first define a binary predicate that checks
for ``proof-equivalence'', here defined to be
either liberal type equivalence,
or alpha-equivalent.
\textbf{No \texttt{TypeTables} information here --- is it needed?}
\begin{code}
-- MAYBE DO THIS DIRECTLY ???
-- might not need mctxt or sc

proofEquiv :: FVSetExpr -> MatchContext -> SideCond -> FPred -> FPred
           -> Bool
proofEquiv fvs mctxt sc pr1 pr2
  = (cp `pequiv` cq)
    ||
    (alphaEquiv fvs mctxt sc cp cq)
 where
  cp = clearPFocus pr1
  cq = clearPFocus pr2

alphaEquiv :: FVSetExpr -> MatchContext -> SideCond -> Pred -> Pred
           -> Bool
alphaEquiv fvs mctxt sc pr1 pr2
 | isNothing cmp                    =  False
 | invalidBnds bnds12               =  False
 | invalidBnds bnds21               =  False
 | incompatibleBinds bnds12 bnds21  =  False
 | otherwise                        =  True
 where
   cmp = alphaCompare fvs mctxt sc pr1 pr2
   (Just (bnds12,bnds21)) = cmp

alphaCompare :: FVSetExpr -> MatchContext -> SideCond -> Pred -> Pred
             -> Maybe (Binding,Binding)
alphaCompare fvs mctxt sc pr1 pr2
 = do bind12 <- lawMatch [] fvs Bnil mctxt sc pr1 (pr2,sc) Bnil
      bind21 <- lawMatch [] fvs Bnil mctxt sc pr2 (pr1,sc) Bnil
      return(bind12,bind21)

invalidBnds bnds = False -- for now

incompatibleBinds bndsA bndsB = False -- for now
\end{code}

When developing a proof-section,
we have a target predicate in mind---once we transform
our current predicate into the target, we are done.
The target depends in general on the goal and strategy:
\begin{code}
proofTarget :: Pred -> Strategy -> Pred
proofTarget _           (Reduce _)                  =  TRUE
proofTarget (PApp nm [_,rhs]) (Lhs2Rhs _) | nm == n_Eqv  =  rhs
proofTarget (PApp nm [lhs,_]) (Rhs2Lhs _) | nm == n_Eqv  =  lhs
proofTarget (PApp nm [_,_])   (RedBoth 1 _ (rfpr,_,_,_))
 | nm == n_Eqv  =  clearPFocus rfpr
proofTarget (PApp nm [_,_])   (RedBoth 2 (lfpr,_,_,_) _)
 | nm == n_Eqv  =  clearPFocus lfpr
proofTarget goal        (LawReduce _ _ _)           =  goal

proofTarget (PApp nm [_,cnsq]) (Assume _ strategy)
 | nm == n_Imp  = proofTarget cnsq strategy

proofTarget _ st = perror "proofTarget - bad strategy"
\end{code}

\newpage
\subsubsection{Checking Proof (for completion)}

We then define a function that analyses a proof
and returns it with the done variable set if the proof is complete
(and branching strategies appropriately marked)
\begin{code}
p =!= q  =  p `predAlphaEqv` q

checkProof proof = proof{ plan=plan' , done= done' }
 where

  goalpr = goal proof
  strat =  plan proof

  tgt = proofTarget goalpr strat

  mctxt = topNonHYPMtchCtxt proof
  sc = side proof

  (done',plan') = checkStrategy sc goalpr tgt strat

  checkStrategy sc _ tgt (Reduce ps@(fpr,fvs,_,_))
    = (clearPFocus fpr =!= tgt, Reduce (setPSFreeVars mctxt sc ps))

  checkStrategy sc (PApp nm [lhs,rhs]) tgt (Lhs2Rhs ps@(fpr,fvs,_,_))
   | nm == n_Eqv
     = ( dbg "chkStrat-L2R.done = "
         ((dbg "chkStrat-L2R.fpr  = "(clearPFocus  fpr))
           =!=
          (dbg "chkStrat-L2R.tgt  = " tgt))
       , Lhs2Rhs (setPSFreeVars mctxt sc ps) )

  checkStrategy sc (PApp nm [lhs,rhs]) tgt st@(Rhs2Lhs ps@(fpr,fvs,_,_))
   | nm == n_Eqv
     = (clearPFocus fpr =!= tgt, Rhs2Lhs (setPSFreeVars mctxt sc ps))

  checkStrategy sc (PApp nm [lhs,rhs]) tgt
                                       st@( RedBoth i lps@(lfpr,lfvs,_,_)
                                                      rps@(rfpr,rfvs,_,_) )
   | nm == n_Eqv
      = if clearPFocus lfpr =!= clearPFocus rfpr
        then (True,RedBoth 0 lps' rps')
        else (False,RedBoth i lps' rps')
     where
       lps' = setPSFreeVars mctxt sc lps
       rps' = setPSFreeVars mctxt sc rps

-- the current proof predicate is a law,
-- (as it was obtained by reduction from a starting law)
-- so leading universal quantifiers are irrelevant,
-- in it, or the goal.

  checkStrategy goalsc goal tgt st@(LawReduce nm sc ps@(fpr,fvs,_,_))
    = (remOuterForall (clearPFocus fpr) =!= remOuterForall tgt
      , LawReduce nm sc (setPSFreeVars mctxt goalsc ps) )

  checkStrategy sc (PApp nm [_,cnsq]) tgt st@(Assume cnsq' strategy)
   | nm == n_Imp
      = (done',Assume cnsq' strategy')
      where (done',strategy') = checkStrategy sc cnsq' tgt strategy

  checkStrategy _ _ _ st = (False,st)

-- end checkProof
\end{code}

We want to set the free variables for the current predicate:
\begin{code}
setPSFreeVars :: MatchContext -> SideCond -> ProofSection -> ProofSection
setPSFreeVars mctxt sc (fpr,_,ttbl,args)
 = ( fpr, evalFreeVars mctxt sc (getPFocus fpr), ttbl, args )

evalFreeVars :: MatchContext -> SideCond -> Pred -> FVSetExpr
evalFreeVars mctxt sc pr
 = reduceFVSetExpr (normaliseSC sc) $ predFVSet mctxt pr
\end{code}


\subsection{QVar replacement}

We provide a function to replace the \texttt{Qvar} of an induction law
by a chosen induction variable.
For now, we only handle ilaw of the relevant shapes
(descend through forall, implication, substitution, conjunction,
and type declarations)
\begin{code}
replaceQVar q ivar ilaw  -- replace q by ivar
 = rQ ilaw
 where
   rQ (TypeOf (Var v) t) = TypeOf (Var (rv v)) t
   rQ (PApp nm prs) = PApp nm (map rQ prs)
   rQ (PAbs nm _ qs pr) = (PAbs nm 0 (rq qs) (rQ pr))
   rQ (Sub pr sub) = Sub (rQ pr) (rqs sub)
   rQ pr = pr

   rq qs = (map rv vs) ++ rest where (vs,rest) = vPartition qs

   rqs (Substn sub) = Substn (map rsub sub)

   rsub (v,a) = (rv v,a)

   rv v = (if v==q then ivar else v)
\end{code}



\subsection{Diagnostics}

All proofs are deemed complete
when either sub-goals are equal to each other,
or all sub-goals are equivalent to $True$.
Sometimes a completeness check can fail
event though the pretty-printed forms appear
identical.
This diagnostic facility gives a detailed account of
how a proof check pans out.
It should not be required in a production version of this tool.
\begin{code}
proofDiagnosis proof
 = diagnoseStrategy (goal proof) (plan proof)
 where

  diagnoseStrategy _ (Reduce ((pr,_,_),_,_,_))
    = unlines ["Comparing curr. pred:\n\t"++dbgPshow 8 pr
              ," with TRUE"
              ,"Outcome: "++show (pr=!=TRUE)]

  diagnoseStrategy (PApp nm [lhs,rhs]) (Lhs2Rhs ((pr,_,_),_,_,_))
   | nm == n_Eqv
      = unlines ["Comparing curr. pred:\n\t"++dbgPshow 8 pr
                ," with goal rhs:\n\t"++dbgPshow 8 rhs
                ,"Outcome: "++show (pr=!=rhs)]

  diagnoseStrategy (PApp nm [lhs,rhs]) (Rhs2Lhs ((pr,_,_),_,_,_))
   | nm == n_Eqv
      = unlines ["Comparing curr. pred:\n\t"++dbgPshow 8 pr
                ," with goal lhs:\n\t"++dbgPshow 8 lhs
                ,"Outcome: "++show (pr=!=lhs)]

  diagnoseStrategy (PApp nm [lhs,rhs])
                   (RedBoth brno ((lpr,_,_),_,_,_) ((rpr,_,_),_,_,_))
   | nm == n_Eqv
      = unlines ["Comparing lhs goal:\n\t"++dbgPshow 8 lpr
                ," with rhs goal:\n\t"++dbgPshow 8 rpr
                ,"Outcome: "++show (lpr =!= rpr)]

  diagnoseStrategy goal (LawReduce _ _ ((pr,_,_),_,_,_))
    = unlines ["Comparing curr. pred:\n\t"++dbgPshow 8 pr
              ," with goal :\n\t"++dbgPshow 8 goal
              ,"Outcome: "++show outcome]
    where outcome = remOuterForall pr `pequiv` remOuterForall goal

  diagnoseStrategy goal (Assume hyp strategy)
    = ("Given hypothesis:\n\t"++dbgPshow 8 hyp)
       ++ diagnoseStrategy goal strategy

  diagnoseStrategy _ strategy
    = "Error --- Mismatch between goal and strategy !"
\end{code}

Another handy facility is giving a proof length:
\begin{code}
proofLength = planLength . plan

planLength (Reduce (_,_,_,args)) = length args
planLength (Lhs2Rhs (_,_,_,args)) = length args
planLength (Rhs2Lhs (_,_,_,args))  = length args
planLength (RedBoth _ (_,_,_,la) (_,_,_,ra)) = length la + length ra
planLength (LawReduce _ _ (_,_,_,args)) = length args
planLength (Assume _ strategy) = 1 + planLength strategy
planLength _ = 0
\end{code}

Hashing a proof (with old Data.HashTable code in locally):
\begin{code}
hashProof :: Proof -> String
hashProof prf
 = show $ hashString $ show prf
 where

  golden :: Int32
  golden = 1013904242

  hashInt32 :: Int32 -> Int32
  hashInt32 x = mulHi x golden + x

  hashInt :: Int -> Int32
  hashInt x = hashInt32 (fromIntegral x)

  mulHi :: Int32 -> Int32 -> Int32
  mulHi a b = fromIntegral (r `shiftR` 32)
     where r :: Int64
           r = fromIntegral a * fromIntegral b

  hashString :: String -> Int32
  hashString = foldl' f golden
     where f m c = fromIntegral (ord c) * magic + hashInt32 m
           magic = -0x21524111 -- 0xdeadbeef
\end{code}


\subsection{Proof Identifiers}

A proof identifier is a composition
of a theory name and proof name,
that uniquely identifies a conjecture/law.
$$
  ProofId = TheoryName \times ConjName
$$
We render these identifiers in two ways:
\begin{enumerate}
  \item
    for internal use as proof identifiers (\texttt{pid}s)
    to index lookup tables:
    \begin{center}
    ConjName\$TheoryName
    \end{center}
    Here the ordering is to ensure quick disambiguation
    and flatter \texttt{Tries}.
  \item
    to generate filenames (\texttt{pfn}s)
    in which the proofs can be stored:
    \begin{center}
    clean(TheoryName)\_clean(ConjName)
    \end{center}
    The names have to be `cleaned' to replace
     characters that cannot be used in filenames,
     and we put theory names first so that directory listings
     show proofs grouped by theory.
\end{enumerate}


Generating and Parsing these can be useful.
\begin{code}
pfnSep = '_'

mkPid pfn thn = pfn ++ qualSep:thn

mkPfn pfn thn = fileNameClean thn ++ pfnSep:fileNameClean pfn

parsePid pid
 = (takeWhile (/=qualSep) pid, tl (dropWhile(/=qualSep)pid) )
 where { tl [] = [] ; tl (_:xs) = xs }

proofId proof = mkPid (pname proof) (thname proof)

proofFn proof = mkPfn (pname proof) (thname proof)

qname2pid qname = mkPid pfnm thnm where (thnm,_,pfnm) = qparse qname
\end{code}

\subsection{Proof Steps}

We need to be able to replace the focus after
a succesful match/operation.
The following functions make use
of \texttt{Focus.repPFocus} and variants (e.g. \texttt{repPFf}).
to do this.


\subsubsection{\texttt{PVar} by definition}
\begin{code}
repFocus penv fpr
 = repPFf (replaceNamedPred penv) fpr

replaceNamedPred penv pr@(PVar name)
 = case lkpProofEnv preds (show name) penv of
     []       ->  pr
     (pr':_)  ->  pr'
replaceNamedPred penv pr = pr
\end{code}


\subsubsection{Recursively expand \texttt{PVar}s}
\begin{code}
expandFocus penv fpr = repPFocus (expandPred id penv (getPFocus fpr)) fpr
\end{code}

\subsubsection{Assert Definedness}
\begin{code}
assertDefFocus fpr = repPFocus (assertDefined (getPFocus fpr)) fpr
\end{code}

\subsubsection{Reduce Application}
\begin{code}
redFocus mctxt sc ptables fpr
 = ( repPFf (reduceApp mctxt sc ptables) fpr
   , Chgd ) -- for now

reduceApp mctxt sc ptables ap@(PApp nm [_,_])
  | nm == n_PVApp  =  predBetaReduce mctxt sc ap

reduceApp mctxt sc ptables asub@(Sub pr subs)
 = case chgd of
    Chgd  ->  pr'
    _     ->  asub
  where (pr',chgd) = predOSub mctxt sc subs pr

reduceApp _ _ _ pr = pr
\end{code}

\subsubsection{$\alpha$ Substitution}
\begin{code}
alfFocus mctxt sc subs fpr = repPFf (predASub mctxt sc subs) fpr
\end{code}

\subsubsection{Predicate Tidy-Up}
\begin{code}
tdyPred tspec fpr = repPFf (tidyPred tspec) fpr
\end{code}

\subsubsection{Convert Predicate to DNF/CNF}
\begin{code}
hm_toDNF = (
    unlines $ [" : Convert to DNF\n",
    "Converts any Boolean expression,",
    "composed of variables and the /\\ and \\/ operators,",
    "to disjunctive normal form (DNF).",
    "DNF is a sum of products form, i.e. an ORing of ANDs.\n",
    "Example:\n",
    "The expression",
    "a /\\ (b \\/ c)",
    "is, in DNF,",
    "(a /\\ b) \\/ (a /\\ c)."])

hm_toCNF = (
    unlines $ [" : Convert to CNF\n",
    "Convert any Boolean expression,",
    "composed of variables and the /\\ and \\/ operators,",
    "to conjunctive normal form (CNF).",
    "CNF is a product of sums form, i.e. an ANDing of ORs.\n",
    "Example:\n",
    "The expression",
    "a /\\ b \\/ c /\\ d",
    "is, in CNF,",
    "(a \\/ c) /\\ (a \\/ d) /\\ (b \\/ c) /\\ (b \\/ d)."])

normPred nf fpr = repPFf nf fpr
\end{code}

\subsubsection{Predicate Simplify}
\begin{code}
simpPred fpr = repPFf predSimp fpr
\end{code}

\subsubsection{Propagate Equality}
Given a predicate of the form:
$$
  \ldots ( e=f \land \ldots \oplus \ldots P(e) \ldots ) \ldots
$$
where $\oplus$ is either $\land$ or $\implies$,
we can replace $e$ by $f$ in $P$.
\begin{code}
hm_propEqPred = (
    unlines $ [" : Propagate Equality\n",
    "Looks up from the current expression focus for a parent of the form",
    "  e=f /\\ ... focus ...    or  e=f => .... focus ....",
    "If the focus matches e (f) precisely, it is replaced by f (e)."])

propEqPred fpr@(PExpr e,_,_,ics)
 | null replcs  =  fpr
 | otherwise =  repPFocus (PExpr e') fpr
 where
   replcs = lookupEqReplacements e ics
   e' = head replcs

propEqPred fpr = fpr
\end{code}

We check this out by starting at  $P(e)$ and searching
up for a conjunction or implication.
The other parts are then examined to see if they are a conjunction
containing equalities, which are then matched against $e$.
We return all such matches we find,
so future extensions to this feature may offer them all via
a pop-up menu.
\begin{code}
lookupEqReplacements e _ = [] -- disabled for now!
-- lookupEqReplacements e [] = []
-- lookupEqReplacements e ((parentpr,n,_):ancpr)
--  = ( case parentpr of
--        And prs    ->  findAndEqRepl e n prs
--        Imp ante _ ->  findAnteEqRepl e ante
--        _                    ->  []
--    ) ++ lookupEqReplacements e ancpr
\end{code}

When searching a conjunction list, remember to ignore our own location!
\begin{code}
findAndEqRepl _ _ [] = []
findAndEqRepl e n (pr:prs)
 | n == 1  =  findAndEqRepl e 0 prs
 | otherwise
    = ( case pr of
         PExpr (App nm [e1,e2]) | nm == n_Equal
           ->  equalRepl e e1 e2
         _ ->  []
      ) ++ findAndEqRepl e (n-1) prs
\end{code}

When searching an implication antecedent
its either an equality, or a conjunction.
\begin{code}
findAnteEqRepl e (PExpr (App nm [e1, e2]))
 | nm == n_Equal    =  equalRepl e e1 e2
findAnteEqRepl e (PApp nm prs)
 | nm == n_And      =  findAndEqRepl e 0 prs
findAnteEqRepl _ _  =  []
\end{code}

Now, deciding do we have equality of expressions:
\begin{code}
equalRepl e e1 e2
 | e1 == e2   =  []    -- ignore reflexive equalities !
 | e == e1    =  [e2]
 | e == e2    =  [e1]
 | otherwise  =  []
\end{code}

\subsubsection{Strip leading for-all}
This action exploits the fact that if any of the following (for arbitrary $\vec v$) are a theorem,
$$
 P \qquad \forall \vec v @ P \qquad [P]
$$
then they all are.
In the LawReduce strategy,
it strips leading universal quantifiers,
provided focus is on the whole
current goal.
\begin{code}
stripPred fpr = repPFf remOuterForall fpr
\end{code}

\subsubsection{Predicate Binder Split}
\begin{code}
bndrSplitPred fpr
 = repPFf (splitPred (isFreeUnder (snd3 $ getPFContext fpr))) fpr
\end{code}

\subsubsection{Predicate Index-Split}
\begin{code}
iSplitPred ixs = repPFf (indicesSplitPred ixs)

txtToIndices txt
 = t2ix [] 0 txt
 where
   t2ix []   0 ""  = Nothing
   t2ix []   n ""  = Just [n]
   t2ix nums 0 ""    = Just $ reverse nums
   t2ix nums n ""    = Just $ reverse (n:nums)
   t2ix nums n (c:cs)
    | isDigit c  =  t2ix nums (10*n+digitToInt c) cs
    | otherwise  =  t2ix (if n==0 then nums else n:nums) 0 cs
\end{code}

\subsubsection{Instantiate Law}
\begin{code}
conjoinLawInstance ilaw = repPFf (conjoinLInst ilaw)

conjoinLInst ilaw pr = mkAnd [pr,ilaw]
\end{code}

\subsubsection{Apply Matched Law}
\begin{code}
applyLaw mctxt match fpr
 = repPFocus (matchReplace mctxt match) fpr
\end{code}

\subsubsection{Existential Witness}

This implements the principle that
$$
 (\exists x @ P)
 \equiv
 ((\exists x @ P) \lor P[e/x])
$$
\begin{code}
applyWitness mctxt sc wsubs fpr
  = repPFf (existentialWitness mctxt sc wsubs) fpr
\end{code}


\subsection{Proof Summary}

\begin{code}
proofSummary prf
 = pname prf
   ++ " - "
   ++ show (goal prf)
   ++ " ,- "
   ++ show (side prf)
   ++ " ("
   ++ planSummary (plan prf)
   ++ ","
   ++ prover prf
   ++ ")"

planSummary NoStrategy = "none!"
planSummary (Reduce ps) = "Reduce - "++ show (pStepCount ps)
planSummary (Lhs2Rhs ps) = "Lhs->Rhs - "++ show (pStepCount ps)
planSummary (Rhs2Lhs ps) = "Rhs->Lhs - "++ show (pStepCount ps)
planSummary (RedBoth _ ps1 ps2)
 = "Both - " ++ show (pStepCount ps1 + pStepCount ps2)
planSummary (LawReduce lname _  ps)
 = "LawReduce."++lname++" - "++ show (pStepCount ps)
planSummary (Assume _ plan')
 = "Assume, then "++ planSummary plan'


pStepCount (_,_,_,steps) = length steps
\end{code}


\newpage
\subsection{Proof State Mapping}

A function that applies mapping functions to all predicates
and expressions in the system.
Rarely used, except to prepare for major datastructure changes,
particularly when theories are under development,
and we don't want to completely re-do that work.

\begin{code}
proofMap :: (Pred->Pred,Expr->Expr) -> Proof -> Proof
proofMap pemap
 = goalSetf (mapP pemap)

theorygraphMap :: (Pred->Pred,Expr->Expr) -> TheoryGraph -> TheoryGraph
theorygraphMap pemap (rdag, trie)
 = (rdag, tmap (theoryMap pemap) trie)

theoryMap :: (Pred->Pred,Expr->Expr) -> Theory -> Theory
theoryMap pemap thry = thry
\end{code}

\newpage
\subsection{Premature Proof Ending}

There are a number of ways to end a proof prematurely:
\begin{description}
  \item[Reduce]
    Given goal $G$, and a proof so far of $G \ldots\equiv\ldots G'$,
    we can convert this into a theorem that $G \equiv G'$.
  \item[Lhs2Rhs]
    Given goal $L \equiv R$ and a proof so far that $L \ldots\equiv\ldots L'$
    we can convert this into a theorem that $L \equiv L'$.
  \item[Rhs2Lhs]
    Given goal $L \equiv R$ and a proof so far that $R \ldots\equiv\ldots R'$
    we can convert this into a theorem that $R \equiv R'$.
  \item[Both]
    Given goal $L \equiv R$ and proofs so far,
    that $L \ldots\equiv\ldots L'$ and $R \ldots\equiv\ldots R'$
    we can convert this into two theorems: $L \equiv L'$ and $R \equiv R'$,
    or a single one: $(L \equiv L') \land (R \equiv R')$
\end{description}
For now, we don't cater for assumption-based strategies.
\begin{code}
prematureEnding :: [Theory] -> Proof -> (Bool,Proof)
prematureEnding penv prf
 = case (goal prf) of

     (PApp nm [glhs, grhs]) | nm == n_Eqv
       -> case (plan prf) of

           Lhs2Rhs (lhs',_,_,_)
             -> if isTrue $ getPFTop lhs'
                 then (True,prf{goal=glhs, done=True})
                 else (True,prf{goal=mkEqv glhs (clearPFocus lhs'), done=True})

           Rhs2Lhs (rhs',_,_,_)
             -> if isTrue $ getPFTop rhs'
                 then (True,prf{goal=grhs, done=True})
                 else (True,prf{goal=mkEqv grhs (clearPFocus rhs'), done=True})

           RedBoth _ (lhs',_,_,_) (rhs',_,_,_)
             -> (True,prf{goal=mkAnd [ mkEqv glhs (clearPFocus lhs')
                                   , mkEqv grhs (clearPFocus rhs')
                                   ], done=True})

           _ -> (False,prf)

     gpred
       -> case (plan prf) of
           Reduce (cpred',_,_,_)
             -> (True,prf{goal=mkEqv gpred (clearPFocus cpred'), done=True})

           _ -> (False,prf)
 where
   isTrue TRUE           =  True
   isTrue _              =  False
\end{code}
