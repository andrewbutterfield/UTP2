\section{Proof Replay}

\begin{code}
module Replay where
import Tables
import Precedences
import Datatypes
import DataText
import Manipulation
import Proof
import Theories
import Utilities
-- import Files
-- import ImportExport
-- import Archive
-- import DocTextParser
-- import LaTeXSetup
-- import LaTeXParserIF
-- import DSL
import Focus

-- import System.IO
-- import Graphics.UI.WX
-- import Graphics.UI.WXCore
--
-- import Text.ParserCombinators.Parsec.Expr
--
-- import Data.List
-- import Data.Maybe
-- import Data.Char
\end{code}


\emph{This may get moved eventually to its own module.}
\begin{code}
getStrategySpec :: Strategy ->  StratSpec
getStrategySpec (Reduce _)        = SSRed
getStrategySpec (Lhs2Rhs _)       = SSL2R
getStrategySpec (Rhs2Lhs _)       = SSR2L
getStrategySpec (RedBoth _ _ _)   = SSRB
getStrategySpec (LawReduce _ _ _) = SSLwR
getStrategySpec (Assume _ strat)  = SSAss (getStrategySpec strat)

setReplayStrategy :: [Theory] -> Proof -> StratSpec -> (Proof, [Theory])
setReplayStrategy thry proof SSRed = setStrategy thry SSRed proof
setReplayStrategy thry proof SSL2R = setStrategy thry SSL2R proof
setReplayStrategy thry proof SSR2L = setStrategy thry SSR2L proof
setReplayStrategy thry proof SSRB  = setStrategy thry SSRB proof
setReplayStrategy thry proof SSLwR = setStrategy thry SSLwR proof
setReplayStrategy thry proof (SSAss strat) = setStrategy thry (SSAss strat) proof
--setReplayStrategy _ proof "none"   = (proof, [])

getAndSet :: Proof -> Proof -> (Proof, [Theory])
getAndSet rplyPrf orgnlPrf
 = setReplayStrategy [] rplyPrf $ getStrategySpec $ plan orgnlPrf
\end{code}

Quick Section to
 pull out the \texttt{Justification}s from a \texttt{Proof}'s \texttt{Strategy}
Very Hacky Solution for pulling out \texttt{ProofSection}s,
to allow for pattern matching
I have it return lists of items so I can return the
 two odd cases \texttt{RedBoth} and \texttt{NoStrategy}.
\begin{code}
getProofSection :: Strategy -> [ProofSection]
getProofSection (Reduce proofSection) = [proofSection]
getProofSection (Lhs2Rhs proofSection) = [proofSection]
getProofSection (Rhs2Lhs proofSection) = [proofSection]
getProofSection (RedBoth int prfSection1 prfSection2) = [prfSection1, prfSection2]
getProofSection (LawReduce _ _ proofSection) = [proofSection]
getProofSection (Assume _ strat) = getProofSection strat
-- a NoStrategy in theory should never come up in use when it's done
getProofSection NoStrategy = []
\end{code}

Next Section Deals with pulling out the Arguments from the ProofSection
Also I reverse the arguments so it's easier to parse them seeing as they're in
the reverse order that they should be applied
\begin{code}
getArgument :: ProofSection -> [Argument]
getArgument (_, _, arg) = reverse arg
\end{code}

code to pull out the Predicate from a Strategy
\begin{code}
pullOutPred :: Strategy -> [Pred]
pullOutPred (NoStrategy) = []
pullOutPred (Reduce  (p, _, _)) = [p]
pullOutPred (Lhs2Rhs (p, _, _)) = [p]
pullOutPred (Rhs2Lhs (p, _, _)) = [p]
pullOutPred (RedBoth _ (p1, _,_) (p2,_,_))  = [p1, p2]
pullOutPred (LawReduce _ _ (p, _, _)) = [p]
pullOutPred (Assume _ strategy) = pullOutPred strategy
\end{code}

\begin{code}
replay :: Proof -> Proof -> [Char]
replay rplyPrf orgPrf
 | done' == True = "Finished Succesfuly"
 | otherwise = error "After applying all previous arguments to " ++ (pname rplyPrf)
                        ++ " proof still did not finish"

   where
    done' = done (checkAndGo rplyPrf arguments)
    arguments =  getArgument $ head $ getProofSection $ plan orgPrf


checkAndGo rplyPrf [] = checkProof rplyPrf
checkAndGo rplyPrf  (arg:args)
 =  case predAlphaEqv rplyPred' orgPred of
            True -> checkAndGo rplyPrf args
            False -> error "There is a problem that has occured"
    where
        (bool, pred) = setPFocusPath fpath rplyPred
        pred' = replayStep infer ctxt pred
        ((prfRel,fpath, infer, bind), orgPred) = (\(Justify prf) -> prf) arg
        rplyPred  = head $ pullOutPred $ plan rplyPrf
        rplyPred' = clearPFocus pred
        ctxt =  context rplyPrf

replayStep :: Inference -> [Theory] -> Pred -> Pred
replayStep (NamedLaw _ _ _) ctxt pred
 =  repFocus ctxt pred
replayStep (InstantLaw _ _) ctxt pred
 = pred
replayStep (NameReplace) ctxt pred
 = pred
replayStep (NameFold _) ctxt pred
 = pred
replayStep (RecExpand) ctxt pred
 = pred
replayStep (ISubstitute) ctxt pred
 = pred
replayStep (AlphaSubs _) ctxt pred
 = pred
replayStep (ITidy _) ctxt pred
 = pred
replayStep (ISimplify) ctxt pred
 = repFocus ctxt (simpPred pred)
replayStep (INorm _) ctxt pred
 = pred
replayStep (ISplit _) ctxt pred
 = pred
replayStep (IApply) ctxt pred
 = pred
replayStep (UName _) ctxt pred
 = pred
replayStep (Witness _ ) ctxt pred
 = pred
replayStep (BinderSplit) ctxt pred
 = pred
replayStep (AssertDefined) ctxt pred
 = pred
replayStep (ForallStrip) ctxt pred
 = pred
replayStep (PropagateEq) ctxt pred
 = pred
\end{code}


