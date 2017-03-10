\section{Proof Replay}

\begin{code}
module ProofReplay where
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
import Normalise
import Proof
import Theories
import DSL
import Files

import Data.List
import Data.Char
--import Data.HashTable
import Data.Maybe

import qualified Test.QuickCheck as QC
import Text.ParserCombinators.Parsec.Expr

-- GHC 7.10 future proofing
import Control.Applicative (Applicative(..))
import Control.Monad       (liftM, ap)
\end{code}

\subsection{Replay Reporting}

For now a replay report is a header followed by a list of strings,
where being empty is good, and non-empty is not so good.
If not so good, the messages will indicate the
extent to which replay was carried out.
\begin{code}
data ReplayReport = RR String [String] deriving (Eq,Ord)

instance Show ReplayReport where
  show (RR hdr []) = "Replay ("++hdr++") OK"
  show (RR hdr lns)
     = unlines $ ("REPLAY ("++hdr++") NOT OK:"):(lns++["...END NOT OK"])
\end{code}

We provide (obvious) ways to build reports:
\begin{code}
rrHdr :: String -> ReplayReport
rrHdr hdr = RR hdr []

rrOK = rrHdr ""
rr msg = RR "" [msg]

rrMerge2 :: ReplayReport -> ReplayReport -> ReplayReport
rrMerge2 (RR hdr rs1) (RR _ rs2) = RR hdr (rs1 ++ rs2)

rrMerge :: [ReplayReport] -> ReplayReport
rrMerge = foldr rrMerge2 (rrHdr "")
\end{code}

We define a Replay Report Result
as having the shape of a state monad,
and insantiate it as a functor
\begin{code}
data RRState = RRS Bool ReplayReport
data RRResult a = RRR (RRState -> (RRState, a))

instance Show RRState where
 show (RRS cont rr)
  = show rr ++ cshow cont
  where cshow True   =  "..."
        cshow False  =  " !"

mkRRF f rs@(RRS False _) = (rs, undefined)
mkRRF f (RRS True rr) = f rr
\end{code}

We instantiate it as a state monad,
where results are propagated,
error messages accumulate, and work continues.
When errors get too serious, we can signal failure,
from which point onwards the results are undefined.
\begin{code}
instance Monad RRResult where

  return x = RRR (\ (RRS _ rr) -> (RRS True rr, x))

  (RRR m) >>= f
   = RRR (
      \ rs ->
        let (rs1@(RRS cont1 rr1), x1) = m rs
        in if cont1
           then let (RRR fint) = f x1 in fint rs1
           else (RRS cont1 rr1, undefined)
        )

  fail msg
    = RRR ( \(RRS _ rrep)
            -> (RRS False (rrep `rrMerge2` rr msg), undefined) )

-- GHC 7.10 future proofing
instance Functor RRResult where fmap = liftM
instance Applicative RRResult where
    pure  = return
    (<*>) = ap
\end{code}

We lift useful \texttt{ReplayReport} functions to \texttt{RRResult}:
\begin{code}
rrsHdr hdr = RRS True $ rrHdr hdr
rrrHdr hdr x  = RRR (\ _ -> (rrsHdr hdr, x) )

rrrOK x  = rrrHdr "" x

rrs msg = RRS True (rr msg)
rrr msg x = RRR (\ _ -> (rrs msg, x) )
\end{code}

We also want to access the report part within
the monad:
\begin{code}
getReport :: RRResult ReplayReport
getReport = RRR (\ rs@(RRS _ rr) -> (rs, rr) )

addReport :: ReplayReport -> RRResult ()
addReport rnew
 = RRR ( \ (RRS cont rr') -> (RRS cont (rr' `rrMerge2` rnew), () ) )

addMsg :: String -> RRResult ()
addMsg = addReport . rr

runReport :: RRState -> RRResult a -> (RRState, a)
runReport rs (RRR f) = f rs
\end{code}




\subsection{Replaying a Proof}

Here we describe how to replay a single proof,
given the original,
plus a replay version which has just started (no strategy chosen yet),
but with a proof context that is current, i.e., newer than that used
by the original.
\begin{code}
replayProof ::  Proof -> Proof -> (RRState, Proof)
replayProof oprf rprf
 = runReport (rrsHdr fullname) preplay
 where
   fullname = mkpid (thname oprf) (pname oprf)
   preplay = do rprf1 <- replaySetStrategy oprf rprf
                rprf2 <- replayProofPlan oprf rprf1
                rprf3 <- replayProofCheck oprf rprf2
                return rprf3
\end{code}

\subsection{Re-setting the strategy}

We need to abstract the original strategy
back to a strategy specification:
\begin{code}
abstractStrategy :: Strategy -> StratSpec

abstractStrategy (Reduce _)        = SSRed
abstractStrategy (Lhs2Rhs _)       = SSL2R
abstractStrategy (Rhs2Lhs _)       = SSR2L
abstractStrategy (RedBoth _ _ _)   = SSRB
abstractStrategy (LawReduce _ _ _) = SSLwR
abstractStrategy (Assume _ str)    = SSAss $ abstractStrategy str

abstractStrategy NoStrategy = error "abstractStrategy - NoStrategy"
\end{code}

We ensure that we can set the strategy of the
replay proof.
In the case of \texttt{LawReduce}, we simply copy over strategy details,
as we have no easy way of reproducing the
setup details, especially if it was originally an induction proof.
\begin{code}
replaySetStrategy :: Proof -> Proof -> RRResult Proof
replaySetStrategy oprf rprf
 | nullStrat ostr   =  fail "SetStrategy: Original Proof has NO STRATEGY"
 | nullStrat rstr'  =  fail ("SetStrategy: Couldn't set Strategy to "++show ostr)
 | otherwise        =  return rprf''{ context = context'
                                    , mtchCtxt = mtchCtxt'
                                    }
 where
   nullStrat NoStrategy = True
   nullStrat _          = False
   ostr = plan oprf
   rss = abstractStrategy ostr
   mctxt = mkMatchContext $ context rprf
   (pred',rtts) = predTypeTables mctxt $ goal rprf
   rprf' = rprf{ goal=pred' }
   (rprf'',hyps') = replaySetStrategy' ostr (context rprf') rss rprf' rtts
   rstr' = plan rprf''
   context' = hyps'++context rprf''
   mtchCtxt' = mkMatchContexts context'

   replaySetStrategy' (LawReduce nlaw sc ps) _ _ rprf rtts
     = (setLawReduce (nlaw,(lgoal,sc)) rtts rprf, [])
     where
       lgoal = psStartPred ps

   replaySetStrategy' _ penv rss rprf rtts
     = setStrategy penv rss rprf rtts
-- end replaySetStrategy
\end{code}


We need to extract the predicate at the
end of a proof-section
\begin{code}
psStartPred ((pr,_,_),_,_,[]) = pr
psStartPred (_,_,_,psteps) = snd $ last psteps
\end{code}

\subsection{Replaying the Proof Plan}

We dispatch based on strategies,
using a short context-string to identify which proof-section,
given that there may be more than one.
\begin{code}
replayProofPlan :: Proof -> Proof -> RRResult Proof
replayProofPlan oprf rprf
 = let oplan = plan oprf
       rplan = plan rprf
       rsc   = side rprf
       rpenv = context rprf
       hctxt = topNonHYPMtchCtxt rprf
       rmctxts = mtchCtxt rprf
   in do (rplan',rpenv',rmctxts')
                    <- replayStrategy "" rpenv hctxt rmctxts rsc oplan rplan
         return rprf{plan=rplan', context=rpenv', mtchCtxt=rmctxts'}

replayStrategy
       :: String -> TheoryStack -> MatchContext -> [MatchContext]
       -> SideCond -> Strategy -> Strategy
       -> RRResult (Strategy, TheoryStack, [MatchContext])


replayStrategy ctxt rpenv hctxt rmctxts rsc (Reduce ops) (Reduce rps)
 = fmap (setfst3 Reduce)
   $ replayProofSection (ctxt++"Red.") rpenv hctxt rmctxts rsc ops rps

replayStrategy ctxt rpenv hctxt rmctxts rsc (Lhs2Rhs ops) (Lhs2Rhs rps)
 = fmap (setfst3 Lhs2Rhs)
   $ replayProofSection (ctxt++"L2R.") rpenv hctxt rmctxts rsc ops rps

replayStrategy ctxt rpenv hctxt rmctxts rsc (Rhs2Lhs ops) (Rhs2Lhs rps)
 = fmap (setfst3 Rhs2Lhs)
   $ replayProofSection (ctxt++"R2L.") rpenv hctxt rmctxts rsc ops rps

replayStrategy ctxt rpenv hctxt rmctxts rsc
              (RedBoth oi ops1 ops2)
              (RedBoth _ rps1 rps2)
 = do (rps1',rpenv1',rmctxts1')
       <- replayProofSection (ctxt++"RB1.") rpenv hctxt rmctxts rsc ops1 rps1
      (rps2',rpenv2',rmctxts2')
       <- replayProofSection (ctxt++"RB2.") rpenv1' hctxt rmctxts1' rsc ops2 rps2
      return $ (RedBoth oi rps1' rps2', rpenv2', rmctxts2')

replayStrategy ctxt rpenv hctxt rmctxts rsc
               (LawReduce _ _ ops)
               (LawReduce s sc rps)
 = fmap (setfst3 $ LawReduce s sc)
   $ replayProofSection (ctxt++"LWR.") rpenv hctxt rmctxts rsc ops rps

replayStrategy ctxt rpenv hctxt rmctxts rsc (Assume opr ostr) (Assume rpr rstr)
 = replayStrategy (ctxt++"ASS:") rpenv hctxt rmctxts rsc ostr rstr

replayStrategy ctxt rpenv hctxt rmctxts rsc oplan rplan
 = fail ("replayStrategy: Original and Replay Strategies DIFFER !!!!, context:"++ctxt)
\end{code}


\subsection{Replaying the Proof Check}

The proof check is very straightforward,
only requiring the proof, and not any other context.
\begin{code}
replayProofCheck :: Proof -> Proof -> RRResult Proof
replayProofCheck oprf rprf
 = if done rprf'
   then return rprf'
   else fail "ProofCheck: failed --- proof replay not deemed complete"
 where rprf' = checkProof rprf
\end{code}

\subsection{Replaying ProofSections}

A proof-section is a sequence of predicates
 interleaved with justifications:
$$
  p_0,j_1,p_1,j_2,p_2,\ldots,p_{n-2},j_{n-1},p_{n-1},j_{n},p_n
$$
We have the property for all $i \in 1\ldots n$,
that $p_i = applyLaw(j_i,p_{i-1})$.
Proof-replay is essentially about ensuring that still holds.

The steps in a completed proof section
run backwards, from the end predicate down to the starting predicate:
$$
p_n, (j_n,p_{n-1})(j_{n-1},p_{n-2})\cdots(j_3,p_2)(j_2,p_1)(j_1,p_0)
$$
so we could check as follows:
\begin{eqnarray*}
   chk~p_0~\nil &\defs& true
\\ chk~p_i~(j_i,p_{i-1})\lcons rest
   &\defs&
   p_i = applyLaw(j_i,p_{i-1})
   \land
   chk~p_{i-1}~rest
\end{eqnarray*}
However we prefer to replay a proof in the same order
as would happen if being re-run manually by a user
---
remember that proof replay is not just for users tinkering
with theories, but also a means of regression testing
software changes, so it is not generally safe
to assume that the above check is accurate - a bug may
produce some form of ``directional divergence''.

So we have to work backwards through the originals
in order to build the replay.
What we do is to `twist' the original proof-section
to
$$
p_0, (j_1,p_1)(j_2,p_2)(j_3,\_)\cdots (\_,p_{n-2})(j_{n-1},p_{n-1})(j_n,p_n)
$$
and then walk through that, as follows:
\begin{eqnarray*}
   chk~p_n~\nil &\defs& true
\\ chk~p_{i-1}~(j_i,p_i)\lcons rest
   &\defs&
   p_i = applyLaw(j_i,p_{i-1})
   \land
   chk~p_i~rest
\end{eqnarray*}
\begin{code}
replayProofSection
  :: String -> TheoryStack -> MatchContext -> [MatchContext]
  -> SideCond -> ProofSection -> ProofSection
  -> RRResult (ProofSection, TheoryStack, [MatchContext])

replayProofSection what rpenv hctxt rmctxts rsc
                   (ofpr@(opr,_,_),_,_,opsteps)
                   rps@((rpr,_,_),_,_,_)
 | opr' =!= rpr
   = replayProofSteps what rpenv hctxt rmctxts rsc rps 1 ops'
 | otherwise
    = fail ( "ProofSection: proof-section STARTING goal mismatch ("++what++")"
           ++ "\nOriginal:\n" ++ show opr'
           ++ "\nReplay:\n"   ++ show rpr
           )
 where
    ops'@(opr',opsteps') = pstwist opr $ reverse opsteps

    pstwist prn [] = (prn,[])
    pstwist prn ((ji,prj):rest)
     = let (pri,rest') = pstwist prn rest
       in (prj,((ji,pri):rest'))
\end{code}

An pre-condition for \texttt{replayProofSteps} is that
\texttt{rpr} (or \texttt{fst3 rps})
and \texttt{opr} are $\alpha$-equivalent.
We do:
\begin{eqnarray*}
   chk~p_n~\nil &\defs& true
\\ chk~p_{i-1}~(j_i,p_i)\lcons rest
   &\defs&
   p_i = applyLaw(j_i,p_{i-1})
   \land
   chk~p_i~rest
\end{eqnarray*}
\begin{code}
replayProofSteps
  :: String -> TheoryStack -> MatchContext -> [MatchContext]
  -> SideCond -> ProofSection -> Int -> (Pred,[ProofStep])
  -> RRResult (ProofSection, TheoryStack, [MatchContext])

replayProofSteps what rpenv hctxt rmctxts rsc rps i (opr,[])
 = return (rps,rpenv,rmctxts)

replayProofSteps what rpenv hctxt rmctxts rsc
                 (rfpr,rfvs,rttbl,rpsteps)
                 i
                 (opr,(just,opr'):opsteps)
-- = do (rpr',rctxt',rpenv',rmctxts',r')
 = do (rfpr',rpenv',rmctxts',r')
          <- replayProofStep rpenv hctxt rmctxts rsc rfpr i just
      assessStep rfpr' rpenv' rmctxts' r'

 where

  assessStep rfpr' rpenv' rmctxts' (RR _s [])
   | opr' =!= getPFTop rfpr'
    = replayProofSteps what rpenv' hctxt rmctxts' rsc
                             (rfpr',rfvs,rttbl,(just,getPFocus rfpr):rpsteps)
                             (i+1)
                             (opr',opsteps)
  assessStep rpr' rpenv' rmctxts' _
    = do addMsg $ mismatch i opr' rpr'
         replayProofSteps what rpenv hctxt rmctxts rsc
                             (setPFocus opr',rfvs,rttbl,(just,getPFocus rfpr):rpsteps)
                             (i+1)
                             (opr',opsteps)

  mismatch i opr' rpr'
   = "ProofSteps: (" ++ what ++ ",step-" ++ show i ++ " : " ++ show just ++ ")"
     ++ "\nOriginal:\n" ++ show opr'
     ++ "\nReplay:\n"   ++ show rpr'
\end{code}

\subsection{Replaying a Proof-Step}

Apply Justification \texttt{(prel,fpath,infer,binds)}  to \texttt{rpr}
\begin{code}
replayProofStep
  :: TheoryStack -> MatchContext -> [MatchContext]
  -> SideCond -> FPred -> Int -> Justification
  -> RRResult (FPred, TheoryStack, [MatchContext], ReplayReport)

replayProofStep rpenv hctxt rmctxts rsc rfpr i (prel,fpath,infer,binds)
 = do let frpr = setPFocusPath fpath $ clearPFocus rfpr
      (rfpr',rpenv',rmctxts', r')
                     <- replayInfer rpenv hctxt rmctxts rsc frpr binds infer
      return $ (rfpr', rpenv', rmctxts',r')
--
-- keep in case we upgrade setPFocusPath to return a flag
--  = do let (ok,frpr) = setpfocuspath fpath $ clearpfocus rfpr
--       if ok
--        then do (rfpr',rpenv',rmctxts', r')
--                      <- replayinfer rpenv hctxt rmctxts rsc frpr binds infer
--                return $ (rfpr', rpenv', rmctxts',r')
--        else
--         rrr msg (rfpr, rpenv, rmctxts, rr msg)
--  where
--    msg = "step:"++show i
--              ++ ", unable to setpfocuspath : "++show fpath
--              ++ "\nreplay predicate:\n" ++ show rfpr
\end{code}


\newpage
\subsection{Replaying an Inference}

The \texttt{Pred} argument here must have the focus set
as specified by the \texttt{Justification}:
\begin{code}
replayInfer
         :: TheoryStack -> MatchContext -> [MatchContext]
         -> SideCond -> FPred -> Binding -> Inference
         -> RRResult (FPred, TheoryStack, [MatchContext], ReplayReport)

replayInfer rpenv hctxt mctxts sc fpr binds
                                    (NamedLaw mtyp fullname prov)
 = replayNamedLaw rpenv hctxt mctxts sc fpr binds
                  mtyp fullname prov

replayInfer rpenv hctxt mctxts sc fpr binds (InstantLaw lname prov)
 = replayInstantLaw rpenv hctxt mctxts sc fpr binds
                    lname prov

replayInfer rpenv hctxt mctxts sc fpr binds NameReplace
 = return (repFocus rpenv fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds (NameFold qtgt)
 = return (repPFocus (PVar $ parseVariable qtgt) fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds RecExpand
 = return (expandFocus (map preds rpenv) fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds ISubstitute
 = return (fst $ subFocus hctxt sc fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds (AlphaSubs esub)
 = return (alfFocus hctxt sc subs fpr, rpenv, mctxts, rrOK)
 where
   subs = mapSub remVar esub
   remVar (Var v) = v
   remVar e = preVar $ show e

replayInfer rpenv hctxt mctxts sc fpr binds (ITidy tspec)
 = return (tdyPred tspec fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds ISimplify
 = return (simpPred fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds (INorm ntype)
 | ntype == "DNF"  =  return (normPred dnf fpr, rpenv, mctxts, rrOK)
 | ntype == "CNF"  =  return (normPred cnf fpr, rpenv, mctxts, rrOK)
 | otherwise       =  fail ("Infer: INorm, unknown normalisation type : "++ntype)

replayInfer rpenv hctxt mctxts sc fpr binds (ISplit ixs)
 = return (iSplitPred ixs fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds IApply
 = return (fst $ redFocus hctxt sc (envPreds rpenv) fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds (UName newvar)
 = let fpr' = repPFocus (PVar $ parseVariable newvar) fpr
       rpenv' = snd $ notePLTPred newvar (getPFocus fpr) rpenv
   in return (fpr', rpenv', mkMatchContexts rpenv', rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds (Witness wsubs)
 = return (applyWitness hctxt sc wsubs fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds BinderSplit
 = return (bndrSplitPred fpr, rpenv, mctxts, rrOK)
 where bs = [] -- NEEDS TO COME FROM FContext

replayInfer rpenv hctxt mctxts sc fpr binds AssertDefined
 = return (assertDefFocus fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds ForallStrip
 = return (stripPred fpr, rpenv, mctxts, rrOK)

replayInfer rpenv hctxt mctxts sc fpr binds PropagateEq
 = return (propEqPred fpr, rpenv, mctxts, rrOK)

ri penv mctxts fpr msg
 = do let rep = rr msg
      addReport rep
      return (fpr, penv, mctxts, rep)

rinyi penv mctxts fpr what = ri penv mctxts fpr ("replayInfer "++what++" NYI")
\end{code}

\newpage
\subsubsection{Replaying \texttt{NamedLaw}}


\begin{code}
replayNamedLaw rpenv hctxt mctxts sc fpr binds mtyp fullname prov
 = case fullLawLookup lname
                      rpenv (hctxt:mctxts) of
     Nothing  -> nlfail "not found"
     Just (law,thnm,thno,mctxt)
      -> let tags = thd3 $ getPFContext fpr
             (fpr',tts) = fpredTypeTables mctxt fpr
             mtchs = filter (hasMType mtyp)
                               $ subLawMatch tags fovs tts mctxt sc fpr' law
         in if null mtchs
            then nlfail (" did not '"++show mtyp++"'-match with "++show fpr)
            else
             do (fpr'', rr')
                       <- replayApplyMatch rpenv mctxt fpr' binds (head mtchs)
                return (fpr'', rpenv, mctxts, rr')
 where
   (thname,_,lname) = qparse fullname
   fovs = evalFreeVars hctxt sc (getPFocus fpr)
   nlfail msg = fail ("NamedLaw: Law '"++lname++"' : "++msg)
   len xs = "length = "++show (length xs)

replayApplyMatch rpenv mctxt fpr binds mtch
 = do (ok,fmatch@(m,p,b,_,reps))
         <- replayFinalise rpenv mctxt binds mtch
      if ok
       then
        do let apred = applyLaw mctxt (0,fmatch,"") fpr
           return (apred, rrOK)
       else fail "ApplyMatch: Couldn't finalise"
\end{code}

\newpage
As \texttt{finaliseMatch} is an IO action, asking the user to complete
missing bindings, we need to do a pure version here that answers
those same questions using the proof bindings as oracles.
\begin{code}
replayFinalise rpenv mctxt
               (ogpbind,ovebind,ottbind)
               mtch@( mtyp, prov
                    ,(gpbind,vebind,ttbind)
                    , sc, [repl] )
 = do let pvars = predFreePVars mctxt repl
      let evars = predFreeVars mctxt repl
      (pok',gpbind')
        <- replayUserBindings True tvlookup ptables  tvupdate ogpbind gpbind pvars
      (eok',vebind')
        <- replayUserBindings pok' tvlookup etables  tvupdate ovebind vebind evars
      return ( eok'
             , ( mtyp
                 , prov
                 , (gpbind',vebind',ttbind)
                 , sc
                 , [repl]
               )
             )
 where
     ptables = map (tmap TO) $ knownPreds mctxt
     etables = map (tmap TO) $ knownExprs mctxt
\end{code}

\begin{code}
replayUserBindings False lkp known upd obnds bnds _   = return (False,bnds)
replayUserBindings True  lkp known upd obnds bnds []  = return (True,bnds)

replayUserBindings True lkp known upd obnds bnds (v:vs)
 = case lkp bnds v of
    (Just _)  ->  replayUserBindings True lkp known upd obnds bnds vs
    Nothing
     ->  case tsvlookup known v of
           (Just x)
            ->  do let bnds' = upd v x bnds
                   replayUserBindings True lkp known upd obnds bnds' vs
           Nothing
            -> do (ok,bnds') <- replayBindingFromUser lkp upd obnds v bnds
                  if ok
                   then replayUserBindings True lkp known upd obnds bnds' vs
                   else return (False,bnds)
\end{code}

We use the original proof bindings as an oracle/proxy for the user's
response:
\begin{code}
replayBindingFromUser lkp upd obnds v bnds
 = case lkp obnds v of
    Nothing     ->  return (False,bnds)
    Just thing  ->  return (True,upd v thing bnds)
\end{code}

\subsection{Replaying \texttt{InstantLaw}}

\begin{code}
replayInstantLaw rpenv hctxt mctxts sc fpr binds lname prov
 = case fullLawLookup lname rpenv mctxts of
    Nothing  ->  ilfail "No such law"
    (Just (law,thnm,thno,mctxt))
            -> do fpr' <- replayInstantiateAndConjoinLaw
                            rpenv fpr binds thnm thno lname law mctxt
                  return(fpr', rpenv, mctxts, rrOK)
 where
   ilfail msg = fail ("InstantLaw: Law '"++lname++"' : " ++ msg)
\end{code}

\begin{code}
replayInstantiateAndConjoinLaw
          rpenv fpr binds thnm thno lname ((lpr,lsc),prov,_) mctxt
 | lsc /= SCtrue  =  fail ( "InstantiateAndConjoinLaw: Instantiated Law '"
                           ++lname
                           ++"' must be side-condition free")
 | otherwise
  = do let mtch = (All,prov,nullBinds,lsc,[lpr])
       (ok,fmatch@(m,p,b,_,reps))
         <- replayFinalise rpenv mctxt binds mtch
       if ok
        then do let fullname = qlawprint3 (thnm,thno,lname)
                let ilaw = matchReplace mctxt (0,fmatch,fullname)
                let ifpred = conjoinLawInstance ilaw fpr
                return ifpred
        else fail ("InstantiateAndConjoinLaw: Instant Law '"++lname++"' - can't finalise")
\end{code}
