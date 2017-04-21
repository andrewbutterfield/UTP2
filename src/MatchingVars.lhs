\section{Variable-List Matching}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module MatchingVars where
import Tables
import Datatypes
import DataText
import Utilities
import MatchTypes
import MatchingVar

import Data.List
import Data.Maybe
\end{code}

\subsection{Basic Quantifier Matching}


\subsubsection{Quantifier-Match Conditioning}

Given a quantifier body match,
the first thing we want to do is to check  for compatibility
with the quantifier lists to be matched and effectively remove
any that have already been matched, to simplify what remains.
We call this step ``conditioning'' the quantifier match.

For example, matching test $\forall a,b @ C$ against pattern $\forall x,y @ P$,
first matches $C$ against $P$.  Say this succeeds, binding $y$ to $a$.
Then, instead of trying to match test quantifier list $a,b$
against $x,y$ and hope to get $y$ bound to $a$,
we simply simplify our quantifier matching problem here to matching $b$
against $x$, and so get the final result $\mapof{x \to b, y \to a}$.
Should the $C$ vs $P$ match return a binding of $y$ to $c$ (say),
then the whole match fails, as the quantifier list match forces $y$
to bind to either on of $a$ or $b$, but not $c$, or any other variable that
might be in $C$.

To condition a match, we work through the pattern variables,
see if they have been bound (in \texttt{ebnds}).
If so, we look for their target in the test variables.
If found, we remove both.
If not found, we fail.
\begin{code}
qMCondition :: Monad m
            => MatchResult -> QVars -> QVars -> m ( QVars, QVars )

qMCondition ((_,vebnds,_),_,_) (Q tqv) (Q pqv)
 = qMcond [] tqv pqv
 where

   qMcond pcv tqv [] = return (Q tqv, Q $ reverse pcv)
   qMcond pcv tqv (pv:pqv)
    = case tvlookup vebnds pv of
       Nothing    ->  qMcond (pv:pcv) tqv pqv -- not matched, so keep
       Just vobj  ->  qMcheck pcv pqv tqv vobj pv  -- matched, check in tqv
\end{code}
If \texttt{pv} is standard, then \texttt{tve} must be a standard variable, and we need
to find it in \texttt{tqv}:
\begin{code}
   qMcheck pcv pqv tqv (TO (Var tv@(Gen (Std _),_,_))) (Gen (Std _),_,_)
     | tv `elem` tqv  =  qMcond pcv (tqv \\ [tv]) pqv
\end{code}
If \texttt{pv} is a list variable, then \texttt{tve} must be a sequence
of variables, and we need
to find them in \texttt{tqv}:
\begin{code}
   qMcheck pcv pqv tqv (VSO tvvs) (Gen (Lst _),_,_)
     =  qMcond pcv (tqv \\ tvvs) pqv
   qMcheck pcv pqv tqv (TSO tves) (Gen (Lst _),_,_)
     | all (`elem` tqv) tvvs  =  qMcond pcv (tqv \\ tvvs) pqv
     where tvvs = map getVar tves
\end{code}
If \texttt{pv} is a reserved variable, we leave everything as is, and move on
(best dealt with by \texttt{qMatch}):
\begin{code}
   qMcheck pcv pqv tqv _ pv@(Rsv _ _,_,_)  =  qMcond (pv:pcv) tqv pqv
\end{code}
All other cases result in failure.
\begin{code}
   qMcheck _ _ _ _ _ = fail "Nothing"
\end{code}

\newpage
\subsection{Quantifier Matcher}

Quantifier-list matching has two phases:
the first (\texttt{qMatch1}) deals with any pattern reserved variables,
while the second (\texttt{qMatch2}) processes the rest.

Given that all these variables are in quantifier lists,
none are considered to be ``known''.

In amongst the list variables are the reserved ones.
The key thing to keep in mind here is that a reserved
variable like $O$ is a shorthand for a list of observation variables.
So the binding of such a variable has to be of something of potentially
the same length. In fact we expect reserved variables in patterns
to match observation variables in scope,
despite being in a binding position
---this is not necessary for the soundness of the prover,
but helps keep things clear for the user.
This is complicated by the presence of list-variables in reserved subtractions
(e.g., $O\less{\lst x}$, where we need to know the binding of $\lst x$
before we can be definitive about what $O\less{\lst x}$ is bound to).
If $O$ stands for $o_1,\ldots,o_n$, then a binding of $O$ to $x_1,\ldots,x_n$
is equivalent to bindings of $o_i$ to $x_i$, for $i \in 1\ldots n$.

We first look for any reserved variables in the pattern,
and see if these can be matched against test variables.
The remaining  parts of pattern and test are then
subject to a number of heuristics,
before being defferred, if necessary.
\begin{code}
qMatch :: Monad m
       => LocalContext
       -> MatchResult
       -> QVars             -- test QVars
       -> QVars             -- pattern QVars
       -> m MatchResult

qMatch here mres (Q tvs) (Q pvs)
 = do let (prvs,pgvs) = partition isRsvV pvs
      let (tks,tus,tls,tRs) = classifyVars (isKnownObsVar . mctx) here tvs
      let tRos = concat $ map denotePair tRs
      let kobs = ( sizeMdl  mctxt > 0
                 , sizeScr  mctxt > 0
                 , sizeMdl' mctxt > 0
                 , sizeScr' mctxt > 0 )
      (ctvs',mres1,umrvs)
                     <- qMatch1 here mres [] (tks,tus,tls,tRs) tRos prvs
      let tvs' = cvmerge ctvs'
      qMatch2 here mres1 tvs' (lnorm (pgvs ++ umrvs))
 where
   mctxt = mctx here
   denotePair tR
    = let (obs,subr) = gVarDenote (mctx here) tR
      in map (pairR tR) obs
   pairR tR ob = (ob,tR)
   cvmerge (kvs,uvs,lvs,rvs) = kvs++uvs++lvs++rvs
\end{code}

\subsubsection{Quantifier Matching, Phase 1}

We handle each reserved variable one at a time,
returning bindings and/or defferred \texttt{QVar} matches,or failing:
\begin{code}
qMatch1 :: Monad m
        => LocalContext
        -> MatchResult
        -> [Variable]
        -> ClassedVars
        -> [(Variable, Variable)]  --   std obs -+-> Rsv
        -> [Variable]
        -> m ( ClassedVars, MatchResult, [Variable] )

qMatch1 here mres umrvs ctvs tRos [] = return(ctvs, mres, umrvs)

qMatch1 here mres umrvs ctvs tRos (prv:prvs)
 = do (ctvs',tRos',mres',umrvs') <- rsvMatch (mctx here) mres umrvs ctvs tRos prv
      qMatch1 here mres' umrvs' ctvs' tRos' prvs
\end{code}

\newpage
Given a pattern reserved variable, we look among the test variables
for possible bindings.
\MRULES{
  \Gamma & R & (v_1,\ldots,v_n) & \beta
}
\begin{code}
rsvMatch :: Monad m
         => MatchContext
         -> MatchResult
         -> [Variable]
         -> ClassedVars
         -> [(Variable,Variable)]
         -> Variable
         -> m ( ClassedVars, [(Variable,Variable)], MatchResult, [Variable] )
\end{code}
We subsume a lot of rules with this case:
\MRULES{
   \Gamma & R & (\ldots,R,\ldots)               & \maplet R R
\\ \Gamma & R & (\ldots,\sem{R},\ldots)         & \maplet{R}{\sem{R}}
\\ \Gamma & R_a & (\ldots,R_b,\ldots)           &  \maplet{R_a}{R_b}
\\ \Gamma & O^d & (\ldots,M^d,S^d,\ldots)       & \maplet{O^d}{(M^d,S^d)}
\\ \Gamma & O^d & (\ldots,M^d,\sem{S^d},\ldots) & \maplet{O^d}{(M^d,\sem{S^d})}
}
The code below also works for $R\less{o1,\ldots,o\ell}$,
where $\setof{o1,\ldots,o\ell} \subseteq \sem R$.
\begin{code}
rsvMatch mctxt mres umvrs ctvs@(tks,tus,tls,tRs) tRos prv
 | prv `elem` tRs
   = do mresult <- mres `mrgRMR` bindO oroots prv prv
        return ( (tks,tus,tls,tRs\\[prv])
               , remRv prv tRos
               , mresult
               , umvrs )
 |  null psubr && (fst $ varsDenote mctxt tmatch)
                `eqvsMS`
                (fst $ varsDenote mctxt pRsem)
   = do bind' <-bindOL oroots prv tmatch
        mres' <- mres `mrgMR` (bind', [], [])
        return ( (tksout,tusout,tls,tRs\\(map snd tRosin))
               , tRosout
               , mres'
               , umvrs)
 | null (tks++tus++tls)
   && length tRs == 1 && length psubr == 1 && length tsubr == 1
   && vdMatch prv trv
   = do mres1 <- mres `mrgRMR` bindO oroots prv trv
        let bindSub = nullBinds
        mres' <- mres1 `mrgMR` ( bindSub, [], [])
        return ( ( [], [] ,[], [] )
                 , remRv prv tRos
                 , mres'
                 , umvrs )
 where
   oroots = obsRoots mctxt

   (pRsem,psubr) = gVarDenote mctxt prv
   (tksin,tksout) = partition (flip elem pRsem) tks
   (tusin,tusout) = partition (flip elemMS pRsem) tus
   (tRosin,tRosout) = partition (flip elemMS pRsem . fst) tRos
   tmatch = lnorm (tksin++tusin++map snd tRosin)

   [trv] = tRs
   (tRsem,tsubr) = gVarDenote mctxt trv
   psub1 = head psubr
   tsub1 = head tsubr
\end{code}

If we get here, then matching this reserved variable is deferred.
For now this is all reserved variables of the form $R\less{\ldots,u,\ldots}$
where $u \notin \sem R$.
\begin{code}
rsvMatch mctxt mres umvrs ctvs@(tks,tus,tls,tRs) tRos prv
 = return (ctvs, tRos, mres, prv:umvrs)
\end{code}

Variable equality, modulo subscripts:
\begin{code}
eqVModSubscript :: Variable -> Variable -> Bool
eqVModSubscript (r1,Subscript _,_) (r2,Subscript _,_)  =  r1 == r2
eqVModSubscript v1                 v2                  =  v1 == v2

[]       `eqvsMS` []        =  True
(v1:vs1) `eqvsMS` (v2:vs2)  =  v1 `eqVModSubscript` v2 && vs1 `eqvsMS` vs2
_        `eqvsMS` _         =  False

tRs `intsctMS` pMS = sort $ intersectBy eqVModSubscript tRs pMS

elemMS = elemBy eqVModSubscript

remRv rv tros = filter (not . (==rv) . snd) tros
\end{code}

\newpage
\subsubsection{Quantifier Matching, Phase 2}


We are now trying to match test
$$
a_1,\ldots,a_n , \lst b_1,\ldots,\lst b_m
$$
against pattern
$$
  u_1,\ldots,u_k ,  \lst v_1,\ldots,\lst v_\ell
$$
which will only work if
$$
n \geq k \land ((n \neq k \lor m > 0) \implies \ell > 0)
$$
A match is infeasible if the number of pattern standard variables
is greater than the number of test standard variables.
\begin{code}
qMatch2 :: Monad m
        => LocalContext -> MatchResult
        -> [Variable] -> [Variable] -> m MatchResult
\end{code}
Initially, we try to pick off some common simple cases.

\MRULES{
   \Gamma & s & t & \maplet s t
}
\begin{code}
qMatch2 here mres [tv@(Gen (Std _),_,_)] [pv@(Gen (Std _),_,_)]
 = mres `mrgRMR` (okBindV pv tv)
\end{code}
\MRULES{
   \Gamma & \lst x & (v_1,\ldots,v_n) & \maplet{\lst x}{(v_1,\ldots,v_n)}
\\ \Gamma|_{u\textsf{ not obs.}} & R\less u & \sem{R}\setminus\setof{k}
  & \mapof{ R\less u \to \sem{R}\setminus\setof k, u \to k }
}
\begin{code}
qMatch2 here mres tvs [pv]
 | isGenV pv  =  mres `mrgRMR` (okBindQL pv tvs)
 | isRsvV pv
   =  let (Rsv pr pless,pd,_) = pv
      in  srvMatch (mctx here) mres tvs pv pr pless pd
 | otherwise     =  fail "Nothing"

-- pattern singles must cover all test singles
-- then look at reserved list variables
qMatch2 here mres tvs pvs
 | n < k                         =  (fail "Nothing")
 | ell == 0 && (n > k || m > 0)  =  (fail "Nothing")
 | otherwise
     =  do (vebinds',tvs',pvs') <- matchRsvVs tvs pvs
           mres `mrgMR` ((tnil,vebinds',tnil),mkQVarsToDo tvs' pvs',[])
 where
   mctxt = mctx here
   (stdt,lstt) = vPartition tvs
   (stdp,lstp) = vPartition pvs
   n = length stdt ; m = length lstt
   k = length stdp ; ell = length lstp

   -- if all reserved list variables are 'clean', match them here
   -- matchRsvVs :: [Variable] -> [Variable]
   --            -> m (VEBind, [Variable], [Variable])
   matchRsvVs tvs pvs
    | tclean && pclean = mRsvVs tnil [] tvs pvs
    | otherwise  =  return (tnil,tvs,pvs)
    where
      tclean = all (cleanVar mctxt) tvs
      pclean = all (cleanVar mctxt) pvs

   -- for every (clean) pattern reserved variable,
   -- pull out its denotation from the test variables
   mRsvVs qbind svp tvs []  =  return $ (qbind,tvs,reverse svp)
   mRsvVs qbind svp tvs (pv:pvs)
    | isRsvV pv  =  do (mvs',tvs') <- getDen dvs tvs
                       qbind' <- veupdateVSO pv mvs' qbind
                       mRsvVs qbind' svp tvs' pvs
    | otherwise     =  mRsvVs qbind (pv:svp) tvs pvs
    where
      (dvs,_) = varExpand mctxt pv -- clean, so no subtractions

      -- getDen :: [Variable] -> [Variable] -> Maybe ([Variable],[Variable])
      getDen dvs tvs = gD dvs [] [] [] tvs

      gD dpv mdvs mvs svt []
        | dpv == mdvs'  =  return (lnorm mvs, reverse svt)
        | otherwise    =  fail ""
        where mdvs' = lnorm mdvs
      gD dpv mdvs mvs svt (tv:tvs)
       | dtv `subsetOf` dpv  =  gD dpv (dtv++mdvs) (tv:mvs) svt      tvs
       | otherwise           =  gD dpv mdvs        mvs        (tv:svt) tvs
       where
         (dtv,_) = varExpand mctxt tv
\end{code}

\newpage

Matching a single reserved list-variable (s.r.v.)
of the form $R\less{\ldots,u,\ldots}$ where $u$ might be an
observation variable.
against an arbitrary \texttt{QVar}-list.
\MRULES{
   \Gamma|_{u\textsf{ not obs.}} & R\less u & \sem{R}\setminus\setof{k}
 & \mapof{ R\less u \to \sem{R}\setminus\setof k, u \to k }
}
At this point we can assume that $R\less u$ iteself is not among the test variables
(as it would have been caught in Phase 1).
\begin{code}
srvMatch :: Monad m
         => MatchContext
         -> MatchResult
         -> [Variable] -- arbitrary test variables
         -> Variable   -- Reserved List-Variable (isRsvV)
         -> RsvRoot
         -> [GenRoot]
         -> Decor
         -> m MatchResult
\end{code}

Simplest case --- one of each, with one unknown subtraction each.
\MRULES{
   \Gamma|_{u,v\textsf{ not obs.}} & R\less u &R\less v
 & \mapof{ R\less u \to R\less v, u \to v }
}
\begin{code}
srvMatch mctxt mres [tv@(Rsv tr [v@(Std _)],td,_)] pv pr [u@(Std ustr)] pd
 | tr == pr && td `dMatch` pd
   = do bindU <- bindu u v
        bindR <- bindOL oroots pv [tv]
        bind' <- bindR `mrgB` bindU
        mres `mrgMR` (bind', [], [])
 where
  oroots = obsRoots mctxt
  bindu u v
   | ustr `elem` oroots  =  fail "Nothing" -- prevent known var matching unknown
   | otherwise           =  return $ bindV (genRootAsVar u) (genRootAsVar v)
\end{code}

Case $pv = R\less{ks,us}$
\begin{eqnarray*}
   \sem R &=& k_1,\ldots,k_i,k_{i+1},\ldots,k_n
\\ \sem{R\less{k_{i+1},\ldots,k_n,u_1,\ldots,u_n}}
   &=& k_1,\ldots,k_i \setminus u_1,\ldots,u_n
\end{eqnarray*}
Matching fails if $n > i$.
\begin{code}
srvMatch mctxt mres tvs pv pr pless@(_:_) pd
 | all isStdG pless && length psubg <= length mkvs
   = do bindR <- bindOL oroots pv $ lnorm (mrest++akvs)
        bind' <- bindR `mrgB` (tnil, subbind, tnil)
        mres `mrgMR` (bind', [], [])
 where
   (pkvs,psubg) = gVarDenote mctxt pv -- (Rsv pr [], pd, varKey pv)
   akvs = tvs `intsctMS` pkvs
   mkvs = pkvs \\ akvs
   oroots = obsRoots mctxt
   (subbind,mrest) = pairup [] psubg mkvs

   -- greedy, match in the order in which they occur
   pairup pairs [] mkvs = (lbuild pairs,mkvs)
   pairup pairs (pg:psubg) (mkv:mkvs)
    = pairup ((renderVar (Gen pg) pd, VO mkv):pairs) psubg mkvs
\end{code}

Case $tvs = ks,R_t\less{ks'}$, and $pv = R_p\less{\lst u}$.
Provided $\sem{R_t}\setminus ks' \subseteq \sem{R_p}$:
\begin{eqnarray*}
   \sem{R_p\less{\lst u}} &=& \sem{R_p} \ominus \setof{\lst u}
\\ \sem{ks,R_t\less{ks'}} &=& ks \cup \sem{R_t} \setminus ks' \ominus \emptyset
\\ \lst u &\mapsto& \sem{R_t}\setminus (ks \cup \sem{R_t} \setminus ks')
\end{eqnarray*}
\begin{code}
srvMatch mctxt mres tvs pv pr [us@(Lst ustr)] pd
 | issing pX && null tX && null (tV\\allV)
   = do bindR <- bindOL oroots pv tvs
        bind' <- bindR `mrgB` bindQL (mkGVar pd us) (allV\\tV)
        mres `mrgMR` (bind', [], [])
 where
   (pV,pX) = gVarDenote mctxt pv
   issing [_] = True
   issing _   = False
   (allV,_) = gVarDenote mctxt $ mkRVar pr [] pd
   (tV,tX) = varsDenote mctxt tvs
   oroots = obsRoots mctxt

srvMatch _ _ _ _ _ _ _ = fail "Nothing"
\end{code}


To allow $Q$ to match against $\forall \lst x @ P$
with $\lst x$ bound to nil, we need a special matcher
\begin{eqnarray*}
   \MRNullQuantZN && \MRNullQuantZ
\end{eqnarray*}
\begin{code}
qMatchNull :: Monad m
           => MatchResult
           -> QVars             -- pattern QVars
           -> m MatchResult

qMatchNull mres (Q qs)
 | all isGenV qs = mres `mrgMR` (injQLbind $ map bindnull qs)
 | otherwise  =  fail "Nothing"
 where bindnull (_,_,vs) = (vs,[])
\end{code}

\newpage
\subsubsection{Valid reserved list-Variable lists}
