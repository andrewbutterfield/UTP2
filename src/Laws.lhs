\section{Laws}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module Laws where
import Tables
import Datatypes
import DataText
import Flatten
import Focus
import MatchTypes
import Matching
import Instantiate
import AlphaSubs
import FreeBound
import Types
import SideConditions
import Heuristics
import Substitution
import Utilities
import DSL
import Data.List
import Data.Maybe
import Debug.Trace
import Control.Monad
\end{code}

\subsection{Theorems are Universal}

A ``law'' (axiom,or theorem)
is a predicate guaranteed to evaluate true for all (well-defined)
values for its free variables.
A consequence of this notion of theoremhood is the fact,
for arbitrary $\vec x$,
that the following statements are equivalent:
\begin{enumerate}
  \item $P$ is a theorem
  \item $\forall \vec x @ P$ is a theorem
  \item $[P]$ is a theorem
  \item $[P]$ evaluates to $\TRUE$.
\end{enumerate}
So when we record laws, we strip out top-level universal quantifiers,
and do the same for any goal predicate being matched against
an \emph{entire}%
\footnote{
 See the section (p\pageref{sssec:law-matches}) on matching types
 for cases where we match against parts of laws.
}
 law.
\begin{code}
hm_stripForall = (
    unlines $
      [ " : Strip Forall\n"
      , "When using the Law Reduce strategy, all proof steps are Theorems"
      , "If P is a theorem, then so are (forall x$ @ P) and [P], and v.v."
      , "In this case, it often makes sense to strip outer forall quantification."
      , "This command does this only for a top-level focus in a Law-Reduce proof."
      ])

remOuterForall (PAbs nm _ _ [p])
 | nm == n_Forall  =  remOuterForall p
 | nm == n_Univ    =  remOuterForall p
remOuterForall p   =  p
\end{code}

\newpage
\subsection{Well-Formed Laws}

If the top-level predicate of a law is \texttt{Eqv},
then the lhs cannot be a single \texttt{PVar},
so laws of the form $F(A)\equiv A$ and $A \equiv F(A)$
are both represented as \texttt{Eqv (repr-F ... PVar "A") (PVar"A")}.

The (vacuous) law $A \equiv A$ is not allowed.
This latter is a nuisance as it always matches,
does nothing and tends to rank very highly,
so we replace it by $True$, which as a theorem is mainly harmless%
\footnote{
Should we perhaps ban the addition of $P \equiv P$ as a conjecture?
}%
.
The replacement of $X \equiv X$ by $True$ in a proof, when required,
is done by matching the rhs of
axiom $\AXeqvId$ ($\AXeqvIdN$).

Also very important is to ensure that a law
uses unique bound variables, which can always be ensured by
alpha-renaming.
\begin{code}
pred2law (PApp nm [PVar s, PVar t])
 | nm == n_Eqv && s==t  =  TRUE
pred2law (PApp nm [pv@(PVar a), rhs])
 | nm == n_Eqv          =  (mkEqv (uniqueBinds rhs) pv)
pred2law pr = uniqueBinds pr

uniqueBinds = freeBoundPartition mctxt0
\end{code}

Often we want to elevate a predicate to a law with a trivial (true) side-condition:
\begin{code}
trivSC pred = (pred,SCtrue)
\end{code}


\newpage
\subsection{Law Tables}

We can match against a list of name-law pairs
(although a better DS for this may someday be introduced%
\footnote{
Whenever we find the need, as at present, matching all the laws and then sorting
the resulting matches to display the top-ranking first 20, after a mouse right-click,
pretty much takes about as much time as the mouse-click~!
}%
):
\begin{code}
type LawTable = [(String,Law)]

lwlookup [] nm = Nothing
lwlookup ((k,d):rest) nm
  | nm == k    =  Just d
  | otherwise  =  lwlookup rest nm
\end{code}

Deleting a law by name is sometimes useful:
\begin{code}
lwdelete _ [] = []
lwdelete nm (law@(k,d):rest)
  | nm == k    =  rest
  | otherwise  =  law : lwdelete nm rest
\end{code}

Adding a law by name:
\begin{code}
lwadd k' d' laws = (k',d'):laws
\end{code}

Replacing a law by name:
\begin{code}
lwupdate k' d' [] = [(k',d')]
lwupdate k' d' (law@(k,d):rest)
 | k' == k  =  (k',d'):rest
 | otherwise  =  law : lwupdate k' d' rest
\end{code}



We define some functions for constructing laws as singleton law
tables and the merging them. The idea is to use heuristics to
determine an suitable ordering (more complex/specific first).
Basic law builders:
\begin{code}
mklaw :: Provenance -> String -> Pred -> SideCond -> LawTable
mklaw prov name pred sc = [(name,((pred2law pred,sc),prov,mkTTable pred))]

mkTTable pred = Bnil -- for now ...

freelaw :: Provenance -> String -> Pred -> LawTable
freelaw prov name pred  = mklaw prov name pred SCtrue

ranklist rankf
 = map (app rankf)
 where app rankf (name,law@(pred,_)) = (name,(rankf pred,law))

infixr 5 ~:~
(~:~) :: LawTable -> LawTable -> LawTable
(~:~) = ltmerge compare
\end{code}


\newpage
\subsection{Side-Condition Matching}

We return all possible side-condition matchings,
as these can guide match completion later on.
Note, the failure to find any match is not a failure here,
as the law may not have a side-condition, or if it is different,
it still may be a consequence of the goal conditions, and hence
the resulting predicate match is still valid.
We assume that all \texttt{SCAnd} side-conditions have been
constructed using \texttt{scand}, and so are flat (no nested \texttt{SCAnd}s),
ordered and with no duplicates.
\begin{code}
scMatch :: MatchContext
        -> TypeTables -> TypeTables
        -> [TTTag] -> [TTTag]
        -> SideCond  -- tsc : test side-condition
        -> SideCond  -- psc : pattern side-condition
        -> [MatchResult]

scMatch mctxt ttts ptts ttags ptags
        (SCisCond ExprM tvar) (SCisCond ExprM pvar)
                 = [(bindV (parseVariable  pvar) (parseVariable  tvar),[],[])]
scMatch mctxt ttts ptts ttags ptags
        (SCisCond PredM tvar) (SCisCond PredM pvar)
            = [(bindP (parseGenRoot  pvar) (PVar $ parseVariable tvar),[],[])]

scMatch mctxt ttts ptts ttags ptags
        (SCfresh ObsM tvar) (SCfresh ObsM pvar)  = [(bindV pvar tvar,[],[])]

scMatch mctxt ttts ptts ttags ptags
        (SCnotFreeIn ExprM tvs tvar) (SCnotFreeIn ExprM pvs pvar)
 = moMerge (bindV (parseVariable pvar) (parseVariable tvar),[],[])
           (allVarMatches mctxt ttts ptts ttags ptags tvs pvs)

scMatch mctxt ttts ptts ttags ptags
        (SCnotFreeIn PredM tvs tvar) (SCnotFreeIn PredM pvs pvar)
 = moMerge (bindP (parseGenRoot pvar) (PVar $ parseVariable tvar),[],[])
           (allVarMatches mctxt ttts ptts ttags ptags tvs pvs)

scMatch mctxt ttts ptts ttags ptags
        (SCareTheFreeOf ExprM tvs tvar) (SCareTheFreeOf ExprM pvs pvar)
 = moMerge (bindV (parseVariable pvar) (parseVariable tvar),[],[])
           (allVarMatches mctxt ttts ptts ttags ptags tvs pvs)

scMatch mctxt ttts ptts ttags ptags
        (SCareTheFreeOf PredM tvs tvar) (SCareTheFreeOf PredM pvs pvar)
 = moMerge (bindP (parseGenRoot pvar) (PVar $ parseVariable tvar),[],[])
           (allVarMatches mctxt ttts ptts ttags ptags tvs pvs)

scMatch mctxt ttts ptts ttags ptags
        (SCcoverTheFreeOf ExprM tvs tvar) (SCcoverTheFreeOf ExprM pvs pvar)
 = moMerge (bindV (parseVariable pvar) (parseVariable tvar),[],[])
           (allVarMatches mctxt ttts ptts ttags ptags tvs pvs)

scMatch mctxt ttts ptts ttags ptags
        (SCcoverTheFreeOf PredM tvs tvar) (SCcoverTheFreeOf PredM pvs pvar)
 = moMerge (bindP (parseGenRoot pvar) (PVar $ parseVariable tvar),[],[])
           (allVarMatches mctxt ttts ptts ttags ptags tvs pvs)

scMatch mctxt ttts ptts ttags ptags tsc psc = []
\end{code}

\newpage
\subsubsection{All Possible Variable Matches}

Given a list of test variables, and a list of pattern variables,
we want all the possible ways in which they can match.
We can consider ourselves as dealing with four kinds of variables,
on both patterns and tests:
\begin{description}
  \item[Known Standard] ($k$)
  \item[Arbitrary Standard] ($a$)
  \item[Reserved List] ($R$)
  \item[Generic List] ($\ell$)
\end{description}
We shall use $pk$, $pa$, $pR$ and $p\ell$ to denote pattern variables,
and $tk$, $ta$, $tR$ and $t\ell$ to denote test variables.
We start by matching test:
\[  tk_1,\ldots,tk_v
~,~ ta_1,\ldots,ta_w
~,~ tR_1,\ldots,tR_x
~,~ t\ell_1,\ldots,t\ell_z \]
against pattern:
\[  pk_1,\ldots,pk_b
~,~ pa_1,\ldots,pa_c
~,~ pR_1,\ldots,pR_d
~,~ p\ell_1,\ldots,p\ell_f \]
\begin{code}
allVarMatches :: MatchContext
              -> TypeTables -> TypeTables
              -> [TTTag] -> [TTTag]
              -> [Variable]
              -> [Variable]
              -> [MatchResult]
allVarMatches mctxt ttts ptts ttags ptags tvs pvs
 = aVMphase1 tks tas tRs tls pks pas pRs pls
 where
   (pss,pms) = vPartition $ lnorm pvs
   (pks,pas) = kPartition mctxt pss
   (pRs,pls) = rPartition pms
   (tss,tms) = vPartition $ lnorm tvs
   (tks,tas) = kPartition mctxt tss
   (tRs,tls) = rPartition tms
\end{code}
The first thing we note is that all the pattern known variables ($pk_i$)
must find and match their counterparts among the test known variables ($tk_i$).
We obtain the bindings $pk_i \mapsto tk_j$, drop all the $pk$s, and remove the
$pk$ values from the $tk$s.
\begin{code}
   aVMphase1 tks tas tRs tls pks pas pRs pls
    | null (pks\\tks)
       = aVMphase2 mr1 (tks\\pks) tas tRs tls pas pRs pls
    | otherwise                   =  [] -- some pks without tks counterpart
    where
      mr1 = ((tnil,lbuild $ map mkKVmr pks,tnil),[],[])
      mkKVmr k = (varKey k,VO k)
\end{code}
We now have the following situation, with test,
\[  tk_1,\ldots,tk_u
~,~ ta_1,\ldots,ta_w
~,~ tR_1,\ldots,tR_x
~,~ t\ell_1,\ldots,t\ell_z
\qquad u=b-v
\]
pattern,
\[  pa_1,\ldots,pa_c
~,~ pR_1,\ldots,pR_d
~,~ p\ell_1,\ldots,p\ell_f \]
and binding: $\maplet{pk_i}{tk_j}$.
We should now be able to discharge all the pattern reserved variables
against remaining test variables. Such variables match themselves,
or members of their denotation (which is why we need the \texttt{MatchContext}).
\begin{code}
   aVMphase2 mr tks tas tRs tls pas [] pls = aVMphase3 mr tks tas tRs tls pas pls
   aVMphase2 mr tks tas tRs tls pas (pR@(pRr,pRd,_):pRs) pls
     -- do we have test MDL and SCR to correspond to a pattern OBS ?
     | pRr==Rsv OBS [] && null (obsAsMdlScr\\tRs)
        =  case (mr `mrgMR` fromJust (okBindQL pR obsAsMdlScr)) of
           Nothing   ->  []
           Just mr2  ->  aVMphase2 mr2 tks tas (tRs\\obsAsMdlScr) tls pas pRs pls
     -- does the pattern reserve occur in the test reserves ?
     | pR `elem` tRs
        = case (mr `mrgMR` fromJust (okBindV pR pR)) of
           Nothing   ->  []
           Just mr2  ->  aVMphase2 mr2 tks tas (tRs\\[pR]) tls pas pRs pls
     | otherwise
        -- does pattern reserve denote some existing test knowns ?
        =  case lVarDenote mctxt pR of
            (_,(_:_))  ->  []  -- !!!!! don't handle subtractions at present
            (pRd,_)
              -> if null (pRd\\tks)
                  then case (mr `mrgMR` fromJust (okBindQL pR pRd)) of
                         Nothing   ->  []
                         Just mr2  ->  aVMphase2 mr2 (tks\\pRd) tas tRs tls pas pRs pls
                  else [] -- cannot find enough known observations.
     where
        obsAsMdlScr = [mkVar (Rsv MDL []) pRd [], mkVar (Rsv SCR []) pRd []]
\end{code}
All the pattern reserved variables are accounted for, so we have test,
\[  tk_1,\ldots,tk_{u'}
~,~ ta_1,\ldots,ta_w
~,~ tR_1,\ldots,tR_{x'}
~,~ t\ell_1,\ldots,t\ell_z
\qquad u=b-v
\]
pattern,
\[  pa_1,\ldots,pa_c
~,~ p\ell_1,\ldots,p\ell_f \]
and binding: $\maplet{pk_i}{tk_j}$ and $\maplet{pR_i}{tR_j,tk_j}$.
At this point the total number of standard test variables remaining
($u'+w$)
should be no less than the number of remaining standard pattern variables ($c$).
We now proceed to generate all the possible ways that each of the $c$ pattern
standard variables can each match precisely one of the $u'+w$ test standard variables,
and then invoke a final phase that works out all the ways that the $f$ pattern list
variables can match what remains of all the test variables,
given each of the standard variable matches.
\begin{code}
   aVMphase3 mr tks tas tRs tls pas pls
    | length pas > length tks + length tas  =  []
    | otherwise = aVMphase4 (allStdMatches mr pas (tks++tas)) tRs tls pls

   allStdMatches mr []       tvs = [(mr,tvs)]
   allStdMatches _  _        []  = []  -- (defensive) should not happen
   allStdMatches mr (pa:pas) tvs = concat $ map (thisStdMatch mr pas pa tvs) tas

   thisStdMatch mr pas pa tvs tv
    = let tvs' = tvs\\[tv]
          rest' = allStdMatches mr pas tvs'
      in concat $ map (addStdMatch pa tv) rest'

   addStdMatch pa tv (mr,tvs)
    = case (mr `mrgMR` fromJust (okBindV pa tv)) of
        Nothing   ->  []
        Just mr'  ->  [(mr,tvs)]
\end{code}
\newpage
All the pattern standard variables are accounted for, so we have test,
\[  tk_1,\ldots,tk_{u''}
~,~ ta_1,\ldots,ta_w'
~,~ tR_1,\ldots,tR_{x'}
~,~ t\ell_1,\ldots,t\ell_z
\qquad u''+w'=u'+w-c
\]
pattern,
\[  p\ell_1,\ldots,p\ell_f \]
and binding: $\maplet{pk_i}{tk_j}$, $\maplet{pR_i}{tR_j,tk_j}$
and $\maplet{pa_i}{tk_j,ta_j}$.
We now want to construct all the ways that the $p\ell_i$
can bind to zero or more of the remaining $tk$, $ta$, $tR$ and $t\ell$ variables,
such that all the latter occur in exactly one binding%
\footnote{
This amounts to enumerating all total functions
from the set of remaining target variables to the set of remaining pattern list variables.
}%
. We only keep those ways compatible with bindings produced so far.
\begin{code}
   aVMphase4 mrtvs tRs tls pls
     =  concat $ map (allLstMatches0 pls tRs tls) mrtvs

   allLstMatches0 pls tRs tls (mr,tvs) = allLstMatches mr pls (tvs++tRs++tls)

   allLstMatches mr [] []  =  [mr]
   allLstMatches mr [] _   =  [] -- discard if not all tvs covered
   allLstMatches mr [pl] tvs
    = case (mr `mrgMR` fromJust (okBindQL pl tvs)) of
        Nothing  ->  []
        Just mr'  -> [mr']
   allLstMatches mr (pl:pls) tvs
     = concat $ map (thisLstMatches mr pl pls tvs) $ subsequences tvs

   thisLstMatches mr pl pls tvs stvs
    = let tvs' = tvs \\ stvs
          mrs' = allLstMatches mr pls tvs'
      in concat $ map (addLstMatch pl stvs) mrs'

   addLstMatch pl stvs mr
    = case (mr `mrgMR` fromJust (okBindQL pl stvs)) of
       Nothing   ->  []
       Just mr'  ->  [mr']
\end{code}
\newpage
\subsection{Law Matching}


\begin{code}
lawMatch :: [TTTag] -> FVSetExpr -> TypeTables -> MatchContext
         -> SideCond -> Pred
         -> Assertion -> TypeTables
         -> Maybe Binding
lawMatch tags fovs ttts mctxt tsc tpr (ppr,lawsc) ptts
  = do pResult <- pMatch (LC mctxt ttts ptts tags [] [] []) noBinding tpr ppr
       let scBinds = scMatch mctxt ttts ptts tags [] tsc lawsc
       let (bindings,qvms,subms) = bestSCFit mctxt pResult scBinds
       let tscnf = normaliseSC tsc
       let pscnf = normaliseSC lawsc
       unboundFresh <- checkFreshness pscnf bindings
       let goalvars = getAllGoalVars bindings
       let frshBinds = lbuild $ mapboth (varKey,TO . Var) $ genFreshVars goalvars unboundFresh
       bindings' <- (tnil,frshBinds,tnil) `mrgB` bindings
       checkPBindings (knownTypes mctxt) $ fst3 bindings'
       completeMatch fovs mctxt tscnf lawsc bindings' qvms subms
\end{code}






\subsubsection{Side-Condition Match Checking}

We identify which of the side-condition results are consistent
with the predicate match outcome, if any.
We merge in the ``best'' one if there is one.
The criteria for being best is currently based on the ``largest''
resulting binding%
\footnote{The best approach might be to carry the \texttt{scBinds} through
to the \texttt{completeMatch} phase, but we defer that until, or if, we
feel we need the extra lift this would give to matching overall.}%
:
\begin{code}
bestSCFit :: MatchContext -> MatchResult -> [MatchResult] -> MatchResult
bestSCFit mctxt bodyResult scResults
 | null fits  =  bodyResult
 | otherwise  =  last $ sort fits -- for now
 where
   fits = catMaybes $ map (scFit mctxt bodyResult) scResults
\end{code}

A side-condition binding `fits' a predicate body binding
if merging the two does not result in any goal variable being mapped
to by more than one pattern variable, and any conflict between a
sidecondition binding of the form $P \mapsto A$
and a body pattern $P \mapsto F$ satisfies the condition $A \in \fv.F$,
in which case the body pattern is retained.
\begin{code}
scFit :: MatchContext -> MatchResult -> MatchResult -> MatchOutcome
scFit mctxt bodyResult@(bnds1@(gp1,ev1,tt1),qvm1,sbm1)
              scResult@(bnds2@(gp2,ev2,tt2),qvm2,sbm2)
 = do gp' <- tglueW pFit gp1 gp2
      ev' <- tglueW eFit ev1 ev2
      tt' <- tt1 `tglue` tt2
      if isInjTrie gp' && isInjTrie ev' && isInjTrie tt'
       then return ((gp',ev',tt'), lnorm (qvm1++qvm2), lnorm (sbm1++sbm2))
       else fail "scFit: non-injective bindings"
 where
   pFit (VO bodyGR) (VO scGR) = scGR == bodyGR
   pFit (TO bodyP)  (VO scGR)
                          = genRootAsVar scGR `elem` predFreePVars mctxt bodyP
   pFit _      _              = False

   eFit (VO bodyVar) (VO scVar) = scVar == bodyVar
   eFit (TO bodyE)   (VO scVar) = scVar `elem` exprFreeVars mctxt bodyE
   eFit _      _                = False
\end{code}


\subsubsection{Freshness Checking}

We need to ensure that fresh (observational%
\footnote{
  expr/pred list-variables are not catered for at present
}%
) pattern variables, are mapped to goal variables that do not occur
in the range of any other bindings.
Also, we expect fresh pattern standard variables to be mapped
to a standard variable (as expression),
and a fresh pattern list variable to be mapped to a single list variable.
\begin{code}
checkFreshness :: SCNF -> Binding -> Maybe [Variable]
checkFreshness SCNFtrue _ = Just []
checkFreshness SCNFfalse _ = Nothing
checkFreshness (SCNFcond vfresh _ _) (gpbinds,vebinds,ttbinds)
 = fmap concat $ sequence $ map checkFreshness' vfresh
 where

-- this code is very clunky! could do with a complete re-write.

  checkFreshness' frshv
   | isLstV frshv  = checkLFreshness frshv
   | otherwise     = checkOFreshness frshv

  checkOFreshness frshv
   = case velookupTO frshv vebinds of
      Nothing             ->  Just [frshv]
      Just (Var goalvar)
       | isStdV goalvar   ->  freshOChk frshv goalvar
      _                   ->  Nothing -- fail if frshv mapped to other than Var

  freshOChk patvar goalvar
   = do freshChk1 sngl                     patvar goalvar $ justVO vebinds
        freshChk1 (map fst . exprAllOVars) patvar goalvar $ justTO vebinds
        freshChk1 (map fst . predAllOVars) patvar goalvar $ justTO gpbinds

  freshChk1 allVars patvar goalvar qbinds
   = fchk $ flattenTrie qbinds
   where
     fchk []  =  Just []
     fchk ((avar,goalexpr):rest)
      | avar == varKey patvar            =  fchk rest -- skip own mapping
      | goalvar `elem` allVars goalexpr  =  Nothing -- fgvar is not fresh
      | otherwise                        =  fchk rest

  checkLFreshness frshv
   = case velookupVSO frshv vebinds of
      Nothing  ->  Just [frshv]
      Just [goalvar]
       | isGenV goalvar  ->  freshLChk frshv goalvar
      _ -> Nothing

  freshLChk patvar goalvar
   = do freshChk2 varKey patvar (varKey goalvar) $ justVSO vebinds
        freshChk2 varKey patvar (varKey goalvar) $ justVSO vebinds
        freshChk2 genRootString patvar (varKey goalvar) $ justVSO gpbinds

  freshChk2 toStr patvar goalvar binds
   = fchk $ flattenTrie binds
   where
     fchk []  =  Just []
     fchk ((avar,vars):rest)
      | avar == varKey patvar            =  fchk rest -- skip own mapping
      | goalvar `elem` map toStr vars    =  Nothing -- fgvar is not fresh
      | otherwise                        =  fchk rest

-- END checkFreshness
\end{code}

We need all the variables mentioned in goal bindings:
\begin{code}
getAllGoalVars :: Binding -> [Variable]
getAllGoalVars (gpbinds,vebinds,_)
 = lnorm (pgvars++egvars++esgvars++qgvars)
 where
   pgvars = concat $ map (map fst . predAllOVars) $ trieRng $ justTO gpbinds
   egvars = (concat $ map (map fst . exprAllOVars) $ trieRng $ justTO vebinds)
            ++
            (concat $ trieRng $ justVSO vebinds)
   esgvars = concat $ map (map fst . exprAllOVars) $ concat $ trieRng $ justTSO vebinds
   qgvars = (trieRng $ justVO vebinds)
            ++
            (concat $ trieRng $ justVSO vebinds)
\end{code}

We want to ensure that any binding from a \texttt{PVar} to an expression
is to a boolean-valued one:
\begin{code}
checkPBindings types gpbinds
 = do let pes = getObs (trieRng gpbinds)
      let ets = map fst (itypes types pes)
      allTypesBool ets
 where
   getObs []                  =  []
   getObs ((TO (PExpr e)):prs)  =  e : getObs prs
   getObs (_:prs)             =  getObs prs
\end{code}

All the top types should be boolean, but we may lack type information
that resides in a theory above the one containing the current law.
So we also accept type variables as acceptable
(there is no type information that rules them out as boolean).
\begin{code}
   allTypesBool []           =  Just ()
   allTypesBool (B:ts)       =  allTypesBool ts
   allTypesBool (Tvar _:ts)  =  allTypesBool ts
   allTypesBool _            =  Nothing
\end{code}

\newpage
We also have a variant of \texttt{lawMatch}
useful for law debugging:
\begin{code}
patternTest :: (Pred -> String)
            -> [TTTag] -> FVSetExpr -> TypeTables -> MatchContext
            -> SideCond -> Pred -> Assertion -> TypeTables
            -> Maybe Binding
patternTest pshow tags fovs ttts mctxt tsc tpr (ppr,lawsc) ptts
 = debug
    ("\n\nMATCH-TEST ----------------"
     ++ "\n ********** GOAL PRED : "     ++ debugPshow tpr
     ++ "\n - GOAL FVARS : " ++ show fovs
     ++ "\n - GOAL SIDECOND : " ++ show tsc
     ++ "\n ********** LAW PRED : "      ++ debugPshow ppr
     ++ "\n - LAW SIDECOND : "  ++ show lawsc
    )
    ( do pResult <- pMatch (LC mctxt ttts ptts tags [] [] []) noBinding tpr ppr
         let scBinds = scMatch mctxt ttts ptts tags [] tsc lawsc
         let (mbnds@(gpbs,vebs,ttbs),qvms,subms) = bestSCFit mctxt pResult scBinds
         debug
          ("\n ****** MATCHED, BINDINGS:"
            ++ ttlshow "\n - PRED-BINDS : " gpbs
            ++ ttlshow "\n - EXPR-BINDS : " vebs
            ++ ttlshow "\n - TYPE-BINDS : " ttbs
            ++ "\n - QVMS : " ++ show qvms
           )
          (let tscnf = normaliseSC tsc ; pscnf = normaliseSC lawsc
           in case checkFreshness pscnf mbnds of
               Nothing -> debug "\n ****** NOT FRESH" Nothing
               Just unboundFresh
                -> debug "\n ****** IS FRESH..."
                  (let
                     goalvars = getAllGoalVars mbnds
                     frshBinds = foldl evvadd tnil $ genFreshVars goalvars unboundFresh
                   in
                     do mbnds' <- (tnil,frshBinds,tnil) `mrgB` mbnds
                        case checkPBindings (knownTypes mctxt) gpbs of
                          Nothing
                            -> debug "\n **** PVar Binds to Non-Bool Expression"
                                     Nothing
                          Just _
                           -> (case completeMatch fovs mctxt tscnf
                                                  lawsc mbnds' qvms subms
                               of
                                 Nothing
                                   -> debug "\n ****** COMPLETION FAILS"
                                            (Just mbnds')
                                 Just cbnds@(cgpbs,cvebs,cttbs)
                                   -> debug
                                        ("\n ***** COMPLETED, REVISED BINDINGS:"
                                         ++ ttlshow "\n - PRED-BINDS : " cgpbs
                                         ++ ttlshow "\n - EXPR-BINDS : " cvebs
                                         ++ ttlshow "\n - TYPE-BINDS : " cttbs
                                        )
                                        (Just cbnds)
                              )
                  )
          )
    )
 where
   ttlshow title otrie
    | isEmptyTrie otrie =  ""
    | otherwise         =  title ++ '\n':(show otrie)
   evvadd embind (vsrc,vtgt) = fromJust $ veupdateTO  vsrc (Var vtgt) embind
\end{code}

\newpage
\subsubsection{Match Completion}

Given a basic structural match,
we first need to try and resolve any outstanding \texttt{QVars}
and \texttt{Substn} matching,
using the bindings and both goal and law side-conditions
as hints, and finally, we check that the law side-condition,
with the proposed match bindings,
is a consequence of the goal side-condition.
\begin{code}
completeMatch
 :: FVSetExpr -> MatchContext -> SCNF -> SideCond
 -> Binding -> [QVarMatchToDo] -> [ESubstMatchToDo]
 -> Maybe Binding

completeMatch fovs mctxt goalsc lawsc binds [] []
 = do transc <- translateSideCondIC fovs mctxt goalsc binds lawsc
      sideCondCheck mctxt binds [] [] goalsc transc

completeMatch fovs mctxt goalsc lawsc binds@(gpbind,vebind,ttbind) qvms subms
 = do let sqvms =  mapboth (map fst,map fst) $ map dropLCtxt subms

      ( binds1@( gpbind1, vebind1, ttbind1 )
       , subms1
       ) <- getFeasibleSubstMatches mctxt (cmv "binds" binds) subms

      let (sngltab1,multtab1) = makeQVarFeasibilityTables $ cmv "qvms" qvms

      ( sngltab2, multtab2
       ) <- pruneSingleMatches mctxt (cmv "qbind1" vebind1)
                           (cmv "multtab1" multtab1) $ cmv "sngltab1" sngltab1

      ( unmatchedP, unmatchedE, sngltab3, multtab3
       ) <- sideCondResolve mctxt goalsc lawsc (cmv "sngltab2" sngltab2)
                               (cmv "multtab2" multtab2) $ cmv "binds1" binds1
      let ( snglitab, multitab
           ) = invertPartTabs isStdV (cmv "sngltab3" sngltab3)
                                    $ cmv "multtab3" multtab3
      let vebind2 = addNullQVarMatches vebind1 multtab3

      let msubtab = makeSubstnFeasibilityTable $ cmv "subms1" subms1
      let (vebind3)
               = addNullSubtsnMatches vebind2 $ cmv "msubtab" msubtab

      let binds2 = (gpbind1,vebind3,ttbind1)

      -- for now we use the round-robin strategy
      -- we really need to try strategies to see what succeeds
      -- using side-conditions and partial bindings as a hint mechanism.
      binds3  <- forceMatch mctxt roundRobin roundRobin (cmv "binds2" binds2)
                             (cmv "snglitab" snglitab)
                             (cmv "multitab" multitab) $ cmv "msubtab" msubtab

      transc <- translateSideCondIC fovs mctxt goalsc (cmv "binds3" binds3) lawsc
      binds' <- sideCondCheck mctxt binds3
                  (cmv "unmatchedP" unmatchedP)
                  (cmv "unmatchedE" unmatchedE) goalsc $ cmv "transc" transc
      return binds'
 where cmv what thing = thing -- dbg ("#CMV## "++what++":\n") thing
-- end completeMatch
\end{code}
We follow a series of steps (see overleaf):
\begin{enumerate}
\newpage
\item
\input{doc/Manipulation-Substitution-Matches}

For now, we look for all possible matches but
return only the ``best'' one.
This is to avoid major-reworking at this stage for \texttt{completeMatch}.
\begin{code}
getFeasibleSubstMatches :: MatchContext
                        -> Binding
                        -> [ESubstMatchToDo]
                        -> Maybe (Binding, [ESubstMatchToDo])
getFeasibleSubstMatches mctxt binds subms
 | null subms     =  return (binds, subms)
 | null feasible  =  Nothing
 | otherwise      =  return $ pick $ feasible
 where
   pick = head  -- for now
   feasible = allFeasible binds subms

   allFeasible binds  [subm]
    = mapsnd (:[]) $ trySubstMatch mctxt binds subm
   allFeasible binds (subm:subms)
    | null results  =  []
    | otherwise = concat $ map distr results
    where
      results              = mapsnd (:[]) $ trySubstMatch mctxt binds subm
      distr (binds',subm') = mapsnd (subm'++) $ allFeasible binds' subms

-- getFeasibleSubstMatches
\end{code}
\newpage
\input{doc/Manipulation-Substitution-Match}
\begin{code}
trySubstMatch :: MatchContext
              -> Binding
              -> ESubstMatchToDo
              -> [ (Binding, ESubstMatchToDo) ]
trySubstMatch mctxt binds todo@(subt, subp, lctxt)
 | null stdp  =  [(binds,todo)] -- succeed with no change
 | any (all isNothing) mtchMatrix  =  fail "unmatchable substitutions"
 | null newMO  =  fail "INTERNAL ERROR - shouldn't happen"
 | isNothing mbinds' = fail "unreconcileable matches"
 | otherwise  =  [(binds',todo')]
 where
   (stdt,lstt) = partition (isStdV . fst) subt
   (stdp,lstp) = partition (isStdV . fst) subp
   -- (LC _ ttts ptts ttags ptags tbv pbv) = lctxt
   mtchMatrix = map (mtchRow stdt) stdp
   mtchRow ts p = map (mtchPair p) ts
   mtchPair p@(vp,ep) t@(vt,et)
    =  do res <- eMatch lctxt noBinding
                  (mkProd [Var vt,et]) (mkProd [Var vp,ep])
          return (p,t,res)

   validBinding Nothing   =  0
   validBinding (Just _)  =  1
   newMO :: [((Variable,Expr),(Variable,Expr),MatchResult)]
   newMO = catMaybes $ findPairings validBinding greedyRC mtchMatrix
   -- newMO is non-empty list

   (mtchdp,mtchdt,newres) = unzip3 newMO
   mbinds' = foldM mrgB binds $ map fst3 newres
   Just binds' = mbinds'
   -- IGNORING deferred matches in newMR !
   todo' = (subt\\mtchdt, subp\\mtchdp, lctxt)
\end{code}
\newpage
\item
\input{doc/Manipulation-Identify-Feasible-QVars}
\begin{code}
makeQVarFeasibilityTables :: [QVarMatchToDo]
                     -> ([(Variable, [Variable])], [(Variable, [Variable])])

makeQVarFeasibilityTables qvms = gFQM [] [] qvms
 where
   gFQM sngltab multtab [] = (sngltab,multtab)
   gFQM sngltab multtab ((tqv,pqv):qvms) = gFQM sngltab' multtab' qvms
    where
      (sngltab',multtab') = addQBindTargets sngltab multtab tqv pqv

-- sngltab :: [(Std,[Std])]
-- multtab :: [(Lst,[Variable])]

addQBindTargets :: [(Variable, [Variable])]      --  sngltab
                -> [(Variable, [Variable])]      --  multtab
                -> [Variable]                    --  test Qvars
                -> [Variable]                    --  pattern Qvars
                -> ( [(Variable, [Variable])]    --  sngltab'
                   , [(Variable, [Variable])] )  --  multtab'
addQBindTargets stab mtab avs xvs = (stab',mtab')
 where
   (as,ass) = vPartition avs
   (xs,xss) = vPartition xvs
   stab0 = map (to (lnorm as)) (lnorm xs)
   aass = if length as == length xs
           then lnorm ass
           else lnorm as ++ lnorm ass
   mtab0 = map (to aass) (lnorm xss)
   stab' = stab `singlemerge` stab0
   mtab' = mtab `singlemerge` mtab0

singlemerge :: Ord a => [(a,[a])] -> [(a,[a])] -> [(a,[a])]
singlemerge = almrgnorm intersect
\end{code}
\newpage
\item
\input{doc/Manipulation-Prune-Single}
\begin{code}
pruneSingleMatches
  :: MatchContext -> VEBind
  -> [(Variable,[Variable])] -> [(Variable,[Variable])]
  -> Maybe ([(Variable,[Variable])], [(Variable,[Variable])])

pruneSingleMatches mctxt vebind multtab sngltab
 = do (sngltab',targetted) <- getTargettedSingles qsngl [] [] sngltab
      sngltab'' <- sstripTargetted targetted [] sngltab'
      let multtab' = mstripTargetted targetted multtab
      return (sngltab'',multtab')

 where
  qsngl = justVO vebind


  getTargettedSingles _ bats targets [] = Just (reverse bats,lnorm targets)

  getTargettedSingles _ _ _ ((x,[]):_) = Nothing  -- (a)

  getTargettedSingles qsngl bats targets (m@(x,as):sngltab)
   = case tvlookup qsngl x of
       Nothing  ->  getTargettedSingles qsngl (m:bats) targets sngltab -- (b)
       Just a   ->  if a `elem` as -- (c)
                    then getTargettedSingles qsngl bats (a:targets) sngltab
                    else Nothing

-- end pruneSingleMatches

mstripTargetted tgtd [] = []
mstripTargetted tgtd ((xs,avs):mtab)
 = (xs,(as \\ tgtd)++ass): mstripTargetted tgtd mtab
 where (as,ass) = vPartition avs

sstripTargetted tgtd bats [] = Just (reverse bats)
sstripTargetted tgtd bats ((x,as):stab)
 | null as'   =  Nothing
 | otherwise  =  sstripTargetted tgtd ((x,as'):bats) stab
 where as' = as \\ tgtd
\end{code}
\newpage
\item
\input{doc/Manipulation-SideCond-Resolve}
\begin{code}
sideCondResolve :: MatchContext -> SCNF -> SideCond
                -> [(Variable,[Variable])]
                -> [(Variable,[Variable])]
                -> Binding
                -> Maybe ( [String]
                         , [String]
                         , [(Variable,[Variable])]
                         , [(Variable,[Variable])]
                         )
sideCondResolve mctxt goalsc lawsc stab mtab binds
 = do let (fvconds,unmatchedP,unmatchedE)
             = translateLawCondMetaVars mctxt goalsc binds lawsc
      let enumconds = filter useableCondFVSetPair
                        $ map simplifyCondFVSetPair $ fvconds
      let lvc = buildLawVarConstraints enumconds
      let stab' = applyLawConstraints scLawPair lvc stab
      let mtab' = applyLawConstraints scLawPair lvc mtab
      return (unmatchedP,unmatchedE,stab',mtab')

-- end sideCondResolve
\end{code}
(continued overleaf)
\newpage
The translation:
\begin{code}
translateLawCondMetaVars :: MatchContext
                         -> SCNF
                         -> Binding
                         -> SideCond
                         -> ([(SideCond, FVSetExpr)],[String],[String])
translateLawCondMetaVars mctxt ctxtnf (gpbind,vebind,_) lawsc
 = tLCMV [] [] lawsc
 where

   pbind = justTO gpbind
   ebind = justTO vebind

   tLCMV unmP unmE SCtrue = ([],unmP,unmE)
   tLCMV unmP unmE sc@(SCisCond m mname) = tMMV m unmP unmE sc mname
   tLCMV unmP unmE sc@(SCnotFreeIn m qvs mname) = tMMV m unmP unmE sc mname
   tLCMV unmP unmE sc@(SCareTheFreeOf m qvs mname)= tMMV m unmP unmE sc mname
   tLCMV unmP unmE sc@(SCcoverTheFreeOf m qvs mname) = tMMV m unmP unmE sc mname
   tLCMV unmP unmE (SCAnd scs) = tLCMVs [] unmP unmE scs
   tLCMV unmP unmE _ = ([],unmP,unmE)

   tLCMVs fvc unmP unmE [] = (fvc,unmP,unmE)
   tLCMVs fvc unmP unmE (sc:scs)
    = let (fvc',unmP',unmE') = tLCMV unmP unmE sc
      in tLCMVs (fvc'++fvc) unmP' unmE' scs

   tMMV PredM unmP unmE sc pname = tPMV unmP unmE sc pname
   tMMV ExprM unmP unmE sc ename = tEMV unmP unmE sc ename
   tMMV _ unmP unmE _ _ = ([],unmP,unmE) -- for now...

   tPMV unmatchedP unmatchedE sc pname
    = case tlookup pbind pname of
        Nothing    ->  ([],pname:unmatchedP,unmatchedE)
        (Just pr)  ->  let fvs = reduceFVSetExpr ctxtnf (predFVSet mctxt pr)
                       in ([(sc,fvs)],unmatchedP,unmatchedE)

   tEMV unmatchedP unmatchedE sc ename
    = case tlookup ebind ename of
        Nothing   ->  ([],unmatchedP,ename:unmatchedE)
        (Just e)  ->  let fvs = reduceFVSetExpr ctxtnf (exprFVSet mctxt e)
                      in ([(sc,fvs)],unmatchedP,unmatchedE)

-- end translateLawCondMetaVars
\end{code}
(continued overleaf)
\newpage
We trim the condition/fv-set pairs:
\begin{enumerate}
  \item We drop \texttt{SCisCond} (not useful)
  \item We retain only enumeration parts of fv-set expressions
    (the rest is too complicated)
\end{enumerate}
\begin{code}
simplifyCondFVSetPair :: (SideCond, FVSetExpr) -> (SideCond, [Variable])
simplifyCondFVSetPair (sc,FVSet condsets)
 = (sc,lnorm $ concat $ map stripCondSet condsets)
simplifyCondFVSetPair (sc,_) = (sc,[])

stripCondSet (CondSet [] (Atom (Enum vs))) = vs
stripCondSet _                             = []

useableCondFVSetPair (SCisCond _ _,_) = False
useableCondFVSetPair (_,[]) = False
-- useableCondFVSetPair (SCtrue,_) = False -- shouldn't occur
-- useableCondFVSetPair (SCAnd _ _,_) = False -- shouldn't occur
useableCondFVSetPair _ = True
\end{code}

We have a list of side-condition/enumeration pairs
representing $(V \mathcal R F)$.
We turn this into a table of the form $V \pfun \power(\mathcal R F)$:
\begin{code}
buildLawVarConstraints :: Ord t => [(SideCond,t)] -> [(Variable,[(SideCond,t)])]
buildLawVarConstraints [] = []
buildLawVarConstraints ((sc,fvs):rest)
 = almrgnorm mrgnorm (mkC sc fvs) (buildLawVarConstraints rest)
 where
   mkC sc fvs = map mkC' (scVars sc)
   mkC' v = (v,[(sc,fvs)])

scVars (SCnotFreeIn _ vs _)       =  vs
scVars (SCareTheFreeOf _ vs _)    =  vs
scVars (SCcoverTheFreeOf _ vs _)  =  vs
scVars (SCfresh _ v)              =  [v]
scVars _ = []
\end{code}
(continued overleaf)
\newpage
We then process the tables using the constraints:
\begin{code}
applyLawConstraints _ [] gs = gs
applyLawConstraints _ cs [] = []
applyLawConstraints apply cs@((x,scfvs):crest) gs@(gy@(y,goalvs):grest)
 | x < y  =  applyLawConstraints apply crest gs
 | x > y  =  gy:(applyLawConstraints apply cs grest)
 | otherwise  =  (x,applyLaws apply scfvs goalvs )
                   :(applyLawConstraints apply crest grest)
 where

   applyLaws _ [] goalvs = goalvs
   applyLaws apply ((sc,fvs):rest) goalvs
    = applyLaws apply rest (applyLaw apply fvs goalvs sc)

   applyLaw (diff,_)   fvs goalvs (SCnotFreeIn _ _ _)    = goalvs `diff` fvs
   applyLaw (_,intsct) fvs goalvs (SCareTheFreeOf _ _ _) = goalvs `intsct` fvs
   applyLaw _          _   goalvs _                      = goalvs

scLawPair :: ( [Variable] -> [Variable] -> [Variable] , [Variable] -> [Variable] -> [Variable] )
scLawPair = ((\\),intersect)
\end{code}
\newpage
\item
The multitables have list patterns that map to empty lists, at least,
so we initialise them as such.
\begin{code}
addNullQVarMatches :: VEBind -> [(Variable,[Variable])] -> VEBind
addNullQVarMatches vebind []  = vebind
addNullQVarMatches vebind ((v,_):mtab)
  = let qmulti' = tsingle (varKey v) [] `tmerge` qmulti
    in  addNullQVarMatches (tmap VO qsngl `tmerge` tmap VSO qmulti') mtab
  where
     qsngl = justVO vebind
     qmulti = justVSO vebind

addNullSubtsnMatches :: VEBind
                     -> [((Variable,Expr),[(Variable,Expr)])]
                     -> VEBind
addNullSubtsnMatches vebind []  = vebind
addNullSubtsnMatches vebind (((v,e),_):mtab)
 = let qlist' = tsingle (varKey v) [] `tmerge` qlist
       estrie' = tenter (++) (varKey $ eDrop e) [] estrie
   in  addNullSubtsnMatches ( tmap TSO estrie'
                              `tmerge`
                              tmap VO qsngl
                              `tmerge`
                              tmap VSO qlist') mtab
 where
   qsngl = justVO vebind
   qlist = justVSO vebind
   estrie = justTSO vebind
\end{code}
\newpage
\item
\input{doc/Manipulation-Identify-Feasible-Substn}
\begin{code}
makeSubstnFeasibilityTable
  :: [ESubstMatchToDo]
     -> [((Variable,Expr), [(Variable,Expr)])]

makeSubstnFeasibilityTable subms = gFSM [] subms
 where
   gFSM msubtab [] = msubtab
   gFSM msubtab ((tsub,psub,_):subms) = gFSM msubtab' subms
    where
     msubtab' = addSBindTargets msubtab tsub psub

-- msubtab :: [((Lst,Lst),[(Variable,Expr)])]

addSBindTargets :: [((Variable,Expr), [(Variable,Expr)])]  --  msubtab
                -> [(Variable,Expr)]                       --  test Substn
                -> [(Variable,Expr)]                       --  pattern Subtsn
                -> [((Variable,Expr), [(Variable,Expr)])]  --  msubtab'
addSBindTargets mtab afs xes
 = mtab `singlemerge` (map (to $ lnorm afs) (lnorm xes))
\end{code}
\newpage
\item
\input{doc/Manipulation-Force-Matches}
\begin{code}
forceMatch :: MatchContext
           -> ResolveStrategy (Variable, Expr) (Variable, Expr)
           -> ResolveStrategy Variable Variable
           -> Binding
           -> [(Variable,[Variable])]
           -> [(Variable,[Variable])]
           -> [((Variable,Expr),[(Variable,Expr)])]
           -> Maybe Binding

forceMatch mctxt edivvy qdivvy bind@(gpbind,vebind,ttbind) sitab mitab msubtab
 = do let msubvtab = mapboth ( fst, map fst) $ fmv "msubtab" msubtab
      let (sistab,mistab) = invertPartTabs isStdV [] $ fmv "msubvtab" msubvtab
      let sitab1 = (fmv "sitab" sitab) `singlemerge` (fmv "sistab" sistab)
      let mitab1 = (fmv "mitab" mitab) `singlemerge` (fmv "mistab" mistab)
      let citab = map snglCount $ fmv "sitab1" sitab1
      let (stab,mtab) = unInvertPartTabs isStdV sitab1 $ fmv "mitab1" mitab1
      let stab' = map (snglSort $ fmv "citab" citab) $ fmv "stab" stab
      (vebind1,mtab')
         <- resolveSingleMatches (fmv "vebind" vebind) (fmv "stab'" stab') $ fmv "mtab" mtab
      let qlist1 = justVSO vebind1
      let qlist2 = resolveMultiMatches qdivvy qadd (fmv "qlist1" qlist1) $ fmv "mtab'" mtab'
      -- should we do this with elist? edivvy, eadd ?
      -- workaround, see sadd definition below.
      let estrieP = resolveMultiMatches edivvy sadd tnil $ fmv "msubtab" msubtab
      --- need to split estrieP across estrie and qlist
      let estrie = justTSO vebind
      let (_,qlist3) = splitESBindPairs (fmv "estrie" estrie) (fmv "qlist2" qlist2) $ flattenTrie $ fmv "estrieP" estrieP
      -- let elist = justVSO vebind1
      vebind2 <- (fmv "vebind1" vebind1) `lmergeSBind` tmap VSO (fmv "qlist3" qlist3)
      checkForcedSizes mctxt (gpbind,fmv "vebind2" vebind2,ttbind)
 where
   fmv what thing = thing -- dbg ("###F "++what++":\n") thing

   snglCount (a,xs) = (a,length $ filter isStdV xs)

   snglSort citab (x,as) = (x,sortBy (countCmp citab) as)
   countCmp citab a1 a2 = compare c1 c2
    where
      c1 = clookup citab a1
      c2 = clookup citab a2
      clookup citab a
        = case alookup citab a of
           Nothing   ->  maxBound -- shouldn't happen, but just in case..
           Just n    ->  n

   qadd :: Trie [Variable] -> (Variable,[Variable]) -> Trie [Variable]
   qadd trie (mv,vs) = tenter mrgnorm (varKey mv) vs trie
   -- resolve and divvy assume one Trie, rather than a pair (MBind)
   -- what follows is a workaround that temporarily encodes
   --  qlist: v$ |-> [u1,...,un]   and  estrie: e$ |-> [f1,..,fn]
   -- as
   -- estrieP:  v$_e$ |->  [u1=f1,..,un=fn]   ! Equal is only 2-Expr constr.

   sadd :: Trie [Expr] -> ((Variable,Expr),[(Variable,Expr)]) -> Trie [Expr]
   sadd trie ((sv,se),sreps)
     = tenter (++)
              (varKey sv++ '_':varKey (eDrop se))             -- v$_e$
              (map mkEq sreps) trie                           -- [..,u=f,..]
     where
       mkEq (u,f) = mkEqual (Var u) f

   -- splitting it apart
   splitESBindPairs :: Trie [Expr] -> Trie [Variable] -> [(String,[Expr])]
                    -> (Trie [Expr], Trie [Variable])
   splitESBindPairs estrie qlist [] = (estrie,qlist)
   splitESBindPairs estrie qlist ((vs_es,usEqFs):rest)
    = splitESBindPairs estrie' qlist' rest
    where
      (vs,_es) = break (=='_') vs_es
      (us,fs) = unzip $ map eqsplit usEqFs
      eqsplit (App nm [Var u, f])
       | nm == n_Equal  =  (u,f)
      eqsplit _         =  (preVar "eqsplit??",EPred FALSE)
      estrie' = tenter (++) (tail _es) fs estrie         -- e$ |-> [..,f,..]
      qlist'  = tenter (++) vs us qlist                  -- v$ |-> [..,u,..]
\end{code}
We process each entry in the single table,
binding $x_i$ to the first entry ($a_{i1}$, greedy!) and then removing that entry
from the ranges of both tables:
\begin{code}
resolveSingleMatches :: VEBind
                     -> [(Variable,[Variable])]
                     -> [(Variable,[Variable])]
                     -> Maybe ( VEBind, [(Variable,[Variable])] )
resolveSingleMatches vebind [] mtab = return (vebind,mtab)
resolveSingleMatches _ ((v,[]):_) _ = fail ("Cannot bind '"++varKey v++"'")
resolveSingleMatches vebind ((v,(a:_)):stab) mtab
 = do vebind' <- mtenter same (varKey v) (VO a) vebind
      let stab' = remRng rems stab a
      let mtab' = remRng rems mtab a
      resolveSingleMatches vebind' stab' mtab'

rems xs x = xs \\ [x]
remq xs x = (xs \\ [x])

remRng rem tab x = map rem2 tab where rem2 (k,d) = (k,d `rem` x)
\end{code}
(continued overleaf)
\newpage
For multi-matching, simply working down the list, binding each mvar
to its full range and then removing that from the rest
gives a bias towards alphabetically earlier multi-variables.
Unfortunately this greedy approach can often fail
\\---e.g. trying to match lhs of axiom \AXorAllOScopeN:
$$\AXorAllOScope.$$
Ideally we should find choices that maximise the chance of side conditions
being satisfied.

We have resolution mechanism
that is parameterised by an resolution strategy.
The idea is that we have a mapping of keys to lists of data items,
where a data-item can be associated with multiple keys.
We want to transform this into a mapping were each data item
appears exactly once.

Now the code:
\begin{code}
type ResolveStrategy k d = [k] -> [d] -> [(k,d)]

resolve :: (Ord k, Ord d)
        => ResolveStrategy k d -> [(k,[d])] -> [(k,[d])]
resolve divvy
 = alloc divvy . img . inv
 where

   -- invert the relation
   inv :: (Ord k, Ord d) => [(k,[d])] -> [(d,[k])]
   inv kds = inv' [] kds

   inv' dks [] = dks
   inv' dks ((k,ds):kds) = inv' (inv'' dks k ds) kds

   inv'' dks k [] = dks
   inv'' dks k (d:ds) = inv'' (ins dks d k) k ds

   -- build "image" - captures contention
   img :: (Ord d, Ord k) => [(d,[k])] -> [([k],[d])]
   img dks = img' [] dks

   img' ksds [] = ksds
   img' ksds ((d,ks):dks1) = img' (ins ksds ks d) dks1

   -- relation insertion
   ins :: (Ord k, Ord d) => [(d,[k])] -> d -> k -> [(d,[k])]
   ins [] d0 k0 = [(d0,[k0])]
   ins dks@(hd@(d,ks):dks1) d0 k0
    | d0 < d   =  (d0,[k0]):dks
    | d0 == d  =  (d,lnorm (k0:ks)):dks1
    | otherwise  =  hd:ins dks1 d0 k0

   -- use strategy to do allocation
   alloc :: (Ord k, Ord d)
         => ([k] -> [d] -> [(k,d)]) -> [([k],[d])] -> [(k,[d])]
   alloc divvy ksds = fins $ concat $ map (uncurry divvy) ksds

   fins [] = []
   fins ((k,d):kds) = ins (fins kds) k d

-- end resolve
\end{code}
\newpage
Now we have three strategies
(the original verison of \texttt{resolveMultiMatches}
effectively used \texttt{allToFirstKey}):
\begin{code}
-- allocate all to first key
allToFirstKey :: ResolveStrategy k d
allToFirstKey _     []      =  []
allToFirstKey (k:_) ds      =  map (\d->(k,d)) ds

-- allocate one per key with last takes all
oneEachThenRestToLast :: ResolveStrategy k d
oneEachThenRestToLast _      []      =  []
oneEachThenRestToLast [k]    ds      =  map (\d->(k,d)) ds
oneEachThenRestToLast (k:ks) (d:ds)  =  (k,d):oneEachThenRestToLast ks ds

-- allocate round-robin among the keys
roundRobin :: ResolveStrategy k d
roundRobin keys dats
 = rrobin keys dats
 where
  rrobin  _      []     =  []
  rrobin []     ds      =  rrobin keys ds
  rrobin (k:ks) (d:ds)  =  (k,d):rrobin ks ds
\end{code}


\begin{code}
resolveMultiMatches :: (Ord k, Ord d)
                    => ResolveStrategy k d
                    -> (Trie t -> (k,[d]) -> Trie t)
                    -> Trie t
                    -> [(k,[d])]
                    -> Trie t
resolveMultiMatches divvy add trie tab
 = let tab1 = resolve divvy tab
   in  foldl add trie tab1
\end{code}

%We need to get the \texttt{EBind}, \texttt{ESBind}  and \texttt{QBind}
%bindings in sync.
%Every binding of a list variable to a list of variables
%should be represented in both tables.
%The \texttt{Expr} tables tend to be properly populated,
%with missing entries in the \texttt{QVar} table,
%so we work through the former, checking against the latter.
%\begin{code}
%mergeEQBinds :: Trie [Variable] -> Trie [Expr] -> Trie [Variable]
%             -> Maybe (Trie [Variable])
%mergeEQBinds elist estrie qlist
% = mrgEQ qlist ((eqv "fT(elist)" $ flattenTrie elist) ++ (eqv "gv(fT(estrie))" $ getVars (flattenTrie estrie)))
% where
%
%   getVars [] = []
%   getVars ((v,es):rest)
%    | all isVar es  =  (v,vs) : getVars rest
%    | otherwise     =  getVars rest
%    where vs = map getVar es
%
%   mrgEQ qlist []  =  return qlist
%   mrgEQ qlist ((k,vs):rest) =  chkEQ (eqv "mEQ.qlist" qlist) rest (eqv "mEQ.k" k) $ eqv "mEQ.vs" vs
%
%   chkEQ qlist rest k vs
%    = case (eqv "LOOKUP" (tlookup qlist k)) of
%       Nothing             ->  mrgEQ (tupdate k vs qlist) rest
%       Just us | null (eqv "us" us)   ->  mrgEQ (tupdate k vs qlist) rest
%               | us == (eqv "vs" vs)  ->  mrgEQ qlist rest
%       _                   ->  Nothing
%
%   eqv what thing =  dbg ("###M "++what++":\n") thing
%\end{code}

\newpage
Now, we need to check our matches conform to size information.
Ideally the strategy above would handle this on the fly.
\begin{code}
checkForcedSizes :: MatchContext
                 -> Binding
                 -> Maybe Binding
checkForcedSizes mctxt bind@(_,vebind,_)
 | all (uncurry $ sizeConformant mctxt) $ flattenTrie qlist  =  return bind
 | otherwise                                                 =  Nothing
 where qlist = justVSO vebind
\end{code}
\newpage
\item
\input{doc/Manipulation-Translate-SideCond}
\begin{code}
translateSideCondIC :: FVSetExpr
                    -> MatchContext
                    -> SCNF
                    -> Binding
                    -> SideCond
                    -> Maybe SideCond
translateSideCondIC fovs mctxt ctxtsc (gpbnds,vebnds,ttbnds) sc
 = transSCIC ctxtsc
 where

   transSCIC SCNFfalse = return SCtrue
   transSCIC _ = tLSCIC sc

   tLSCIC SCtrue = return SCtrue
   tLSCIC (SCfresh mtyp fv)
    = return $ scand $ map (SCfresh mtyp) (trFV $ varKey fv)

   tLSCIC (SCisCond PredM pnm)
    = evalPredSideCondition mctxt ctxtsc (SCisCond PredM "_") (trP pnm)
   tLSCIC (SCisCond ExprM enm)
    = evalExprSideCondition mctxt ctxtsc (SCisCond ExprM "_") (trE enm)

   tLSCIC (SCnotFreeIn PredM qvs pnm)
    = evalPredSideCondition mctxt ctxtsc
                           (SCnotFreeIn PredM (trQs qvs) "_") (trP pnm)
   tLSCIC (SCnotFreeIn ExprM qvs enm)
    = evalExprSideCondition mctxt ctxtsc
                           (SCnotFreeIn ExprM (trQs qvs) "_") (trE enm)

   tLSCIC (SCareTheFreeOf PredM qvs pnm)
    = evalPredSideCondition mctxt ctxtsc
                        (SCareTheFreeOf PredM (trQs qvs) "_") (trP pnm)
   tLSCIC (SCareTheFreeOf ExprM qvs enm)
    = evalExprSideCondition mctxt ctxtsc
                        (SCareTheFreeOf ExprM (trQs qvs) "_") (trE enm)

   tLSCIC (SCcoverTheFreeOf PredM qvs pnm)
    = evalPredSideCondition mctxt ctxtsc
                      (SCcoverTheFreeOf PredM (trQs qvs) "_") (trP pnm)
   tLSCIC (SCcoverTheFreeOf ExprM qvs enm)
    = evalExprSideCondition mctxt ctxtsc
                      (SCcoverTheFreeOf ExprM (trQs qvs) "_") (trE enm)

   tLSCIC (SCAnd scs)
    = fmap scand (sequence (map tLSCIC scs))

   trFV vnm = case tlookup vebnds vnm of
                Just (TO (Var v))  ->  [v]
                Just (TO e)        ->  [queryVString $ show e]
                Just (VSO vs)      ->  vs
                Just (TSO es)      ->  map getVar es
                _                  ->  [queryVString vnm]

   trE enm = case tlookup vebnds enm of
              Just (TO e)    ->  e
              Just (VSO vs)  ->  mkEVar $ queryVString $ show vs
              _              ->  mkEVar $ queryVString enm

   trP pnm = case tlookup gpbnds pnm of
              Just (TO pr)   ->  pr
              Just (VSO vs)  ->  PVar $ queryVString $ show vs
              _              ->  PVar $ queryVString pnm

   trQs = lnorm . concat
          . map (translateQVar vebnds (knownObs mctxt)
                                      (knownConsts mctxt))
-- end translateLawSideCondIC
\end{code}
We need to mark variables that are (currently) untranslatable:
\begin{code}
queryVar  :: Variable -> Variable
queryVar v = queryVString $ varKey v
queryVString  :: String -> Variable
queryVString str = preVar ('?':str)
\end{code}

We need to translate \texttt{QVar}s properly, looking at theory tables
for observation variables and constants
\begin{code}
translateQVar :: VEBind -> [Trie ObsKind] -> [Trie Expr] -> Variable
              -> [Variable]
translateQVar vebnds obs konsts qv
 = case tvlookup vebnds qv of
    Just (VO x)    ->  [x]
    Just (VSO xs)  ->  xs
    _  -> case tsvlookup obs qv of
           Just _ -> [qv]
           Nothing -> case tsvlookup konsts qv of
             Just _   ->  [qv]
             Nothing  ->  [queryVar qv]
\end{code}
%
\newpage
\item
\input{doc/Manipulation-Check-SideCond}
\begin{code}
sideCondCheck :: MatchContext
              -> Binding
              -> [String]
              -> [String]
              -> SCNF
              -> SideCond
              -> Maybe Binding
sideCondCheck mctxt binds unuE unuP goalsc transc
 | not (null unuE)               =  return binds
 | not (null unuP)               =  return binds
 | goalsc `nscIFImplies` transc  =  return binds
 | otherwise                     =  fail ""
 where
   -- transc = scQVarTranslate mctxt qbnds mtchsc

-- scQVarTranslate mctxt qbnds sc
--  = scQTrans sc
--  where
--
--   scQTrans SCtrue = SCtrue
--
--   scQTrans (SCnotFreeIn PredM qvs pname)
--                                  = (SCnotFreeIn PredM (qtrans qvs) pname)
--   scQTrans (SCnotFreeIn ExprM qvs ename)
--                                  = (SCnotFreeIn ExprM (qtrans qvs) ename)
--
--   scQTrans (SCareTheFreeOf PredM qvs pname)
--                               = (SCareTheFreeOf PredM (qtrans qvs) pname)
--   scQTrans (SCareTheFreeOf ExprM qvs ename)
--                               = (SCareTheFreeOf ExprM (qtrans qvs) ename)
--
--   scQTrans (SCcoverTheFreeOf PredM qvs pname)
--                             = (SCcoverTheFreeOf PredM (qtrans qvs) pname)
--   scQTrans (SCcoverTheFreeOf ExprM qvs ename)
--                             = (SCcoverTheFreeOf ExprM (qtrans qvs) ename)
--
--   scQTrans (SCAnd scs) = scand (map scQTrans scs)
--
--   scQTrans sc = sc
--
--   qtrans = lnorm . concat
--            . map (translateQVar qbnds (knownObs mctxt)
--                                       (knownConsts mctxt))
\end{code}
\end{enumerate} % outer list
\newpage


\newpage
\subsection{Match Ranking}


Given a test-predicate and a law
we return a list of the possible ways
to match against it.
We also adjust the ranking based on the kind of matching%
\footnote{%
  We may look at the replacement predicates as well --- the simpler these
  are, the better in general.
}%
:
\begin{code}
rankAdjust :: MatchContext -> Pred -> MatchType -> Rank -> Rank
rankAdjust mctxt lawpart       All   rank = 100*rank  -- complete matches are very valuable
rankAdjust mctxt lawpart       LEqv  rank = 10*rank   -- prefer equivalences
rankAdjust mctxt lawpart       REqv  rank = 10*rank

rankAdjust mctxt (PVar root) TREqv rank
 = case tslookup (knownPreds mctxt) (show root) of
     Nothing   ->  rank `div` 5   -- trivial matches  are usually uninteresting
     (Just _)  ->  5 * rank       -- except if it applies to "known" predicates

rankAdjust mctxt (PExpr (Var v)) TREqv rank
 | isEVar v
 = case tsvlookup (knownExprs mctxt) v of
     Nothing -> rank `div` 5 -- trivial matches  are usually uninteresting
     (Just _) -> 5 * rank -- except if it applies to "known" expressions

 | otherwise
 = case tsvlookup (knownObs mctxt) v of
   (Just _) -> 10 * rank -- except if it applies to observational variables
   Nothing
    -> case tsvlookup (knownConsts mctxt) v of
        (Just _) -> 5 * rank  -- or if it applies to "known" constants
        Nothing -> rank `div` 5  -- trivial matches  are usually uninteresting

rankAdjust _ _ _ rank = rank
\end{code}

\newpage
\subsection{Matching Variety}

The function \texttt{subMatch} matches the test predicate against a law
in a variety of ways
 --- the whole law, its lhs/rhs or antecedent/consequent.

We first define a function that takes
a law and returns all the ways to match against it:
\begin{code}
type MatchVariant
 = ( MatchType  -- match variant indication
   , Pred       -- match pattern predicate
   , SideCond   -- match pattern side-condition
   , TypeTables -- law type-tables
   , [Pred]     -- list of match replacement predicates
   )

lawMatchPossibilities :: Law -> [MatchVariant]
lawMatchPossibilities law@(ass@(pr,sc),_,tts)
  = [( All, pr, sc, tts, [TRUE] )]  -- always a viable match possibility
    ++ lEqvPossibilities tts ass
    ++ rEqvPossibilities tts ass
    ++ antePossibilities tts ass
    ++ cnsqPossibilities tts ass
    -- ++ lceqvPossibilities tts ass
    -- ++ rceqvPossibilities tts ass
    ++ treqvPossibilities tts ass
\end{code}

\texttt{LEqv} matching only succeeds
on laws of the form $P \equiv Q$ or $e = f$,
and compares the test predicate
to the lefthand-side of the equivalence/equality,
returning the rhs as the replacement, if successful.
\begin{code}
lEqvPossibilities tts
  ( PApp nm [lhs, rhs], sc )
  | nm == n_Eqv  =  [( LEqv, lhs, sc, tts, [rhs] )]
lEqvPossibilities tts
  (PExpr ( App nm [lhs, rhs]), sc )
  | nm == n_Equal  =  [( LEqv, PExpr lhs, sc, tts, [PExpr rhs] )]
-- lEqvPossibilities tts (PExpr (Equal lhs rhs),sc)
--                                 = [( LEqv, PExpr lhs, sc, tts, [PExpr rhs] )]
lEqvPossibilities _ _ = []
\end{code}

\texttt{REqv} matching is the obvious ``dual'' of the above,
except that it fails if the rhs is a single predicate,
observation or meta-variable --- i.e. matches that would always succeed.
\textbf{Note: }
\emph{The completeness of this assumes that \texttt{pred2law} has been
applied to every law.}
\begin{code}
rEqvPossibilities tts
  ( PApp nm [lhs, rhs@(PVar _)], sc )
  | nm == n_Eqv  =  []
rEqvPossibilities tts
  (PExpr ( App nm [lhs, rhs@(Var _)] ), sc )
  | nm == n_Equal  =  []

rEqvPossibilities tts
  ( PApp nm [lhs, rhs], sc )
  | nm == n_Eqv  =  [( REqv, rhs,sc, tts, [lhs] )]
rEqvPossibilities tts
  (PExpr ( App nm [lhs, rhs] ), sc )
  | nm == n_Equal  =  [( REqv, PExpr rhs, sc, tts, [PExpr lhs] )]
-- rEqvPossibilities tts (PExpr (Equal lhs rhs),sc)
--      = [( REqv, PExpr rhs, sc, tts, [PExpr lhs] )]

rEqvPossibilities _ _ = []
\end{code}

\texttt{Ante} matching only applies to laws of the form $P \implies Q$,
and matches against the antecedent $P$.
The replacement returned is $P \land Q$%
\footnote{%
 For now we return a single replacement ($P \land Q$)
 as only equivalence steps are currently supported in the prover.
 Later, when implicative steps are handled, we will return
 a list of replacements ($\seqof{Q,P}$),
 which will then be used as required in the proof step.
 This observation also applies to
 the \texttt{Cnsq}, \texttt{LCEqv} and \texttt{RCEqv} matchers.
}%
,
in keeping with the equivalent equational law $P \equiv P \land Q$.
\begin{code}
antePossibilities tts
  ( PApp nm [ante, cnsq], sc )
  | nm == n_Imp  =  [( Ante, ante, sc, tts, [mkAnd [ante,cnsq]] )]
antePossibilities _ _ = []
\end{code}

\texttt{Cnsq} matching, as expected, works with law $P \implies Q$,
and matches against the consequent $Q$,
with replacement $Q \lor P$.
\begin{code}
cnsqPossibilities tts
  ( PApp nm [ ante, cnsq], sc )
  | nm == n_Imp  =  [( Cnsq, cnsq, sc, tts, [mkOr [cnsq,ante]] )]
cnsqPossibilities _ _ = []
\end{code}

\texttt{LCEqv} matching (currently unused)
matches against $Q$ in law $P \implies (Q \equiv R)$
and uses $\seqof{P,R}$ as replacements.
\begin{code}
lceqvPossibilities tts
  ( PApp nm1 [ ante
             , PApp nm2 [clhs, crhs] ]
  , sc )
  | nm1 == n_Imp && nm2 == n_Eqv  =  [( LCEqv, clhs, sc, tts, [ante,crhs] )]
lceqvPossibilities _ _ = []
\end{code}

\texttt{RCEqv} matching  (currently unused)
matches against $R$ in law $P \implies (Q \equiv R)$
and uses $\seqof{P,Q}$ as replacements.
\begin{code}
rceqvPossibilities tts
  ( PApp nm1 [ ante
             , PApp nm2 [clhs, crhs] ]
  , sc )
  | nm1 == n_Imp && nm2 == n_Eqv  =  [( RCEqv, crhs, sc, tts, [ante,clhs] )]
rceqvPossibilities _ _ = []
\end{code}

\texttt{TREqv} matching fills in the gaps left by \texttt{REQv} matching,
namely those equivalences/equalities
where the rhs is a single variable.
These are singled out for special treatment, as generally
they are nuisance matches, but it is useful to be able to call
upon them from time to time.
\begin{code}
treqvPossibilities tts (PApp nm [lhs, rhs@(PVar _)],sc)
  | nm == n_Eqv  = [( TREqv, rhs, sc, tts, [lhs] )]
treqvPossibilities tts (PExpr (App nm [lhs,rhs@(Var _)]),sc)
  | nm == n_Equal  = [( TREqv, PExpr rhs, sc, tts, [PExpr lhs] )]
-- treqvPossibilities tts (PExpr (Equal lhs rhs@(Var _)),sc)
--       = [( TREqv, PExpr rhs, sc, tts, [PExpr lhs] )]
-- treqvPossibilities tts (PExpr (Equal lhs rhs@(Evar _)),sc)
--       = [( TREqv, PExpr rhs, sc, tts, [PExpr lhs] )]

treqvPossibilities _ _ = []
\end{code}

\subsubsection{Variant Matching}

\begin{code}
subMatch
 :: ([TTTag] -> FVSetExpr -> TypeTables -> MatchContext
      -> SideCond -> Pred -> Assertion -> TypeTables
     -> Maybe Binding)
 -> [TTTag] -> FVSetExpr -> TypeTables -> MatchContext  -> SideCond -> FPred -> Law
 -> [LawMatch]

subMatch match tags fovs ttts mctxt tsc tfpr law@(_,prov,_)
 = catMaybes $ map (doMatch $ getPFocus tfpr )
             $ lawMatchPossibilities law
 where
\end{code}

\texttt{All} matching first strips outer universal quantifiers
from the test predicate, and then matches against the whole
law --- the replacement for a successful match being $\True$.
\textbf{Note: }
\emph{The completeness of this matching depends crucially
on all laws having had \texttt{remOuterForall} applied.}
\begin{code}
   doMatch tpr (All, ppr, psc, ptts, repls)
    = do binds <- match tags fovs ttts mctxt tsc (remOuterForall tpr) (ppr, psc) ptts
         return $ (All, prov, binds, psc, repls)

   doMatch tpr (mtyp, ppr, psc, ptts, repls)
    = do binds <- match tags fovs ttts mctxt tsc tpr (ppr, psc) ptts
         return $ (mtyp, prov, binds, psc, repls)
-- end subMatch
\end{code}

We build two matchers on top of \texttt{subMatch}:
a standard one where the matcher is \texttt{lawMatch},
and a debug testing one
\begin{code}
hm_matchGivenLaw = (
    unlines $ [" : Match against named law\n",
    "In this case, ",
    "you are prompted to enter the name of the law",
    "to which you want to match your expression.",
    "If there is one or more matches,",
    "they will appear in a list and can be applied using the \'l\' command."])

subLawMatch :: [TTTag] -> FVSetExpr -> TypeTables -> MatchContext
               -> SideCond -> FPred -> Law
               -> [LawMatch]
subLawMatch = subMatch lawMatch

subPatternTest :: (Pred->String)
                  -> [TTTag] -> FVSetExpr -> TypeTables -> MatchContext
                  -> SideCond -> FPred -> Law
                  -> [LawMatch]
subPatternTest pshow = subMatch (patternTest pshow)
\end{code}

Matching is a form of inverse search:
\begin{code}
findLaws :: FContext -> FVSetExpr -> TypeTables -> MatchContext
            -> SideCond -> FPred
            -> LawTable
            -> [(LawMatch,String)]

findLaws (_,_,tags) fovs ttts mctxt tsc tfpr laws
 = fl laws
 where
   fl [] = []
   fl ((name,law):rest)
     = (map (app name) (subLawMatch tags fovs ttts mctxt tsc tfpr law))
       ++(fl rest)
   app name lawm = (lawm,name)
\end{code}

\subsection{Law Application}

We have matched a predicate (\texttt{tpr})
(which may in fact be focussed onto an expression
of non-boolean type),
against a law to get a replacement predicate (\texttt{rep})
(which may be an expression wrapped in \texttt{PExpr}).

We have a range of combinations we may want to handle:

\begin{tabular}{|l|p{1.5in}|p{1.5in}|}
  \hline
  \texttt{tpr}$\backslash$ \texttt{rep} & Pred & Expr (inside PExpr) \\
  \hline
  Pred
  & replace Pred by Pred
  & replace Pred by PExpr Expr \\
  \hline
  Focussed Expr
  & should not occur except at top-level
  & replace Expr by Expr   \\
  \hline
  Focussed Subs-Expr
  & should not occur
  & replace Subs-Expr by Expr   \\
  \hline
\end{tabular}

\textbf{Deprecated: Also, any \texttt{PVar} in the replacement, not bound to any predicate,
is replaced by its known equivalent.}

The only variables (PVar, Var, Evar) replaced below
are those that occur explicitly in the bindings.
\begin{code}
hm_applyLaw = (
    unlines $ [" : Apply Matched Law\n",
    "When \'l\' is typed, ",
    "you will be prompted to type in a number,",
    "this number identifies which match in the list of matches",
    "you are choosing to replace the current focus. ",
    "The list of matches will be generated by",
    "either the \'m\' command or the \'?\' command. ",
    "Note that if \'l\' is used in conjunction with the \'?\' command,",
    "soundness of the proof is threatened.",
    "More on this in the section about \'?\'."])

-- matchReplace mctxt tpr@(PExpr fe@(Efocus _ eancs)) (_,(mtyp,_,bnds,reps),_)
--  = case instantiatePred mctxt bnds (head reps) of
--     (PExpr e)  ->  PExpr (repEFocus e fe)
--     rpred       ->  if null eancs
--                      then rpred
--                      else tpr  -- no replacement done
--
-- matchReplace mctxt tpr@(Sub pr sub@(Substn i _ _)) (_,(mtyp,_,bnds,reps),_)
--  | i==0  = rpred -- no substitution focus
--  | otherwise
--    = case rpred of
--        (PExpr e)  ->  (Sub pr (repSFocus e sub))
--        _           ->  tpr -- should never happen !!
--  where
--   rpred = instantiatePred mctxt bnds (head reps)
--
matchReplace :: MatchContext -> RankedMatch -> Pred
matchReplace mctxt (_,(mtyp,_,bnds,_,reps),_)
 = instantiatePred mctxt bnds (head reps)
\end{code}

\subsubsection{Law Display}

\begin{code}
displayPfxLaws pfx [] = return ()
displayPfxLaws pfx ((name,law):rest)
 = do (if pfx `isPrefixOf` name
       then displayLaw name law
       else return ())
      displayPfxLaws pfx rest
displayLaw name law
 = do putStr name
      putStr " = "
      putStrLn (show law)

showLawsAsText [] = "-\n"
showLawsAsText ((name,law):rest)
 = (name++"      :-      "++show law++"\n") ++ showLawsAsText rest

showLawsByContextAsText [] = ""
showLawsByContextAsText ((cname,laws):rest)
 = "[ "++cname++" ]\n"
   ++ showLawsAsText laws
   ++ showLawsByContextAsText rest
\end{code}

\subsection{Existential Witness}


Law:
$$
 (\exists x,y @ P)
 \equiv
 (\exists x @ P[e/y]) \lor (\exists x,y @ P)
$$
We assume that this is called with \texttt{wsubs}
such that its free-variables do not overlap any \texttt{qvs}.
\textbf{As currently formulated it does not tidy-up \texttt{qvs}.
}
\begin{code}
existentialWitness mctxt sc wsubs epr@(PAbs nm _ qvs [body])
 | nm == n_Exists
  = mkOr [wpr,epr] -- put witness first
  where
    wpr
     | null qws  =  wbody
     | otherwise  =  mkExists qws wbody
    qws = remSubVars (lnorm (snd (unwrapQV wsubs))) (lnorm(getqovars qvs))
    wbody = predONSub mctxt sc wsubs body

existentialWitness mctxt sc wsubs pr = pr

remSubVars subvs qvs = (qvs \\ subvs)
\end{code}
