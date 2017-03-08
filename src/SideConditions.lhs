\section{Side Conditions}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module SideConditions where
import Tables
import Datatypes
import DataText
import Flatten
import Focus
import MatchTypes
--import Matching
import FreeBound
import Types
import Utilities
import DSL
import Data.List
import Data.Maybe
import Data.Char
\end{code}

\input{doc/SideConditions-Preamble}

\subsubsection{Side-Condition Normal Form}

\input{doc/SideConditions-NF}


So we can represent a side condition in normal form
as either $\TRUE$, $\FALSE$ or a triple
of a set of fresh variables, plus two tables, one each for
expression and predicate metavariables, mapping them to
their simplified side-conditions.
\begin{eqnarray*}
  scnf \in SCNF
  &::=& \textbf{true} | (V!,sctbl,sctbl) | \textbf{false}
\end{eqnarray*}
A single-MV normal form
is one or both of a $\isCond M$ assertion
and a MV relational assertion.
A MV relational assertion is either an equality,
a subset or a disjoint assertion.
The meta-variable $M$ is implicit here as it is indexed via a table.
\begin{eqnarray*}
   scsngl \in SCSngl
   &::=&
   \isCond M |  M~setsc  |  \isCond M \land M~setsc
\\ sctbl \in SCTbl &\defs& V \fun SCSngl
\\   setsc \in SetSC
   &::=&
   ( = | \subseteq | \DISJ ) V
\end{eqnarray*}
\begin{code}
data SCNF
 = SCNFtrue
 | SCNFcond [Variable]  -- Fresh Variables
            SCNFTbl     -- Expr Metavariable Conditions
            SCNFTbl     -- Pred Metavariable Conditions
 | SCNFfalse
 deriving (Eq,Ord)

type SCNFTbl = Trie SCSingle

data SCSingle = SCSingle
                  Bool   -- true if c.M is asserted
                  (Maybe SetSC)
 deriving (Eq,Ord,Show)

data SetSC
 = SCequal [Variable]
 | SCsub   [Variable]
 | SCdisj  [Variable]
 deriving (Eq,Ord,Show)
\end{code}

Display and lookup for the normal form:
\begin{code}
instance Show SCNF where
 show SCNFtrue = "SCNF-TRUE"
 show SCNFfalse = "SCNF-FALSE"
 show (SCNFcond freshvars evars pvars)
  = showSCNFfresh freshvars
    ++ showSCNFCond "EVARS:" evars
    ++ showSCNFCond "PVARS:" pvars

showSCNFfresh [] = "FRESH:(null)"
showSCNFfresh (v:vs)
 = "FRESH: " ++ varKey v ++ (concat $ map ((',':) . varKey) vs)

showSCNFCond hdr trie
 =  "\nSCNF-" ++ hdr ++ showSCNFtrie trie

showSCNFtrie trie
 | trie == tnil  =  " (nil)"
 | otherwise     =  '\n':show trie

eSCNFlookup :: SCNF -> String -> Maybe SCSingle
eSCNFlookup (SCNFcond _ econd _) enm  =  tlookup econd enm
eSCNFlookup _   _                     =  Nothing

pSCNFlookup :: SCNF -> String -> Maybe SCSingle
pSCNFlookup (SCNFcond _ _ pcond) pnm  =  tlookup pcond pnm
pSCNFlookup _   _                     =  Nothing
\end{code}

Now normalisation is done by merging a side-condition
with a trivially true normal form:
\begin{code}
normaliseSC = mergeSCintoNF SCNFtrue
\end{code}
Code
to merge a \texttt{SideCond} into a normal form:
\begin{code}
mergeSCintoNF :: SCNF -> SideCond -> SCNF

mergeSCintoNF SCNFfalse _            =  SCNFfalse
mergeSCintoNF scnf      SCtrue       =  scnf
mergeSCintoNF scnf      (SCAnd scs)  =  foldl mergeSCintoNF scnf scs

mergeSCintoNF SCNFtrue (SCisCond PredM pvar) = scIsCondPNF pvar
mergeSCintoNF SCNFtrue (SCisCond ExprM evar) = scIsCondENF evar

mergeSCintoNF SCNFtrue (SCnotFreeIn PredM vs pvar) = scNotFreeInPNF pvar vs
mergeSCintoNF SCNFtrue (SCnotFreeIn ExprM vs evar) = scNotFreeInENF evar vs

mergeSCintoNF SCNFtrue (SCareTheFreeOf PredM vs pvar) = scAreTheFreeOfPNF pvar vs
mergeSCintoNF SCNFtrue (SCareTheFreeOf ExprM vs evar) = scAreTheFreeOfENF evar vs

mergeSCintoNF SCNFtrue (SCcoverTheFreeOf PredM vs pvar) = scCoverTheFreeOfPNF pvar vs
mergeSCintoNF SCNFtrue (SCcoverTheFreeOf ExprM vs evar) = scCoverTheFreeOfENF evar vs

mergeSCintoNF SCNFtrue (SCfresh _ var) = scFreshPNF var

mergeSCintoNF scnf@(SCNFcond vfresh etbl ptbl) (SCfresh _ vf)
 = case (noteFreshness [vf] etbl,noteFreshness [vf] ptbl) of
    (Just etbl',Just ptbl')  ->  SCNFcond (lnorm (vf:vfresh)) etbl' ptbl'
    _                        ->  SCNFfalse

mergeSCintoNF scnf@(SCNFcond vfresh etbl ptbl) sc
 = case scMetaType sc of
    ExprM -> case scUpdate vfresh sc etbl of
               Nothing      ->  SCNFfalse
               Just etbl'   ->  SCNFcond vfresh etbl' ptbl
    PredM -> case scUpdate vfresh sc  ptbl of
               Nothing      ->  SCNFfalse
               Just ptbl'   ->  SCNFcond vfresh etbl ptbl'
    _ -> scnf -- ignore others
\end{code}

Next, injecting simple side-conditions into a single and general normal forms:
$\isCond M$
\begin{code}
scIsCondSingle    =  SCSingle True Nothing
scIsCondPNF pvar  =  SCNFcond [] tnil (tsingle pvar scIsCondSingle)
scIsCondENF evar  =  SCNFcond [] (tsingle evar scIsCondSingle) tnil
\end{code}

$M \DISJ V$
\begin{code}
scNotFreeInSingle vs  =  SCSingle False (Just (SCdisj (lnorm vs)))
scNotFreeInPNF pvar vs
            = SCNFcond [] tnil (tsingle pvar $ scNotFreeInSingle vs)
scNotFreeInENF evar vs
            = SCNFcond [] (tsingle evar $ scNotFreeInSingle vs) tnil
\end{code}

$M = V$
\begin{code}
scAreTheFreeOfSingle vs = SCSingle False (Just (SCequal (lnorm vs)))
scAreTheFreeOfPNF pvar vs
         = SCNFcond [] tnil (tsingle pvar $ scAreTheFreeOfSingle vs)
scAreTheFreeOfENF evar vs
         = SCNFcond [] (tsingle evar $ scAreTheFreeOfSingle vs) tnil
\end{code}

$M \subseteq V$
\begin{code}
scCoverTheFreeOfSingle vs = SCSingle False (Just (SCsub (lnorm vs)))
scCoverTheFreeOfPNF pvar vs
       = SCNFcond [] tnil (tsingle pvar $scCoverTheFreeOfSingle vs)
scCoverTheFreeOfENF evar vs
       = SCNFcond [] (tsingle evar $ scCoverTheFreeOfSingle vs) tnil
\end{code}

$\isFresh V$
\begin{code}
scFreshPNF var = SCNFcond [var] tnil tnil
scFreshENF var = SCNFcond [var] tnil tnil
\end{code}

Next, embedding an atomic non-trivial metavariable side-condition into a ``single'':
\begin{code}
atomicSC2Single :: SideCond -> SCSingle

atomicSC2Single (SCisCond _ _) = scIsCondSingle

atomicSC2Single (SCnotFreeIn PredM vs pvar) = scNotFreeInSingle vs
atomicSC2Single (SCnotFreeIn ExprM vs evar) = scNotFreeInSingle vs

atomicSC2Single (SCareTheFreeOf PredM vs pvar) = scAreTheFreeOfSingle vs
atomicSC2Single (SCareTheFreeOf ExprM vs evar) = scAreTheFreeOfSingle vs

atomicSC2Single (SCcoverTheFreeOf PredM vs pvar) = scCoverTheFreeOfSingle vs
atomicSC2Single (SCcoverTheFreeOf ExprM vs evar) = scCoverTheFreeOfSingle vs

atomicSC2Single sc = error ("atomicSC2Single - not atomic: "++show sc)
\end{code}

Code to merge \texttt{SCsingle}s
\begin{code}
mergeSCSingle :: SCSingle -> SCSingle -> Maybe SCSingle

mergeSCSingle (SCSingle isC1 Nothing) (SCSingle isC2 mset2)
 = checkSCSingle (isC1||isC2) mset2

mergeSCSingle (SCSingle isC1 mset1) (SCSingle isC2 Nothing)
 = checkSCSingle (isC1||isC2) mset1

mergeSCSingle (SCSingle isC1 (Just mset1)) (SCSingle isC2 (Just mset2))
 = do mset' <-  mset1 `mergeSCSet` mset2
      checkSCSingle (isC1||isC2) $ Just mset'
\end{code}

We need to check is being undashed consistent with
a set relation:
\begin{eqnarray*}
   M=V\land \isCond M &\equiv&  M=V \cond{\isCond V} \FALSE
\\ M \subseteq V\land \isCond M &\equiv& M \subseteq V\!|_{\isCond{\_}}
\\ S\!|_p &\defs& \setof{x | x \in S \land p(x)}
\\ M \DISJ V\land \isCond M &\equiv& M \DISJ V\land \isCond M
\end{eqnarray*}
\begin{code}
checkSCSingle :: Bool -> Maybe SetSC -> Maybe SCSingle
checkSCSingle True (Just setsc)
 = do mset' <- checkSCSetIsCond setsc
      return $ SCSingle True $ Just setsc
checkSCSingle isC mset = Just $ SCSingle isC mset

checkSCSetIsCond :: SetSC -> Maybe SetSC
checkSCSetIsCond mset@(SCequal vs)
     | all isPreVariable vs  =  return mset
     | otherwise             =  fail ""
checkSCSetIsCond (SCsub vs)  =  return $ SCsub $ filter isPreVariable vs
checkSCSetIsCond mset        =  return mset
\end{code}

So now we merge SC-sets, which may fail if things are inconsistent.
\begin{code}
mergeSCSet :: SetSC -> SetSC -> Maybe SetSC
\end{code}

\begin{eqnarray*}
   M=V_1 \land M=V_2  &\equiv& M = V_1 \cond{V_1 = V_2} \FALSE
\end{eqnarray*}
\begin{code}
mergeSCSet setsc@(SCequal vs1) (SCequal vs2)
 | vs1 == vs2  =  Just setsc
 | otherwise   =  Nothing
\end{code}

\begin{eqnarray*}
   M=V_1  \land M \subseteq V_2 &\equiv& M = V_1 \cond{V_1 \subseteq V_2} \FALSE
\end{eqnarray*}
\begin{code}
mergeSCSet setsc@(SCequal vs1) (SCsub vsub2)
 | vs1 `issubset` vsub2   =  Just setsc
 | otherwise              =  Nothing
\end{code}

\begin{eqnarray*}
   M=V_1  \land M \DISJ V_2 &\equiv& M = V_1 \cond{V_1 \DISJ V_2} \FALSE
\end{eqnarray*}
\begin{code}
mergeSCSet setsc@(SCequal vs1) (SCdisj vdisj2)
 | vs1 `disjoint` vdisj2  =  Just setsc
 | otherwise              =  Nothing
\end{code}

\begin{eqnarray*}
   M \subseteq V_1  \land M \subseteq V_2 &\equiv& M \subseteq (V_1 \cap V_2)
\\ M \subseteq \emptyset  &\equiv& M = \emptyset
\end{eqnarray*}
\begin{code}
mergeSCSet (SCsub vsub1)  (SCsub vsub2)
 | null vsub'  =  Just (SCequal [])
 | otherwise   =  Just (SCsub vsub')
 where vsub' = vsub1 `intersect` vsub2
\end{code}

\begin{eqnarray*}
   M \DISJ V_1 \land M \DISJ V_2 &\equiv& M \DISJ (V_1 \cup V_2)
\end{eqnarray*}
\begin{code}
mergeSCSet (SCdisj vdisj1) (SCdisj vdisj2)
 = Just (SCdisj (vdisj1 `union` vdisj2))
\end{code}

\begin{eqnarray*}
   M \subseteq V_1  \land M \DISJ V_2 &\equiv& M \subseteq (V_1 \setminus V_2)
\\ M \subseteq \emptyset  &\equiv& M = \emptyset
\end{eqnarray*}
\begin{code}
mergeSCSet (SCsub vsub1)  (SCdisj vdisj2)
 | null vsub'  =  Just (SCequal [])
 | otherwise   =  Just (SCsub vsub')
 where vsub' = vsub1 \\ vdisj2

mergeSCSet (SCdisj vdisj1) (SCsub vsub2)
 | null vsub'  =  Just (SCequal [])
 | otherwise   =  Just (SCsub vsub')
 where vsub' = vsub2 \\ vdisj1
\end{code}

Finally, we exploit the fact that \texttt{mergeSCSet} is commutative
to process the other argument:
\begin{code}
mergeSCSet setsc scset2 = scset2 `mergeSCSet` setsc
\end{code}

When a fresh variable is noted,
we need to go through variable tables and add in the fact that
they need to be disjoint w.r.t. to the new variable:
\begin{code}
noteFreshness :: [Variable] -> SCNFTbl -> Maybe SCNFTbl
noteFreshness fvs trie
 = trie `mrg` ftrie
 where
   vfdisj = SCSingle False $ Just $ SCdisj fvs
   ftrie = tmap (const vfdisj) trie
   mrg = tmmerge mergeSCSingle
\end{code}


Now, merging an atomic side-condition into a table
\begin{code}
scUpdate :: [Variable] -> SideCond -> SCNFTbl -> Maybe SCNFTbl

scUpdate fvs sc mvars
 = case tlookup mvars mvar of
       Nothing  ->  noteFreshness fvs $ tupdate mvar newsngl mvars
       Just single
         ->  do single' <-  newsngl `mergeSCSingle` single
                noteFreshness fvs $ tupdate mvar single' mvars
 where
  mvar = scMetaVar sc
  newsngl = atomicSC2Single sc
\end{code}



\newpage
Sometimes full normalisation is more than what's required,
but it is useful to partition a side-condition
by the meta-variables it mentions:
\begin{code}
partitionSC :: SideCond -> (Trie SideCond,Trie SideCond)
partitionSC sc
 = partSC (tnil,tnil) sc
 where
   partSC (evs,pvs) SCtrue = (evs,pvs)

   partSC (evs,pvs) sc@(SCisCond PredM pv) = (evs,add pv sc pvs)
   partSC (evs,pvs) sc@(SCisCond ExprM ev) = (add ev sc evs,pvs)

   partSC (evs,pvs) sc@(SCnotFreeIn PredM qvs pv) = (evs,add pv sc pvs)
   partSC (evs,pvs) sc@(SCnotFreeIn ExprM qvs ev) = (add ev sc evs,pvs)

   partSC (evs,pvs) sc@(SCareTheFreeOf PredM qvs pv) = (evs,add pv sc pvs)
   partSC (evs,pvs) sc@(SCareTheFreeOf ExprM qvs ev) = (add ev sc evs,pvs)

   partSC (evs,pvs) sc@(SCcoverTheFreeOf PredM qvs pv) = (evs,add pv sc pvs)
   partSC (evs,pvs) sc@(SCcoverTheFreeOf ExprM qvs ev) = (add ev sc evs,pvs)

   partSC (evs,pvs) sc@(SCfresh PredM pv) = (evs,add (varKey pv) sc pvs)
   partSC (evs,pvs) sc@(SCfresh ExprM ev) = (add (varKey ev) sc evs,pvs)

   partSC (evs,pvs) (SCAnd scs) = partSCs (evs,pvs) scs

   partSC (evs,pvs) _ = (evs,pvs) -- ignore other MTypes for now

   partSCs (evs,pvs) [] = (evs,pvs)
   partSCs (evs,pvs) (sc:scs) = partSCs (partSC (evs,pvs) sc) scs
   add v sc vs = tenter scext v sc vs
   scext (SCAnd scs1) (SCAnd scs2) = scand (scs1++scs2)
   scext (SCAnd scs1) sc2          = scand (sc2:scs1)
   scext sc1          (SCAnd scs2) = scand (sc1:scs2)
   scext sc1          sc2          = scand [sc1,sc2]
\end{code}


\subsubsection{Side-Condition Entailment}

We accept side-conditions only
if they are entailed by those associated with a proof goal.
$$
  goalSC \implies lawSC
$$
%We shall define entailment over side-condition normal forms.
%\begin{eqnarray*}
%   \FALSE &\implies& lawSC
%\\ goalSC &\implies& \TRUE
%\\ goalSC \implies lawSC
%   &\equiv&
%   \forall P @ P \in goalSC \implies P \in lawSC
%\\ && \qquad\qquad {} \land (~goalSC(P) \implies lawSC(P)~)
%\end{eqnarray*}
%At the single-MV normal form level we can separate the $\isCond M$
%case out from the set-conditions.
%\begin{eqnarray*}
%   \TRUE &\implies& cond
%\\ \isCond M &\implies& \isCond M
%\end{eqnarray*}
%The set-condition entailments are:
%\begin{eqnarray*}
%   M = V_1 \implies M = V_2 &\equiv&  V_1 = V_2
%\\ M = V_1 \implies M \subseteq V_2 &\equiv&  V_1 \subseteq V_2
%\\ M = V_1 \implies M \DISJ V_2 &\equiv&  V_1 \DISJ V_2
%\\ M \subseteq V_1 \implies M = V_2 &\equiv& V_1 = V_2 = \emptyset
%\\ M \subseteq V_1 \implies M \subseteq V_2 &\equiv& V_1 \subseteq V_2
%\\ M \subseteq V_1 \implies M \DISJ V_2 &\impliedBy & V_1 \DISJ V_2
%\\ M \DISJ V_1 \implies M = V_2 &\implies& V_1 \DISJ V_2
%\\ M \DISJ V_1 \implies M \subseteq V_2 &\impliedBy& V_1 \DISJ V_2
%\\ M \DISJ V_1 \implies M \DISJ V_2 &\impliedBy& V_2 \subseteq V_1
%\end{eqnarray*}
%We cannot always determine entailment exactly.
We simply note that this is that same as checking
$$
    goalSC \equiv goalSC \land lawSC
$$
\begin{code}
goalSC `scImplies` lawSC
    =  (normaliseSC goalSC) == (normaliseSC (scand [goalSC,lawSC]))

goalSC `nscImplies` lawSC  =  goalSC == (mergeSCintoNF goalSC lawSC)
\end{code}

An important variant is one that ignores freshness checks:
\begin{code}
ignoreFreshness :: SideCond -> SideCond
ignoreFreshness (SCfresh _ _)  =  SCtrue
ignoreFreshness (SCAnd scs)    =  scand $ map ignoreFreshness scs
ignoreFreshness sc             =  sc

ignoreFreshnessNF :: SCNF -> SCNF
ignoreFreshnessNF (SCNFcond _ tbl1 tbl2)  =  SCNFcond [] tbl1 tbl2
ignoreFreshnessNF scnf                    =  scnf

goalSC `scIFImplies` lawSC
 = (ignoreFreshness goalSC) `scImplies` (ignoreFreshness lawSC)

goalSC `nscIFImplies` lawSC
 = (ignoreFreshnessNF goalSC) `nscImplies` (ignoreFreshness lawSC)
\end{code}


\newpage
\subsubsection{Reducing Set-Expressions w.r.t Side-Conditions}

\input{doc/SideConditions-Reduce-I}
\begin{code}
reduceFVSetExpr :: SCNF -> FVSetExpr -> FVSetExpr

-- we can ignore fresh-vars as their effect is incorporated into (e/p)conds
reduceFVSetExpr (SCNFcond _ econds pconds) (FVSet condsets)
 = FVSet $ fvsSubsume $ lnorm $ filter nonnullCondSet
         $ map (reduceCondSet econds pconds) condsets

reduceFVSetExpr scnf fvset = fvset
\end{code}

\input{doc/SideConditions-Reduce-II}
\begin{code}
reduceCondSet :: SCNFTbl -> SCNFTbl -> CondSet -> CondSet

reduceCondSet econds pconds (Atom atom)
 = Atom (reduceAtomSet econds pconds atom)

reduceCondSet econds pconds (CondSet setconds cres)
 = case reduceMmbrShps econds pconds setconds of
     Nothing      ->  condSetNull
     Just []      ->  reduceCondSet econds pconds cres
     Just rconds  ->  CondSet rconds (reduceCondSet econds pconds cres)

reduceCondSet econds pconds (QCondSet setcond r vs)
 = case reduceQMmbrShp econds pconds setcond of
     Nothing  ->  condSetNull
     Just rconds  ->  QCondSet rconds r vs
\end{code}

\newpage
\input{doc/SideConditions-Reduce-III}
\begin{code}
reduceMmbrShps :: SCNFTbl -> SCNFTbl -> [MmbrShp] -> Maybe [MmbrShp]
reduceMmbrShps econds pconds setconds
 = rSCS [] setconds
 where

   rSCS okconds [] = return (reverse okconds)

   rSCS okconds (setcond:setconds)
    = do (isSat,redcond) <- reduceMmbrShp econds pconds setcond
                            -- Nothing if setcond is false
         if isSat                               -- setcond is not false
          then rSCS okconds setconds            -- setcond is true
          else rSCS (redcond:okconds) setconds  -- setcond is undetermined
\end{code}


\newpage
\input{doc/SideConditions-Reduce-IV}
\begin{code}
reduceMmbrShp :: SCNFTbl -> SCNFTbl -> MmbrShp -> Maybe (Bool,MmbrShp)

reduceMmbrShp econds pconds m@(MmbrShp v (Atom (Enum vs)))
 | v `elem` vs  =  return (True,m)
 | otherwise    =  fail (varKey v++" not in "++show vs)

reduceMmbrShp econds pconds m@(MmbrShp v (Atom (NameE enm lessvs)))
 = reduceMetaVarCond NameE (tlookup econds) v enm lessvs

reduceMmbrShp econds pconds m@(MmbrShp v (Atom (NameP pnm lessvs)))
 = reduceMetaVarCond NameP (tlookup pconds) v pnm lessvs

--reduceMmbrShp econds pconds m@(MmbrShp v (Atom (NameQ qnm lessvs)))
-- nothing we can do without ebnds with an entry for qnm

reduceMmbrShp econds pconds m = return (False,m)
\end{code}

\begin{code}
reduceQMmbrShp :: SCNFTbl-> SCNFTbl -> MmbrShp -> Maybe MmbrShp

reduceQMmbrShp econds pconds setcond = Just setcond -- FOR NOW
-- again, we need bindings
\end{code}

\newpage
\input{doc/SideConditions-Reduce-V}
\begin{code}
reduceAtomSet :: SCNFTbl -> SCNFTbl -> AtomicSet -> AtomicSet

reduceAtomSet econds pconds atom@(NameE enm lessvs)
 = case tlookup econds enm of

    Just (SCSingle _ (Just (SCequal vs)))
       ->  Enum (lnorm vs \\ lessvs)

    Just (SCSingle _ (Just (SCsub vs)))
      | lnorm vs `subsetOf` lnorm lessvs  -> Enum []
      | otherwise  ->  NameE enm (lessvs `intersect` vs)

    Just (SCSingle _ (Just (SCdisj vs)))
       ->  NameE enm (lessvs \\ vs)

    _ -> atom

reduceAtomSet econds pconds atom@(NameP pnm lessvs)
 = case tlookup pconds pnm of

    Just (SCSingle _ (Just (SCequal vs)))
       ->  Enum (lnorm vs \\ lessvs)

    Just (SCSingle _ (Just (SCsub vs)))
      | lnorm vs `subsetOf` lnorm lessvs  -> Enum []
      | otherwise  ->  NameP pnm (lessvs `intersect` vs)

    Just (SCSingle _ (Just (SCdisj vs)))
       ->  NameP pnm (lessvs \\ vs )

    _ -> atom

reduceAtomSet econds pconds atom = atom
\end{code}

\input{doc/SideConditions-Reduce-VI}
\begin{code}
reduceMetaVarCond :: (String -> [Variable] -> AtomicSet)
                     -> (String -> Maybe SCSingle)
                     -> Variable -> String -> [Variable] -> Maybe (Bool,MmbrShp)
reduceMetaVarCond aset lkp v nm lessvs
 | v `elem` lessvs  =  fail (varKey v++" in "++show lessvs)
 | otherwise
    = case lkp nm of

        Just (SCSingle iscond Nothing)
         | iscond && not (isPreVariable v)  ->  fail (show v++" is not undashed")

        Just (SCSingle iscond (Just (SCequal eqvs)))
         | iscond && not (isPreVariable v)  ->  fail (show v++" is not undashed")
         | v `elem` (eqlessvs)              ->  return (True,eqcond)
         | otherwise        ->  fail (show v++" not in "++show eqlessvs)
         where eqlessvs = eqvs \\lessvs
               eqcond = MmbrShp v $ Atom (aset nm eqlessvs)

        Just (SCSingle iscond (Just (SCsub supvs)))
         | iscond && not (isPreVariable v)  ->  fail (show v++" is not undashed")
         | v `elem` supvs                   ->  return (False,subcond)
         | otherwise           ->  fail (show v++" not in "++show supvs)
         where
          subcond = MmbrShp v $ Atom (aset nm (lessvs `intersect` supvs))

        Just (SCSingle iscond (Just (SCdisj disjvs)))
         | iscond && not (isPreVariable v)  ->  fail (show v++" is not undashed")
         | v `elem` disjvs                  ->  fail (show v++" in "++show disjvs)
         | otherwise                        ->  return (False,disjcond)
         where
           disjcond = MmbrShp v $ Atom (aset nm (lessvs \\ disjvs))

        Nothing -> return(False,MmbrShp v $ Atom (aset nm lessvs))

-- end reduceMetaVarCond

isPreVariable (Gen (Std _),Pre,_)  =  True
isPreVariable _                    =  False
\end{code}

\newpage
\subsubsection{Evaluating Side-Conditions}

We want to take an atomic side-condition
over a predicate meta-variable
and apply it to a predicate
(that is the expansion of that meta-variable)
to get a new side-condition.
We parameterise this with a context side-condition
in normal form, that can be used to supply further information
about free variables associated with meta-variables found inside expansions.
We assume that the meta-variable in the atomic condition \texttt{atmsc}
was expanded by translation to the predicate argument \texttt{pr}.
\begin{code}
evalPredSideCondition
      :: MatchContext -> SCNF -> SideCond -> Pred -> Maybe SideCond

evalPredSideCondition mctxt goalscnf atmsc pr

 = case fovs of
    BadFVSet _  ->  Nothing
    _           ->  ePSC atmsc
 where

   fovs = predFVSet mctxt pr
   fovs' = reduceFVSetExpr goalscnf fovs
   fpvs = predFreePVars nullMatchContext pr
   fevs = predFreeEVars nullMatchContext pr

   ePSC SCtrue            =  return SCtrue
   ePSC sc@(SCfresh _ _)  =  return sc -- won't occur in normal usage

   ePSC (SCisCond _ _) = isFVSetACondition fovs'

   ePSC (SCnotFreeIn _ vs _)
    = areVariablesNotInFVSet vs fovs'

   ePSC (SCcoverTheFreeOf _ vs _)
     =  doVariablesCoverFVSet vs fovs'

   ePSC (SCareTheFreeOf _ vs _)
     = areVariablesTheFVSet vs fovs'

 -- shouldn't occur in general use.
 -- if it does, then all atomic conditions should refer to same meta-variable

   ePSC (SCAnd scs) = fmap scand $ mapM ePSC scs

-- end evalPredSideCondition

evalExprSideCondition mctxt scnf sc e
                               = evalPredSideCondition mctxt scnf sc (pExpr e)
\end{code}
\newpage
\paragraph{Is it a Condition?}

\input{doc/SideConditions-Precondition}
\begin{code}
isFVSetACondition :: FVSetExpr -> Maybe SideCond
isFVSetACondition (FVSet condsets)
 = do scs <- mapM isCondSetACondition condsets
      return (scand scs)

isCondSetACondition (Atom atom)
 = isAtomACondition atom -- worst case, memberships all true

isCondSetACondition (CondSet _ subcond)
 = isCondSetACondition subcond -- worst case, memberships all true

isCondSetACondition (QCondSet _ _ _) = Nothing

isAtomACondition (Enum as)
 | any (not . isPreVariable) as  =  Nothing
 | otherwise                     =  Just SCtrue

isAtomACondition (NameP pnm _) = Just (SCisCond PredM pnm)

isAtomACondition (NameE enm _) = Just (SCisCond ExprM enm)
\end{code}

\newpage
\paragraph{Are they not free?}

\input{doc/SideConditions-Not-Free}
\begin{code}
areVariablesNotInFVSet :: [Variable] -> FVSetExpr -> Maybe SideCond
areVariablesNotInFVSet vs (FVSet condsets)
 = do scs <- mapM (areVariablesNotInCondSet vs) condsets
      return (scand scs)

areVariablesNotInCondSet vs (Atom atom)
 = areVariablesNotInAtom vs atom

areVariablesNotInCondSet vs (CondSet _ subcond)
 = areVariablesNotInCondSet vs subcond -- ????

areVariablesNotInCondSet vs (QCondSet _ _ _) = Nothing

areVariablesNotInAtom vs (Enum fvs)
 | null (vs `intersect` fvs)  =  Just SCtrue
 | otherwise                  =  Nothing

areVariablesNotInAtom vs (NameP pnm lessvs)
 | lnorm vs `subsetOf` lnorm lessvs  =  Just SCtrue
 | otherwise                         =  Just (SCnotFreeIn PredM vs pnm)

areVariablesNotInAtom vs (NameE enm lessvs)
 | lnorm vs `subsetOf` lnorm lessvs  =  Just SCtrue
 | otherwise                         =  Just (SCnotFreeIn ExprM vs enm)
\end{code}

\newpage
\paragraph{Do they include all free?}

\input{doc/SideConditions-Cover-Free}
\begin{code}
doVariablesCoverFVSet ::  [Variable] -> FVSetExpr -> Maybe SideCond
doVariablesCoverFVSet vs (FVSet condsets)
 = do scs <- mapM (doVariablesCoverCondSet vs) condsets
      return (scand scs)

doVariablesCoverCondSet vs (Atom atom)
 = doVariablesCoverAtom vs atom

doVariablesCoverCondSet vs (CondSet _ subcond)
 = doVariablesCoverCondSet vs subcond

doVariablesCoverCondSet vs (QCondSet _ _ _) = Nothing

doVariablesCoverAtom vs (Enum fvs)
 | lnorm fvs `subsetOf` lnorm vs  =  Just SCtrue
 | otherwise                      =  Nothing

doVariablesCoverAtom vs (NameP pnm lessvs)
  = Just (SCcoverTheFreeOf PredM (lnorm (vs++lessvs)) pnm)

doVariablesCoverAtom vs (NameE enm lessvs)
  = Just (SCcoverTheFreeOf ExprM (lnorm (vs++lessvs)) enm)
\end{code}

\newpage
\paragraph{Are they precisely those free?}

\input{doc/SideConditions-The-Free}
\begin{code}
areVariablesTheFVSet ::  [Variable] -> FVSetExpr -> Maybe SideCond
areVariablesTheFVSet vs (FVSet condsets)
 = do scs <- mapM (areVariablesTheCondSet vs) condsets
      return (scand (concat scs))

areVariablesTheCondSet vs (Atom atom)
 = areVariablesTheAtom vs atom

areVariablesTheCondSet _ _ = Nothing

areVariablesTheAtom vs (Enum fvs)
 | fvs == vs  =  Just [SCtrue]
 | otherwise  =  Nothing

areVariablesTheAtom vs (NameP pnm []) = Just [SCareTheFreeOf PredM vs pnm]
areVariablesTheAtom vs (NameP pnm lessvs)
 | null (vs `intersect` lessvs)
     = Just [SCareTheFreeOf PredM vs pnm,SCnotFreeIn PredM lessvs pnm]
 | otherwise  =  Nothing

areVariablesTheAtom vs (NameE enm []) = Just [SCareTheFreeOf ExprM vs enm]
areVariablesTheAtom vs (NameE enm lessvs)
 | null (vs `intersect` lessvs)
     = Just [SCareTheFreeOf ExprM vs enm,SCnotFreeIn ExprM lessvs enm]
 | otherwise  =  Nothing
\end{code}
