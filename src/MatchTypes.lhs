\section{Match Types}

\begin{code}
module MatchTypes where
import Tables
import Datatypes
import DataText
import Flatten
import Utilities

import Data.List
import Data.Maybe
\end{code}

Here matching is the activity of taking a
\emph{test} predicate \texttt{tpr}
(usually a sub-part of a proof goal)
and comparing it against a
\emph{pattern} predicate \texttt{ppr}
(typically part of a law)
to see if they match.
A successful match then returns a binding from variables
in the pattern to corresponding parts of the test.
Matches need to be performs in a context that identifies
``known'' variables  (those predefined to mean something specific).

Here we provide the key datatypes for matching plus some associated
functions.

\subsection{Matching Type Utilities}

Given type-tables, and a list of \texttt{TTTag}s,
lookup the type of a variable w.r.t. those:
\begin{code}
ttsLookup :: TypeTables -> String -> [TTTag] -> Type
ttsLookup tts v [] = Terror ("No Type-entry for : "++v) Tarb
ttsLookup tts v (tag:tags)
 = case btlookup tts tag of
     Nothing  ->  Terror ("Invalid Type-table Tag : "++show tag) Tarb
     Just vtyps
       -> case tlookup vtyps v of
            Just t   ->  t
            Nothing  ->  ttsLookup tts v tags
ttsVLookup :: TypeTables -> Variable -> [TTTag] -> Type
ttsVLookup tts (_,_,s) = ttsLookup tts s
\end{code}


Given type-tables, and a list of \texttt{TTTag}s leading to an expression,
evaluate its type.
We assume things are well-typed.
\begin{code}
evalExprType :: TypeTables -> [TTTag] -> Expr -> Type

evalExprType tts tags e
 = typof e
 where

   typof T  =  B
   typof F  =  B
   typof (Num i)  =  Z
   typof (Var v)  =  ttsVLookup tts v tags
   typof (Prod es)  =  Tprod $ map typof es
   typof (App f e)
     = case ttsLookup tts f tags of
        Tfun _ tr  ->  tr
        t          ->  Terror (f++" not a function") t
   typof (Bin op i e1 e2)
     = case ttsLookup tts op tags of
        Tfun (Tprod [_,_]) tr  ->  tr
        t                      ->  Terror (op++" not a bin-op.") t
   typof (Equal e1 e2)  =  B
   typof (Set [])  =  Tset Tarb
   typof (Set (e:_))  =  Tset $ typof e
   typof (Setc tag qvs pr e)  =  evalExprType tts (tag:tags) e
   typof (Seq [])  =  Tseq Tarb
   typof (Seq (e:_))  =  Tseq $ typof e
   typof (Seqc tag qvs pr e)  =  evalExprType tts (tag:tags) e
   typof (Map [])  =  Tmap Tarb Tarb
   typof (Map ((d,r):_))  =  Tmap (typof d) (typof r)
   typof (Cond pr e1 e2)  =  typof e1
   typof (Build str es)  =  Tfree "?" [(str,map typof es)]
   typof (The tag v pr)  =  ttsVLookup tts v (tag:tags)
   typof (Evar v)  =  ttsVLookup tts v tags
   typof (Eabs tag qvs e)  =  evalExprType tts (tag:tags) e
   typof (Esub e esub)  =  typof e
   typof (Efocus e)  =  typof e
   typof (Eerror str)  =  Terror ("Eerror "++str) Tarb
   typof (EPred pr)  =  Terror ("EPred "++show pr) B
\end{code}

\subsubsection{Type-related Equivalences}

We shall also introduce a ``liberal type equivalence'',
used in pattern matching, that treats type errors as arbitrary
types, which solves the problem of matching against
quantified variables which don't have types,
and is necessary given that our quantifiers do not provide type
information:
\begin{code}
tlequiv Tarb       t             =  True
tlequiv (Tvar s)   t             =  True -- should bind s to t
tlequiv (Terror _ _) t           =  True
tlequiv t          Tarb          =  True
tlequiv t          (Tvar s)      =  True -- should bind s to t
tlequiv t          (Terror _ _)  =  True
tlequiv (Tprod ts) (Tprod ts')   =  tslequiv ts ts'
tlequiv (Tmap d r) (Tmap d' r')  =  tslequiv [d,r] [d',r']
tlequiv (Tfun d r) (Tfun d' r')  =  tslequiv [d,r] [d',r']
tlequiv (Tset t)   (Tset t')     =  tlequiv t t'
tlequiv (Tseq t)   (Tseq t')     =  tlequiv t t'
tlequiv (Tfree n cs) (Tfree n' cs') =  n==n' && cslequiv cs cs'
tlequiv t          t'            =  t==t'

tslequiv []     []        =  True
tslequiv (t:ts) (t':ts')  =  tlequiv t t' && tslequiv ts ts'
tslequiv _      _         =  False

cslequiv []          []              =  True
cslequiv ((n,ts):cs) ((n',ts'):cs')
  =  n==n' && tslequiv ts ts' && cslequiv cs cs'
cslequiv _           _               = False
\end{code}

\newpage
\subsection{Bindings}

When we match a test predicate against a pattern law (predicate),
we need to return bindings from pattern variables
to corresponding parts of the test predicate.
We have different kinds of variables binding to different kinds
of ``parts'', so we actually need a  number of sub-bindings,
each modelled as a partial function from variable strings
to objects of the relevant kind, here implemented using \texttt{Trie}s.

We expect the collection of sub-bindings of a succesful match
to satisfy the following
 conditions:
\begin{itemize}
  \item Every unknown pattern variable is bound to an appropriate object
  \item Each pattern variable occurs only in one sub-binding
  \item
    A known variable is never bound if it matches itself, only if it
    matches it's definition (e.g. a \texttt{PVar} defined as some other predicate)
\end{itemize}
We now discuss the required sub-bindings:
\begin{description}
  \item[Standard Variables] can occur in three contexts:
    \begin{description}
      \item[Regular]
         is an ordinary occurence in some expression,
         e.g. $x$ in $x+3$ or $P$ in $P \land \True$.
         If not in the scope of an outer quantifier, these can match
         expressions and predicates respectively.
         If bound, they can only match variables of the same kind.
      \item[Quantifier-List]
         is an occurence in a quantifier list of variables,
         e.g. $y$ in $\exists y @ \ldots$ or $Q$ in $\forall Q @ \ldots$.
         These can only match other variables of the same kind.
      \item[Substitution-Target]
         is an occurence in a substitution
         as a target variable to be replaced, e.g. $z$ in $[3/z]$,
         or $R$ in $[\True/R]$.
         These can only match other variables of the same kind.
    \end{description}
  \item[List Variables] can occur in four contexts:
    \begin{description}
      \item[Quantifier-List]
         is an occurrence in a quantifier variable list,
         e.g. $\lst a$ in $\forall \lst a @ \ldots$.
         These can only match lists of variables of the same kind.
      \item[Substitution-Target]
         is an occurence as a target variable
         in a substitution, e.g. $\lst b$ in $[\lst e/\lst b]$.
         These can only match lists of variables of the same kind.
      \item[Substitution-Replacement]
         is an occurence as a replacement expression variable
         in a substitution, e.g. $\lst e$ in $[\lst e/\lst b]$.
         These can only match lists of expressions of the same kind.
      \item[2-Place Predicates]
         look like \textbf{Standard Regular} occurrences,
         except that they occur in pairs in a 2-place predicate,
         e.g. like $\lst c$ and $\lst d$ in $\lst c \leq \lst d$.
         These variables match lists of corresponding expressions
         in conjunctive chains of instances of that 2-place predicate.
    \end{description}
\end{description}
From the above we see that we need the following sub-bindings:

\begin{tabular}{|c|l|}
  \hline
  Variable $\fun$ Expr
  & Std (Regular, not bound)
  \\\hline
  GenRoot $\fun$ Pred
  & Std (Regular, not bound)
  \\\hline
  Variable $\fun$ Variable
  & Std (Regular, bound; Quantifier-List; Substitution-Target)
  \\\hline
  GenRoot $\fun$ GenRoot
  & Std (Regular, bound; Quantifier-List; Substitution-Target)
  \\\hline
  Variable $\fun$ Variable${}^*$
  & Lst (Quantifier-List; Substitution-Target)
  \\\hline
  GenRoot $\fun$ GenRoot${}^*$
  & Lst (Quantifier-List; Substitution-Target)
  \\\hline
  Variable $\fun$ Expr${}^*$
  & Lst (Substitution-Replacement; 2-Place Predicates)
  \\\hline
  GenRoot $\fun$ Pred${}^*$
  & Lst (Substitution-Replacement; 2-Place Predicates)
  \\\hline
\end{tabular}


\subsubsection{Binding Types}
We see a pattern emerging, given a variable type $V$
and an object type $T$, we get the following four bindings:
\begin{eqnarray*}
   V|_{Std} &\fun& T
\\ V|_{Std} &\fun& V
\\ V|_{Lst} &\fun& V^*
\\ V|_{Lst} &\fun& T^*
\end{eqnarray*}
We shall implement the above four lookup functions
as a single \texttt{Trie}, which simplifies the enforcing of the
rule regarding exactly one binding per variable.
\[ V \fun (T + V + V^* + T^*)\]
It also encapsulates the \textbf{Std} vs \textbf{Lst} distinction.

A binding object represents the sum type $T+V+V^*+T^*$:
\begin{code}
data BObj v t
 = TO t       -- Std, Regular not bound
 | VO v       -- Std, Irregular
 | VSO [v]    -- Lst, Quantifier, Subst-Target
 | TSO [t]    -- Lst, Subst-Replace, 2-Place
 deriving (Eq,Ord)

showBObj :: (v -> String, t-> String) -> BObj v t -> String
showBObj (shwv, shwt) (TO t)  =  shwt t
showBObj (shwv, shwt) (VO v)  =  shwv v
showBObj (shwv, shwt) (VSO [])  = "."
showBObj (shwv, shwt) (VSO vs)  = concat $ intersperse "," $ map shwv vs
showBObj (shwv, shwt) (TSO [])  = "."
showBObj (shwv, shwt) (TSO ts)  = concat $ intersperse "," $ map shwt ts

instance (Show v, Show t) => Show (BObj v t) where
  show = showBObj (show, show)
\end{code}
We define a sub-binding as:
\begin{code}
type SBind v t = Trie (BObj v t)

sbnil :: SBind v t
sbnil = tnil

-- explicitly show tagging of object types
oShow :: (v -> String, t -> String) -> SBind v t -> String
oShow (vshw, tshw) = unlines . map oshow . flattenTrie
 where
   oshow (str,obj) = str ++ " >-> " ++ oshow' obj
   oshow' (TO t)   = "TO   " ++ tshw t
   oshow' (VO v)   = "VO " ++ vshw v
   oshow' (VSO vs) = "VSO " ++ show (map vshw vs)
   oshow' (TSO ts) = "TSO " ++ show (map tshw ts)
\end{code}


\newpage
\subsubsection{Binding Update and Lookup}


The \texttt{BObj v t} type involves a linkage between variables ($V$)
and some type of interest ($T$,
usually one of \texttt{Pred}, \texttt{Expr} or \texttt{Type}).
We also assume the existence of a total injective function $vinj : V \fun T$
that embeds a variable in an object of the relevant type,
and a partial projection function $vproj : T \pfun V$ whose domain of definition
is precisely the image of $vinj$.

The idea is to view $V$ as ``lower'' than $T$
(think of $vinj$ as a sub-object embedding).
The plan is always to record a range item at the lowest possible level:
\begin{eqnarray*}
   updVO &:& V \fun V \fun (SBind~V~T) \fun \mathbf{1}+(SBind~V~T)
\\ updVO~k~v~\beta &\defs& \beta\uplus\maplet k {VO~v}
\\
\\ updTO &:& V \fun T \fun (SBind~V~T) \fun \mathbf{1}+(SBind~V~T)
\\ updTO~k~t~\beta
   &\defs&
   \left\{
     \begin{array}{ll}
        updVO~k~(vproj~t)~\beta,     &  t \in vinj(V)
     \\ \beta\uplus\maplet k {TO~t}, & \hbox{otherwise}
     \end{array}
   \right.
\end{eqnarray*}
Here $\uplus$ denotes an update that fails if the new entry conflicts
with an existing one.

Lookup expecting a $V$ result succeeds only if a $VO$ object is found,
while those expecting a $T$ result will accept a $TO$ result,
but also use $vinj$ if a $VO$ result is found.

We do similarly for $VSO$ and $TSO$, provided all list elements are in the
image of $vinj$.

For now, we enforce the Std/Lst variable separation at update time.
This check might be removed to improve performance later,
if we can be sure that calls are OK.

\paragraph{$VO$ update and lookup}~

\begin{code}
updateVO :: (Monad m, Eq v, Eq t)
         => String -> v -> SBind v t -> m (SBind v t)
updateVO key v sbind
 | isStdS key  =  m2m $ mtenter same key (VO v) sbind
 | otherwise   =  nowt

lookupVO :: (Monad m, Eq v, Eq t) => String -> SBind v t -> m v
lookupVO key sbind
  = case tlookup sbind key of
      Just (VO v)  ->  return v
      _            ->  nowt
\end{code}

\paragraph{$TO$ update and lookup}~

\begin{code}
updateTO :: (Monad m, Eq v, Eq t)
         => (t -> Maybe v) -> String -> t -> SBind v t -> m (SBind v t)
updateTO vproj key t sbind
 | isLstS key   =  nowt
 | otherwise
   =  case vproj t of
        Nothing  ->  m2m $ mtenter same key (TO t) sbind
        Just v   ->  m2m $ mtenter same key (VO v) sbind

lookupTO :: (Monad m, Eq v, Eq t)
         => (v -> t) -> String -> SBind v t -> m t
lookupTO vinj key sbind
  = case tlookup sbind key of
      Just (TO t)  ->  return t
      Just (VO v)  ->  return $ vinj v
      _            ->  nowt
\end{code}

\newpage
\paragraph{$VSO$ update and lookup}~

\begin{code}
updateVSO :: (Monad m, Eq v, Eq t) => String -> [v] -> SBind v t -> m (SBind v t)
updateVSO key vs sbind
 | isLstS key  =  m2m $ mtenter same key (VSO vs) sbind
 | otherwise   =  nowt

lookupVSO :: (Monad m, Eq v, Eq t) => String -> SBind v t -> m [v]
lookupVSO key sbind
  = case tlookup sbind key of
      Just (VSO vs)  ->  return vs
      _              ->  nowt
\end{code}

\paragraph{$TSO$ update and lookup}~

\begin{code}
updateTSO :: (Monad m, Show v, Show t, Eq v, Eq t)
          => (t -> Maybe v) -> String -> [t] -> SBind v t -> m (SBind v t)
updateTSO vproj key ts sbind
 | isStdS key      =  nowt
 | all isJust mvs  =  m2m $ mtenter same key (VSO $ map fromJust mvs) sbind
 | otherwise       =  m2m $ mtenter same key (TSO ts)                 sbind
 where
    mvs = map vproj ts

lookupTSO :: (Monad m, Eq v, Eq t)
           => (v -> t) -> String -> SBind v t -> m [t]
lookupTSO vinj key sbind
  = case tlookup sbind key of
      Just (TSO ts)  ->  return ts
      Just (VSO vs)  ->  return $ map vinj vs
      _              ->  nowt
\end{code}

\newpage
\subsubsection{Merging Bindings}

We will need to be able to merge bindings,
where for the VO and TO cases, the two values must agree (as per tglue)
but for VSO and TSO we merge the two lists, using helper functions:
\begin{code}
mergeBObj :: (Eq v, Eq t)
          => ([v] -> [v] -> Maybe [v])
          -> ([t] -> [t] -> Maybe [t])
          -> BObj v t -> BObj v t
          -> Maybe (BObj v t)
mergeBObj vsmrg tsmrg t1@(TO obj1) (TO obj2)
 | obj1 == obj2            =  Just t1
mergeBObj vsmrg tsmrg v1@(VO var1) (VO var2)
 | var1 == var2            =  Just v1
mergeBObj vsmrg tsmrg (TSO objs1) (TSO objs2)
 = case objs1 `tsmrg` objs2 of
     Nothing     ->  Nothing
     Just objs'  ->  Just $ TSO objs'
mergeBObj vsmrg tsmrg (VSO vars1) (VSO vars2)
 = case vars1 `vsmrg` vars2 of
     Nothing     ->  Nothing
     Just vars'  ->  Just $ VSO vars'
mergeBObj vsmrg tsmrg _ _  =  Nothing

mergeSBind :: (Eq v, Eq t)
           => ([v] -> [v] -> Maybe [v])
           -> ([t] -> [t] -> Maybe [t])
           -> SBind v t -> SBind v t
           -> Maybe (SBind v t)
mergeSBind vsmrg tsmrg = tmmerge (mergeBObj vsmrg tsmrg)
\end{code}

The most common use case is to concatentate the two lists,
removing duplicates and sorting:
\begin{code}
lmergeBObj :: Ord a => [a] -> [a] -> Maybe [a]
lmergeBObj xs ys  = Just $ lnorm (xs ++ ys)

lmergeSBind :: (Ord v, Ord t)
            => SBind v t -> SBind v t
            -> Maybe (SBind v t)
lmergeSBind = mergeSBind lmergeBObj lmergeBObj
\end{code}

\newpage
\subsubsection{The Bindings}

We will have three instances, one each for predicates, expressions and types:
\begin{code}
type GPBind = SBind GenRoot Pred
showGPObj = showBObj (genRootString, show)
showGPBind  :: GPBind -> String
showGPBind = unlines' . trieShowWith showGPObj
gpInj :: GenRoot -> Pred
gpInj = Pvar
gpProj :: Pred -> Maybe GenRoot
gpProj (Pvar g)  =  Just g
gpProj _         =  Nothing

type VEBind = SBind Variable Expr
showVEObj = showBObj (varKey, show)
showVEBind :: VEBind -> String
showVEBind = unlines' . trieShowWith showVEObj
veInj :: Variable -> Expr
veInj = Var
veProj :: Expr -> Maybe Variable
veProj (Var v)    =  Just v
veProj (Evar ev)  =  Just ev
veProj _          =  Nothing

type TTBind = SBind TVar Type
showTTObj = showBObj (id, show)
showTTBind :: TTBind -> String
showTTBind = unlines' . trieShowWith showTTObj
ttInj :: TVar -> Type
ttInj = Tvar
ttProj :: Type -> Maybe TVar
ttProj (Tvar t)  =  Just t
ttProj _         =  Nothing
\end{code}
We now define the overall binding as a triple of sub-bindings,
one each for predicates, expressions and types:
\begin{code}
type Binding = (GPBind, VEBind, TTBind)

nullBinds :: Binding
nullBinds = (tnil,tnil,tnil)

showBinding :: Binding -> [String]
showBinding (gpbnds,vebnds,ttbnds)
 = let
     (gpkeysize,gppairs) = flattenTrieD gpbnds
     (vekeysize,vepairs) = flattenTrieD vebnds
     (ttkeysize,ttpairs) = flattenTrieD ttbnds
     keywidth = maximum [gpkeysize,vekeysize,ttkeysize]
     gpShown = bshow keywidth gppairs
     veShown = bshow keywidth vepairs
     ttShown = bshow keywidth ttpairs
   in concat [gpShown,veShown,ttShown]
 where
   bshow _ [] = []
   bshow w pairs = showFlatTrieWith show "" (w,pairs)
\end{code}


\paragraph{Specialising for \texttt{GenRoot}, \texttt{Pred}}~

\begin{code}
gpupdateTO :: Monad m => GenRoot -> Pred -> GPBind -> m GPBind
gpupdateTO r = updateTO gpProj (genRootString r)

gplookupTO :: Monad m => GenRoot -> GPBind -> m Pred
gplookupTO r = lookupTO Pvar (genRootString r)

gpupdateVO :: Monad m => GenRoot -> GenRoot -> GPBind -> m GPBind
gpupdateVO r = updateVO (genRootString r)

gplookupVO :: Monad m => GenRoot -> GPBind -> m GenRoot
gplookupVO r = lookupVO (genRootString r)

gpupdateVSO :: Monad m => GenRoot -> [GenRoot] -> GPBind -> m GPBind
gpupdateVSO r = updateVSO (genRootString r)

gplookupVSO :: Monad m => GenRoot -> GPBind -> m [GenRoot]
gplookupVSO r = lookupVSO (genRootString r)

gplookupTSO :: Monad m => GenRoot -> GPBind -> m [Pred]
gplookupTSO r = lookupTSO Pvar (genRootString r)

gpupdateTSO :: Monad m => GenRoot -> [Pred] -> GPBind -> m GPBind
gpupdateTSO r  = updateTSO gpProj (genRootString r)
\end{code}

\paragraph{Specialising for \texttt{Variable}, \texttt{Expr}}~

\begin{code}
veupdateTO :: Monad m => Variable -> Expr -> VEBind -> m VEBind
veupdateTO v  = updateTO veProj (varKey v)

velookupTO :: Monad m => Variable -> VEBind -> m Expr
velookupTO v = lookupTO Var (varKey v)

veupdateVO :: Monad m => Variable -> Variable -> VEBind -> m VEBind
veupdateVO v = updateVO (varKey v)

velookupVO :: Monad m => Variable -> VEBind -> m Variable
velookupVO v = lookupVO (varKey v)

veupdateVSO :: Monad m => Variable -> [Variable] -> VEBind -> m VEBind
veupdateVSO v = updateVSO (varKey v)

velookupVSO :: Monad m => Variable -> VEBind -> m [Variable]
velookupVSO v = lookupVSO (varKey v)

veupdateTSO :: Monad m => Variable -> [Expr] -> VEBind -> m VEBind
veupdateTSO v = updateTSO veProj (varKey v)

velookupTSO :: Monad m => Variable -> VEBind -> m [Expr]
velookupTSO v = lookupTSO Var (varKey v)
\end{code}

A useful specialisation are variants of \texttt{lbuild} tailored
for variables:
\begin{code}
vbuild :: [(Variable,Variable)] -> VEBind
vbuild = lbuild . mapboth (varKey,VO)

vlbuild :: [(Variable,[Variable])] -> VEBind
vlbuild = lbuild . mapboth (varKey,VSO)
\end{code}

\paragraph{Specialising for \texttt{TVar}, \texttt{Type}}~

\begin{code}
ttupdateTO :: Monad m => TVar -> Type -> TTBind -> m TTBind
ttupdateTO  = updateTO ttProj

ttlookupTO :: Monad m => TVar -> TTBind -> m Type
ttlookupTO = lookupTO Tvar

ttupdateVO :: Monad m => TVar -> TVar -> TTBind -> m TTBind
ttupdateVO  = updateVO

ttlookupVO :: Monad m => TVar -> TTBind -> m TVar
ttlookupVO = lookupVO

ttupdateVSO :: Monad m => TVar -> [TVar] -> TTBind -> m TTBind
ttupdateVSO  = updateVSO

ttlookupVSO :: Monad m => TVar -> TTBind -> m [TVar]
ttlookupVSO = lookupVSO

ttupdateTSO :: Monad m => TVar -> [Type] -> TTBind -> m TTBind
ttupdateTSO  = updateTSO ttProj

ttlookupTSO :: Monad m => TVar -> TTBind -> m [Type]
ttlookupTSO = lookupTSO Tvar
\end{code}


Also useful are tailored \texttt{tmap}s:
\begin{code}
mapT :: (t -> s) -> BObj v t -> BObj v s
mapT f (TO x)   =  TO $ f x
mapT f (TSO xs) =  TSO $ map f xs
mapT _ (VO v)   =  VO v
mapT _ (VSO v)  =  VSO v

tmapT :: (t -> s) -> SBind v t -> SBind v s
tmapT f = tmap (mapT f)
\end{code}


\subsubsection{Binding Injections}

Basic injections, starting with a safe way to get a sub-binding:
\begin{code}
mkSubBind :: Maybe (SBind v t) -> SBind v t
mkSubBind (Just sbind) = sbind
mkSubBind Nothing      = sbnil

bindP :: GenRoot -> Pred -> Binding
bindP r pr = ( mkSubBind $ gpupdateTO r pr sbnil, tnil, tnil )
bindE :: Variable -> Expr -> Binding
bindE v e = ( tnil, mkSubBind $ veupdateTO v e sbnil, tnil )

bindT :: TVar -> Type -> Binding
bindT tv t = ( tnil, tnil, mkSubBind $ ttupdateTO tv t sbnil )

bindQ :: Variable -> Variable -> Binding
bindQ v vv = ( tnil, mkSubBind $ veupdateVO v vv sbnil, tnil )

bindQL :: Variable -> [Variable] -> Binding
bindQL v vs = ( tnil, sBindQL v vs, tnil )
sBindQL v vs = mkSubBind $ veupdateVSO v vs sbnil
\end{code}

Putting a variable/variable binding into the right place:
\begin{code}
bindV :: Variable -> Variable -> Binding
bindV v x
 | isStdV v   =  bindQ  v  x
 | otherwise  =  bindQL v [x]
\end{code}
Putting a variable/variable-list binding into the right place,
if possible:
\begin{code}
bindVL :: Variable -> [Variable] -> Binding
bindVL v [x]
 | isStdV v && isStdV x  =  bindQ v x
 | otherwise             =  bindQL v [x]
bindVL v xs
 | isStdV v              =  nullBinds
 | otherwise             =  bindQL v xs
\end{code}

A special case occurs when pattern and test variables
are both the same reserved variable, and the pattern has a subscript.
If $R_a \to R^d$ then we include all three bindings
\[
  \setof{  O_a \to O^d, M_a \to M^d, S_a \to S^d }
\]
This is to prevent bindings such as
\[
 \setof{ M_a \to M_1, S_a \to S' }
\]
that are inconsistent with the intended meaning of reserved variables.
In fact whenever we bind any subscripted known observation variable
we need to do the same.
Let $\omega \in \sem{O} \cup \setof{O,M,S}$.
Then , if we want a binding $\omega_a \to \psi_b$,
the binding we construct is
\[
 \mapof{
   O_a \to O_b
 , M_a \to M_b
 , S_a \to S_b
 , o1_a \to o1_b
 , \ldots
 , ok_a \to o\ell_b
 }
 \override
 \maplet{\omega_a}{\psi_b}
\]
where $\sem{O} = \setof{o1,\ldots,o\ell}$.

We first start with a function that,
given the list $o1,\ldots,o\ell$ of observable roots (undecorated)
and a pair of subscripts $a$ and $b$,
generates the lefthand map above:
\begin{code}
genObsSubscriptMap :: [String] -- undecorated observable roots
                   -> String   -- from subscript
                   -> String   -- to subscript
                   -> VEBind
genObsSubscriptMap roots froms tos
 = lbuild (rsvMap ++ map (mkTo froms tos) roots)
 where

   rsvMap = [ ( strOBS ++ sFrom, VSO $ [mkRVar OBS [] sTo] )
            , ( strMDL ++ sFrom, VSO $ [mkRVar MDL [] sTo] )
            , ( strSCR ++ sFrom, VSO $ [mkRVar SCR [] sTo] ) ]

   mkTo froms tos root = ( root++sFrom, VO $ mkSVar root sTo )

   sFrom = chrSUBS:froms
   sTo = Subscript tos
\end{code}

\begin{code}
mergeMR :: Monad m => MatchResult -> MatchResult -> m MatchResult
(bnds1,qvm1,sbm1) `mergeMR` (bnds2,qvm2,sbm2)
  = do bnds' <- bnds1 `mrgB` bnds2
       return (bnds', lnorm (qvm1++qvm2), lnorm (sbm1++sbm2))
\end{code}


Another case we must consider is where we have matched pattern $R\less{x}$
against $R\less{y}$. In addition to the obvious binding $\maplet{R\less{x}}{R\less{y}}$,
we also need to add the binding $\maplet x y$, except if $x$ is known and equal to $y$.
This prevents $x$ matching anything else elsewhere.

We now supply a function that takes two reserved variables: one the pattern,
the other the test, and produces all such extra bindings.
If there is more than one possible such binding then a deferred match is returned.
\begin{code}
genRsvLessMap :: [String] -- undecorated observable roots
              -> Variable -- pattern reserved variable
              -> Variable -- test reserved variable
              -> MatchResult

genRsvLessMap roots (Rsv _ pless,_,_) (Rsv _ tless,_,_)
 = case (pstrs, tstrs) of
     ([pstr], _) -- shouldn't have to use parseVariable here.... !!!!
       -> ( bindVL (parseVariable pstr) (map parseVariable tstrs)
          , [], [] )
     _ -> ( nullBinds
          , [ (map parseVariable pstrs, map parseVariable tstrs) ]
          , [])
 where
   pstrs = (map genRootString pless) \\ roots
   tstrs = (map genRootString tless) -- \\ roots

genRsvLessMap roots prv trv = noBinding
\end{code}

Now functions to bind taking account the above considerations:
\begin{code}
bindO :: Monad m => [String] -> Variable -> Variable -> m MatchResult
bindO roots p@(pr, pd@(Subscript ps), pkey)
            m@(_, md@(Subscript ms), _)
 | isObsVarRelated roots pr
 = ( bindV p m `lmrgJB` ( tnil, genObsSubscriptMap roots ps ms, tnil )
   , [], [] )
   `mergeMR` genRsvLessMap roots p m
bindO roots rp rt
 = ( bindV rp rt, [], [] ) `mergeMR` (genRsvLessMap roots rp rt)

isObsVarRelated :: [String] -> Root -> Bool
isObsVarRelated _     (Rsv _ _)          =  True
isObsVarRelated roots (Gen (Std root) )  =  root `elem` roots
isObsVarRelated _     _                  =  False
\end{code}

When binding to observation-related variable lists,
we want to ensure all subscripts are the same
\begin{code}
bindOL :: Monad m => [String] -> Variable -> [Variable] -> m Binding

bindOL roots p@(pr,(Subscript ps),_) mvs
 | isObsVarRelated roots pr
 = case getSubscripts mvs of
    []    ->  return $ bindQL p mvs
    [ms]  ->  return ( tnil
                   , genObsSubscriptMap roots ps ms `tmerge` sBindQL p mvs
                   , tnil )
    _     ->  fail "bindOL: differing subscripts"

bindOL roots pobs mvs  =  return $ bindQL pobs mvs


lmergeVE :: [Variable] -> [Variable] -> Maybe [Variable]
lmergeVE xs ys
 | sameSubscripts mrgdvs  =  Just mrgdvs
 | otherwise              =  Nothing
 where
   mrgdvs  = lnorm (xs ++ ys)

getSubscripts :: [Variable] -> [String]
getSubscripts = lnorm . concat . map getSubs
 where
   getSubs (_,(Subscript s),_) = [s]
   getSubs _                   = []

sameSubscripts :: [Variable] -> Bool
sameSubscripts [] = True
sameSubscripts ((_,(Subscript s),_):rest)
 = same s rest
 where
   same s [] = True
   same s ((_,Subscript t,_):rest) = s==t && same s rest
   same s (_:rest) = same s rest
sameSubscripts (_:rest) = sameSubscripts rest


lmergeObs :: VEBind -> VEBind -> Maybe VEBind
lmergeObs = mergeSBind lmergeVE lmergeBObj

lmrgObs :: Binding -> Binding -> Maybe Binding
(gp1,ev1,tt1) `lmrgObs` (gp2,ev2,tt2)
  = do gp' <- gp1 `lmergeSBind` gp2
       ev' <- ev1 `lmergeObs` ev2
       tt' <- tt1 `lmergeSBind` tt2
       return (gp',ev',tt')
\end{code}


non-Std Variables in substitution replacement lists,
and 2-place predicates
need to bind to lists of expressions.
\begin{code}
bindES :: Variable -> [Expr] -> Binding
bindES v es = ( tnil, mkSubBind $ veupdateTSO v es sbnil, tnil )
\end{code}

\subsubsection{SBind Projections}

Sometimes it is useful to be able to slice up a binding based
on the bind-object type or tag:
\begin{code}
justTO :: SBind v t ->  Trie t
justTO = lbuild . catMaybes . map getTO . flattenTrie
 where getTO (k,TO t) = Just (k, t)
       getTO _        = Nothing

justVO :: SBind v t ->  Trie v
justVO = lbuild . catMaybes . map getVO . flattenTrie
 where getVO (k,VO v) = Just (k, v)
       getVO _        = Nothing

justTSO :: SBind v t ->  Trie [t]
justTSO = lbuild . catMaybes . map getTSO . flattenTrie
 where getTSO (k,TSO ts) = Just (k, ts)
       getTSO _          = Nothing

justVSO :: SBind v t ->  Trie [v]
justVSO = lbuild . catMaybes . map getVSO . flattenTrie
 where getVSO (k,VSO vs) = Just (k, vs)
       getVSO _        = Nothing
\end{code}
However note that some bindings may not occur where you expect, due
to the variable/type injection and projection done by lookup and update.


\subsection{Binding Operations}

A very common operation is that of merging two bindings
($\beta_1 \uplus \beta_2$), which simply amalgamates
all the bindings into one,
provided that the bindings both agree on any variables
they share ($\beta_1 \cong \beta_2$).
Merging bindings will fail if the same name is bound
to different values in $\beta_1$ and $\beta_2$.
Operationally, the check that $\beta_1 \cong \beta_2$
is carried out while attempting to compute $\beta_1 \uplus \beta_2$:
\begin{code}
mrgB :: Monad m => Binding -> Binding -> m Binding
(gp1,ev1,tt1) `mrgB` (gp2,ev2,tt2)
  = do gp' <- gp1 `tglue` gp2
       ev' <- ev1 `tglue` ev2
       tt' <- tt1 `tglue` tt2
       return (gp',ev',tt')

mrgMB :: Monad m => m Binding -> m Binding -> m Binding
mrgMB mb1 mb2
 = do b1 <- mb1
      b2 <- mb2
      b1 `mrgB` b2
\end{code}

We also have variants that fuse lists in VSO/TSO bindings:
\begin{code}
lmrgB :: Binding -> Binding -> Maybe Binding
(gp1,ev1,tt1) `lmrgB` (gp2,ev2,tt2)
  = do gp' <- gp1 `lmergeSBind` gp2
       ev' <- ev1 `lmergeSBind` ev2
       tt' <- tt1 `lmergeSBind` tt2
       return (gp',ev',tt')

lmrgJB :: Binding -> Binding -> Binding
bnd1 `lmrgJB` bnd2
 = case bnd1 `lmrgB` bnd2 of
     Nothing    ->  (tnil, tnil, tnil)
     Just bnd'  ->  bnd'
\end{code}

\newpage
\subsubsection{Deferred Matching}

Some matches, to do with \texttt{QVars}, have to be deferred for
post-processing that requires free-variable information,
as well using side-conditions as hints.
\begin{code}
type QVarMatchToDo = ([Variable],[Variable]) -- (test,pattern)
\end{code}
We expect all instances of \texttt{QVarMatchToDo},
here shown w.l.og. as:
\begin{eqnarray*}
   \mbox{test} && a_1,\ldots,a_n,\lst b_1,\ldots,b_m
\\ \mbox{pattern} && u_1,\ldots,u_k,\lst v_1,\ldots,\lst v_\ell
\end{eqnarray*}
to satisfy the follow
well-formedness conditions:
\begin{itemize}
  \item 
    The number of standard and list variables in both test and pattern
    must satisfy the following relationship, which is derived
    from a counting argument that establishes a necessary
    (but not sufficient) condition for a match to be possible:
    \[
      n \geq k \land \left( (n\neq k \lor m > 0) \implies \ell > 0 \right)
    \]
\end{itemize}
\begin{code}
isWFQVarToDo :: [Variable] -> [Variable] -> Bool
isWFQVarToDo tvs pvs
 | n <  k            =  False
 | n == k && m == 0  =  True
 | otherwise         =  ell > 0
 where
  (n,m) = setboth (length,length) (partition isStdV tvs)
  (k,ell) = setboth (length,length) (partition isStdV pvs)
\end{code}

We also have do do something similar with substitution matching.
But we also need a local match context
for passing type and free-variable information
local to the relevant point on a match
\begin{code}
data LocalContext
 = LC {
     mctx :: MatchContext
   , ttts  :: TypeTables
   , ptts  :: TypeTables
   , ttags :: [TTTag]
   , ptags :: [TTTag]
   , tbvs  :: [Variable]  -- test variables bound here
   , pbvs  :: [Variable]  -- pattern variables bound here
   } deriving (Eq, Ord, Show)

noLocalContext :: LocalContext
noLocalContext = LC nullMatchContext Bnil Bnil [] [] [] []

type SubstMatchToDo v a
 = ( [(v,a)]  -- test substitution pairs
   , [(v,a)]  -- pattern substitution pairs
   , LocalContext
   )
\end{code}

Well-formedness when \texttt{v} is instantiated by \texttt{Variable} is as for 
\texttt{QVars}:
\begin{code}
type ESubstMatchToDo = SubstMatchToDo Variable Expr

isWFSubstToDo :: [(Variable,Expr)] -> [(Variable,Expr)] -> Bool
isWFSubstToDo tsubs psubs = isWFQVarToDo (map fst tsubs) (map fst psubs)

dropLCtxt  :: SubstMatchToDo v a -> ([(v,a)],[(v,a)])
dropLCtxt (ts,ps,_) = (ts,ps)
\end{code}
A match-result is bindings with lists of deferred \texttt{QVar} and \texttt{Substn}
matches.
\begin{code}
type MatchResult = (Binding,[QVarMatchToDo],[ESubstMatchToDo])

mkQVarsToDo []  vs2  =  []
mkQVarsToDo vs1 []   =  []
mkQVarsToDo vs1 vs2  =  [(vs1,vs2)]

mkSubstToDo _ []  vs2  =  []
mkSubstToDo _ vs1 []   =  []
mkSubstToDo lctxt vs1 vs2  =  [(vs1,vs2,lctxt)]


isCompleteMatch :: MatchResult -> Bool
isCompleteMatch (_,qvms,subms) = null qvms && null subms

noBinding :: MatchResult
noBinding  = ( nullBinds, [], [] )

deferQMatch :: QVars -> QVars -> MatchResult
deferQMatch (Q tv) (Q pv) = ( nullBinds, [(tv,pv)], [] )

deferSMatch :: LocalContext -> ESubst -> ESubst -> MatchResult
deferSMatch lctxt (Substn ts) (Substn ps)
 = ( nullBinds, [], [(ts,ps,lctxt)] )
\end{code}

\newpage
Some matching is simpler and just returns a single binding,
so it helps to be able to inject one of these into a full match result:
\begin{code}
injPbind :: [(String,Pred)] -> MatchResult
injPbind pbnd = ((lbuild $ mapsnd TO pbnd,tnil,tnil),[],[])

injEbind :: [(String,Expr)] -> MatchResult
injEbind ebnd = ((tnil,lbuild $ mapsnd TO ebnd,tnil),[],[])

injTbind :: [(String,Type)] -> MatchResult
injTbind tbnd = ((tnil,tnil,lbuild $ mapsnd TO tbnd),[],[])

injQbind :: [(String,Variable)] -> MatchResult
injQbind qbnd = ((tnil,lbuild $ mapsnd VO qbnd,tnil),[],[])

injQLbind :: [(String,[Variable])] -> MatchResult
injQLbind qbnd = ((tnil,lbuild $ mapsnd VSO qbnd,tnil),[],[])
\end{code}

A match-outcome either fails,
or returns a binding with deferred \texttt{QVars} and \texttt{ESubst} matches.
\begin{code}
type MatchOutcome = Maybe MatchResult

okNoBinding :: Monad m => m MatchResult
okNoBinding  = return noBinding

okBindP :: Monad m => GenRoot -> Pred -> m MatchResult
okBindP pv p = return ((bindP pv p),[],[])

okBindE :: Monad m => Variable -> Expr -> m MatchResult
okBindE ev e = return ((bindE ev e),[],[])

okBindT :: Monad m => TVar -> Type -> m MatchResult
okBindT tv t = return ((bindT tv t),[],[])

okBindQ :: Monad m => Variable -> Variable -> m MatchResult
okBindQ qv q = return ((bindQ qv q),[],[])

okBindQL :: Monad m => Variable -> [Variable] -> m MatchResult
okBindQL qv qvs = return ((bindQL qv qvs),[],[])

okBindV :: Monad m => Variable -> Variable -> m MatchResult
okBindV v x = return ((bindV v x),[],[])

okBindO :: Monad m => [String] -> Variable -> Variable -> m MatchResult
okBindO roots v x = bindO roots v x  -- difference has disappeared !

okBindES :: Monad m => Variable -> [Expr] -> m MatchResult
okBindES v es = return ((bindES v es),[],[])

okBindEQ :: Monad m => Variable -> Expr -> m MatchResult
okBindEQ pv te = okBindES pv [te]
\end{code}



To simplify matters, we do not maintain a separate binding list
for predicate-set names, but instead let them share
the predicate binding space by prefixing their names
with \lit\{.
This is safe as no name can start with such a character.
\begin{code}
psName nm = '{':nm
\end{code}

\newpage
\subsection{Match Types}

We also note that some laws are best used with partial
matches, so we have a mechanism for describing
which parts of certain laws have been matched against.
\begin{code}
data MatchType
 = All -- matched whole law
 | LEqv -- matched lhs of equivalence
 | REqv -- matched rhs of equivalence
 | Ante -- matched lhs of implication
 | Cnsq -- matched rhs of implication
 | LCEqv -- matched lhs of an conditional equivalence
 | RCEqv -- matched rhs of an conditional equivalence
 | TREqv -- matched single-Pvar rhs of equivalence
 deriving (Eq,Ord,Show)

stateMTyp :: MatchType -> String
stateMTyp All = ""    -- whole law
stateMTyp LEqv = " (L-to-R)"
stateMTyp REqv = " (R-to-L)"
stateMTyp Ante = " (ante-by-cnsq)"
stateMTyp Cnsq = " (cnsq-by-ante)"
stateMTyp LCEqv = " (L-to-R, cond. holds)"
stateMTyp RCEqv = " (R-to-L, cond. holds)"
stateMTyp TREqv = " (R-to-L expansion)"
\end{code}

We want to be able to rank based on match-type,
level of trust, as well as the bindings and replacement predicates that are part
of a successful match.
\begin{code}
type LawMatch = (MatchType,Provenance,Binding,SideCond,[Pred])
\end{code}

Sometimes we want to discriminate by \texttt{MatchType}
or \texttt{Provenance}:
\begin{code}
hasMType :: MatchType -> LawMatch -> Bool
hasMType m' (m,_,_,_,_) = m == m'

hasProvClass :: Provenance -> LawMatch -> Bool
hasProvClass p' (_,p,_,_,_) = sameProvClass p' p

sameProvClass (FromUSER _)   (FromUSER _)   = True
sameProvClass (UserDEFN _)   (UserDEFN _)   = True
sameProvClass (FromSOURCE _) (FromSOURCE _) = True
sameProvClass (ViaPROOF _)   (ViaPROOF _)   = True
sameProvClass _              _              = False
\end{code}




\subsection{Matching Context}

\input{doc/Matching-Known}

\subsubsection{Language Definitions}

In addition, in order to handle user-defined language constructs properly,
we need a mapping from construct names to lists
of definitions, each represented as a lhs/rhs predicate pair.
\begin{code}
type LangDefn = (Pred,Pred)
\end{code}

In general we allow multiple definitions
for any given construct, but the preferred usage
is for only one to be present in the system.
Definitions will be matched in order \emph{using basic matching only},
with the first successful
match being used, so multiple matches only make sense if earlier
ones have more specific patterns, which means repeated pattern variables.
There should be at least one entry whose left-hand side has
no repeated variables, so matching the most general case.

These definition pairs are not required for basic matching itself,
but are required to establish the free variables of such constructs,
which itself requires basic matching.
As the \texttt{MatchContext} is threaded through all the matching code,
it is simplest for these pairs to live here.

It is also useful for matching infix operators (\S\ref{ssec:infix-matching}),
as an exception is a language construct denoting an infix operator
without such laws, which is interpreted as standing for a generic/arbitrary
instance of such an infix operator.

In some cases we want to introduce language constructs
and then define their behaviour axiomatically,
without having given them definitions as explicit predicates.
In order to do this, and allow basic matching,
we will provide a predicate matching list-variable ($\_UNINT$)
that indicates a language construct is ``uninterpreted''.
This meta-predicate always has an empty free variable set.

It should also be noted, that what has just been described is
a global matching context, defined by ``where'' a match pattern
is located, not to be confused with the local matching context
described earlier,
that depends on which pattern in that location is being matched
as well as the test pattern being matched.

\subsubsection{Matching Context Contents}

All components are lists of tables, drawn from
the current active stack of theories.
\begin{code}
data MatchContext
  = MatchContext {
      mcThName    :: String -- name of relevant theory
    , knownObs    :: [Trie ObsKind]
    , knownTypes  :: [Trie Type]
    , knownConsts :: [Trie Expr]
    , knownExprs  :: [Trie Expr]
    , knownPreds  :: [Trie Pred]
    , langDefns   :: [Trie [LangDefn]]
    -- derived
    , mdlObs, srcObs, mdlObs', srcObs' :: [Variable]
    , sizeObs,  sizeMdl,  sizeScr
    , sizeObs', sizeMdl', sizeScr' :: Int
    , mdlRoots :: [String]
    , scrRoots :: [String]
    , obsRoots :: [String]
    }
  deriving (Eq,Ord)

instance Show MatchContext where
 show mctxt
  = unlines [ "MatchContext("++mcThName mctxt++")"
            , "  obs. -"
              ++ showObs " Model: " (mdlObs mctxt++mdlObs' mctxt)
              ++ showObs " Script: " (srcObs mctxt++srcObs' mctxt)
            , "  types        : " ++ showKnown knownTypes  mctxt
            , "  constants    : " ++ showKnown knownConsts mctxt
            , "  expressions  : " ++ showKnown knownExprs  mctxt
            , "  predicates   : " ++ showKnown knownPreds  mctxt
            , "  lang. cnstr. : " ++ showKnown langDefns   mctxt
            ]
  where
   showObs _ [] = ""
   showObs typ obs = typ ++ (concat $ intersperse "," $ map showVar obs)
   showKnown sel mctxt
    = concat $ intersperse ";" $  map showMCTrie $ sel mctxt
   showMCTrie = concat . intersperse "," . trieDom
\end{code}

Checking known variables:
\begin{code}
isKnownVar :: MatchContext -> Variable -> Bool
isKnownVar mctxt v
 = tsvlookup (knownObs mctxt) v /= Nothing
   &&
   tsvlookup (knownConsts mctxt) v /= Nothing

kPartition mctxt = partition (isKnownVar mctxt)

isKnownExpr :: MatchContext -> Variable -> Bool
isKnownExpr mctxt v = tsvlookup (knownExprs mctxt) v /= Nothing

isKnownPred :: MatchContext -> GenRoot -> Bool
isKnownPred mctxt r = tslookup (knownPreds mctxt) (genRootString r) /= Nothing
\end{code}

We derive some useful \texttt{knownObs} lookups
\begin{code}
deriveMatchContext mctxt
 = mctxt{ mdlObs = mobs, mdlObs' = mobs'
        , srcObs = sobs, srcObs' = sobs'
        , sizeObs  = lenMdl+lenScr,   sizeMdl  = lenMdl,  sizeScr  = lenScr
        , sizeObs' = lenMdl'+lenScr', sizeMdl' = lenMdl', sizeScr' = lenScr'
        , mdlRoots = mroots
        , scrRoots = sroots
        , obsRoots = mroots `mrgnorm` sroots
        }
 where
   kobs = concat $ map trieRng $ knownObs mctxt
   (mdls,scrs) = partition ((==Model).snd3) kobs
   (mobs,mobs') = partition before $ map fst3 $ mdls
   (sobs,sobs') = partition before $ map fst3 $ scrs
   before (_, Pre, _)  =  True
   before _            =  False
   lenMdl  = length mobs
   lenMdl' = length mobs'
   lenScr  = length sobs
   lenScr' = length sobs'
   mroots = lnorm $ map varRootAsString (mobs++mobs')
   sroots = lnorm $ map varRootAsString (sobs++sobs')

nullMatchContext
 = MatchContext
       { mcThName     = "null-theory"
       , knownObs     =  []
       , knownTypes   =  []
       , knownConsts  =  []
       , knownExprs   =  []
       , knownPreds   =  []
       , langDefns    =  []
       , mdlObs       =  []
       , srcObs       =  []
       , mdlObs'      =  []
       , srcObs'      =  []
       , sizeObs      =  0
       , sizeMdl      =  0
       , sizeScr      =  0
       , sizeObs'     =  0
       , sizeMdl'     =  0
       , sizeScr'     =  0
       , mdlRoots     =  []
       , scrRoots     =  []
       , obsRoots     =  []
       }
mctxt0 = nullMatchContext -- handy shorthand


isObsVar mctxt v
 = isRsvV v
   || v `elem` mdlObs mctxt
   || v `elem` srcObs mctxt
   || v `elem` mdlObs' mctxt
   || v `elem` srcObs' mctxt

isPureObsVar mctxt v
 = isPureList v
   || v `elem` mdlObs mctxt
   || v `elem` srcObs mctxt
   || v `elem` mdlObs' mctxt
   || v `elem` srcObs' mctxt

isKnownObsVar mctxt v
 =  v `elem` mdlObs mctxt
 || v `elem` srcObs mctxt
 || v `elem` mdlObs' mctxt
 || v `elem` srcObs' mctxt

getSrcObs Pre  mctxt  =  srcObs  mctxt
getSrcObs Post mctxt  =  srcObs' mctxt
getSrcObs d    mctxt  =  map (decorVar d) $ srcObs mctxt

getMdlObs Pre  mctxt  =  mdlObs  mctxt
getMdlObs Post mctxt  =  mdlObs' mctxt
getMdlObs d    mctxt  =  map (decorVar d) $ mdlObs mctxt

rsvVRoots :: MatchContext -> Variable -> [String]
rsvVRoots mctxt (Rsv r _,_,_) = rsvRoots mctxt r
rsvVRoots _ _ = []

rsvRoots :: MatchContext -> RsvRoot -> [String]
rsvRoots mctxt OBS  = obsRoots mctxt
rsvRoots mctxt MDL  = mdlRoots mctxt
rsvRoots mctxt SCR  = scrRoots mctxt
\end{code}

We can classify variables as being:
\begin{itemize}
  \item standard known ($k$)
  \item standard unknown ($u$)
  \item general list ($\lst x$)
  \item reserved list ($R$)
\end{itemize}
\begin{code}
type ClassedVars
 = ( [Variable]    -- standard known
   , [Variable]    -- standard unknown
   , [Variable]    -- general list
   , [Variable] )  -- reserved list

classifyVars :: (LocalContext -> Variable -> Bool)
             -> LocalContext
             -> [Variable]
             -> ClassedVars
classifyVars _ _ [] = ([],[],[],[])
classifyVars isknown here (v:vs)
 = (k,u,xs,r) `cmrg` (ks,us,xss,rs)
 where
   (ks,us,xss,rs) = classifyVars isknown here vs
   (k,u,xs,r)
      = case v of
          (Gen (Std _),_,_)
             | isknown here v  ->  ([v],[],[],[])
             | otherwise        ->  ([],[v],[],[])
          (Gen (Lst _),_,_)     ->  ([],[],[v],[])
          (Rsv _ _,_,_)         ->  ([],[],[],[v])

(a,b,c,d) `cmrg` (e,f,g,h) = (a++e,b++f,c++g,d++h)
\end{code}

\newpage
\subsubsection{Binding Lookup, knowingly\ldots }

These lookups return the key if not bound and ``known''.
\begin{code}
bevalP :: MatchContext -> Binding -> GenRoot -> Pred
bevalP mctxt (gpbnds,_,_) r
 = case gplookupTO r gpbnds of
    Just pr -> pr
    Nothing ->
     case tslookup (knownPreds mctxt) rs of
      Just _   ->  Pvar r
      Nothing  ->  Pvar $ gmap ('?':) r
 where rs = genRootString r

bevalE :: MatchContext -> Binding -> Variable -> Expr
bevalE mctxt (_,vebnds,_) v
 = case velookupTO v vebnds of
    Just e  -> e
    Nothing ->
     case tslookup (knownObs mctxt) vs of
      Just _  -> Var v
      Nothing ->
       case tslookup (knownExprs mctxt) vs of
        Just _   ->  Var v
        Nothing  ->  Var $ varmap ('?':) v
 where vs = varKey v

bevalT :: MatchContext -> Binding -> TVar -> Type
bevalT mctxt (_,_,ttbnds) tv
 = case ttlookupTO tv ttbnds of
    Just t  -> t
    Nothing ->
     case tslookup (knownTypes mctxt) tv of
      Just _   ->  Tvar tv
      Nothing  ->   Tvar ('?':tv)

bevalQ :: MatchContext -> Binding -> Variable -> QVars
bevalQ _ (_,vebnds,_) v  -- mctxt ignored for now..
 | isStdV v   =  case velookupVO v vebnds of
                   Just v   ->  Q [v]
                   Nothing  ->  Q [varmap ('?':) v]
 | otherwise  =  case velookupVSO v vebnds of
                   Just vs  ->  Q vs
                   Nothing  ->  Q [varmap ('?':) v]

bevalV :: MatchContext -> Binding -> Variable -> Either Variable [Variable]
bevalV mctxt bind v
 | isStdV v
   = case bevalE mctxt bind v of
       Var v   ->  Left v
       Evar v  ->  Left v
       e       ->  Left $ noDecorVariable ('?':show e)
 | otherwise
   = case bevalQ mctxt bind v of
       Q vs  ->  Right vs

bevalES :: MatchContext -> Binding -> Variable -> [Expr]
bevalES mctxt (_,vebnds,_) v  -- mctxt ignored
  | isStdV v  =  [Var $ varmap ('?':) v]
  | otherwise
     = case velookupTSO v vebnds of
        Just es  ->  es
        Nothing  ->  [Var $ varmap ('?':) v]

bevalEE :: MatchContext -> Binding -> Expr -> [Expr]
bevalEE mctxt bind e  -- mctxt effectively ignored
  | isVar e    =  bevalES mctxt bind $ getVar e
  | otherwise  =  [Var $ noDecorVariable ('?':show e)]

bevalVar :: MatchContext -> Binding -> Variable -> Expr
bevalVar mctxt bind@(_,vebnds,_) v  -- mctxt ignored
  = case velookupTO v vebnds of
     Just  e -> e
     Nothing ->
      case velookupVSO v vebnds of
       Just vs -> Var $ varmap ("??"++) v
       Nothing -> Var $ varmap ('?':) v
\end{code}


\newpage
\subsubsection{List-Variable Denotations}

\input{doc/Matching-List-Roots}


\input{doc/Matching-List-Denote}


Function \texttt{lVarDenote}  computes $\sem{L^d\setminus R}_{\Gamma}$,
to the form $V \ominus X$ such that $X$ contains non-observation variables only.
\begin{code}
lVarDenote :: MatchContext -> Variable -> ([Variable],[GenRoot])
lVarDenote mctxt (Rsv root subs,decor,_)
 | root == SCR  =  lVarDenote' obsvars srcvars decor subs
 | root == MDL  =  lVarDenote' obsvars mdlvars decor subs
 | root == OBS  =  lVarDenote' obsvars obsvars decor subs
 where
   srcvars = getSrcObs decor mctxt
   mdlvars = getMdlObs decor mctxt
   obsvars = mdlvars ++ srcvars
lVarDenote _ v = ([v],[])

lVarDenote' :: [Variable]   -- all known observables
            -> [Variable]   -- observable for this meta-root
            -> Decor        -- associated decoration
            -> [GenRoot]    -- non-observable roots being subtracted
            -> ([Variable],[GenRoot])
lVarDenote' ovars dvars decor subs
 =  (denotation,csub)
 where
  denotation = lnorm $ filter keptv dvars
  keptv (Gen r,_,_) = not (r `elem` subs)
  keptv _           = False
  csub = lnorm $ filter kepts subs
  kepts sr = not (Gen sr `elem` oroots)
  oroots = map varRoot ovars
\end{code}

Given a general variable, if a reserved list-variable,
we replace it by its denotation:
\begin{code}
varExpand :: MatchContext -> Variable -> ([Variable],[GenRoot])
varExpand mctxt var
 | isRsvV var  =  ( lnorm vars', lnorm roots' )
 | otherwise      =  ( [var], [] )
 where
   (vars',roots') =  lVarDenote mctxt var

varsExpand :: MatchContext -> [Variable] -> [([Variable],[GenRoot])]
varsExpand mctxt = map $ varExpand mctxt
\end{code}

A useful variant is a table binding variables to their expansion:
\begin{code}
varExpandMaplet :: MatchContext -> Variable -> (String,([Variable],[GenRoot]))
varExpandMaplet mctxt var
 | isRsvV var  =  ( varKey var, varExpand mctxt var )
 | otherwise      =  ( varKey var, ([var],[])          )

varExpandTable :: MatchContext -> [Variable] -> Trie ([Variable],[GenRoot])
varExpandTable mctxt = lbuild . map (varExpandMaplet mctxt)
\end{code}

A useful predicate is one that assesses when the denotation
of a reserved list variable is ``clean'', that is with
out any lingering subtracted roots (not matching an observation variable).
\begin{code}
cleanVar :: MatchContext -> Variable -> Bool
cleanVar mctxt v = null $ snd $ varExpand mctxt v
\end{code}

Sometimes it is useful to convert a list of variables to their
combined denotations:
\begin{code}
varsDenote :: MatchContext -> [Variable] -> ([Variable],[GenRoot])
varsDenote mctxt = vDmerge . map (lVarDenote mctxt)
 where
   vDmerge []  = ([],[])
   vDmerge [d] = d
   vDmerge (d:ds) = d `vDm` vDmerge ds
   (obs1,sub1) `vDm` (obs2,sub2) = (lnorm (obs1++obs2),lnorm(sub1++sub2))
\end{code}

\subsubsection{Reserved Variable ``Size''}

Once we have information that allows us to compute a denotation
for a reserved variable, we can esitmate its ``size'' --- the number
of variable to which it binds.
The estimation aspect arises when the denotation is empty,
or the sutraction lists contains general list variables.
We represent the outcome as a unary relation on numbers,
of the form less than ($\_ < k$), equal to ($\_ = k$) or greater than ($\_ > k$)
some constant $k$:
\begin{code}
varSize :: MatchContext -> Variable -> (Ordering,Int)
varSize _ (Gen (Std _),_,_) = (EQ,1)
varSize _ (Gen (Lst _),_,_) = (GT,-1) -- can be anything from zero upwards...
varSize mctxt (Rsv r subs,decor,_) = rsvSize mctxt r decor subs

rsvSize :: MatchContext -> RsvRoot -> Decor ->  [GenRoot] -> (Ordering,Int)
rsvSize mctxt OBS Post subs  =  subSize (sizeObs' mctxt) subs
rsvSize mctxt OBS _    subs  =  subSize (sizeObs  mctxt) subs
rsvSize mctxt MDL Post subs  =  subSize (sizeMdl' mctxt) subs
rsvSize mctxt MDL _    subs  =  subSize (sizeMdl  mctxt) subs
rsvSize mctxt SCR Post subs  =  subSize (sizeScr' mctxt) subs
rsvSize mctxt SCR _    subs  =  subSize (sizeScr  mctxt) subs

subSize :: Int -> [GenRoot] -> (Ordering,Int)
subSize 0 _         = (GT,-1)
subSize rsize []    = (EQ,rsize)
subSize rsize subs
 | any isLstG subs  =  (LT,rsize+1)
 | otherwise        =  (EQ,max 0 (rsize - length subs))
\end{code}

\newpage
We can give a commutative predicate ($\Bumpeq$) that determines when two relations
are mutually satisfiable.
\begin{eqnarray*}
   \mbox{case} & \mbox{SAT} & \mbox{merge}
\\ (\_ = s) \Bumpeq (\_ = t)  & s=t     &  \_=s
\\ (\_ = s) \Bumpeq (\_ < t)  & s<t     &  \_=s
\\ (\_ = s) \Bumpeq (\_ > t)  & s>t     &  \_=s
\\ (\_ < s) \Bumpeq (\_ < t)  & True    & \_ < min(s,t)
\\ (\_ < s) \Bumpeq (\_ > t)  & s > t+1 & \mbox{not this simple}
\\ (\_ > s) \Bumpeq (\_ > t)  & True    & \_ > max(s,t)
\end{eqnarray*}
\begin{code}
sizeRelSat2 :: (Ordering,Int) -> (Ordering,Int) -> Bool
sizeRelSat2 (EQ,s) (EQ,t)  =  s == t
sizeRelSat2 (EQ,s) (LT,t)  =  s < t
sizeRelSat2 (EQ,s) (GT,t)  =  s > t
sizeRelSat2 (LT,s) (LT,t)  =  True
sizeRelSat2 (LT,s) (GT,t)  =  s > t+1
sizeRelSat2 (GT,s) (GT,t)  =  True
sizeRelSat2 r1     r2      =  sizeRelSat2 r2 r1
\end{code}
Given a list of variables, we might want to determine their sizes.
We can define a notion of ``adding'' size relations together:
\begin{eqnarray*}
   (\_ = s) + (\_ = t)  &\defs&  (\_ = s+t)
\\ (\_ = s) + (\_ < t)  &\defs&  (\_ < s+t)
\\ (\_ = s) + (\_ > t)  &\defs&  (\_ > s+t)
\\ (\_ < s) + (\_ < t)  &\defs&  (\_ < s+t-1)
\\ (\_ < s) + (\_ > t)  &\defs&  (\_ > t)
\\ (\_ > s) + (\_ > t)  &\defs&  (\_ > s+t+1)
\end{eqnarray*}
Note that $(\_=0)$ is a unit for this addition.
\begin{code}
sizeRelAdd :: (Ordering,Int) -> (Ordering,Int) -> (Ordering,Int)
sizeRelAdd (EQ,s) (EQ,t)     =  (EQ,s+t)
sizeRelAdd (EQ,s) (LT,t)     =  (LT,s+t)
sizeRelAdd (EQ,s) (GT,t)     =  (GT,s+t)
sizeRelAdd (LT,s) (LT,t)     =  (LT,s+t-1)
sizeRelAdd (LT,s) r2@(GT,t)  =  r2
sizeRelAdd (GT,s) (GT,t)     =  (GT,s+t+1)
sizeRelAdd r1     r2         =  sizeRelAdd r2 r1
\end{code}


\begin{code}
sizeConformant  :: MatchContext -> String -> [Variable] -> Bool
sizeConformant mctxt s qvs
  = sizeRelSat2 (varSize mctxt $ parseVariable s)
                (foldl sizeRelAdd (EQ,0) $ map (varSize mctxt) qvs)
\end{code}

\newpage
\subsection{Well-formed \texttt{QVars}}


\input{doc/Quantifier-Invariant}

We start with the ``can escape'' relation:
\begin{eqnarray*}
   x \notObsInRSV (V \ominus X)
   &\defs&
   \exists \mu @ x \notin (V \setminus \mu X)
\end{eqnarray*}
Here we wrap a variable and its denotation together,
to keep things consistent with \texttt{possDisjRSV} below.
\begin{code}
obsCanEscapeRSV :: Variable -> (Variable,([Variable],[GenRoot])) -> Bool
obsCanEscapeRSV v (_,(vs,[]))  =  not (v `elem` vs)
obsCanEscapeRSV v _            =  True
\end{code}
and next, the ``possible disjoint'' reserved-variable relation:
\begin{eqnarray*}
   (V_1\ominus X_1) \disjRSV (V_2\ominus X_2)
   &\defs&
   \exists \mu @ (V_1\setminus \mu X_1) \cap (V_2\setminus \mu X_2) = \emptyset
\\ Obs^d \disjRSV Mdl^e &\equiv& d \neq e
\\ Obs^d \disjRSV Scr^e &\equiv& d \neq e
\\ Mdl^d \disjRSV Scr^e &\equiv& \True
\end{eqnarray*}
Here we wrap a variable and its denotation together,
in case that denotation should be empty.
\begin{code}
possDisjRSV :: (Variable,([Variable],[GenRoot]))
            -> (Variable,([Variable],[GenRoot]))
            -> Bool
possDisjRSV ((Rsv r1 [],d1,_),([],[]))
            ((Rsv r2 [],d2,_),([],[]))   =  d1 /= d2 || isDisjRSV r1 r2
possDisjRSV (_,(vs1,[]))  (_,(vs2,[]))   =  vs1 `disjoint` vs2
possDisjRSV (_,(vs1,gs1)) (_,(vs2,gs2))  =  vs1 /= vs2 || gs1 /= gs2

isDisjRSV OBS MDL  =  False
isDisjRSV OBS SCR  =  False
isDisjRSV MDL SCR  =  True
isDisjRSV r1  r2
      | r1 == r2   =  False
      | otherwise  =  isDisjRSV r2 r1
\end{code}

The invariant:
\begin{code}
invQVars :: MatchContext -> QVars -> Bool
invQVars mctxt (Q qvs)
 = sort qvs == lnorm qvs -- fails if any duplicates
   &&
   all (\ v -> all (obsCanEscapeRSV v) rsvs) obs
   &&
   selfpairwise possDisjRSV rsvs
 where
   obs = filter (isKnownObsVar mctxt) qvs
   rsvs = fgraph (varExpand mctxt) $ filter isRsvV qvs
\end{code}
Now, lifting to predicates and expressions:
\begin{code}
predQVarInv :: MatchContext -> Pred -> Bool
exprQVarInv :: MatchContext -> Expr -> Bool

qVarInvFold mctxt = ( (True,predQVarInv mctxt,id,all id )
                    , (True,exprQVarInv mctxt,id,all id) )

predQVarInv mctxt (Forall _ qvs pr) = invQVars mctxt qvs && predQVarInv mctxt pr
predQVarInv mctxt (Exists _ qvs pr) = invQVars mctxt qvs && predQVarInv mctxt pr
predQVarInv mctxt (Exists1 _ qvs pr) = invQVars mctxt qvs && predQVarInv mctxt pr
predQVarInv mctxt (Peabs qvs pr) = invQVars mctxt qvs && predQVarInv mctxt pr

predQVarInv mctxt pr = foldP (qVarInvFold mctxt) pr

exprQVarInv mctxt (Setc _ qvs pr e)
 = invQVars mctxt qvs && predQVarInv mctxt pr && exprQVarInv mctxt e
exprQVarInv mctxt (Seqc _ qvs pr e)
 = invQVars mctxt qvs && predQVarInv mctxt pr && exprQVarInv mctxt e
exprQVarInv mctxt (Eabs _ qvs e) = invQVars mctxt qvs && exprQVarInv mctxt e

exprQVarInv mctxt e = foldE (qVarInvFold mctxt) e
\end{code}


We have code to fix things up:
\begin{code}
fixQVarsInv :: MatchContext -> QVars -> Maybe QVars
fixQVarsInv mctxt (Q qvs) = Just $ lstqnorm mctxt qvs

lstqnorm :: MatchContext -> [Variable] -> QVars
lstqnorm mctxt vs
 = Q $ lnorm vs'
 where
   nvs = lnorm vs
   vs' = filter keep nvs
   keep v = not(v `elem` stripset)
   stripset = concat $ map (fst . lVarDenote mctxt) mvs
   safemvs = filter safe mvs
   safe (Rsv _ rs,_,_)  =  all isStdG rs
   safe _               =  True
   mvs = filter isLstV nvs
\end{code}

We can lift this to \texttt{QVars} and \texttt{Pred} levels:
\begin{code}
lQnorm :: MatchContext -> QVars -> QVars
lQnorm mctxt (Q vs) = lstqnorm mctxt vs

lPQnorm :: MatchContext -> Pred -> Pred
lPQnorm mctxt (Forall tt qvs pr)
 = Forall tt (lQnorm mctxt qvs) (lPQnorm mctxt pr)
lPQnorm mctxt (Exists tt qvs pr)
 = Exists tt (lQnorm mctxt qvs) (lPQnorm mctxt pr)
lPQnorm mctxt (Exists1 tt qvs pr)
 = Exists1 tt (lQnorm mctxt qvs) (lPQnorm mctxt pr)
lPQnorm mctxt pr = mapP (lPQnorm mctxt,lEQnorm mctxt) pr

lEQnorm :: MatchContext -> Expr -> Expr
lEQnorm mctxt (Setc tt qvs pr e)
 = Setc tt (lQnorm mctxt qvs) (lPQnorm mctxt pr) (lEQnorm mctxt e)
lEQnorm mctxt (Seqc tt qvs pr e)
 = Seqc tt (lQnorm mctxt qvs) (lPQnorm mctxt pr) (lEQnorm mctxt e)
lEQnorm mctxt (Eabs tt qvs e)
 = Eabs tt (lQnorm mctxt qvs) (lEQnorm mctxt e)
lEQnorm mctxt e = mapE (lPQnorm mctxt,lEQnorm mctxt) e
\end{code}

\newpage
\subsection{Well-formed \texttt{Substn}}


\input{doc/Substitution-Invariant}

The invariant:
\begin{code}
invESubst :: MatchContext -> ESubst -> Bool
invESubst mctxt (Substn sub)
 = invQVars mctxt (Q $ map fst sub)
   &&
   all listReplList sub
 where
   listReplList ( (Gen (Std _),_,_), _     )  =  True
   listReplList ( (Gen (Lst _),_,_), Var v )  =  isLstV v
   listReplList ( (Rsv _ _,_,_)    , Var v )  =  isLstV v
   listReplList _                             =  False
\end{code}

Lifting to \texttt{Expr} and \texttt{Pred}:
\begin{code}
predESubstInv :: MatchContext -> Pred -> Bool
exprESubstInv :: MatchContext -> Expr -> Bool

eSubInvFold mctxt = ( (True,predESubstInv mctxt,id,all id )
                    , (True,exprESubstInv mctxt,id,all id) )

predESubstInv mctxt (Sub pr subs)
 = predESubstInv mctxt pr && invESubst mctxt subs

predESubstInv mctxt pr = foldP (eSubInvFold mctxt) pr

exprESubstInv mctxt (Esub e subs)
 = exprESubstInv mctxt e && invESubst mctxt subs

exprESubstInv mctxt e = foldE (eSubInvFold mctxt) e
\end{code}

\newpage
\subsection{$\alpha$-equivalence}

\input{doc/Manipulation-Alpha-Equiv-1}


\newpage
\subsubsection{Bijection Code}

We use lists to represent the explicit bijection and sets
\begin{code}
type ExplBij = [(Variable, Variable)]  -- ordered, unique
type ImplBij = ([Variable],[Variable])  -- both ordered, unique
type BIJ = ( ExplBij, ImplBij )

nullbij :: BIJ
nullbij = ([],([],[]))
aok :: Maybe BIJ
aok  = Just nullbij
\end{code}
First, code to merge two explicit bijections:
\begin{code}
ebijGlue :: Monad m => ExplBij -> ExplBij -> m ExplBij
ebijGlue [] bij2  =  return bij2
ebijGlue (xy1:rest1) bij2
 = do bij2' <- ebijIns xy1 bij2
      ebijGlue rest1 bij2'

ebijIns :: Monad m => (Variable, Variable) -> ExplBij -> m ExplBij
ebijIns xy [] = return [xy]
ebijIns xy1@(x1,y1) bij2@(xy2@(x2,y2):rest2)
 | x1 <  x2
   = if y1 == y2 then fail "explicit BIJ: L out, R in" else return (xy1:bij2)
 | x1 == x2
   = if y1 == y2 then return bij2 else fail "explicit BIJ: L in, R out"
 | otherwise -- x1 > x2
   = if y1 == y2 then fail "explicit BIJ:  L out, R in"
                 else do rest' <- ebijIns xy1 rest2
                         return (xy2:rest')
\end{code}
Next, code to merge implicit bijections:
\begin{code}
ibijGlue :: Monad m => ImplBij -> ImplBij -> m ImplBij
ibijGlue ([],[]) bij2   =  return bij2
ibijGlue ((x:xs),(y:ys)) bij2
 = do bij2' <- ibijIns x y bij2
      ibijGlue (xs,ys) bij2'
ibijGlue _ _  =  fail "implicit BIJ: diff. len."

ibijIns :: Monad m => Variable -> Variable -> ImplBij -> m ImplBij
ibijIns x y (xs,ys)
 | xsgrew == ysgrew  =  return (xs',ys')
 | otherwise         =  fail "implicit BIJ: diff. len."
 where
   (xsgrew,xs') = ins x xs
   (ysgrew,ys') = ins y ys
   ins x0 [] = (True,[x0])
   ins x0 xs@(x:rest)
    | x0 <  x    =  (True,x0:xs)
    | x0 == x    =  (False,xs)
    | otherwise  =  (grew,x:rest')
    where
      (grew,rest') = ins x0 rest
\end{code}
\newpage
Finally, code to glue our \texttt{BIJ}ections together:
\begin{code}
bijglue :: Monad m => BIJ -> BIJ -> m BIJ
bijglue (ebij1,(l1,r1)) (ebij2,(l2,r2))
 = do ebij' <- ebij1 `ebijGlue` ebij2   -- fail early !
      let (dom1,rng1) = unzip ebij1
      let (dom2,rng2) = unzip ebij2
      let l1' = l1 \\ dom2
      let r1' = r1 \\ rng2
      let l2' = l2 \\ dom1
      let r2' = r2 \\ rng1
      ibij' <- (l1',r1') `ibijGlue` (l2',r2')
      return (ebij',ibij')
\end{code}


\newpage
\input{doc/Manipulation-Alpha-Equiv-2}


\newpage
\subsubsection{$\alpha$-Equivalence Code}

First, some boilerplate --- processing lists of equivalences:
\begin{code}
alflist :: (([Variable],[Variable]) -> a -> a -> Maybe BIJ)
        -> ([Variable],[Variable])
        -> [a] -> [a]
        -> Maybe BIJ
alflist eqv bvs [] [] = aok
alflist eqv bvs (a1:as1) (a2:as2)
 = do bnd <- eqv bvs a1 a2
      bnds <- alflist eqv bvs as1 as2
      bnd `bijglue` bnds
alflist _ _ _ _ = Nothing
\end{code}

We need a form of bijection restriction:
\ALFMAPRESTRICT
\begin{code}
alwres :: Monad m => ([Variable],[Variable]) -> BIJ -> m BIJ
alwres (b1,b2) (explbij,(implbijL,implbijR))
 = do let implbijL' = implbijL \\ b1
      let implbijR' = implbijR \\ b2
      if length implbijL' /= length implbijR'
       then fail "implicit bij sizes differ"
       else do explbij' <- alwres' explbij
               return (explbij',(implbijL',implbijR'))
 where
   alwres' [] = return []
   alwres' (hd@(l,r):rest)
     | l `elem` b1
        = if r `elem` b2
           then alwres' rest               -- both in, so drop
           else fail "Left in, Right not"  -- l in, r not, so fail
     | otherwise
        = if r `elem` b2
           then fail "Right in, Left not"  -- r in, l not, so fail
           else do rest' <- alwres' rest   -- both out , keep
                   return (hd:rest')
\end{code}


\begin{eqnarray*}
   x_1 \balfeqv{B_1 \cup \setof{x_1}}{B_2\cup\setof{x_2}} x_2
   &\defs& \mapof{x_1 \to x_2}
\\ x \balfeqv{B_1 \setminus \setof{x}}{B_2 \setminus\setof{x}} x
   &\defs& \mapof{}
\end{eqnarray*}
\begin{code}
valfequiv :: ([Variable],[Variable]) -> Variable -> Variable -> Maybe BIJ
valfequiv (bvs1,bvs2) v1 v2
 | bound1 && bound2  =  Just ([(v1,v2)],([],[]))
 | bound1            =  Nothing
 | bound2            =  Nothing
 | v1 == v2          =  aok      -- no binding for free vars.
 | otherwise         =  Nothing
 where
   bound1 = v1 `elem` bvs1
   bound2 = v2 `elem` bvs2
\end{code}

\newpage
Predicate $\alpha$-equivalence:
\begin{code}
predAlphaEqv :: Pred -> Pred -> Bool
predAlphaEqv (Pfocus pr1) pr2 = predAlphaEqv pr1 pr2
predAlphaEqv pr1 (Pfocus pr2) = predAlphaEqv pr1 pr2
predAlphaEqv pr1 pr2 = isJust $ palfequiv ([],[]) pr1 pr2

palfequiv :: ([Variable],[Variable]) -> Pred -> Pred -> Maybe BIJ
\end{code}

\begin{eqnarray*}
   \alfFreeMVarL &\defs& \alfFreeMVarR
\end{eqnarray*}
\begin{code}
palfequiv bvs (Pvar s1) (Pvar s2) | s1==s2  = aok
\end{code}
\begin{eqnarray*}
   \alfCompL &\defs& \alfCompR
\end{eqnarray*}
\begin{code}
palfequiv bvs TRUE TRUE = aok
palfequiv bvs FALSE FALSE = aok
palfequiv bvs (Obs e1) (Obs e2)   =  ealfequiv bvs e1 e2
palfequiv bvs (Defd e1) (Defd e2)   =  ealfequiv bvs e1 e2
palfequiv bvs (TypeOf e1 t1) (TypeOf e2 t2)
 | t1 `tlequiv` t2  = ealfequiv bvs e1 e2
palfequiv bvs (Not pr1) (Not pr2) = palfequiv bvs pr1 pr2
palfequiv bvs (And prs1) (And prs2) = alflist palfequiv bvs prs1 prs2
palfequiv bvs (Or prs1) (Or prs2) = alflist palfequiv bvs prs1 prs2
palfequiv bvs (NDC pr11 pr21) (NDC pr12 pr22)
                                = alflist palfequiv bvs [pr11,pr21] [pr12,pr22]
palfequiv bvs (Imp pr11 pr21) (Imp pr12 pr22)
                                = alflist palfequiv bvs [pr11,pr21] [pr12,pr22]
palfequiv bvs (RfdBy pr11 pr21) (RfdBy pr12 pr22)
                                = alflist palfequiv bvs [pr11,pr21] [pr12,pr22]
palfequiv bvs (Eqv pr11 pr21) (Eqv pr12 pr22)
                                = alflist palfequiv bvs [pr11,pr21] [pr12,pr22]
palfequiv bvs (If prc1 prt1 pre1) (If prc2 prt2 pre2)
                      = alflist palfequiv bvs [prc1,prt1,pre1] [prc2,prt2,pre2]
palfequiv bvs (Univ _ pr1) (Univ _ pr2) = palfequiv bvs pr1 pr2
palfequiv bvs (Peabs s1 pr1) (Peabs s2 pr2) | s1==s2  =  palfequiv bvs pr1 pr2
palfequiv bvs (Ppabs s1 pr1) (Ppabs s2 pr2) | s1==s2  =  palfequiv bvs pr1 pr2
palfequiv bvs (Papp prf1 pra1) (Papp prf2 pra2)
                                = alflist palfequiv bvs [prf1,pra1] [prf2,pra2]
palfequiv bvs (Lang n1 _ lelems1 syn1) (Lang n2 _ lelems2 syn2)
 | n1 == n2 && syn1 == syn2
   =  alflist lalfequiv bvs lelems1 lelems2
\end{code}
\newpage
\begin{eqnarray*}
   (\exists x_1 @ P_1) \balfeqv{B_1}{B_2} (\exists x_2 @ P_2)
   &\defs&
   (P_1 \balfeqv{B_1 \cup \setof{x_1}}{B_2\cup\setof{x_2}} P_2)
   |_{(B_1 \cup B_2)}
\end{eqnarray*}
\begin{code}
palfequiv bvs (Forall _ (Q qs1) pr1) (Forall _ (Q qs2) pr2)
 = qalfequiv bvs ([pr1],qs1) ([pr2],qs2)

palfequiv bvs (Exists _ (Q qs1) pr1) (Exists _ (Q qs2) pr2)
 = qalfequiv bvs ([pr1],qs1) ([pr2],qs2)

palfequiv bvs (Exists1 _ (Q qs1) pr1) (Exists1 _ (Q qs2) pr2)
 = qalfequiv bvs ([pr1],qs1) ([pr2],qs2)
\end{code}
\begin{eqnarray*}
   \alfSubL &\defs& \alfSubR
\end{eqnarray*}
\begin{code}
palfequiv bvs (Sub pr1 (Substn sub1))
              (Sub pr2 (Substn sub2))
                = salfequiv bvs palfequiv id ealfequiv (pr1, sub1) (pr2, sub2)

palfequiv bvs (Psub pr1 (Substn sub1))
              (Psub pr2 (Substn sub2))
      = salfequiv bvs palfequiv genRootAsVar palfequiv (pr1, sub1) (pr2, sub2)
\end{code}
Leftover stuff
\begin{code}
palfequiv bvs (Pfocus pr1) (Pfocus pr2) = palfequiv bvs pr1 pr2
palfequiv bvs (Pfocus pr1) pr2          = palfequiv bvs pr1 pr2
palfequiv bvs pr1 (Pfocus pr2)          = palfequiv bvs pr1 pr2

palfequiv _ _ _ = Nothing
\end{code}

Quantifier equivalence
\begin{eqnarray*}
   \alfQuantL &\defs& \alfQuantR
\end{eqnarray*}
\begin{code}
qalfequiv :: ([Variable],[Variable])
          -> ([Pred],[Variable])
          -> ([Pred],[Variable])
          -> Maybe BIJ
qalfequiv (bvs1,bvs2) (prs1,qs1) (prs2,qs2)
 | length sq1 /= length sq2  =  fail ""
 | length mq1 /= length mq2  =  fail ""
 | otherwise
 = do let bvs' = (bvs1 `bvext` qs1,bvs2 `bvext` qs2)
      prbij <- alflist palfequiv bvs' prs1 prs2
      qsbij <- (sq1,sq2) `ibijGlue` (mq1,mq2)
      bij' <- prbij `bijglue` ([],qsbij)
      alwres (bvs1,bvs2) bij'
 where
  (sq1,mq1) = vPartition qs1
  (sq2,mq2) = vPartition qs2
  bvs `bvext` vs = lnorm (vs++bvs)
  ubvs = lnorm (bvs1++bvs2)
\end{code}

Substitution equivalence
\begin{code}
salfequiv bvs beqv asVar reqv (body1, sub1) (body2, sub2)
 = do prbij  <- beqv bvs body1 body1
      tgtbij <- alflist valfequiv bvs (map asVar spv1) (map asVar spv2)
      repbij <- alflist reqv bvs srp1 srp2
      subbij <- tgtbij `bijglue` repbij
      prbij `bijglue` subbij
 where
   (spv1,srp1) = unzip sub1
   (spv2,srp2) = unzip sub2
\end{code}

\newpage
Now expressions:
\begin{code}
exprAlphaEqv (Efocus e1) e2 = exprAlphaEqv e1 e2
exprAlphaEqv e1 (Efocus e2) = exprAlphaEqv e1 e2
exprAlphaEqv e1 e2
 = case ealfequiv ([],[]) e1 e2 of
    Nothing  ->  False
    Just _   ->  True

ealfequiv :: ([Variable],[Variable]) -> Expr -> Expr -> Maybe BIJ

ealfequiv bvs (Efocus e1) e2 = ealfequiv bvs e1 e2
ealfequiv bvs e1 (Efocus e2) = ealfequiv bvs e1 e2

ealfequiv bvs T T = aok
ealfequiv bvs F F = aok
ealfequiv bvs (Num i1) (Num i2) | i1==i2  = aok
\end{code}
\begin{eqnarray*}
   x_1 \balfeqv{B_1 \cup \setof{x_1}}{B_2\cup\setof{x_2}} x_2
   &\defs& \mapof{x_1 \to x_2}
\\ x \balfeqv{B_1 \setminus \setof{x}}{B_2 \setminus\setof{x}} x
   &\defs& \mapof{}
\end{eqnarray*}
\begin{code}
ealfequiv bvs (Var s1) (Var s2) = valfequiv bvs s1 s2
\end{code}
\begin{eqnarray*}
   M \balfeqv{B_1}{B_2} M &\defs& \mapof{}
\\ M \balfeqv{B_1}{B_2\setminus \setof x} x &\defs& \mapof{}, \quad \IF~x=M
\end{eqnarray*}
\begin{code}
ealfequiv bvs (Evar s1) (Evar s2)      | s1==s2                       =  aok
ealfequiv (_,bvs2) (Evar s1) (Var s2)  | s1==s2 && s2 `notElem` bvs2  =  aok
ealfequiv (bvs1,_) (Var s1)  (Evar s2) | s1==s2 && s1 `notElem` bvs1  =  aok
\end{code}
\begin{eqnarray*}
   (P_1 \land Q_1) \balfeqv{B_1}{B_2} (P_2 \land Q_2)
   &\defs&
   (P_1 \balfeqv{B_1}{B_2} P_2)
   \uplus
   (Q_1 \balfeqv{B_1}{B_2} Q_2)
\end{eqnarray*}
\begin{code}
ealfequiv bvs (Prod es1) (Prod es2) = alflist ealfequiv bvs es1 es2
ealfequiv bvs (App s1 e1) (App s2 e2) | s1==s2 = ealfequiv bvs e1 e2
ealfequiv bvs (Bin s1 _ e11 e21) (Bin s2 _ e12 e22)
 | s1==s2 =  alflist ealfequiv bvs [e11,e21] [e12,e22]
ealfequiv bvs (Equal e11 e21) (Equal e12 e22) = alflist ealfequiv bvs [e11,e21] [e12,e22]
ealfequiv bvs (Set es1) (Set es2) = alflist ealfequiv bvs es1 es2
ealfequiv bvs (Seq es1) (Seq es2) = alflist ealfequiv bvs es1 es2
\end{code}

\newpage
\begin{eqnarray*}
   (\exists x_1 @ P_1) \balfeqv{B_1}{B_2} (\exists x_2 @ P_2)
   &\defs&
   (P_1 \balfeqv{B_1 \cup \setof{x_1}}{B_2\cup\setof{x_2}} P_2)
   |_{(B_1 \cup B_2)}
\end{eqnarray*}
\begin{code}
ealfequiv bvs (Setc _ (Q qs1) pr1 e1) (Setc _ (Q qs2) pr2 e2)
                         = qalfequiv bvs ([pr1,Obs e1],qs1) ([pr2,Obs e2],qs2)
ealfequiv bvs (Seqc _ (Q qs1) pr1 e1) (Seqc _ (Q qs2) pr2 e2)
                         = qalfequiv bvs ([pr1,Obs e1],qs1) ([pr2,Obs e2],qs2)
ealfequiv bvs (The _ x1 pr1) (The _ x2 pr2)
                                     = qalfequiv bvs ([pr1],[x1]) ([pr2],[x2])
ealfequiv bvs (Eabs _ (Q qs1) e1) (Eabs _ (Q qs2) e2)
                                 = qalfequiv bvs ([Obs e1],qs1) ([Obs e2],qs2)

ealfequiv bvs (Map drs1) (Map drs2)
 = alflist ealfequiv bvs (ds1++rs1) (ds2++rs2)
 where
  (ds1,rs1) = unzip drs1
  (ds2,rs2) = unzip drs2

ealfequiv bvs (Cond pc1 et1 ee1) (Cond pc2 et2 ee2)
 = do cbnds <- palfequiv bvs pc1 pc2
      ebnds <- alflist ealfequiv bvs [et1,ee1] [et2,ee2]
      bijglue cbnds ebnds

ealfequiv bvs (Build s1 es1) (Build s2 es2)
  | s1==s2  =  alflist ealfequiv bvs es1 es2
\end{code}
\begin{eqnarray*}
   \alfSubL &\defs& \alfSubL
\end{eqnarray*}
\begin{code}
ealfequiv bvs (Esub e1 (Substn sub1))
              (Esub e2 (Substn sub2))
                  = salfequiv bvs ealfequiv id ealfequiv (e1, sub1) (e2, sub2)

ealfequiv bvs _ _ = Nothing
\end{code}

And for language constructs,
we ignore the bound variables,
as all variables in here are script variables
\begin{code}
lalfequiv :: ([Variable],[Variable]) -> LElem -> LElem -> Maybe BIJ

lalfequiv bvs (LVar s1)   (LVar s2)  | s1 == s2         =  aok
lalfequiv bvs (LType t1)  (LType t2) | t1 `tlequiv` t2  =  aok
lalfequiv bvs (LExpr e1)  (LExpr e2)   =  ealfequiv ([],[]) e1 e2
lalfequiv bvs (LPred pr1) (LPred pr2)  =  palfequiv ([],[]) pr1 pr2
lalfequiv bvs (LList l1)  (LList l2)   =  alflist lalfequiv ([],[]) l1 l2
lalfequiv bvs (LCount l1) (LCount l2)  =  alflist lalfequiv ([],[]) l1 l2
lalfequiv _   _           _            =  Nothing
\end{code}
