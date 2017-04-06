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
lookup the type of a variable w.r.t. those,
returning \texttt{Tarb} if nothing found.
This facilitates early matching before types have been inferred.
\begin{code}
mttsLookup :: TypeTables -> Variable -> [TTTag] -> Type
mttsLookup tts v [] = Tarb
mttsLookup tts v (tag:tags)
 = case btlookup tts tag of
     Nothing  ->  Tarb
     Just vtyps
       -> case tvlookup vtyps v of
            Just t   ->  t
            Nothing  ->  mttsLookup tts v tags
\end{code}



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

   typof (Num i)  =  Z
   typof (Var v)  =  ttsVLookup tts v tags
   typof (App n es)
     = case ttsLookup tts n tags of
        Tfun _ tr  ->  tr
        t          ->  Terror (n++" not a function") t
   typof (Abs n tag qvs e)  =  undefined -- evalExprType tts (tag:tags) e
   typof (ESub e esub)  =  typof e
   typof (EPred _) = B
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
tlequiv (Tfun d r) (Tfun d' r')  =  tslequiv [d,r] [d',r']
tlequiv (TApp n ts) (TApp n' ts') =  n==n' && tslequiv ts ts'
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

We expect the collection of sub-bindings of a successful match
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
         is an ordinary occurrence in some expression,
         e.g. $x$ in $x+3$ or $P$ in $P \land \True$.
         If not in the scope of an outer quantifier, these can match
         expressions and predicates respectively.
         If bound, they can only match variables of the same kind.
      \item[Quantifier-List]
         is an occurrence in a quantifier list of variables,
         e.g. $y$ in $\exists y @ \ldots$ or $Q$ in $\forall Q @ \ldots$.
         These can only match other variables of the same kind.
      \item[Substitution-Target]
         is an occurrence in a substitution
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
         is an occurrence as a target variable
         in a substitution, e.g. $\lst b$ in $[\lst e/\lst b]$.
         These can only match lists of variables of the same kind.
      \item[Substitution-Replacement]
         is an occurrence as a replacement expression variable
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
  Variable $\fun$ Pred
  & Std (Regular, not bound)
  \\\hline
  Variable $\fun$ Variable
  & Std (Regular, bound; Quantifier-List; Substitution-Target)
  \\\hline
  Variable $\fun$ Variable
  & Std (Regular, bound; Quantifier-List; Substitution-Target)
  \\\hline
  Variable $\fun$ Variable${}^*$
  & Lst (Quantifier-List; Substitution-Target)
  \\\hline
  Variable $\fun$ Variable${}^*$
  & Lst (Quantifier-List; Substitution-Target)
  \\\hline
  Variable $\fun$ Expr${}^*$
  & Lst (Substitution-Replacement; 2-Place Predicates)
  \\\hline
  Variable $\fun$ Pred${}^*$
  & Lst (Substitution-Replacement; 2-Place Predicates)
  \\\hline
\end{tabular}


\subsubsection{Binding Types}
We see a pattern emerging, given a variable type $Var$
and an term type $Trm$, we get the following four bindings:
\begin{eqnarray*}
   Var|_{Std} &\fun& Trm
\\ Var|_{Std} &\fun& Var
\\ Var|_{Lst} &\fun& Var^*
\\ Var|_{Lst} &\fun& Trm^*
\end{eqnarray*}
We shall implement the above four lookup functions
as a single \texttt{Trie}, which simplifies the enforcing of the
rule regarding exactly one binding per ``variable name''.
\[ Var \fun (Trm + Var + Var^* + Trm^*)\]
It also encapsulates the \textbf{Std} vs \textbf{Lst} distinction.

A binding object represents the sum type $Trm + Var + Var^* + Trm^*$:
\begin{code}
data BObj var trm
 = TO trm       -- Std, Regular not bound
 | VO var       -- Std, Irregular
 | VSO [var]    -- Lst, Quantifier, Subst-Target
 | TSO [trm]    -- Lst, Subst-Replace, 2-Place
 deriving (Eq,Ord)

showBObj :: (var -> String, trm -> String) -> BObj var trm -> String
showBObj (shwv, shwt) (TO t)  =  shwt t
showBObj (shwv, shwt) (VO v)  =  shwv v
showBObj (shwv, shwt) (VSO [])  = "."
showBObj (shwv, shwt) (VSO vs)  = concat $ intersperse "," $ map shwv vs
showBObj (shwv, shwt) (TSO [])  = "."
showBObj (shwv, shwt) (TSO ts)  = concat $ intersperse "," $ map shwt ts

instance (Show var, Show trm) => Show (BObj var trm) where
  show = showBObj (show, show)
\end{code}
We define a sub-binding as:
\begin{code}
type SBind var trm = Trie (BObj var trm)

sbnil :: SBind var trm
sbnil = tnil

-- explicitly show tagging of object types
oShow :: (var -> String, trm -> String) -> SBind var trm -> String
oShow (vshw, tshw) = unlines . map oshow . flattenTrie
 where
   oshow (str,obj) = str ++ " >-> " ++ oshow' obj
   oshow' (TO trm)   = "Trm  " ++ tshw trm
   oshow' (VO var)   = "Var  " ++ vshw var
   oshow' (VSO vars) = "Var$ " ++ show (map vshw vars)
   oshow' (TSO trms) = "Trm$ " ++ show (map tshw trms)
\end{code}


\newpage
\subsubsection{Binding Update and Lookup}


The \texttt{BObj var trm} type involves a linkage between variables ($Var$)
and some term of interest ($Trm$,
usually one of \texttt{Pred}, \texttt{Expr} or \texttt{Type}).
We also assume the existence of a total injective function $vinj : Var|_{Std} \fun Trm$
that embeds a \emph{standard} variable in an term of the relevant type,
and a partial projection function $vproj : Trm \pfun Var$ whose domain of definition
is precisely the image of $vinj$.

The idea is to view $Var|_{Std}$ as ``lower'' than $Trm$
(think of $vinj$ as a sub-object embedding).
The plan is always to record a range item at the lowest possible level:
\begin{eqnarray*}
   updVO &:& Var \fun Var \fun (SBind~Var~Trm) \fun \mathbf{1}+(SBind~Var~Trm)
\\ updVO~k~v~\beta &\defs& \beta\uplus\maplet k {VO~v}
\\
\\ updTO &:& Var \fun Trm \fun (SBind~Var~Trm) \fun \mathbf{1}+(SBind~Var~Trm)
\\ updTO~k~t~\beta
   &\defs&
   \left\{
     \begin{array}{ll}
        updVO~k~(vproj~t)~\beta,     &  t \in vinj(Var|_{Std})
     \\ \beta\uplus\maplet k {TO~t}, & \hbox{otherwise}
     \end{array}
   \right.
\end{eqnarray*}
Here $\uplus$ denotes an update that fails if the new entry conflicts
with an existing one.

Lookup expecting a $Var$ result succeeds only if a $VO$ object is found,
while those expecting a $Trm$ result will accept a $TO$ result,
but also use $vinj$ if a $VO$ result is found.

However, for  $VSO$ and $TSO$, we do not use $vinj$ or $vproj$ in this way.


\paragraph{$VO$ update and lookup}~

\begin{code}
updateVO :: (Monad m, Eq var, Eq trm)
         => String -> var -> SBind var trm -> m (SBind var trm)
updateVO key v sbind
 | isStdS key  =  m2m $ mtenter same key (VO v) sbind
 | otherwise   =  nowt

lookupVO :: (Monad m, Eq var, Eq trm) => String -> SBind var trm -> m var
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
 | otherwise       =  m2m $ mtenter same key (TSO ts) sbind

lookupTSO :: (Monad m, Eq v, Eq t)
           => (v -> t) -> String -> SBind v t -> m [t]
lookupTSO vinj key sbind
  = case tlookup sbind key of
      Just (TSO ts)  ->  return ts
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
type VPBind = SBind ListVar Pred
showVPObj = showBObj (varKey, show)
showVPBind  :: VPBind -> String
showVPBind = unlines' . trieShowWith showVPObj
vpInj :: ListVar -> Pred
vpInj (V v) = PVar v
vpInj (L (nm,_,_) _) = vinjErr nm
vpProj :: Pred -> Maybe ListVar
vpProj (PVar v)  =  Just $ V v
vpProj _         =  Nothing

vinjErr nm =  error ("vpInj/veInj not defined for list-variable : "++nm)

type VEBind = SBind ListVar Expr
showVEObj = showBObj (varKey, show)
showVEBind :: VEBind -> String
showVEBind = unlines' . trieShowWith showVEObj
veInj :: ListVar -> Expr
veInj (V v) = Var v
veInj (L (nm,_,_) _) = vinjErr nm
veProj :: Expr -> Maybe ListVar
veProj (Var v)    =  Just $ V v
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
type Binding = (VPBind, VEBind, TTBind)

nullBinds :: Binding
nullBinds = (tnil,tnil,tnil)

showBinding :: Binding -> [String]
showBinding (vpbnds,vebnds,ttbnds)
 = let
     (vpkeysize,vppairs) = flattenTrieD vpbnds
     (vekeysize,vepairs) = flattenTrieD vebnds
     (ttkeysize,ttpairs) = flattenTrieD ttbnds
     keywidth = maximum [vpkeysize,vekeysize,ttkeysize]
     vpShown = bshow keywidth vppairs
     veShown = bshow keywidth vepairs
     ttShown = bshow keywidth ttpairs
   in concat [vpShown,veShown,ttShown]
 where
   bshow _ [] = []
   bshow w pairs = showFlatTrieWith show "" (w,pairs)
\end{code}


\paragraph{Specialising for \texttt{Name}, \texttt{Pred}}~

\begin{code}
vpupdateTO :: Monad m => Name -> Pred -> VPBind -> m VPBind
vpupdateTO nm = updateTO vpProj (varStringRoot nm)

vplookupTO :: Monad m => Name -> VPBind -> m Pred
vplookupTO nm = lookupTO PVar (varStringRoot nm)

vpupdateVO :: Monad m => Name -> Name -> VPBind -> m VPBind
vpupdateVO nm = updateVO (varStringRoot nm)

vplookupVO :: Monad m => Name -> VPBind -> m Name
vplookupVO nm = lookupVO (varStringRoot nm)

vpupdateVSO :: Monad m => Name -> [Name] -> VPBind -> m VPBind
vpupdateVSO nm = updateVSO (varStringRoot nm)

vplookupVSO :: Monad m => Name -> VPBind -> m [Name]
vplookupVSO nm = lookupVSO (varStringRoot nm)

vplookupTSO :: Monad m => Name -> VPBind -> m [Pred]
vplookupTSO nm = lookupTSO PVar (varStringRoot nm)

vpupdateTSO :: Monad m => Name -> [Pred] -> VPBind -> m VPBind
vpupdateTSO nm  = updateTSO vpProj (varStringRoot nm)
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

\newpage
\subsubsection{Binding Injections}

Basic injections, starting with a safe way to get a sub-binding:
\begin{code}
mkSubBind :: Maybe (SBind v t) -> SBind v t
mkSubBind (Just sbind) = sbind
mkSubBind Nothing      = sbnil

bindP :: Name -> Pred -> Binding
bindP r pr = ( mkSubBind $ vpupdateTO r pr sbnil, tnil, tnil )
bindE :: Variable -> Expr -> Binding
bindE v e = ( tnil, mkSubBind $ veupdateTO v e sbnil, tnil )

bindT :: TVar -> Type -> Binding
bindT tv t = ( tnil, tnil, mkSubBind $ ttupdateTO tv t sbnil )

bindV :: Variable -> Variable -> Binding
bindV v vv = ( tnil, mkSubBind $ veupdateVO v vv sbnil, tnil )

bindQL :: ListVar -> VarList -> Binding
bindQL lv vs = ( tnil, sBindQL lv vs, tnil )

sBindQL lv vs = mkSubBind $ veupdateVSO lv vs sbnil
\end{code}

Putting a variable/variable-list binding into the right place,
if possible:
\begin{code}
bindVL :: ListVar -> VarList -> Binding
bindVL (V v) [(V x)]  =  bindV v x
bindVL lv xs          =  bindQL lv xs
\end{code}

\newpage
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
genObsSubscriptMap :: [Name] -- undecorated observable roots
                   -> String   -- from subscript
                   -> String   -- to subscript
                   -> VEBind
genObsSubscriptMap roots froms tos
 = lbuild (rsvMap ++ map (mkTo froms tos) roots)
 where

   rsvMap = [ ( strOBS ++ sFrom, VSO $ [mkRVar strOBS [] sTo] )
            , ( strMDL ++ sFrom, VSO $ [mkRVar strMDL [] sTo] )
            , ( strSCR ++ sFrom, VSO $ [mkRVar strSCR [] sTo] ) ]

   mkTo froms tos root = ( root++sFrom, VO (mkSVar root sTo ) )

   sFrom = chrSUBS:froms
   sTo = VInter tos
\end{code}

\begin{code}
mergeMR :: Monad m => MatchResult -> MatchResult -> m MatchResult
(bnds1,qvm1,sbm1) `mergeMR` (bnds2,qvm2,sbm2)
  = do bnds' <- bnds1 `mrgB` bnds2
       return (bnds', lnorm (qvm1++qvm2), lnorm (sbm1++sbm2))
\end{code}

\newpage
Another case we must consider is where we have matched pattern $R\less{x}$
against $R\less{y}$. In addition to the obvious binding $\maplet{R\less{x}}{R\less{y}}$,
we also need to add the binding $\maplet x y$, except if $x$ is known and equal to $y$.
This prevents $x$ matching anything else elsewhere.

We now supply a function that takes two reserved variables: one the pattern,
the other the test, and produces all such extra bindings.
If there is more than one possible such binding then a deferred match is returned.
\begin{code}
genRsvLessMap :: [Name] -- undecorated observable roots
              -> ListVar -- pattern reserved variable
              -> ListVar -- test reserved variable
              -> MatchResult

genRsvLessMap roots (L (_, _, _) pless) (L (_ , _, _) tless)
 = case (pstrs, tstrs) of
     ([pstr], [tstr]) | isLstN pstr
       -> ( bindVL (var pstr) (var tstr)
          , [], [] )
     ([pstr], _) | isLstN pstr
       -> ( bindVL (lvar pstr) (map var tstrs)
          , [], [] )
     _ -> ( nullBinds
          , [ (map var pstrs, map var tstrs) ]
          , [])
 where
   pstrs = pless \\ roots
   tstrs = tless -- \\ roots
   var nm
    | isLstN nm  =  L (nm, VObs, VPre) []
    | otherwise  =  V (nm, VObs, VPre)
   lvar nm = L (nm, VObs, VPre) []

genRsvLessMap roots prv trv = noBinding
\end{code}

Now functions to bind taking account the above considerations:
\begin{code}
bindO :: Monad m => [Name] -> Variable -> Variable -> m MatchResult
bindO roots p@(pr, _, pd@(VInter ps)) m@(_, _,md@(VInter ms))
 | isObsVarRelated roots pr
 = ( bindV p m `lmrgJB` ( tnil, genObsSubscriptMap roots ps ms, tnil )
   , [], [] )
   `mergeMR` genRsvLessMap roots p m
bindO roots rp rt
 = ( bindV rp rt, [], [] ) `mergeMR` (genRsvLessMap roots rp rt)

isObsVarRelated :: [Name] -> Name -> Bool
isObsVarRelated roots root
 | isRsv root  =  True
 | otherwise   =  root `elem` roots
isObsVarRelated _ _ =  False
\end{code}

When binding to observation-related variable lists,
we want to ensure all subscripts are the same
\begin{code}
bindOL :: Monad m => [Name] -> Variable -> [Variable] -> m Binding

bindOL roots p@(pr,_,VInter ps) mvs
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
   getSubs (_,_,VInter s) = [s]
   getSubs _              = []

sameSubscripts :: [Variable] -> Bool
sameSubscripts [] = True
sameSubscripts ((_,_,VInter s):rest)
 = same s rest
 where
   same s [] = True
   same s ((_,_,VInter t):rest) = s==t && same s rest
   same s (_:rest) = same s rest
sameSubscripts (_:rest) = sameSubscripts rest


lmergeObs :: VEBind -> VEBind -> Maybe VEBind
lmergeObs = mergeSBind lmergeVE lmergeBObj

lmrgObs :: Binding -> Binding -> Maybe Binding
(vp1,ev1,tt1) `lmrgObs` (vp2,ev2,tt2)
  = do vp' <- vp1 `lmergeSBind` vp2
       ev' <- ev1 `lmergeObs` ev2
       tt' <- tt1 `lmergeSBind` tt2
       return (vp',ev',tt')
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
(vp1,ev1,tt1) `mrgB` (vp2,ev2,tt2)
  = do vp' <- vp1 `tglue` vp2
       ev' <- ev1 `tglue` ev2
       tt' <- tt1 `tglue` tt2
       return (vp',ev',tt')

mrgMB :: Monad m => m Binding -> m Binding -> m Binding
mrgMB mb1 mb2
 = do b1 <- mb1
      b2 <- mb2
      b1 `mrgB` b2
\end{code}

We also have variants that fuse lists in VSO/TSO bindings:
\begin{code}
lmrgB :: Binding -> Binding -> Maybe Binding
(vp1,ev1,tt1) `lmrgB` (vp2,ev2,tt2)
  = do vp' <- vp1 `lmergeSBind` vp2
       ev' <- ev1 `lmergeSBind` ev2
       tt' <- tt1 `lmergeSBind` tt2
       return (vp',ev',tt')

lmrgJB :: Binding -> Binding -> Binding
bnd1 `lmrgJB` bnd2
 = case bnd1 `lmrgB` bnd2 of
     Nothing    ->  (tnil, tnil, tnil)
     Just bnd'  ->  bnd'
\end{code}

\newpage
\subsubsection{Deferred Matching}

Some matches, to do with variable lists (usually in binders),
have to be deferred for
post-processing that requires free-variable information,
as well using side-conditions as hints.
\begin{code}
type QVarMatchToDo = (VarList,VarList) -- (test,pattern)
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
isWFQVarToDo :: VarList -> VarList -> Bool
isWFQVarToDo tvs pvs
 | n <  k            =  False
 | n == k && m == 0  =  True
 | otherwise         =  ell > 0
 where
  (n,m) = setboth (length,length) (partition isStdLV tvs)
  (k,ell) = setboth (length,length) (partition isStdLV pvs)
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
\texttt{VarList}:
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

deferQMatch :: VarList -> VarList -> MatchResult
deferQMatch tv pv = ( nullBinds, [(tv,pv)], [] )

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
or returns a binding with deferred \texttt{VarList} and \texttt{ESubst} matches.
\begin{code}
type MatchOutcome = Maybe MatchResult

okNoBinding :: Monad m => m MatchResult
okNoBinding  = return noBinding

okBindP :: Monad m => Name -> Pred -> m MatchResult
okBindP pv p = return ((bindP pv p),[],[])

okBindE :: Monad m => Variable -> Expr -> m MatchResult
okBindE ev e = return ((bindE ev e),[],[])

okBindT :: Monad m => TVar -> Type -> m MatchResult
okBindT tv t = return ((bindT tv t),[],[])

okBindQ :: Monad m => Variable -> Variable -> m MatchResult
okBindQ qv q = return ((bindV qv q),[],[])

okBindQL :: Monad m => Variable -> [Variable] -> m MatchResult
okBindQL qv qvs = return ((bindQL qv qvs),[],[])

okBindV :: Monad m => Variable -> Variable -> m MatchResult
okBindV v x = return ((bindV v x),[],[])

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
 | TREqv -- matched single-PVar rhs of equivalence
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
    , mdlRoots :: [Name]
    , scrRoots :: [Name]
    , obsRoots :: [Name]
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

isKnownPred :: MatchContext -> Name -> Bool
isKnownPred mctxt r = tslookup (knownPreds mctxt) r /= Nothing
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
   before (_, _, VPre)  =  True
   before _             =  False
   lenMdl  = length mobs
   lenMdl' = length mobs'
   lenScr  = length sobs
   lenScr' = length sobs'
   mroots = lnorm (mobs++mobs')
   sroots = lnorm (sobs++sobs')

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

getSrcObs VPre  mctxt  =  srcObs  mctxt
getSrcObs VPost mctxt  =  srcObs' mctxt
getSrcObs d     mctxt  =  map (updVRole d) $ srcObs mctxt

getMdlObs VPre  mctxt  =  mdlObs  mctxt
getMdlObs VPost mctxt  =  mdlObs' mctxt
getMdlObs d     mctxt  =  map (updVRole d) $ mdlObs mctxt

rsvVRoots :: MatchContext -> ListVar -> [String]
rsvVRoots mctxt (L r _)  =  rsvRoots mctxt r
rsvVRoots _ _            =  []

rsvRoots :: MatchContext -> Name -> [String]
rsvRoots mctxt root
 | root == strOBS  =  obsRoots mctxt
 | root == strMDL  =  mdlRoots mctxt
 | root == strSCR  =  scrRoots mctxt
 | otherwise       =  []
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
 = ( [Variable]  -- standard known
   , [Variable]  -- standard unknown
   , VarList     -- general list
   , VarList )   -- reserved list

classifyVars :: (LocalContext -> Variable -> Bool)
             -> LocalContext
             -> VarList
             -> ClassedVars
classifyVars _ _ [] = ([],[],[],[])
classifyVars isknown here (lv:lvs)
 = (k,u,xs,r) `cmrg` (ks,us,xss,rs)
 where
   (k,u,xs,r)
      = case lv of
          (V v)
             | isknown here v  ->  ([v],[],[],[])
             | otherwise       ->  ([],[v],[],[])
          (L v _)
            | isRsvV v         ->  ([],[],[],[lv])
          otherwise            ->  ([],[],[lv],[])
   (ks,us,xss,rs) = classifyVars isknown here lvs

(a,b,c,d) `cmrg` (e,f,g,h) = (a++e,b++f,c++g,d++h)
\end{code}


\newpage
\subsubsection{List-Variable Denotations}

\input{doc/Matching-List-Roots}


\input{doc/Matching-List-Denote}


Function \texttt{lVarDenote}  computes $\sem{L^d\setminus R}_{\Gamma}$,
to the form $V \ominus X$ such that $X$ contains non-observation variables only.
\begin{code}
lVarDenote :: MatchContext -> ListVar -> (VarList,[Name])
lVarDenote mctxt (L (root, _, decor) subs)
 | root == strSCR  =  lVarDenote' obsvars srcvars decor subs
 | root == strMDL  =  lVarDenote' obsvars mdlvars decor subs
 | root == strOBS  =  lVarDenote' obsvars obsvars decor subs
 where
   srcvars = getSrcObs decor mctxt
   mdlvars = getMdlObs decor mctxt
   obsvars = mdlvars ++ srcvars
lVarDenote _ lv = ([lv],[])

lVarDenote' :: [Variable]   -- all known observables
            -> [Variable]   -- observable for this meta-root
            -> VRole        -- associated decoration
            -> [Name]    -- non-observable roots being subtracted
            -> (VarList,[Name])
lVarDenote' ovars dvars decor subs
 =  (denotation,csub)
 where
  denotation = map V $ lnorm $ filter keptv dvars
  keptv (r,_,_) = not (r `elem` subs)
  csub = lnorm $ filter kepts subs
  kepts sr = not (sr `elem` oroots)
  oroots = map varRoot ovars
\end{code}

Given a general variable, if a reserved list-variable,
we replace it by its denotation:
\begin{code}
varExpand :: MatchContext -> Variable -> ([Variable],[Name])
varExpand mctxt var
 | isRsvV var  =  ( lnorm vars', lnorm roots' )
 | otherwise      =  ( [var], [] )
 where
   (vars',roots') =  lVarDenote mctxt var

varsExpand :: MatchContext -> [Variable] -> [([Variable],[Name])]
varsExpand mctxt = map $ varExpand mctxt
\end{code}

A useful variant is a table binding variables to their expansion:
\begin{code}
varExpandMaplet :: MatchContext -> Variable -> (String,([Variable],[Name]))
varExpandMaplet mctxt var
 | isRsvV var  =  ( varKey var, varExpand mctxt var )
 | otherwise      =  ( varKey var, ([var],[])          )

varExpandTable :: MatchContext -> [Variable] -> Trie ([Variable],[Name])
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
varsDenote :: MatchContext -> [Variable] -> ([Variable],[Name])
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
varSize :: MatchContext -> ListVar -> (Ordering,Int)
varSize _     (V _)                 =  (EQ,1)
varSize mctxt (L (r,_,decor) subs)
 | r == strOBS  =  subSize (roleSize (sizeObs,sizeObs') decor $ mctxt) subs
 | r == strMDL  =  subSize (roleSize (sizeMdl,sizeMdl') decor $ mctxt) subs
 | r == strSCR  =  subSize (roleSize (sizeScr,sizeScr') decor $ mctxt) subs
 | otherwise  = (GT,-1) -- can be anything from zero upwards...

roleSize :: (a -> b, a -> b) -> VRole -> a -> b
roleSize (_, size') VPost  =  size'
roleSize (size,  _) _      =  size

subSize :: Int -> [Name] -> (Ordering,Int)
subSize 0 _         = (GT,-1)
subSize rsize []    = (EQ,rsize)
subSize rsize subs
 | any isLstN subs  =  (LT,rsize+1)
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
sizeConformant  :: MatchContext -> String -> VarList -> Bool
sizeConformant mctxt s qvs
  = sizeRelSat2 (varSize mctxt $ parseListVar s)
                (foldl sizeRelAdd (EQ,0) $ map (varSize mctxt) qvs)
\end{code}

\newpage
\subsection{Well-formed \texttt{VarList}}


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
obsCanEscapeRSV :: ListVar -> (ListVar,([Variable],[Name])) -> Bool
obsCanEscapeRSV (V v) (_,(vs,[]))  =  not (v `elem` vs)
obsCanEscapeRSV lv _               =  True
\end{code}
and next, the ``possible disjoint'' reserved-variable relation:
\begin{eqnarray*}
   (V_1\ominus X_1) \disjRSV (V_2\ominus X_2)
   &\defs&
   \exists \mu @ (V_1\setminus \mu X_1) \cap (V_2\setminus \mu X_2) = \emptyset
\\ PExpr^d \disjRSV Mdl^e &\equiv& d \neq e
\\ PExpr^d \disjRSV Scr^e &\equiv& d \neq e
\\ Mdl^d \disjRSV Scr^e &\equiv& \True
\end{eqnarray*}
Here we wrap a variable and its denotation together,
in case that denotation should be empty.
\begin{code}
possDisjRSV :: (ListVar,([Variable],[Name]))
            -> (ListVar,([Variable],[Name]))
            -> Bool
possDisjRSV ((Rsv r1 [],d1,_),([],[]))
            ((Rsv r2 [],d2,_),([],[]))   =  d1 /= d2 || isDisjRSV r1 r2
possDisjRSV (_,(vs1,[]))  (_,(vs2,[]))   =  vs1 `disjoint` vs2
possDisjRSV (_,(vs1,gs1)) (_,(vs2,gs2))  =  vs1 /= vs2 || gs1 /= gs2

isDisjRSV OBS MDL  =  Falseh
isDisjRSV OBS SCR  =  False
isDisjRSV MDL SCR  =  True
isDisjRSV r1  r2
      | r1 == r2   =  False
      | otherwise  =  isDisjRSV r2 r1
\end{code}

The invariant:
\begin{code}
invQVars :: MatchContext -> VarList -> Bool
invQVars mctxt qvs
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

predQVarInv mctxt (PAbs _ _ qvs prs)
 = invQVars mctxt qvs && all (predQVarInv mctxt) prs

predQVarInv mctxt pr = foldP (qVarInvFold mctxt) pr

exprQVarInv mctxt (Abs _ _ qvs es)
 = invQVars mctxt qvs && all (exprQVarInv mctxt) es

exprQVarInv mctxt e = foldE (qVarInvFold mctxt) e
\end{code}


We have code to fix things up:
\begin{code}
fixQVarsInv :: MatchContext -> VarList -> Maybe VarList
fixQVarsInv mctxt qvs = Just $ lstqnorm mctxt qvs

lstqnorm :: MatchContext -> [Variable] -> VarList
lstqnorm mctxt vs
 = lnorm vs'
 where
   nvs = lnorm vs
   vs' = filter keep nvs
   keep v = not(v `elem` stripset)
   stripset = concat $ map (fst . lVarDenote mctxt) mvs
   mvs = filter isLstV nvs
\end{code}

We can lift this to \texttt{VarList} and \texttt{Pred} levels:
\begin{code}
lQnorm :: MatchContext -> VarList -> VarList
lQnorm mctxt vs = lstqnorm mctxt vs

lPQnorm :: MatchContext -> Pred -> Pred
lPQnorm mctxt (PAbs nm tt qvs prs)
 = PAbs nm tt (lQnorm mctxt qvs) (map (lPQnorm mctxt) prs)

lEQnorm :: MatchContext -> Expr -> Expr
lEQnorm mctxt (Abs nm tt qvs es)
 = Abs nm tt (lQnorm mctxt qvs) (map (lEQnorm mctxt) es)
lEQnorm mctxt e = mapE (lPQnorm mctxt,lEQnorm mctxt) e
\end{code}

\newpage
\subsection{Well-formed \texttt{Substn}}


\input{doc/Substitution-Invariant}

The invariant:
\begin{code}
invESubst :: MatchContext -> ESubst -> Bool
invESubst mctxt (Substn sub)
 = invQVars mctxt (map fst sub)
   &&
   all listReplList sub
 where
   listReplList ((_, VList VObs, _, _), Var v )  =  isLstV v
   listReplList ((_, VObs,       _, _), _     )  =  True
   listReplList _                                =  False
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

exprESubstInv mctxt (ESub e subs)
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
predAlphaEqv pr1 pr2 = isJust $ palfequiv ([],[]) pr1 pr2

palfequiv :: ([Variable],[Variable]) -> Pred -> Pred -> Maybe BIJ
\end{code}

\begin{eqnarray*}
   \alfFreeMVarL &\defs& \alfFreeMVarR
\end{eqnarray*}
\begin{code}
palfequiv bvs (PVar s1) (PVar s2) | s1==s2  = aok
\end{code}
\begin{eqnarray*}
   \alfCompL &\defs& \alfCompR
\end{eqnarray*}
\begin{code}
palfequiv bvs TRUE TRUE = aok
palfequiv bvs FALSE FALSE = aok
palfequiv bvs (PExpr e1) (PExpr e2)   =  ealfequiv bvs e1 e2
palfequiv bvs (PApp s1 prs1) (PApp s2 prs2)
  | s1==s2  =  alflist palfequiv bvs prs1 prs2
\end{code}
\newpage
\begin{eqnarray*}
   (\exists x_1 @ P_1) \balfeqv{B_1}{B_2} (\exists x_2 @ P_2)
   &\defs&
   (P_1 \balfeqv{B_1 \cup \setof{x_1}}{B_2\cup\setof{x_2}} P_2)
   |_{(B_1 \cup B_2)}
\end{eqnarray*}
\begin{code}
palfequiv bvs (PAbs n1 _ qs1 prs1) (PAbs n2 _ qs2 prs2)
 | n1==n2 = qalfequiv bvs (prs1,qs1) (prs2,qs2)
\end{code}
\begin{eqnarray*}
   \alfSubL &\defs& \alfSubR
\end{eqnarray*}
\begin{code}
palfequiv bvs (Sub pr1 (Substn sub1))
              (Sub pr2 (Substn sub2))
                = salfequiv bvs palfequiv id ealfequiv (pr1, sub1) (pr2, sub2)
\end{code}
Leftover stuff
\begin{code}
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
exprAlphaEqv e1 e2
 = case ealfequiv ([],[]) e1 e2 of
    Nothing  ->  False
    Just _   ->  True

ealfequiv :: ([Variable],[Variable]) -> Expr -> Expr -> Maybe BIJ

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
--should be part of the previous match...
\end{code}
\begin{eqnarray*}
   (P_1 \land Q_1) \balfeqv{B_1}{B_2} (P_2 \land Q_2)
   &\defs&
   (P_1 \balfeqv{B_1}{B_2} P_2)
   \uplus
   (Q_1 \balfeqv{B_1}{B_2} Q_2)
\end{eqnarray*}
\begin{code}
ealfequiv bvs (App s1 es1) (App s2 es2) | s1==s2
  = alflist ealfequiv bvs es1 es2
\end{code}

\begin{eqnarray*}
   (\exists x_1 @ P_1) \balfeqv{B_1}{B_2} (\exists x_2 @ P_2)
   &\defs&
   (P_1 \balfeqv{B_1 \cup \setof{x_1}}{B_2\cup\setof{x_2}} P_2)
   |_{(B_1 \cup B_2)}
\end{eqnarray*}
\begin{code}
ealfequiv bvs (Abs n1 _ qs1 es1) (Abs n2 _ qs2 es2)
 | n1 == n2 = qalfequiv bvs (map PExpr es1,qs1) (map PExpr es2,qs2)
\end{code}
\begin{eqnarray*}
   \alfSubL &\defs& \alfSubL
\end{eqnarray*}
\begin{code}
ealfequiv bvs (ESub e1 (Substn sub1))
              (ESub e2 (Substn sub2))
                  = salfequiv bvs ealfequiv id ealfequiv (e1, sub1) (e2, sub2)

ealfequiv bvs _ _ = Nothing
\end{code}
