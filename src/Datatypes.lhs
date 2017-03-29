\section{Data Types}

\begin{code}
module Datatypes where
import Data.Char
import Data.List
import Tables
import Utilities

import Data.Maybe
import System.IO
\end{code}


We have the notion of types, expressions and predicates,
plus many aliases for \texttt{String}s.
\begin{code}
type Message = String
\end{code}

\newpage
\subsection{Variables}

A variable has a \emph{name}.
\begin{code}
type Name = String -- no whitespace !
\end{code}

A variable will have one of the following \emph{kinds}:
\begin{description}
  \item[Observational]
    Corresponds to some observation that can be made of a program,
    and hence belongs, in UTP,  to the alphabet of the corresponding predicate.
  \item[Schematic]
    Stands for an arbitrary chunk of abstract syntax,
    of which we recognise two broad classes:
    \begin{description}
      \item[Expression] denotes an arbitrary expression
      \item[Predicate] denotes an arbitrary predicate
    \end{description}
  \item[Script]
    Represents an actual program variable itself,
    rather than any associated value it may take.
  \item[List]
   In a context where a list of variables is required,
   this can stand for zero or more variables,
   all belonging to precisely one of the categories detailed above.
\end{description}
The above kinds all have different roles in the logic underlying UTP.

\begin{code}
data VKind = VObs
           | VExpr
           | VPred
           | VScript
           | VList
               VKind -- cannot be ListV !
           deriving (Eq, Ord, Show)
\end{code}

In addition, with most of the variable kinds above,
we can associate one of the following \emph{roles}:
\begin{description}
  \item[Static]
    variables whose values a fixed for the life of a (program) behaviour
  \item[Dynamic]
    variables whose values are expected to change over the life of a behaviour.
    \begin{description}
      \item[Pre]
        variables that record the values taken when a behaviour starts
      \item[Post]
        variables that record the values taken when a behaviour ends
      \item[Relational]
        Expression or Predicate variables that denote relations
        between the start and end of behaviours.
      \item[Intermediate]
        indexed variables that record values that arise between successive behaviours
    \end{description}
\end{description}
These distinct roles do not effect how the underlying logic handles
variables, but are used to tailor definitional shorthands that
assume that these are enacting the relevant UTP variable conventions.

\begin{code}
data VRole = VStatic
           | VPre
           | VPost
           | VRel          -- VExpr, VPred only
           | VInter String -- VObs, VList VObs only
           deriving (Eq, Ord, Show)
\end{code}


A variable has a name, kind and role,
as well as a list of names used to identify exceptions
to one of the reserved list variables
\begin{code}
type Variable = ( Name
                , VKind
                , VRole
                , [Name] -- only VList, with name in O,M,S
                )
\end{code}

Invariant:
\begin{enumerate}
  \item the argument of a \texttt{VList} cannot be another \texttt{VList}.
  \item only kinds \texttt{VExpr} and \texttt{VPred} can have role \texttt{VRel}.
  \item only kind \texttt{VObs} or \texttt{VList VObs} can have role \texttt{VInter}.
  \item only kind \texttt{VList VObs} can have roots (lists of names).
\end{enumerate}
\begin{code}
invVariable reserved (name, kind, role, roots)
 = invKind kind
   && (role == VRel)    `implies`  (kind `elem` [VExpr,VPred])
   && isVInter role     `implies`  (kind `elem` [VObs,VList VObs])
   && not (null roots)  `implies`  (kind == VList VObs)

invKind (VList (VList _)) = False
invKind _                 = True

isVInter (VInter _) = True
isVInter _          = False
\end{code}

Some useful predicates on variables:
\begin{code}
isStdV (_,VList _,_,_) = False
isStdV _               = True

isLstV (_,VList _,_,_) = True
isLstV _               = False
\end{code}



Variable utility code.
First three are used to create non-parseable error variables"
\begin{code}
varmap :: (String -> String) -> Variable -> Variable
varmap f (n,k,r,ns) = (f n, k, r,ns)
\end{code}

\begin{code}
varKey :: Variable -> String
varKey (n,_,_,_) = n
\end{code}

\newpage
We will often want to store variable information
in string-indexed tables (\texttt{Trie}), which is what the 3rd component
(\texttt{varKey}) is for:
\begin{code}
tvlookup :: Trie t -> Variable -> Maybe t
tvlookup trie = tlookup trie . varKey

svlookup :: Trie t -> Variable -> Bool
svlookup trie = slookup trie . varKey

tsvlookup :: [Trie t] -> Variable -> Maybe t
tsvlookup tries = tslookup tries . varKey

ssvlookup :: [Trie t] -> Variable -> Bool
ssvlookup tries = sslookup tries . varKey

tvupdate :: Variable -> t -> Trie t -> Trie t
tvupdate v a trie = tupdate (varKey v) a trie
\end{code}


\newpage
\subsection{Substitutions}

Substitutions associate a list of things (types,expressions,predicates)
with some (quantified) variables.
This is just
\begin{code}
data Substn v a
 = Substn [( v   -- variable type
           , a   -- replacement object
           )]
 deriving (Eq,Ord,Show)

type VSubst = Substn Variable Variable
\end{code}

It helps to convert \texttt{Substn} into pairs of lists
or lists of pairs (assuming no meta-variables, and correct matching),
and vice-versa:
\begin{code}
unwrapQV  (Substn ssub)  =  twist $ unzip $ ssub
sublistQV (Substn ssub)  =  map twist ssub
mkSubs a v       =  Substn [(v,a)]
packlistQV subs  =  Substn (map twist subs)
packflipQV subs  =  Substn subs -- now a misnomer
\end{code}
The use of \texttt{twist} here is because
the new revised \texttt{Substn} datatype
now puts entries in association-list order \texttt{(from,to)}
rather than substitution notation order \texttt{[to/from]},
which was the basis for the old%
\footnote{pre May 27th 2010}
datatype.

We provide a constructor
that supports the old type, where we had a list of things and
a corresponding \texttt{Variable},
as well as a destructor that returns \texttt{QVars}.

(We note that \texttt{QVars} have been demoted
from \texttt{data} to \texttt{type}
and will be phased out).
\begin{code}
mkQsubst as xs = Substn $ zip xs as

mkSubQ (Substn ssub) =  map fst ssub
\end{code}


Mapping across \texttt{Substn} types is also helpful:
\begin{code}
mapSub :: (a -> b) -> Substn v a -> Substn v b
mapSub f (Substn ssub)
 = Substn (map (lift f) ssub)
 where lift f (v,a) = (v,f a)
\end{code}

\begin{code}
qvunzip :: Substn v a -> ([a],[v])
qvunzip (Substn sub) = twist $ unzip sub

qvunzipWith :: (v -> Variable) -> Substn v a -> ([a],[Variable])
qvunzipWith toV sub = setsnd (map toV ) $ qvunzip sub
\end{code}

\subsection{Types}

For now, type variables are strings:
\begin{code}
type TVar = String
\end{code}

The ordering of data-constructors here is important,
as type-inference relies on it.
\begin{code}
data Type -- most general types first
 = Tarb
 | Tvar TVar
 | TApp String [Type]
 | Tfree String [(String,[Type])]
 | Tfun Type Type
 | Tenv
 | Z
 | B
 | Terror String Type
 deriving (Eq,Ord,Show)

type TSubst = Substn String   Type

nonTypeCons Tarb      =  True
nonTypeCons (Tvar _)  =  True
nonTypeCons Tenv      =  True
nonTypeCons Z         =  True
nonTypeCons B         =  True
nonTypeCons _         =  False
\end{code}

\newpage
\subsection{Type-Tables}
When we do type-inference,
we need to maintain tables mapping variables to types.
Given the presence of binders/quantifiers,
these tables need to be nested.
We shall use integer tags to identify the tables:
\begin{code}
type TTTag = Int
\end{code}

At each level we have a table mapping variables to types,
and then we maintain a master table mapping type-table tags to such
tables:
\begin{code}
type VarTypes = Trie Type                -- Var -+-> Type
type TVarTypes = Trie Type               -- TVar -+-> Type
type TypeTables = Btree TTTag VarTypes
\end{code}
Quantifiers induce nested scopes which we capture as a list of
type-table tags. Tag 0 is special and always denotes the topmost global
table.

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

\newpage
\subsection{Terms}

We can posit a very general notion of terms ($t$),
within which we can also embed some other term syntax ($s$).
Terms are parameterised by a notion of constants ($k$)
and with some fixed notion of variables ($v$)
and a distinct notion of \emph{names} ($n$).
\begin{eqnarray*}
   n &\in& Names
\\ k &\in& Constants
\\ v &\in& Variables
\\ \ell &\in& ListVar
\\ vs \in VarList &=& (v | \ell)^*
\\ s &\in& Syntax (other)
\\ t \in Term~k~s
   &::=& k
\\ & | & v
\\ & | & n(t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t)
\\ & | & t[t,\dots,t/v,\dots,v]
\\ & | & [s]
\end{eqnarray*}

So, we expect to have two mutually recursive instantiations
of terms: Expressions ($E$) and Predicates ($P$).
\begin{eqnarray*}
   E &\simeq& Term~\Int~P
\\ P &\simeq& Term~\Bool~E
\end{eqnarray*}

We need to consider zippers.
For term alone, assuming fixed $s$:
\begin{eqnarray*}
   t' \in Term'~k~s
   &::=& n(t,\dots,t,[\_]t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t,[\_]t,\dots,t)
\\ & | & \_[t,\dots,t/v,\dots,v]
\\ & | & t[t,\dots,t,[\_]t,\dots,t/v,\dots,v,v,v,\dots,v]
\end{eqnarray*}
Intuitively, if we have descended into $s$, then
we should have $s'$ here.
So we really have:
\begin{eqnarray*}
   t' \in Term'~k~s
   &::=& n(t,\dots,t [\_]t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t [\_]t,\dots,t)
\\ & | & \_[t,\dots,t/v,\dots,v]
\\ & | & t[t,\dots,t,[\_]t,\dots,t/v,\dots,v,v,v,\dots,v]
\\ & | & [s']
\end{eqnarray*}


\newpage
\subsection{Expressions}

We have a very simple expression abstract syntax
\begin{code}
data Expr
 = Num Int
 | Var Variable
 | App String [Expr]
 | Abs String TTTag [Variable] [Expr]
 | ESub Expr ESubst
 | EPred Pred
 deriving (Eq, Ord, Show)


n_Eerror = "EXPR_ERR: "
eerror str = App (n_Eerror ++ str) []

type ESubst = Substn Variable Expr
\end{code}

We need some builders that perform
tidying up for corner cases:
\begin{code}
mkEsub e (Substn []) = e
mkEsub e sub = ESub e sub
\end{code}

Useful to know when an expression is a variable:
\begin{code}
isVar :: Expr -> Bool
isVar (Var _)   =  True
isVar _         =  False

getVar :: Expr -> Variable
getVar (Var v)   =  v
getVar _         =  nullVar
nullVar  = ("",VScript,VStatic,[])

mgetVar :: Expr -> Maybe Variable
mgetVar (Var v)   =  Just v
mgetVar _         =  Nothing
\end{code}

\newpage
\subsection{Predicates}

Again, a very simple abstract syntax,
but with the add of a typing hook:

\begin{code}
data Pred
 = TRUE
 | FALSE
 | PVar Variable
 | PApp String [Pred]
 | PAbs String TTTag [Variable] [Pred]
 | Sub Pred ESubst
 | PExpr Expr
 | TypeOf Expr Type
 deriving (Eq, Ord, Show)


n_Perror = "PRED_ERR: "
perror str = PApp (n_Perror ++ str) []

type PSubst = Substn Variable  Pred
\end{code}

We define two constructor functions to handle the \texttt{Expr}/\texttt{Pred} ``crossovers'':
\begin{code}
ePred (PExpr e)           = e
ePred (Sub (PExpr e) sub) = ESub e sub
ePred pr                  = EPred pr

pExpr (EPred pr)            = pr
pExpr (ESub (EPred pr) sub) = Sub pr sub
pExpr e                     = PExpr e
\end{code}

We also define smart constructors for certain constructs
to deal with corner cases.

THIS NEEDS TO GO TO A SPECIAL "builtins" MODULE

\begin{code}
n_Not = "Not"
mkNot p = PApp n_Not [p]

n_And = "And"
mkAnd [] = TRUE
mkAnd [pr] = pr
mkAnd prs = PApp "And" prs

n_Or = "Or"
mkOr [] = FALSE
mkOr [pr] = pr
mkOr prs = PApp "Or" prs

n_Eqv = "Eqv"
mkEqv pr1 pr2 = PApp n_Eqv [pr1,pr2]

n_Forall = "Forall"
mkForall ([]) p = p
mkForall qvs p = PAbs "Forall" 0 qvs [p]

n_Exists = "Exists"
mkExists ([]) p = p
mkExists qvs p = PAbs "Exists" 0 qvs [p]

n_Exists1 = "Exists1"
mkExists1 ([]) p = FALSE
mkExists1 qvs p = PAbs "Exists1" 0 qvs [p]

n_Univ = "Univ"
mkUniv p =  PAbs n_Univ 0 [] [p]

mkSub p (Substn []) = p
mkSub p sub = Sub p sub

n_Pforall = "Pforall"
mkPforall ([]) p  = p
mkPforall qvs p = PAbs "Pforall" 0 qvs [p]

n_Pexists = "Pexists"
mkPexists ([]) p  = p
mkPexists qvs p = PAbs "Pexists" 0 qvs [p]

mkPsub p (Substn []) = p
mkPsub p sub = Sub p $ mapSub EPred sub

n_Peabs = "Peabs"
mkPeabs ([]) p  = p
mkPeabs qvs p = PAbs "Peabs" 0 qvs [p]

n_Equal = "Equal"
mkEqual e1 e2 = App n_Equal [e1,e2]
\end{code}
Some query functions:
\begin{code}
isObs (PExpr _) = True
isObs _       = False
\end{code}

\newpage
\subsection{Quantifier Variables}

We want to be able to match predicates and expressions
against laws involving quantifiers in a flexible manner,
so we need to represent quantified variables, and lists of them
as well as variables that can match against these.
Generally we want to match against a specified list of
variables, and then ``all the rest''.

We have changed \texttt{QVars}
from a \texttt{data}-type
to a \texttt{type}-synonym.
Functions below are to be deprecated.
\begin{code}
type QVars = [Variable]

mkQ :: [Variable] -> QVars
mkQ = lnorm

snglQ :: Variable -> QVars
snglQ v = [v]

qvarmrg qs rs = mkQ (qs++rs)

qsmrg :: QVars -> QVars -> QVars -- no normalisation for subst-lists!
qs `qsmrg` rs  = qs ++ rs

-- except when we explicitly want it!
as `mrgqnorm` bs = as `mrgnorm` bs
\end{code}


\subsection{Language Constructs}

We need to surround language elements by a syntax specification:
\begin{code}
data SynSpec
 = SSNull
 | SSTok String
 | SSObj String  -- Type, Expr, Pred, List, Tuple....
 | SSSep String
 deriving (Eq,Ord,Show)
\end{code}

A Language Specification is list of \texttt{SynSpec}:
\begin{code}
data LangSpec = LangSpec [SynSpec] deriving (Eq,Ord,Show)
\end{code}


\subsection{Equality}

These are old definitions used when type-table information
was stored in expressions and predicates
We want to define equality that ignores type-inference markings
(\texttt{TTTag}s).

We want to compare two predicates for equality,
 modulo ``liberal type equivalence''
\begin{code}
pequiv :: Pred -> Pred -> Bool

pequiv TRUE TRUE = True
pequiv FALSE FALSE = True
pequiv (PExpr e1) (PExpr e2) = e1 `eequiv` e2

pequiv (Sub pr1 sub1) (Sub pr2 sub2) = pr1 `pequiv` pr2 && sub1 `estlequiv` sub2

pequiv (PVar s1) (PVar s2) = s1==s2
pequiv (PAbs s1 _ qs1 prs1) (PAbs s2 _ qs2 prs2)
  = s1==s2 && qs1==qs2 && samelist pequiv prs1 prs2
pequiv (PApp s1 prs1) (PApp s2 prs2)
  = s1==s2 && samelist pequiv prs1 prs2

pequiv _ _ = False
\end{code}

And for expressions:
\begin{code}
eequiv :: Expr -> Expr -> Bool

eequiv (Num i1) (Num i2) = i1==i2
eequiv (Var v1) (Var v2) = v1==v2
eequiv (App s1 es1) (App s2 es2)
 = s1==s2 && samelist eequiv es1 es2
eequiv (Abs s1 _ qs1 es1) (Abs s2 _ qs2 es2)
 = s1==s2 && qs1==qs2 && samelist eequiv es1 es2
eequiv (ESub e1 sub1) (ESub e2 sub2)
 = e1 `eequiv` e2 && sub1 `estlequiv`  sub2

eequiv _ _ = False

esequiv [] [] = True
esequiv (e1:es1) (e2:es2) = e1 `eequiv` e2 && es1 `esequiv` es2
esequiv _ _ = False
\end{code}

Substitution equivalence:
\begin{code}
estlequiv (Substn ssub1)  (Substn ssub2) = samealist eequiv ssub1 ssub2

pstlequiv (Substn ssub1)  (Substn ssub2) = samealist pequiv ssub1 ssub2
\end{code}

For now:
\begin{code}
tequiv :: Type -> Type -> Bool
tequiv = (==)
\end{code}




\newpage
\subsection{Observation Variables}

UTP is based on the notion of alphabetised predicates,
which we support by maintaining information about
variables in the alphabet.
In addition to alphabet membership,
it is useful to be able to distinguish observation variables
that corresponds to program/specification variables ($Script$),
and those that describe other aspects of a languages behaviour ($Model$),
capturing the peculiarities of a given semantic model%
\footnote{
Often referred to in the literature, as \emph{auxiliary} variables
}.
\begin{code}
data OClass = Model | Script deriving (Eq,Ord,Show)

type ObsKind = (Variable,OClass,Type)
\end{code}




\subsubsection{Change Marker}
\begin{code}
data ChgMrk = Chgd | NoChg deriving (Eq,Show)

chgmrg Chgd _ = Chgd
chgmrg _ Chgd = Chgd
chgmrg _    _ = NoChg

chgmap f [] = ([],NoChg)
chgmap f (x:xs)
 = let (x',xchgd) = f x
       (xs',xschgd) = chgmap f xs
   in (x':xs',xchgd `chgmrg` xschgd)
\end{code}



\newpage
\subsection{Single Recursion Boilerplate}

The following routines ignore the mutual recursion,
and only cover a subset of most cases.

\subsubsection{Type Single Recursion}

\begin{code}

typeRec merge spec base ty
 = case spec ty of
     (Just res)  ->  res
     Nothing     ->  tRecurse ty
 where

  typerec = typeRec merge spec base

  tRecurse (Tfree _ fs) = merge $ map typerec $ concat $ map snd fs
  tRecurse (TApp _ ts) = merge $ map typerec ts
  tRecurse (Tfun ty1 ty2) = merge $ map typerec [ty1,ty2]
  tRecurse _ = base

\end{code}

\subsubsection{\texttt{Expr} Single Recursion}

\begin{code}
exprRec merge spec base ex
 = case spec ex of
     (Just res)  ->  res
     Nothing     ->  eRecurse ex
 where

  exprrec = exprRec merge spec base
  exprrec2 (de,re) = merge $ map exprrec [de,re]

  eRecurse (App _ exs) = merge $ map exprrec exs
  eRecurse (Abs _ _ _ exs) = merge $ map exprrec exs
  eRecurse (ESub ex (Substn ssub))
    = merge $ map exprrec (ex:(map snd ssub))
  eRecurse _ = base
\end{code}

\subsubsection{\texttt{Pred} Single Recursion}

The use of this function is not currently recommended
when predicate-sets
are present.
\begin{code}
predRec merge spec base pr
 = case spec pr of
     (Just res)  ->  res
     Nothing     ->  pRecurse pr
 where

  predrec = predRec merge spec base

  pRecurse (Sub pr _) = predrec pr
  pRecurse (PAbs _ _ _ prs) = merge $ map predrec prs
  pRecurse (PApp _ prs) = merge $ map predrec prs
  pRecurse _ = base
\end{code}

\subsection{Mutual Recursion Boilerplate}

We shall describe the key concepts using the follow (singly-)recursive
datatype:
\begin{eqnarray*}
  D &::=&  K_0 | K_1 D | K_2 D^*
\end{eqnarray*}
where $K_i$ are the constructors (tags).

Over this datatype we may want to recursively define functions
with signatures as follows:
\begin{itemize}
  \item $D \fun A$
    \\ A straight recursive \emph{fold}.
  \item $D \fun D$
    \\ A straight recursive \emph{map}.
  \item $A \fun D \fun (D,A)$
    \\ A fusion of fold and map with an accumulator (\emph{accfuse}).
    \\ This can operate in two modes:
    \begin{itemize}
      \item parallel --- the $A$ parameter is passed identically to all
      sub-components, and the returned $A$ values are then merged (\emph{accpar})
      \item sequential --- the $A$ parameter is
          threaded in sequence through sub-componets
          with the final value being returned
          (\emph{accseq})
    \end{itemize}
\end{itemize}

\subsubsection{Recursion boilerplate: \emph{map}}

We want to define
\begin{eqnarray*}
   f &:& D \fun D
\\ f~K_0 &\defs& g~K_0
\\ f~(K_1~d) &\defs& K_1~(f~d)
\\ f~(K_2~\delta) &\defs& K_2~(f^*~\delta)
\end{eqnarray*}
The boilerplate:
\begin{eqnarray*}
   map~g~K_0 &\defs& g~K_0
\\ map~g~(K_1~d) &\defs& K_1~(map~g~d)
\\ map~g~(K_2~\delta) &\defs& K_2~((map~g)^*~\delta)
\end{eqnarray*}
We can write $f$ as:
\begin{eqnarray*}
  f &\defs& map~g
\end{eqnarray*}

\newpage
In practice we have two mutually recursive types,
\texttt{Pred} and \texttt{Expr},
so we pass in two functions, one for each datatype:
\begin{code}
mapP :: (Pred -> Pred,Expr -> Expr) -> Pred -> Pred
mapE :: (Pred -> Pred,Expr -> Expr) -> Expr -> Expr

mapPf :: (Pred -> (Pred,Bool), Expr -> (Expr,Bool)) -> Pred -> (Pred,Bool)
mapEf :: (Pred -> (Pred,Bool), Expr -> (Expr,Bool)) -> Expr -> (Expr,Bool)

run f e = f e

mapPf (fp,fe) (PExpr e) = (PExpr e', dif)
  where (e', dif) = fe e
mapPf (fp,fe) (Sub pr sub) = (Sub pr' sub', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (sub', dif2) = mapSf fe sub

mapPf (fp,fe) (PAbs s ttts vs prs) = (PAbs s ttts vs prs', or difs)
  where (prs', difs) = unzip $ map (mapPf (fp,fe)) prs

mapPf (fp,fe) pr = (pr, False)

mapEf (fp,fe) (App s es) = (App s es', or difs)
  where (es',difs) = unzip $ map fe es
mapEf (fp,fe) (Abs s ttts qs es) = (Abs s ttts qs es', or difs)
  where (es',difs) = unzip $ map fe es
mapEf (fp,fe) (ESub e sub) = (ESub e' sub', dif1 || dif2)
  where
    (sub', dif1) = mapSf fe sub
    (e', dif2) = fe e

mapEf (fp,fe) e = (e, False)
\end{code}

The intended usage is for the two functions
to handle the specific cases,
and then call \texttt{mapP}/\texttt{mapE} as appropriate
\begin{verbatim}
myPredMap TRUE = ...
myPredMap (Exists ...) = ...
myPredMap pr = mapP (myPredMap,myExprMap) pr
\end{verbatim}

Now the \texttt{mapP}/\texttt{E} boilerplate:
\begin{code}
mapP (fp,fe) (PExpr e) = PExpr (fe e)
mapP (fp,fe) (Sub pr sub) = Sub (fp pr) (mapS fe sub)

mapP (fp,fe) pr = pr

mapE (fp,fe) (App s es)    = App s (map fe es)
mapE (fp,fe) (Abs s ttts qs es) = Abs s ttts qs (map fe es)
mapE (fp,fe) (ESub e sub)  = ESub (fe e) (mapS fe sub)

mapE (fp,fe) e = e

mapS f (Substn ssub) = Substn (maparng f ssub)

mapSf f (Substn ssub) = (Substn ssub', or dif)
 where
    (ssub', dif) = unzip (maparngf f ssub)
\end{code}

\newpage
\subsubsection{Recursion boilerplate: \emph{fold}}

We want to define
\begin{eqnarray*}
   f &:& D \fun A
\\ f~K_0 &\defs& g_0~K_0
\\ f~(K_1~d) &\defs& g_1~(f~d)
\\ f~(K_2~\delta) &\defs& g_2(f^*~\delta)
\end{eqnarray*}
The boilerplate:
\begin{eqnarray*}
   fold (g_0,g_1,g_2) K_0 &\defs& g_0~K_0
\\ fold (g_0,g_1,g_2) (K_1~d) &\defs& g_1~(fold (g_0,g_1,g_2)~d)
\\ fold (g_0,g_1,g_2) (K_2~\delta) &\defs& g_2~((fold(g_0,g_1,g_2))^*~\delta)
\end{eqnarray*}
We can write $f$ as:
\begin{eqnarray*}
  f &\defs& fold(g_0,g_1,g_2)
\end{eqnarray*}
In many cases we will have $g_1(a) = g_2\seqof a$.

As above, we have mutually recursive Pred and Expr to handle
so we need two function quadruples:
\begin{code}
type PFold a = (a,Pred -> a,a -> a,[a]->a)
type EFold a = (a,Expr -> a,a -> a,[a]->a)
foldP :: (PFold a,EFold a) -> Pred -> a
foldE :: (PFold a,EFold a) -> Expr -> a
\end{code}

Folding over predicates:
\begin{code}
foldP pef@((pa,f0,f1,f2),(ea,g0,g1,g2)) pr
 = f pr
 where
  f (PApp s prs) = f2 $ map f0 prs
  f (PAbs s ttts qvs prs) = f2 $ map f0 prs
  f (PExpr e) = f1 $ g0 e
  f (Sub p sub) = f2 (f p : foldES g0 sub)

  f pr = pa -- recursion must stop here !

-- end foldP
\end{code}

Folding over Expressions:
\begin{code}
foldE pef@((pa,f0,f1,f2),(ea,g0,g1,g2)) e
 = f e
 where
  f (App s es) = g2 $ map g0 es
  f (Abs s ttts qvs es) = g2 $ map g0 es
  f (ESub e sub) = g2 (g0 e : foldES g0 sub)

  f e = ea -- recursion must stop here !
-- end foldE
\end{code}

Folding auxilliaries:
\begin{code}
foldPS :: (Pred -> a) -> PSubst -> [a]
foldPS f0 (Substn ssub) = map (f0 . snd) ssub

foldES :: (Expr -> a) -> ESubst -> [a]
foldES g0 (Substn ssub) = map (g0 . snd) ssub
\end{code}



\subsubsection{Recursion boilerplate: \emph{accseq}}

We want to define
\begin{eqnarray*}
   f &:& A \fun D \fun (D,A)
\\ f~a~K_0 &\defs& f_0~a~K_0
\\ f~a~(K_1~d) &\defs& (K_1~d',a') \WHERE (d',a') = f~a~d
\\ f~a~(K_2~\delta) &\defs& (K_2~\delta',a') \WHERE (\delta',a') = seq~f~a~\delta
\\
\\ seq~f~a~\nil &\defs& (\nil,a)
\\ seq~f~a~(d:\delta) &\defs& (d':\delta',a'') \WHERE
\\ && (d',a') = f~a~d
\\ && (\delta',a'') = seq~f~a'~\delta
\end{eqnarray*}
Here $f_0$ handles the base-case appropriately.
The boilerplate support we provide
is code to handle the recursive calls and their plumbing,
but not the top-level case-split on the datatype $D$.
\begin{eqnarray*}
    accseq~f~a~(K_1~d) &\defs& (K_1~d',a') \WHERE (d',a') = f~a~d
\\  accseq~f~a~(K_2~\delta) &\defs& (K_2~\delta',a') \WHERE (\delta',a') = seq~f~a~\delta
\end{eqnarray*}
So now we can write $f$ as:
\begin{eqnarray*}
   f~a~K_0 &\defs& f_0~a~K_0
\\ f~a~d &\defs& accseq~f~a~d
\end{eqnarray*}
We can add additional cases if some recursive cases need special handling,
and we add a handler for base cases to be treated uniformly
Note that $f$ itself needs to call $accseq$ to ensure recursion occurs.

As \texttt{Pred} and \texttt{Expr} are mutually recursive we have
to pass around a pair of functions.
Also, the focus variants of both must always be handled explicitly.
\begin{code}
accPseq :: (a -> Pred -> (Pred,a),a -> Expr -> (Expr,a))
            -> a -> Pred -> (Pred,a)

accPseq (pf,ef) a (PExpr e) = (PExpr e',a') where (e',a') = ef a e

accPseq (pf,ef) a (Sub pr sub) = (Sub pr' sub',a'')
 where (pr',a') = pf a pr
       (sub',a'') = accESseq (pf,ef) a' sub

accPseq (pf,ef) a pr = (pr,a)

accPseqs pf a [] = ([],a)
accPseqs pf a (pr:prs) = (pr':prs',a'')
 where (pr',a') = pf a pr
       (prs',a'') = accPseqs pf a' prs
\end{code}

The \texttt{Expr} version:
\begin{code}
accEseq :: (a -> Pred -> (Pred,a),a -> Expr -> (Expr,a))
            -> a -> Expr -> (Expr,a)
accEseq (pf,ef) a (App s es) = (App s es',a')
  where (es',a') = accEseqs ef a es
accEseq (pf,ef) a (Abs s ttts qs es) = (Abs s ttts qs es',a')
 where (es',a') = accEseqs ef a es
accEseq (pf,ef) a (ESub e sub) = (ESub e' sub',a'')
 where (e',a') = ef a e
       (sub',a'') = accESseq (pf,ef) a' sub
accEseq (pf,ef) a e = (e,a)

accEseqs ef a [] = ([],a)
accEseqs ef a (e:es) = (e':es',a'')
 where (e',a') = ef a e
       (es',a'') = accEseqs ef a' es

accEseqm ef a [] = ([],a)
accEseqm ef a ((de,re):ms) = ((de',re'):ms',a'')
 where ([de',re'],a') = accEseqs ef a [de,re]
       (ms',a'') = accEseqm ef a' ms
\end{code}

The Substitution versions
\begin{code}
accESseq (pf,ef) a (Substn ssub) = (Substn ssub',a')
 where  (ssub',a')   =  accSseqs ef a ssub

accPSseq (pf,ef) a (Substn ssub) = (Substn ssub',a')
 where (ssub',a')   =  accSseqs pf a ssub

accSseqs f a [] = ([],a)
accSseqs f a ((v,rep):rest) = ((v,rep'):rest',a'')
 where
  (rep',a') = f a rep
  (rest',a'') = accSseqs f a' rest
\end{code}



\subsubsection{Debugging}

\begin{code}
instance Dshow Pred  where dshow = debugPshow
instance Dshow Expr  where dshow = debugEshow
instance Dshow Type  where dshow = debugTshow
instance Dshow SideCond where dshow sc = "SC"
instance Dshow QVars where dshow = debugQSshow

instance (Dshow a,Dshow b) => Dshow (a,b) where
 dshow (a,b) = "FIRST:\n"++dshow a++"\nSECOND\n"++dshow b

debugPshow pr = dbgPshow 0 pr

debugEshow  =  dbgEshow 0

debugTshow  =  dbgTshow 0

debugLshow (LangSpec ss)
 =  "LANGSPEC"
    ++ concat (map (dbgSSshow 1) ss)

debugAshow (pr,sc)
 = "ASSERTION"
    ++ dbgPshow 3 pr
    ++ dbgSCshow 1 sc

hdr i  = '\n':(replicate i ' ')

dbgPshow i  TRUE     = hdr i ++ "TRUE"
dbgPshow i  FALSE    = hdr i ++ "FALSE"
dbgPshow i  (PVar pv) = hdr i ++ "PVAR "++dbgVshow pv
dbgPshow i  (PExpr e)  = hdr i ++ "PEXPR " ++ dbgEshow (i+1) e
dbgPshow i  (TypeOf e t)
 = hdr i ++ "TYPEOF " ++ dbgEshow (i+1) e ++ dbgTshow (i+1) t
dbgPshow i  (PApp nm prs)
 = hdr i ++ "PAPP " ++ nm ++ concat (map (dbgPshow (i+1)) prs)
dbgPshow i  (PAbs nm tts qs prs)
 = hdr i ++ "PABS " ++ nm ++ show tts
   ++ dbgQSshow (i+1) qs
   ++ concat (map (dbgPshow (i+1)) prs)
dbgPshow i  (Sub pr sub)
 = hdr i ++ "SUB" ++ dbgESshow (i+1) sub++dbgPshow (i+1) pr

dbgSSshow i SSNull      = hdr i ++ "SSNULL"
dbgSSshow i (SSTok s)   = hdr i ++ "SSTOK "  ++ s
dbgSSshow i (SSSep s)   = hdr i ++ "SSSEP "  ++ s

dbgEshow i (Num n)         = hdr i ++ "NUM "++show n
dbgEshow i (Var v)         = hdr i ++ "VAR " ++ dbgVshow v
dbgEshow i (App s es)
 = hdr i ++ "APP "++s++concat (map (dbgEshow (i+1)) es)
dbgEshow i (Abs s tts qs es)
 = hdr i ++ "ABS "++s++" "++show tts
   ++ dbgQSshow (i+1) qs
   ++ concat (map (dbgEshow (i+1)) es)
dbgEshow i (ESub e sub)
 = hdr i ++ "ESUB "++dbgESshow (i+1) sub ++ dbgEshow (i+1) e

dbgKshow VObs = "VOBS"
dbgKshow VExpr = "VEXP"
dbgKshow VPred = "VPRD"
dbgKshow VScript = "VSCRPT"
dbgKshow (VList k) = "LSTV "++dbgKshow k

dbgRshow VStatic = "VSTATIC"
dbgRshow VPre = "VPRE"
dbgRshow VPost = "VPOST"
dbgRshow VRel = "VREL"
dbgRshow (VInter s) = "VINTER "++s

dbgVshow (n,k,r,ns) = dbgKshow k
                    ++ ' ':n
                    ++ ' ':dbgRshow r
                    ++ ' ':show ns

dbgVSshow vs = "<"
               ++ (concat $ intersperse ">, <" $ map dbgVshow vs)
               ++ ">"

debugQSshow :: QVars -> String
debugQSshow = dbgQSshow 0

dbgQSshow i ( [])  = hdr i ++ "QVARS(empty)"
dbgQSshow i ( qs)
 = hdr i ++ "QVARS:"
   ++ (concat $ map ( (hdr (i+1) ++) . dbgVshow ) qs)


dbgMshow i (x,y) = hdr i ++ "DOM" ++ dbgEshow (i+1) x ++ hdr i ++ "RNG" ++ dbgEshow (i+1) y

dbgESshow :: Int -> ESubst -> String
dbgESshow i (Substn sub)
  = hdr i ++ "E-SUBSTN" ++ dbgSshow dbgVshow dbgEshow (i+1) sub

dbgPSshow :: Int -> PSubst -> String
dbgPSshow i (Substn sub)
  = hdr i ++ "P-SUBSTN" ++ dbgSshow dbgVshow dbgPshow (i+2) sub

dbgSshow :: (v -> String) -> (Int -> a -> String) -> Int -> [(v,a)]
         -> String
dbgSshow shv shth i  [] = ""
dbgSshow shv shth i ((v,thing):rest)
 = hdr i ++ shv v ++ "  |->" ++ shth (i+3) thing
   ++ dbgSshow shv shth i rest

dbgTshow i Tarb = hdr i ++ "TARB"
dbgTshow i (Tvar s) = hdr i ++ "TVAR "++s
dbgTshow i (TApp s ts) = hdr i ++ "TAPP "++s ++ concat(map (dbgTshow (i+1)) ts)
dbgTshow i (Tfree s cs) = hdr i ++ "TFREE "++s ++ concat(map (dbgFshow (i+1)) cs)
dbgTshow i (Tfun t1 t2) = hdr i ++ "TFUN" ++ dbgTshow (i+1) t1 ++ dbgTshow (i+1) t2
dbgTshow i Tenv = hdr i ++ "TENV"
dbgTshow i Z = hdr i ++ "TINT"
dbgTshow i B = hdr i ++ "TBOOL"
dbgTshow i (Terror s t) = hdr i ++ "TERROR "++s++dbgTshow (i+1) t

dbgFshow i (s,ts) = hdr i ++ "CONS "++s++concat(map (dbgTshow (i+1)) ts)

dbgSCshow i SCtrue
  =  hdr i ++ "SC-TRUE"
dbgSCshow i (SCisCond mtyp str)
  =  hdr i ++ "SC-ISCOND "++show mtyp++" "++str
dbgSCshow i (SCnotFreeIn mtyp qs str)
  =  hdr i ++ "SC-NOTFREEIN "++show mtyp++" "++dbgVSshow qs++" "++str
dbgSCshow i (SCareTheFreeOf mtyp qs str)
  =  hdr i ++ "SC-ARETHEFREEOF "++show mtyp++" "++dbgVSshow qs++" "++str
dbgSCshow i (SCcoverTheFreeOf mtyp qs str)
  =  hdr i ++ "SC-COVERTHEFREEOF "++show mtyp++" "++dbgVSshow qs++" "++str
dbgSCshow i (SCfresh mtyp str)
  =  hdr i ++ "SC-FRESH "++show mtyp++" "++dbgVshow str
dbgSCshow i (SCAnd scs)
  =  hdr i ++ "SC-AND" ++ concat(map (dbgSCshow (i+1)) scs)
\end{code}


\newpage
\subsection{Side-Conditions}

A side-condition is a syntactic property,
and therefore in principle ought to be statically checkable.
\begin{code}
data MType = ObsM | TypeM | ExprM | PredM deriving (Eq,Ord)

instance Show MType where
  show ObsM = "O"
  show TypeM = "T"
  show ExprM = "E"
  show PredM = "P"

data SideCond
 = SCtrue
 | SCisCond MType String                     -- Mvar
 | SCnotFreeIn MType [Variable] String       -- Qvars, Mvar
 | SCareTheFreeOf MType [Variable] String    -- Qvars, Mvar
 | SCcoverTheFreeOf MType [Variable] String  -- Qvars, Mvar
 | SCfresh MType Variable                    -- ObsM for now
 | SCAnd [SideCond]
 deriving (Eq,Ord,Show)

scMetaType (SCisCond m _)            =  m
scMetaType (SCnotFreeIn m _ _)       =  m
scMetaType (SCareTheFreeOf m _ _)    =  m
scMetaType (SCcoverTheFreeOf m _ _)  =  m
scMetaType (SCfresh m _)             =  m

scMetaVar (SCisCond _ mvar)            =  mvar
scMetaVar (SCnotFreeIn _ _ mvar)       =  mvar
scMetaVar (SCareTheFreeOf _ _ mvar)    =  mvar
scMetaVar (SCcoverTheFreeOf _ _ mvar)  =  mvar

isCondP pn = SCisCond PredM pn
isCondE en = SCisCond ExprM en
v `notPfree` pn = SCnotFreeIn PredM [v] pn
v `notEfree` en = SCnotFreeIn ExprM [v] en
vs `arentPfree` pn = SCnotFreeIn PredM vs pn
vs `arentEfree` en = SCnotFreeIn ExprM vs en
vs `areFreeOfP` pn = SCareTheFreeOf PredM vs pn
vs `coverFreeOfP` pn = SCcoverTheFreeOf PredM vs pn
vs `areFreeOfE` en = SCareTheFreeOf ExprM vs en
vs `coverFreeOfE` en = SCcoverTheFreeOf ExprM vs en
isFreshP pn = SCfresh ObsM pn
isFreshE en = SCfresh ObsM en
scand scs
 = mkand $ filter (/= SCtrue) $ concat $ map flatten scs
 where
   flatten (SCAnd scs) = concat $ map flatten scs
   flatten sc = [sc]
   mkand [] = SCtrue
   mkand [sc] = sc
   mkand scs = SCAnd $ lnorm scs
\end{code}

\newpage
\subsection{Assertions/Laws}

An assertion is simply a predicate,
with an attached side condition, which is syntactic in nature.
\begin{code}
type Assertion = (Pred,SideCond)
\end{code}

\input{doc/Datatypes-Provenance}

\begin{code}
data Provenance
 = FromUSER String
 | ViaPROOF [Provenance] -- contents never ViaPROOF, unique, ordered
 | UserDEFN String
 | FromSOURCE String
 deriving (Eq,Ord)

  -- ViaPROOF contents are never themselves ViaPROOF
  -- also they are ordered with no duplicates
  -- we provide a special constructor:

viaPROOF = ViaPROOF . lnorm . concat . map stripViaProof
stripViaProof (ViaPROOF provs) = provs
stripViaProof prov = [prov]
\end{code}

We use simple pretty-printing:
\begin{code}
instance Show Provenance where
 show (FromSOURCE src) = "SOURCE:"++src
 show (ViaPROOF prv) = "Proof."++(concat $ intersperse "," $ map show  prv)
 show (FromUSER user) = "user'"++user++"'"
 show (UserDEFN user) = "DEFN'"++user++"'"

instance Dshow Provenance where dshow = show

shortProv (FromSOURCE _) = "S"
shortProv (ViaPROOF pvs) = 'P':(lnorm $ concat $ map shortProv pvs)
shortProv (FromUSER _) = "U"
shortProv (UserDEFN _) = "D"

isUserProv (FromUSER _) = True
isUserProv (UserDEFN _) = True
isUserProv _            = False

isUserLaw = isUserProv . snd
\end{code}

A law is an assertion coupled with a provenance
and a type-table
\begin{code}
type Law = (Assertion,Provenance,TypeTables)
\end{code}





\subsection{Alphabets}

An alphabet is a set of names simply represented as a \texttt{Trie} of unit:
\begin{code}
type Alphabet = Trie ()

mkAlpha  = lbuild . map (flip(,)())

mofA v alpha = isJust (tlookup alpha v)

isInA  ""  =  False
isInA   v  =  last v /= '\''
isOutA ""  =  False
isOutA  v  =  last v == '\''

inAlpha   = mkAlpha . filter isInA  . trieDom
outAlpha  = mkAlpha . filter isOutA . trieDom
\end{code}


\subsection{Parts}


For debugging it is useful to be able to take predicates
and expressions apart:
\begin{code}
predParts :: Pred -> (String,[Pred],[Expr],[QVars],[Type])
predParts TRUE = ("TRUE",[],[],[],[])
predParts FALSE = ("FALSE",[],[],[],[])
predParts (PVar pv) = ("PVar-"++varKey pv,[],[],[],[])
predParts (PExpr e) = ("PExpr",[],[e],[],[])

predParts (Sub (PExpr e) sub@(Substn ssub))
   = ( "(e)Sub"
     , []
     , [ESub e sub]
     , [map fst ssub]
     , []
     )
predParts (Sub pr (Substn ssub))
   = ( "Sub"
     , [pr]
     , map snd ssub
     , [map fst ssub]
     , []
     )

predParts _ = ("pred",[],[],[],[])

predNPart  = fst5 . predParts
predPParts = snd5 . predParts
predEParts = thd5 . predParts
predQParts = frt5 . predParts
predTParts = fth5 . predParts
\end{code}

Generally we pull out expressions using \texttt{predParts},
and collecting top-level expressions before those
in sub-predicates.
\begin{code}
exprParts :: Expr -> (String,[Pred],[Expr],[QVars])
exprParts (Num _)          =  ("Num",[],[],[])
exprParts (Var (n,_,_,_))  =  ("Var:"++n,[],[],[])
exprParts (App s es)       =  ("App",[],es,[])
exprParts (Abs s _ qs es)  =  ("Abs",[],es,[qs])
exprParts (ESub e (Substn ssub))
  = ( "ESub"
    , []
    , e:(map snd ssub)
    , [map fst ssub]
    )
exprParts _ = ("expr",[],[],[])

exprNPart  = fst4 . exprParts
exprPParts = snd4 . exprParts
exprEParts = thd4 . exprParts
exprQParts = frt4 . exprParts
\end{code}

Generally we pull out predicates from expressions using \texttt{exprParts},
and collecting top-level predicates before those
in sub-expressions.
\begin{code}
predsOf e
 = let (_,prs,es,_) = exprParts e
   in prs ++ (concat $ map predsOf es)
\end{code}

Similarly we pull out expressions from predicates using \texttt{predParts},
and collecting top-level predicates before those
in sub-expressions.
\begin{code}
exprsOf pr
 = let (_,prs,es,_,_) = predParts pr
   in es ++ (concat $ map exprsOf prs)
\end{code}

\subsubsection{PVar table building}

Building tables from \texttt{PVar}-value lists:
\begin{code}
plupdate :: Trie t -> [(Pred, t)] -> Trie t
plupdate = foldr mkpentry
mkpentry (PVar pv,t) trie = tupdate (varKey pv) t trie
mkpentry _          trie = trie
\end{code}
