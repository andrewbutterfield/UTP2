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
 deriving (Eq,Ord)

nonTypeCons Tarb      =  True
nonTypeCons (Tvar _)  =  True
nonTypeCons Tenv      =  True
nonTypeCons Z         =  True
nonTypeCons B         =  True
nonTypeCons _         =  False
\end{code}

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


\subsection{Variables}

\input{doc/Variable-Syntax}

A variable has a root and decoration.
\begin{code}
data GenRoot = Std String       -- single (Standard) variable
             | Lst String       -- List variables
             deriving (Eq,Ord)

data RsvRoot = OBS  -- all observations
             | MDL  -- model observations
             | SCR  -- script observations
             deriving (Eq,Ord)

data Root = Gen GenRoot
          | Rsv RsvRoot [GenRoot]
          deriving (Eq,Ord)

data Decor
 = NoDecor    -- for variable were decoration is irrelevant
 | Pre
 | Post
 | Subscript String
 | Scrpt             -- script variables, know or unknown
 deriving (Eq,Ord)

type Variable = ( Root      -- variable (main) root
                , Decor     -- variable decoration
                , String    -- text representation (used as table key)
                )
type Vs = [Variable]
\end{code}

Variable utility code.
First three are used to create non-parseable error variables"
\begin{code}
gmap :: (String -> String) -> GenRoot -> GenRoot
gmap f (Std s) = Std $ f s
gmap f (Lst s) = Lst $ f s

rmap :: (String -> String) -> Root -> Root
rmap f (Gen g) = Gen $ gmap f g
rmap _ r@(Rsv _ _) = r

varmap :: (String -> String) -> Variable -> Variable
varmap f (r,d,k) = (rmap f r,d,f k)

isStdG,isLstG :: GenRoot -> Bool
isStdG (Std _)  =  True
isStdG _        =  False
isLstG (Std _)  =  False
isLstG _        =  True

isStdR,isLstR :: Root -> Bool
isStdR (Gen (Std _))  =  True
isStdR _              =  False
isLstR (Gen (Std _))  =  False
isLstR _              =  True
\end{code}

We adopt the following ASCII representations of these variables:

\begin{tabular}{|c|c||c|c|}
  \hline
  % after \\: \hline or \cline{col1-col2} \cline{col3-col4} ...
  $Obs$ & \verb"O" & $Obs'$ & \verb"O'" \\\hline
  $Mdl$ & \verb"M" & $Mdl'$ & \verb"M'" \\\hline
  $Scr$ & \verb"S" & $Scr'$ & \verb"S'" \\
  \hline
\end{tabular}
List variables are distinguished from ordinary variables by a postfix $\lst{}$
(e.g. $\lst x$).

In effect, \texttt{O}, \texttt{S} and \texttt{M} are reserved variable roots.
\begin{code}
listVarFlag = '$'

chrOBS = 'O'
chrMDL = 'M'
chrSCR = 'S'
strOBS = [chrOBS]
strMDL = [chrMDL]
strSCR = [chrSCR]
strOMS = [chrOBS,chrMDL,chrSCR]

genRootString :: GenRoot -> String
genRootString (Std s)  =  s
genRootString (Lst s)  =  s ++ [listVarFlag]

rootString :: Root -> String
rootString (Gen r)  =  genRootString r
rootString (Rsv OBS grs)    =  strOBS ++ lessString grs
rootString (Rsv MDL grs)    =  strMDL ++ lessString grs
rootString (Rsv SCR grs)    =  strSCR ++ lessString grs
lessString [] = ""
lessString grs = '\\':(concat $ intersperse ":" $ map genRootString grs)

stringToRoot :: String -> Root -- accepts ill-formed roots !!!
stringToRoot  s
  | null s                 =  Gen $ Std s
  | s == strOBS            =  Rsv OBS []
  | s == strMDL            =  Rsv MDL []
  | s == strSCR            =  Rsv SCR []
  | last s == listVarFlag  =  Gen $ Lst (init s)
  | otherwise              =  Gen $ Std s

forceLst :: String -> Root  -- make it a listvar, even if last $ is missing
forceLst  s
  | null s                 =  Gen $ Lst s
  | s == strOBS            =  Rsv OBS []
  | s == strMDL            =  Rsv MDL []
  | s == strSCR            =  Rsv SCR []
  | last s == listVarFlag  =  Gen $ Lst (init s)
  | otherwise              =  Gen $ Lst s

varRoot :: Variable -> Root
varRoot (r,_,_) = r
varGenRoot :: Variable -> GenRoot
varGenRoot (Gen g,_,_) = g
varGenRoot (r@(Rsv _ _),_,_) = Lst ('!':rootString r)
varDecor :: Variable -> Decor
varDecor (_,d,_) = d
varLess :: Variable -> [GenRoot]
varLess (Rsv _ rs,_,_) = rs
varLess (_,_,_) = []
varKey :: Variable -> String
varKey (_,_,s) = s

varRootAsString :: Variable -> String -- ignores decoration, etc..
varRootAsString = rootString . varRoot

isStdV,isLstV,isGenV,isRsvV :: Variable -> Bool

isStdV (Gen (Std _), _, _)  =  True
isStdV _                    =  False

isLstV (Gen (Std _), _, _)  =  False
isLstV _                    =  True

isGenV (Gen (Lst _), _, _)  =  True
isGenV _                    =  False

isRsvV (Rsv _ _, _, _)    =  True
isRsvV _                    =  False

isStdS,isLstS,isRsv :: String -> Bool -- roots only

isStdS ""   =  False
isStdS [c]  =  not(c `elem` strOMS)
isStdS (c:n:_)
 | c `elem` strOMS && not (isAlphaNum n) = False
isStdS s    =  last s /= listVarFlag

isLstS ""   =  False
isLstS [c]  =  c `elem` strOMS
isLstS (c:n:_)
 | c `elem` strOMS && not (isAlphaNum n) = True
isLstS s    =  last s == listVarFlag

isRsv [c]   =  c `elem` strOMS
isRsv _     =  False

normalVariable, noDecorVariable :: String -> Variable
normalVariable  s   =  (stringToRoot s, Pre,     s)
noDecorVariable  s  =  (stringToRoot s, NoDecor, s)
nullVar = noDecorVariable ""

rootAsVar :: Root -> Variable
rootAsVar r = (r,NoDecor,rootString r)
genRootAsVar :: GenRoot -> Variable
genRootAsVar = rootAsVar . Gen
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
We want support for \texttt{GenRoot} lookups as well:
\begin{code}
tglookup :: Trie t -> GenRoot -> Maybe t
tglookup trie = tlookup trie . genRootString

tsglookup :: [Trie t] -> GenRoot -> Maybe t
tsglookup tries = tslookup tries . genRootString

tgupdate :: GenRoot -> t -> Trie t -> Trie t
tgupdate g a trie = tupdate (genRootString g) a trie
\end{code}

We will often want to split variable lists into
two: the standard variables, and the rest.
Also, list variables can be split into general, and reserved.
\begin{code}
vPartition :: [Variable] -> ([Variable],[Variable])
vPartition = partition isStdV
rPartition :: [Variable] -> ([Variable],[Variable])
rPartition = partition isRsvV
\end{code}



\subsection{Quantifier Variables}

We want to be able to match predicates and expressions
against laws involving quantifiers in a flexible manner,
so we need to represent quantified variables, and lists of them
as well as variables that can match against these.
Generally we want to match against a specified list of
variables, and then ``all the rest''.
\begin{code}
data QVars
 = Q{outQ::[Variable]}
 deriving (Eq,Ord)

mkQ :: [Variable] -> QVars
mkQ = Q . lnorm

snglQ :: Variable -> QVars
snglQ v = Q [v]

qvarmrg (Q qs) (Q rs) = mkQ (qs++rs)

qsmrg :: QVars -> QVars -> QVars -- no normalisation for subst-lists!
(Q qs) `qsmrg` (Q rs)  = Q (qs ++ rs)

-- except when we explicitly want it!
(Q as) `mrgqnorm` (Q bs) = Q (as `mrgnorm` bs)
\end{code}

We get observation variables  and ``multiple'' meta-variables
from quantifier lists:
\begin{code}
getqovars = filter isStdV . outQ
getqqvars = filter isLstV . outQ
getqvars  = outQ

lqnorm :: QVars -> QVars
lqnorm = Q . lnorm . outQ
\end{code}
(Normalising these lists is also useful)



\subsection{Substitutions}

Substitutions associate a list of things (types,expressions,predicates)
with some (quantified) variables.
This is just
\begin{code}
data Substn v a
 = Substn [( v   -- variable type
           , a   -- replacement object
           )]
 deriving (Eq,Ord)

type VSubst = Substn Variable Variable
type TSubst = Substn String   Type
type ESubst = Substn Variable Expr
type PSubst = Substn GenRoot  Pred
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
as well as a destructor that returns QVars:
\begin{code}
mkQsubst as xs = Substn $ zip xs as

mkSubQ (Substn ssub) =  map fst ssub
\end{code}

It is useful to be able to partition substitutions on Variables
between those that are standard and those that are list:
\begin{code}
sPartition :: [(Variable,a)] -> ([(Variable,a)],[(Variable,a)])
sPartition = partition (isStdV . fst)
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


\subsection{Expressions}

\begin{code}
data Expr
 = T
 | F
 | Num Int
 | Var Variable
 | Prod [Expr]
 | App String Expr
 | Bin String Int Expr Expr
 | Equal Expr Expr
 | Set [Expr]
 | Setc TTTag QVars Pred Expr
 | Seq [Expr]
 | Seqc TTTag QVars Pred Expr
 | Map [(Expr,Expr)]
 | Cond Pred Expr Expr
 | Build String [Expr]
 | The TTTag Variable Pred -- definite description
 | Evar Variable -- meta-variable denoting an expression (or list)
 | Eabs TTTag QVars Expr -- a lambda abstraction
 | Esub Expr ESubst
 | Eerror String
 | Efocus Expr -- expression focus marker
 | EPred Pred  -- converse of 'Obs'
               -- EPred $ Obs e   =  e
               -- Obs $ EPred pr  =  pr



instance Eq Expr where -- we ignore type-table and focus parts
 T           == T            =  True
 F           == F            =  True
 (Num i)     == (Num j)      =  i == j
 (Var u)     == (Var v)      =  u == v
 (Prod es)   == (Prod fs)    =  es == fs
 (App str e) == (App txt f)  =  str == txt && e == f
 (Bin str i e1 e2) == (Bin txt j f1 f2)
                     =  str == txt && i == j && e1 == f1 && e2 == f2
 (Equal e1 e2) == (Equal f1 f2)  =  e1 == f1 && e2 == f2
 (Set es)      == (Set fs)       =  es == fs
 (Setc _ qus p e) == (Setc _ qvs q f)
                                   =  qus == qvs && p == q && e == f
 (Seq es)  == (Seq fs)  =  es == fs
 (Seqc _ qus p e) == (Seqc _ qvs q f)
                                   =  qus == qvs && p == q && e == f
 (Map abs)      == (Map cds)       =  abs == cds
 (Cond p e1 e2) == (Cond q f1 f2)  =  p == q && e1 == f1 && e2 == f2
 (Build str es) == (Build txt fs)  =  str == txt && es == fs
 (The _ str p)  == (The _ txt q)   =  p == q && str == txt
 (Evar str)     == (Evar txt)      =  str == txt
 (Eabs _ qus e) == (Eabs _ qvs f)  =  e == f && qus == qvs
 (Esub e esub)  == (Esub f fsub)   =  e == f && esub == fsub
 (Eerror str)   == (Eerror txt)    =  str == txt
 (Efocus e)     == (Efocus f)      =  e == f
 (Efocus e)     == f               =  e == f
 e              == (Efocus f)      =  e == f
 (EPred p)      == (EPred q)       =  p == q
 _              == _ = False

deriving instance Eq Expr => Ord Expr
\end{code}

We need some builders that perform
tidying up for corner cases:
\begin{code}
noDecorVar = Var . noDecorVariable

mkProd [e] = e
mkProd es = Prod es

mkSetc (Q []) _ _  = Set []
mkSetc qvs p e = Setc 0 qvs p e

mkSeqc (Q []) _ _  = Seq []
mkSeqc qvs p e = Seqc 0 qvs p e

mkEabs (Q []) e = e
mkEabs qvs e = Eabs 0 qvs e

mkEsub e (Substn []) = e
mkEsub e sub = Esub e sub
\end{code}

Drop is  useful:
\begin{code}
eDrop (Var v)   =  v
eDrop (Evar e)  =  e
eDrop _         =  (Gen $ Std ee, NoDecor, ee) where ee = "eDrop?"
\end{code}

Useful to know when an expression is a variable:
\begin{code}
isVar :: Expr -> Bool
isVar (Var _)   =  True
isVar (Evar _)  =  True
isVar _         =  False

getVar :: Expr -> Variable
getVar (Var v)   =  v
getVar (Evar v)  =  v
getVar _         =  nullVar

mgetVar :: Expr -> Maybe Variable
mgetVar (Var v)   =  Just v
mgetVar (Evar v)  =  Just v
mgetVar _         =  Nothing
\end{code}

\newpage
\subsection{Predicates}

Monadic(?) 2nd-order logic syntax
with fundamental UTP operators explicitly represented
($;$, $\cond{}$, $\refinedby$ and $\intchoice$),
and general facilities for syntax extensions to cover
programming and specification constructs.

\begin{code}
data Pred
 = TRUE
 | FALSE
 | Obs Expr
 | Defd Expr
 | TypeOf Expr Type
 | Not Pred
 | And [Pred]
 | Or [Pred]
 | Imp Pred Pred
 | Eqv Pred Pred
 | Forall TTTag QVars Pred
 | Exists TTTag QVars Pred
 | Exists1 TTTag QVars Pred
 | Univ TTTag Pred
 | Sub Pred ESubst
 | Pvar GenRoot -- predicate meta-variable
 -- UTP fundamentals ("open" language constructs)
 | If Pred Pred Pred
 | NDC Pred Pred
 | RfdBy Pred Pred
 -- Language extensions (Lexts)
 | Lang String    -- construct name
        Int       -- precedence, if binary
        [LElem]   -- Language elements
        [SynSpec] -- Interleaving Tokens
 -- higher order stuff (logic)
 | Pforall QVars Pred  -- !!! [GenRoot]
 | Pexists QVars Pred  -- !!! [GenRoot]
 | Psub Pred PSubst
 | Psapp Pred PredSet  -- Predicate set-application
 | Psin Pred PredSet   -- Predicate set-membership
 -- higher order stuff (functions)
 | Peabs QVars Pred  -- abstracting over expression variables
 | Ppabs QVars Pred  -- abstracting over predicate variables !! [GenRoot] !!!
 | Papp Pred Pred
 | Perror String
 | Pfocus Pred   -- predicate focus marker

instance Eq Pred where -- we ignore type-tables and focus
 TRUE              == TRUE               =  True
 FALSE             == FALSE              =  True
 (Obs e)           == (Obs f)            =  e == f
 (Defd e)          == (Defd f)           =  e == f
 (TypeOf e t)      == (TypeOf f u)       =  e == f && t == u
 (Not p)           == (Not q)            =  p == q
 (And ps)          == (And qs)           =  ps == qs
 (Or ps)           == (Or qs)            =  ps == qs
 (Imp p1 p2)       == (Imp q1 q2)        =  p1 == q1 && p2 == q2
 (Eqv p1 p2)       == (Eqv q1 q2)        =  p1 == q1 && p2 == q2
 (Forall _ qus p)  == (Forall _ qvs q)   =  p == q && qus == qvs
 (Exists _ qus p)  == (Exists _ qvs q)   =  p == q && qus == qvs
 (Exists1 _ qus p) == (Exists1 _ qvs q)  =  p == q && qus == qvs
 (Univ _ p)        == (Univ _ q)         =  p == q
 (Sub p esub)      == (Sub q fsub)       =  p == q && esub == fsub
 (Pvar str)        == (Pvar txt)         =  str == txt
 (If pc pt pe) == (If qc qt qe)  =  pc == qc && pt == qt && pe == qe
 (NDC p1 p2)        == (NDC q1 q2)    =  p1 == q1 && p2 == q2
 (RfdBy p1 p2)      == (RfdBy q1 q2)  =  p1 == q1 && p2 == q2
 (Lang str i ls ss) == (Lang txt j ks ts)
   =  str == txt && i == j && ls == ks && ss == ts
 (Pforall qus p) == (Pforall qvs q)  =  qus == qvs && p == q
 (Pexists qus p) == (Pexists qvs q)  =  qus == qvs && p == q
 (Psub p psub)   == (Psub q qsub)    =  p == q && psub == qsub
 (Psapp p pset)  == (Psapp q qset)   =  p == q && pset == qset
 (Psin p pset)   == (Psin q qset)    =  p == q && pset == qset
 (Peabs qus p)   == (Peabs qvs q)    =  qus == qvs && p == q
 (Ppabs qus p)   == (Ppabs qvs q)    =  p == q && qus == qvs
 (Papp p1 p2)    == (Papp q1 q2)     =  p1 == q1 && p2 == q2
 (Perror str)    == (Perror txt)     =  str == txt
 (Pfocus p)      == (Pfocus q)       =  p == q
 (Pfocus p)      == q                =  p == q
 p               == (Pfocus q)       =  p == q
 _               == _                =  False

deriving instance Eq Pred => Ord Pred
\end{code}

We define two constructor functions to handle the \texttt{Expr}/\texttt{Pred} ``crossovers'':
\begin{code}
ePred (Obs e)    = e
ePred pr         = EPred pr
pExpr (EPred pr) = pr
pExpr e          = Obs e
\end{code}

We also define smart constructors for certain constructs
to deal with corner cases:
\begin{code}
mkAnd [] = TRUE
mkAnd [pr] = pr
mkAnd prs = And prs

mkOr [] = FALSE
mkOr [pr] = pr
mkOr prs = Or prs

mkForall (Q []) p = p
mkForall qvs (Imp TRUE p) = Forall 0 qvs p
mkForall qvs p = Forall 0 qvs p

mkExists (Q []) p = p
mkExists qvs (And [TRUE,p]) = Exists 0 qvs p
mkExists qvs p = Exists 0 qvs p

mkExists1 (Q []) p = FALSE
mkExists1 qvs p = Exists1 0 qvs p

mkSub p (Substn []) = p
mkSub p sub = Sub p sub

mkPforall (Q []) p  = p
mkPforall qvs p = Pforall qvs p

mkPexists (Q []) p  = p
mkPexists qvs p = Pexists qvs p

mkPsub p (Substn []) = p
mkPsub p sub = Psub p sub

mkPeabs (Q []) p  = p
mkPeabs qvs p = Peabs qvs p

mkPpabs (Q []) p  = p
mkPpabs qvs p = Ppabs qvs p
\end{code}
Some query functions:
\begin{code}
isObs (Obs _) = True
isObs _       = False
\end{code}
Drop is handy:
\begin{code}
pDrop (Pvar p) = p
pDrop _ = Std "?pDrop"
\end{code}


\subsection{Predicate Sets}

We need a simple syntax for predicate sets:
\begin{eqnarray*}
  S \in PredSet
  &::=& N
      | \{ P_1, \ldots , P_n \}
      | \{ N_1,\ldots,N_n | R @ P \}
      | S_1 \cup S_2
\end{eqnarray*}
\begin{code}
data PredSet
 = PSName String
 | PSet [Pred]
 | PSetC QVars Pred Pred
 | PSetU PredSet PredSet
 deriving (Eq,Ord)
\end{code}


\subsection{Language Constructs}

We provide general support in predicates for language
constructs, which are built from variables, types, expressions
and predicates (which may include further sub-constructs).

A Language element identifies a language component
\begin{code}
data LElem
 = LVar GenRoot -- we don't need decorations for script variables!
 | LType Type
 | LExpr Expr
 | LPred Pred
 | LList [LElem] -- all of same type
 | LCount [LElem] -- same type, also same length
 deriving (Eq,Ord)

isLELstV :: LElem -> Bool
isLELstV (LVar g)          =  isLstG g
isLELstV (LExpr (Var v))   =  isLstV v
isLELstV (LExpr (Evar e))  =  isLstV e
isLELstV _                 =  False

isLEVar :: LElem -> Bool
isLEVar (LVar _)               =  True
isLEVar (LExpr (Var _))        =  True
isLEVar (LPred (Obs (Var _)))  =  True
isLEVar _                      =  False

isLEExpr :: LElem -> Bool
isLEExpr (LVar _)         =  True
isLEExpr (LExpr _)        =  True
isLEExpr (LPred (Obs _))  =  True
isLEExpr _                =  False
\end{code}

We need to surround language elements by a syntax specification:
\begin{code}
data SynSpec
 = SSNull
 | SSTok String
 | SSSep String
 deriving (Eq,Ord)
\end{code}

A Language Specification is a pairing of two lists,
one of \texttt{LElem}, the other of \texttt{SynSpec}:
\begin{code}
data LangSpec = LangSpec [LElem] [SynSpec] deriving (Eq,Ord)
\end{code}


\subsection{Equality}

We want to define equality that ignores type-inference markings
(\texttt{TTTag}s).

We want to compare two predicates for equality,
 modulo ``liberal type equivalence''
\begin{code}
pequiv :: Pred -> Pred -> Bool

pequiv TRUE TRUE = True
pequiv FALSE FALSE = True
pequiv (Obs e1) (Obs e2) = e1 `eequiv` e2
pequiv (Defd e1) (Defd e2) = e1 `eequiv` e2
pequiv (TypeOf e1 t1) (TypeOf e2 t2)
 = e1 `eequiv` e2 && t1 `tequiv` t2

pequiv (Not pr1) (Not pr2) = pr1 `pequiv` pr2
pequiv (And prs1) (And prs2) = samelist pequiv prs1 prs2
pequiv (Or prs1) (Or prs2) = samelist pequiv prs1 prs2
pequiv (NDC pr11 pr21) (NDC pr12 pr22) = samelist pequiv [pr11,pr21] [pr12,pr22]
pequiv (Imp pr11 pr21) (Imp pr12 pr22) = samelist pequiv [pr11,pr21] [pr12,pr22]
pequiv (RfdBy pr11 pr21) (RfdBy pr12 pr22) = samelist pequiv [pr11,pr21] [pr12,pr22]
pequiv (Eqv pr11 pr21) (Eqv pr12 pr22) = samelist pequiv [pr11,pr21] [pr12,pr22]
pequiv (If prc1 prt1 pre1) (If prc2 prt2 pre2)
  = samelist pequiv [prc1,prt1,pre1] [prc2,prt2,pre2]
pequiv (Univ _ pr1) (Univ _ pr2) = pr1 `pequiv` pr2

pequiv (Forall _ qs1 pr1) (Forall _ qs2 pr2)
 = qs1==qs2 && pequiv pr1 pr2
pequiv (Exists _ qs1 pr1) (Exists _ qs2 pr2)
 = qs1==qs2 && pequiv pr1 pr2
pequiv (Exists1 _ qs1 pr1) (Exists1 _ qs2 pr2)
 = qs1==qs2 && pequiv pr1 pr2

pequiv (Sub pr1 sub1) (Sub pr2 sub2) = pr1 `pequiv` pr2 && sub1 `estlequiv` sub2

pequiv (Psub pr1 sub1) (Psub pr2 sub2) = pr1 `pequiv` pr2 && sub1 `pstlequiv` sub2

pequiv (Lang n1 p1 lelems1 syn1) (Lang n2 p2 lelems2 syn2)
   = n1 == n2 && p1 == p2 && syn1 == syn2 && samelist ltlequiv lelems1 lelems2

pequiv (Pvar s1) (Pvar s2) = s1==s2
pequiv (Peabs s1 pr1) (Peabs s2 pr2) = s1==s2 && pr1 `pequiv` pr2
pequiv (Ppabs s1 pr1) (Ppabs s2 pr2) = s1==s2 && pr1 `pequiv` pr2
pequiv (Papp prf1 pra1) (Papp prf2 pra2) = samelist pequiv [prf1,pra1] [prf2,pra2]

pequiv _ _ = False
\end{code}

And for expressions:
\begin{code}
eequiv :: Expr -> Expr -> Bool

eequiv T T = True
eequiv F F = True
eequiv (Num i1) (Num i2) = i1==i2
eequiv (Var v1) (Var v2) = v1==v2
eequiv (Prod es1) (Prod es2) = samelist eequiv es1 es2
eequiv (App s1 e1) (App s2 e2) = s1==s2 && e1 `eequiv` e2
eequiv (Bin s1 i1 e11 e21) (Bin s2 i2 e12 e22)
 = s1==s2 && i1==i2 && samelist eequiv [e11,e21] [e12,e22]
eequiv (Equal e11 e21) (Equal e12 e22) = samelist eequiv [e11,e21] [e12,e22]
eequiv (Set es1) (Set es2) = samelist eequiv es1 es2
eequiv (Setc _ qs1 pr1 e1) (Setc _ qs2 pr2 e2)
 = qs1==qs2 && pr1 `pequiv` pr2 && e1 `eequiv` e2
eequiv (Seq es1) (Seq es2) = samelist eequiv es1 es2
eequiv (Seqc _ qs1 pr1 e1) (Seqc _ qs2 pr2 e2)
 = qs1==qs2 && pr1 `pequiv` pr2 && e1 `eequiv` e2
eequiv (Map drs1) (Map drs2)
 = samelist eequiv (ds1++rs1) (ds2++rs2)
 where
  (ds1,rs1) = unzip drs1
  (ds2,rs2) = unzip drs2
eequiv (Cond pc1 et1 ee1) (Cond pc2 et2 ee2)
 =   pc1 `pequiv` pc2 && samelist eequiv [et1,ee1] [et2,ee2]
eequiv (Build s1 es1) (Build s2 es2) = s1==s2 && samelist eequiv es1 es2
eequiv (The _ qs1 pr1) (The _ qs2 pr2) = qs1==qs2 && pequiv pr1 pr2
eequiv (Evar s1) (Evar s2) = s1==s2
eequiv (Eabs _ qs1 e1) (Eabs _ qs2 e2) = qs1==qs2 && e1 `eequiv` e2
eequiv (Esub e1 sub1) (Esub e2 sub2)
 = e1 `eequiv` e2 && sub1 `estlequiv`  sub2

eequiv _ _ = False
\end{code}

Substitution equivalence:
\begin{code}
estlequiv (Substn ssub1)  (Substn ssub2) = samealist eequiv ssub1 ssub2

pstlequiv (Substn ssub1)  (Substn ssub2) = samealist pequiv ssub1 ssub2
\end{code}

And for language constructs:
\begin{code}
ltlequiv :: LElem -> LElem -> Bool

ltlequiv (LVar s1)   (LVar s2)    =  s1 == s2
ltlequiv (LType t1)  (LType t2)   =  t1 `tequiv` t2
ltlequiv (LExpr e1)  (LExpr e2)   =  e1 `eequiv` e2
ltlequiv (LPred pr1) (LPred pr2)  =  pr1 `pequiv` pr2
ltlequiv (LList l1)  (LList l2)   =  samelist ltlequiv l1 l2
ltlequiv (LCount l1) (LCount l2)  =  samelist ltlequiv l1 l2
\end{code}

For now:
\begin{code}
tequiv = (==)
\end{code}



\newpage
\subsection{Focus Datatypes}

``Focus'' is the mechanism for restricting attention
to part of a predicate or expression.
It is supported by both the \texttt{Expr} and \texttt{Pred}
in that they have constructors to mark the focus
datatypes:
\begin{verbatim}
 data Expr = ...
  | Efocus Expr
 data Pred = ...
  | Pfocus  Pred
\end{verbatim}


\subsubsection{Focus Context}

Contexts, associated with predicate-focii,
provide useful information about how the focus
is situated within the top-level predicate.
At present we:
\begin{itemize}
    \item indicate the polarity of the focus w.r.t the implication ordering;
    \item list the object variable bindings encountered on the way to the focus.
\end{itemize}

\paragraph{Polarity}

\begin{code}
data Polarity = Pos | Neg | Mxd deriving (Eq,Ord)

polneg Pos = Neg
polneg Neg = Pos
polneg Mxd = Mxd

instance Show Polarity where
 show Pos = "+ve"
 show Neg = "-ve"
 show Mxd = "mxd"
\end{code}

\paragraph{Bindings on-route}

We record bindings as a variable-name list
\begin{code}
type Binders = [Variable]
\end{code}

\paragraph{Focus Context Definition}


\begin{code}
type FContext = (Polarity,Binders,[TTTag])

nullCtxt, baseCtxt, mxdCtxt :: FContext
nullCtxt = (Pos,[],[])
baseCtxt = (Pos,[],[0])
mxdCtxt = (Mxd,[],[0])
\end{code}

When we move down, the context needs to be updated
to reflect changes in polarity,
as well as any variable bindings that might be encountered.
Also we should track type-table tags.
We provide some context update functions:

\begin{code}
ctxtId,ctxtNeg,ctxtMxd :: FContext -> FContext
ctxtId = id
ctxtNeg (pol,bs,tags) = (polneg pol,bs,tags)
ctxtMxd (pol,bs,tags) = (Mxd,bs,tags)
\end{code}

\paragraph{Binders}
\begin{code}
ctxtPush :: ([Variable],TTTag) -> FContext -> FContext
ctxtPush (vs,tag) (pol,bs,tags) = (pol,lnorm (vs++bs),tag:tags)
ctxtPPush vs (pol,bs,tags) = (pol,lnorm (vs++bs),tags)
\end{code}

\subsubsection{Focus Path}

We use a list of numbers identifying the
relevant sub-expressions,
from the top downwards, each paired with an \texttt{FContext}.
\begin{code}
type FocusPath = [ ( Int       -- index into parent predicate
                   , FContext  --  context of parent
                   )
                 ]
\end{code}


\subsubsection{Focussed Entities}

A focussed entity is a quadruple,
with the focus predicate, the context, the top-level predicate
and a stack of index-context pairs.
\begin{code}
type FPred = ( Pred       -- Focus Predicate
             , FContext   -- Focus Context
             , Pred       -- Top-Level Predicate
             , FocusPath  -- path from top downto focus (with contexts)
             )
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

  tRecurse (Tset ty) = typerec ty
  tRecurse (Tseq ty) = typerec ty
  tRecurse (Tseqp ty) = typerec ty
  tRecurse (Tprod tys) = merge $ map typerec tys
  tRecurse (Tfree _ fs) = merge $ map typerec $ concat $ map snd fs
  tRecurse (Tfun ty1 ty2) = merge $ map typerec [ty1,ty2]
  tRecurse (Tpfun ty1 ty2) = merge $ map typerec [ty1,ty2]
  tRecurse (Tmap ty1 ty2) = merge $ map typerec [ty1,ty2]
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

  eRecurse (Prod exs) = merge $ map exprrec exs
  eRecurse (App _ ex) = exprrec ex
  eRecurse (Bin _ _ ex1 ex2) = merge $ map exprrec [ex1,ex2]
  eRecurse (Equal ex1 ex2) = merge $ map exprrec [ex1,ex2]
  eRecurse (Set exs) = merge $ map exprrec exs
  eRecurse (Setc _ _ _ ex) = exprrec ex
  eRecurse (Seq exs) = merge $ map exprrec exs
  eRecurse (Seqc _ _ _ ex) = exprrec ex
  eRecurse (Map drs) = merge $ map exprrec2 drs
  eRecurse (Cond _ ex1 ex2) = merge $ map exprrec [ex1,ex2]
  eRecurse (Build _ exs) = merge $ map exprrec exs
  eRecurse (Eabs _ _ ex) = exprrec ex
  eRecurse (Esub ex (Substn ssub))
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

  pRecurse (Not pr) = predrec pr
  pRecurse (And prs) = merge $ map predrec prs
  pRecurse (Or prs) = merge $ map predrec prs
  pRecurse (Imp pr1 pr2) = merge $ map predrec [pr1,pr2]
  pRecurse (Eqv pr1 pr2) = merge $ map predrec [pr1,pr2]
  pRecurse (Forall _ _ pr) = predrec pr
  pRecurse (Exists _ _ pr) = predrec pr
  pRecurse (Exists1 _ _  pr) = predrec pr
  pRecurse (Univ _ pr) = predrec pr
  pRecurse (Sub pr _) = predrec pr
  pRecurse (Psub pr _) = predrec pr
  pRecurse (If pr1 pr2 pr3) = merge $ map predrec [pr1,pr2,pr3]
  pRecurse (NDC pr1 pr2) = merge $ map predrec [pr1,pr2]
  pRecurse (RfdBy pr1 pr2) = merge $ map predrec [pr1,pr2]
  pRecurse (Peabs _ pr) = predrec pr
  pRecurse (Ppabs _ pr) = predrec pr
  pRecurse (Papp pr1 pr2) = merge $ map predrec [pr1,pr2]
  pRecurse (Pforall _ pr) = predrec pr
  pRecurse (Pexists _ pr) = predrec pr
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

mapPf (fp,fe) (Obs e) = (Obs e', dif)
  where (e', dif) = fe e
mapPf (fp,fe) (Defd e) = (Defd e', dif)
  where (e', dif) = fe e
mapPf (fp,fe) (TypeOf e t) = (TypeOf e' t, dif)
  where (e', dif) = fe e
mapPf (fp,fe) (Not pr) = (Not pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (And prs) = (And prs', or dif)
  where (prs', dif) = unzip (map fp prs)
mapPf (fp,fe) (Or prs) = (Or prs', or dif)
  where (prs', dif) = unzip (map fp prs)
mapPf (fp,fe) (NDC pr1 pr2) = (NDC pr1' pr2', dif1 || dif2)
  where
  (pr1', dif1) = fp pr1
  (pr2', dif2) = fp pr2
mapPf (fp,fe) (Imp pr1 pr2) = (Imp pr1' pr2', dif1 || dif2)
  where
  (pr1', dif1) = fp pr1
  (pr2', dif2) = fp pr2
mapPf (fp,fe) (RfdBy pr1 pr2) = (RfdBy pr1' pr2', dif1 || dif2)
  where
  (pr1', dif1) = fp pr1
  (pr2', dif2) = fp pr2
mapPf (fp,fe) (Eqv pr1 pr2) = (Eqv pr1' pr2', dif1 || dif2)
  where
  (pr1', dif1) = fp pr1
  (pr2', dif2) = fp pr2
mapPf (fp,fe) (Lang s p les ss) = (Lang s p les' ss, or dif)
  where (les', dif) = unzip (map (mapLf (fp,fe)) les)
mapPf (fp,fe) (If prc prt pre) = (If prc' prt' pre', dif1 || dif2 || dif3)
  where
  (prc', dif1) = fp prc
  (prt', dif2) = fp prt
  (pre', dif3) = fp pre
mapPf (fp,fe) (Forall tt qs pr) = (Forall tt qs pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Exists tt qs pr) = (Exists tt qs pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Exists1 tt qs pr) = (Exists1 tt qs pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Univ tt pr) = (Univ tt pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Sub pr sub) = (Sub pr' sub', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (sub', dif2) = mapSf fe sub
mapPf (fp,fe) (Psub pr sub) = (Psub pr' sub', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (sub', dif2) = mapSf fp sub
mapPf (fp,fe) (Peabs s pr) = (Peabs s pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Ppabs s pr) = (Ppabs s pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Papp prf pra) = (Papp prf' pra', dif1 || dif2)
  where
    (prf', dif1) = fp prf
    (pra', dif2) = fp pra
mapPf (fp,fe) (Psapp pr spr) = (Psapp pr' spr', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (spr', dif2) = mapPSf fp spr
mapPf (fp,fe) (Psin pr spr) = (Psin pr' spr', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (spr', dif2) = mapPSf fp spr
mapPf (fp,fe) (Pforall pvs pr) = (Pforall pvs pr', dif)
  where (pr', dif) = fp pr
mapPf (fp,fe) (Pexists pvs pr) = (Pforall pvs pr', True)
  where (pr', _) = fp pr
mapPf (fp,fe) pr@(Pfocus _)
  = error ("mapP cannot handle focii"++debugPshow pr)

mapPf (fp,fe) pr = (pr, False)

mapEf (fp,fe) (Prod es) = (Prod es', or dif)
  where (es', dif) = unzip (map fe es)
mapEf (fp,fe) (App s e) = (App s e', dif)
  where (e', dif) = fe e
mapEf (fp,fe) (Bin s i e1 e2) = (Bin s i e1' e2', dif1 || dif2)
  where
    (e1', dif1) = fe e1
    (e2', dif2) = fe e2
mapEf (fp,fe) (Equal e1 e2) = (Equal e1' e2', dif1 || dif2)
  where
    (e1', dif1) = fe e1
    (e2', dif2) = fe e2
mapEf (fp,fe) (Set es) = (Set es', or dif)
  where (es', dif) = unzip (map fe es)
mapEf (fp,fe) (Setc tt qs pr e) = (Setc tt qs pr' e', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (e', dif2) = fe e
mapEf (fp,fe) (Seq es) = (Seq es', or dif)
  where (es', dif) = unzip (map fe es)
mapEf (fp,fe) (Seqc tt qs pr e) = (Seqc tt qs pr' e', dif1 || dif2)
  where
    (pr', dif1) = fp pr
    (e', dif2) = fe e
mapEf (fp,fe) (Map drs) = (Map drs', or dif)
  where (drs', dif) = unzip (mapDRf fe drs)
mapEf (fp,fe) (Cond pc et ee) = (Cond pc' et' ee', dif1 || dif2 || dif3)
  where
    (pc', dif1) = fp pc
    (et', dif2) = fe et
    (ee', dif3) = fe ee
mapEf (fp,fe) (Build s es) = (Build s es', or dif)
  where (es', dif) = unzip (map fe es)
mapEf (fp,fe) (The tt qs pr) = (The tt qs pr', dif)
  where (pr', dif) = fp pr
mapEf (fp,fe) (Eabs tt qs e) = (Eabs tt qs e', dif)
  where (e', dif) = fe e
mapEf (fp,fe) (Esub e sub) = (Esub e' sub', dif1 || dif2)
  where
    (sub', dif1) = mapSf fe sub
    (e', dif2) = fe e
mapEf (fp,fe) (EPred p) = (EPred p',dif)
 where (p', dif) = fp p
mapEf (fp,fe) e@(Efocus _)
  = error ("mapEf cannot handle focii"++debugEshow e)

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
mapP (fp,fe) (Obs e) = Obs (fe e)
mapP (fp,fe) (Defd e) = Defd (fe e)
mapP (fp,fe) (TypeOf e t) = TypeOf (fe e) t
mapP (fp,fe) (Not pr) = Not (fp pr)
mapP (fp,fe) (And prs) = And (map fp prs)
mapP (fp,fe) (Or prs) = Or (map fp prs)
mapP (fp,fe) (NDC pr1 pr2) = NDC (fp pr1) (fp pr2)
mapP (fp,fe) (Imp pr1 pr2) = Imp (fp pr1) (fp pr2)
mapP (fp,fe) (RfdBy pr1 pr2) = RfdBy (fp pr1) (fp pr2)
mapP (fp,fe) (Eqv pr1 pr2) = Eqv (fp pr1) (fp pr2)
mapP (fp,fe) (Lang s p les ss) = Lang s p (map (mapL (fp,fe)) les) ss
mapP (fp,fe) (If prc prt pre) = If (fp prc) (fp prt) (fp pre)
mapP (fp,fe) (Forall tt qs pr) = Forall tt qs (fp pr)
mapP (fp,fe) (Exists tt qs pr) = Exists tt qs (fp pr)
mapP (fp,fe) (Exists1 tt qs pr) = Exists1 tt qs (fp pr)
mapP (fp,fe) (Univ tt pr) = Univ tt (fp pr)
mapP (fp,fe) (Sub pr sub) = Sub (fp pr) (mapS fe sub)
mapP (fp,fe) (Psub pr sub) = Psub (fp pr) (mapS fp sub)
mapP (fp,fe) (Peabs s pr) = Peabs s (fp pr)
mapP (fp,fe) (Ppabs s pr) = Ppabs s (fp pr)
mapP (fp,fe) (Papp prf pra) = Papp (fp prf) (fp pra)
mapP (fp,fe) (Psapp pr spr) = Psapp (fp pr) (mapPS fp spr)
mapP (fp,fe) (Psin pr spr) = Psin (fp pr) (mapPS fp spr)
mapP (fp,fe) (Pforall pvs pr) = Pforall pvs (fp pr)
mapP (fp,fe) (Pexists pvs pr) = Pexists pvs (fp pr)
mapP (fp,fe) (Pfocus pr) = Pfocus $ fp pr

mapP (fp,fe) pr = pr

mapPS :: (Pred -> Pred) -> PredSet -> PredSet
mapPS fp (PSet prs) = PSet (map fp prs)
mapPS fp (PSetC nms pr1 pr2) = PSetC nms (fp pr1) (fp pr2)
mapPS fp (PSetU s1 s2) = PSetU (mapPS fp s1) (mapPS fp s2)
mapPS fp s = s

mapPSf :: (Pred -> (Pred,Bool)) -> PredSet -> (PredSet, Bool)
mapPSf fp (PSet prs) = (PSet prs', or dif)
  where
    (prs', dif) = unzip (map fp prs)
mapPSf fp (PSetC nms pr1 pr2) = (PSetC nms pr1' pr2', dif1 || dif2)
  where
    (pr1', dif1) = fp pr1
    (pr2', dif2) = fp pr2
mapPSf fp (PSetU s1 s2) = (PSetU s1' s2', dif1 || dif2)
  where
    (s1', dif1) = mapPSf fp s1
    (s2', dif2) = mapPSf fp s2
mapPSf fp s = (s, False)


mapE (fp,fe) (Prod es)         = Prod (map fe es)
mapE (fp,fe) (App s e)         = App s (fe e)
mapE (fp,fe) (Bin s i e1 e2)   = Bin s i (fe e1) (fe e2)
mapE (fp,fe) (Equal e1 e2)     = Equal (fe e1) (fe e2)
mapE (fp,fe) (Set es)          = Set (map fe es)
mapE (fp,fe) (Setc tt qs pr e) = Setc tt qs (fp pr) (fe e)
mapE (fp,fe) (Seq es)          = Seq (map fe es)
mapE (fp,fe) (Seqc tt qs pr e) = Seqc tt qs (fp pr) (fe e)
mapE (fp,fe) (Map drs)         = Map (mapDR fe drs)
mapE (fp,fe) (Cond pc et ee)   = Cond (fp pc) (fe et) (fe ee)
mapE (fp,fe) (Build s es)      = Build s (map fe es)
mapE (fp,fe) (The tt qs pr)    = The tt qs (fp pr)
mapE (fp,fe) (Eabs tt qs e)    = Eabs tt qs (fe e)
mapE (fp,fe) (Esub e sub)      = Esub (fe e) (mapS fe sub)
mapE (fp,fe) (EPred p)         = EPred $ fp p
mapE (fp,fe) (Efocus e)        = Efocus $ fe e

mapE (fp,fe) e = e

mapS f (Substn ssub) = Substn (maparng f ssub)

mapSf f (Substn ssub) = (Substn ssub', or dif)
 where
    (ssub', dif) = unzip (maparngf f ssub)

mapDR fe [] = []
mapDR fe ((de,re):ms) = (fe de,fe re):(mapDR fe ms)

mapDRf fe [] = []
mapDRf fe ((de,re):[]) = [((de', re'), dif1 || dif2)]
  where
    (de', dif1) = fe de
    (re', dif2) = fe re
mapDRf fe ((de,re):ms) = ((de', re'), dif1 || dif2):(mapDRf fe ms)
  where
    (de', dif1) = fe de
    (re', dif2) = fe re

mapL (fp,fe) (LExpr e)    =  LExpr (fe e)
mapL (fp,fe) (LPred pr)   =  LPred (fp pr)
mapL (fp,fe) (LList les)  =  LList (map (mapL (fp,fe)) les)
mapL (fp,fe) (LCount les) =  LCount (map (mapL (fp,fe)) les)
mapL (fp,fe) lelem        =  lelem

mapLf (fp,fe) (LExpr e)    =  (LExpr e', dif)
  where (e', dif) = fe e
mapLf (fp,fe) (LPred pr)   =  (LPred pr', dif)
  where (pr', dif) = fp pr
mapLf (fp,fe) (LList les)  =  (LList les', or dif)
  where (les', dif) = unzip (map (mapLf (fp,fe)) les)
mapLf (fp,fe) (LCount les) =  (LCount les', or dif)
  where (les', dif) = unzip (map (mapLf (fp,fe)) les)
mapLf (fp,fe) lelem        =  (lelem, False)
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
  f (Obs e) = f1 $ g0 e
  f (Defd e) = f1 $ g0 e
  f (TypeOf e t) = f1 $ g0 e
  f (Not p) = f1  $ f0 p
  f (And ps) = f2 $ map f0 ps
  f (Or ps) = f2 $ map f0 ps
  f (Imp p1 p2) = f2 $ map f0 [p1,p2]
  f (Eqv p1 p2) = f2 $ map f0 [p1,p2]
  f (Forall tt qvs pr) = f1 $ f0 pr
  f (Exists tt qvs pr) = f1 $ f0 pr
  f (Exists1 tt qvs pr) = f1 $ f0 pr
  f (Univ tt p) = f1 $ f0 p
  f (Sub p sub) = f2 (f p : foldES g0 sub)
  f (If pc pt pe) = f2 $ map f0 [pc,pt,pe]
  f (NDC p1 p2) = f2 $ map f0 [p1,p2]
  f (RfdBy p1 p2) = f2 $ map f0 [p1,p2]
  f (Pforall vs p) = f1 $ f0 p
  f (Pexists vs p) = f1 $ f0 p
  f (Psub p sub) = f2 (f p : foldPS f0 sub)
  f (Psapp p ps) = f2 (foldPP f0 ps)
  f (Psin p ps) = f2 (foldPP f0 ps)
  f (Peabs vs p) = f1 $ f0 p
  f (Ppabs vs p) = f1 $ f0 p
  f (Papp p1 p2) = f2 $ map f0 [p1,p2]
  f (Pfocus p) = f1 $ f0 p

  f (Lang s i les ss) = foldL pef les

  f pr = pa -- recursion must stop here !

-- end foldP
\end{code}

Folding over Expressions:
\begin{code}
foldE pef@((pa,f0,f1,f2),(ea,g0,g1,g2)) e
 = f e
 where
  f (Prod es) = g2 $ map g0 es
  f (App s e) = g1 $ g0 e
  f (Bin s i e1 e2) = g2 $ map g0 [e1,e2]
  f (Equal e1 e2) = g2 $ map g0 [e1,e2]
  f (Set es) = g2 $ map g0 es
  f (Setc tt qvs p e) = g2 [f0 p, g0 e]
  f (Seq es) = g2 $ map g0 es
  f (Seqc tt qvs p e) = g2 [f0 p, g0 e]
  f (Map drs) = g2 $ concat $ map gg0 drs
  f (Cond p e1 e2) = g2 (f0 p : map g0 [e1,e2])
  f (Build s es) = g2 $ map g0 es
  f (The tt qvs p2) = g1 $ f0 p2
  f (Eabs tt qvs e) = g1 $ g0 e
  f (Esub e sub) = g2 (g0 e : foldES g0 sub)
  f (EPred p) = g1 $ f0 p
  f (Efocus e) = g1 $ g0 e

  f e = ea -- recursion must stop here !

  gg0 (d,r) = [g0 d, g0 r]

-- end foldE
\end{code}

Folding auxilliaries:
\begin{code}
foldPS :: (Pred -> a) -> PSubst -> [a]
foldPS f0 (Substn ssub) = map (f0 . snd) ssub

foldES :: (Expr -> a) -> ESubst -> [a]
foldES g0 (Substn ssub) = map (g0 . snd) ssub

foldPP :: (Pred -> a) -> PredSet -> [a]
foldPP f0 (PSet ps) = map f0 ps
foldPP f0 (PSetC _ p1 p2) = map f0 [p1,p2]
foldPP f0 (PSetU ps1 ps2) = foldPP f0 ps1 ++ foldPP f0 ps2
foldPP f0 pset = []
\end{code}

Folding over Language constructs:
\begin{code}
foldL pef@((pa,f0,f1,f2),(ea,g0,g1,g2)) les
 = f2 $ concat $ foldL' les
 where

   foldL' [] = []
   foldL' (le:les) = foldE le : foldL' les

   foldE (LExpr e)     =  [g0 e]
   foldE (LPred pr)    =  [f0 pr]
   foldE (LList les)   =  concat $ foldL' les
   foldE (LCount les)  =  concat $ foldL' les
   foldE _             =  []
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

accPseq (pf,ef) a (Obs e) = (Obs e',a') where (e',a') = ef a e
accPseq (pf,ef) a (Defd e) = (Defd e',a') where (e',a') = ef a e
accPseq (pf,ef) a (TypeOf e t)
 = (TypeOf e' t,a') where (e',a') = ef a e

accPseq (pf,ef) a (Not pr) = (Not pr',a') where (pr',a') = pf a pr
accPseq (pf,ef) a (And prs)
 = (And prs',a') where (prs',a') = accPseqs pf a prs
accPseq (pf,ef) a (Or prs)
 = (Or prs',a') where (prs',a') = accPseqs pf a prs
accPseq (pf,ef) a (NDC pr1 pr2) = (NDC pr1' pr2',a')
  where ([pr1',pr2'],a') = accPseqs pf a [pr1,pr2]
accPseq (pf,ef) a (Imp pr1 pr2) = (Imp pr1' pr2',a')
  where ([pr1',pr2'],a') = accPseqs pf a [pr1,pr2]
accPseq (pf,ef) a (RfdBy pr1 pr2) = (RfdBy pr1' pr2',a')
  where ([pr1',pr2'],a') = accPseqs pf a [pr1,pr2]
accPseq (pf,ef) a (Eqv pr1 pr2) = (Eqv pr1' pr2',a')
  where ([pr1',pr2'],a') = accPseqs pf a [pr1,pr2]

accPseq (pf,ef) a (Lang n p les ss) = error "accPseq Lang NYI"

accPseq (pf,ef) a (If prc prt pre) = (If prc' prt' pre',a')
  where ([prc',prt',pre'],a') = accPseqs pf a [prc,prt,pre]

accPseq (pf,ef) a (Forall tt qs pr) = (Forall tt qs pr',a')
  where (pr',a') = pf a pr
accPseq (pf,ef) a (Exists tt qs pr) = (Exists tt qs pr',a')
  where (pr',a') = pf a pr
accPseq (pf,ef) a (Exists1 tt qs pr) = (Exists1 tt qs pr',a')
  where (pr',a') = pf a pr
accPseq (pf,ef) a (Univ tt pr) = (Univ tt pr',a') where (pr',a') = pf a pr
accPseq (pf,ef) a (Sub pr sub) = (Sub pr' sub',a'')
 where (pr',a') = pf a pr
       (sub',a'') = accESseq (pf,ef) a' sub

accPseq (pf,ef) a (Psub pr sub) = (Psub pr' sub',a'')
 where (pr',a') = pf a pr
       (sub',a'') = accPSseq (pf,ef) a' sub
accPseq (pf,ef) a (Peabs s pr)
 = (Peabs s pr',a') where (pr',a') = pf a pr
accPseq (pf,ef) a (Ppabs s pr)
 = (Ppabs s pr',a') where (pr',a') = pf a pr
accPseq (pf,ef) a (Papp prf pra) = (Papp prf' pra',a')
  where ([prf',pra'],a') = accPseqs pf a [prf,pra]

accPseq (pf,ef) a (Psapp pr spr)
 = (Psapp pr' spr',a'')
 where (pr',a') = pf a pr
       (spr',a'') = accPSetseq pf a' spr
accPseq (pf,ef) a (Psin pr spr)
 = (Psin pr' spr',a'')
 where (pr',a') = pf a pr
       (spr',a'') = accPSetseq pf a' spr

accPseq (pf,ef) a (Pforall pvs pr)
 = (Pforall pvs pr',a') where (pr',a') = pf a pr
accPseq (pf,ef) a (Pexists pvs pr)
 = (Pforall pvs pr',a') where (pr',a') = pf a pr

accPseq (pf,ef) a pr = (pr,a)

accPseqs pf a [] = ([],a)
accPseqs pf a (pr:prs) = (pr':prs',a'')
 where (pr',a') = pf a pr
       (prs',a'') = accPseqs pf a' prs

accPSetseq pf a (PSet prs)
 = (PSet prs',a') where (prs',a') = accPseqs pf a prs
accPSetseq pf a (PSetC nms pr1 pr2)
 = (PSetC nms pr1' pr2',a')
 where ([pr1',pr2'],a') = accPseqs pf a [pr1,pr2]
accPSetseq pf a (PSetU s1 s2)
 = (PSetU s1' s2',a'')
 where (s1',a') = accPSetseq pf a s1
       (s2',a'') = accPSetseq pf a' s2
accPSetseq pf a s = (s,a)
\end{code}

The \texttt{Expr} version:
\begin{code}
accEseq :: (a -> Pred -> (Pred,a),a -> Expr -> (Expr,a))
            -> a -> Expr -> (Expr,a)
accEseq (pf,ef) a (Prod es) = (Prod es',a') where (es',a') = accEseqs ef a es
accEseq (pf,ef) a (App s e) = (App s e',a') where (e',a') = ef a e
accEseq (pf,ef) a (Bin s i e1 e2) = (Bin s i e1' e2',a')
  where ([e1',e2'],a') = accEseqs ef a [e1,e2]
accEseq (pf,ef) a (Equal e1 e2) = (Equal e1' e2',a')
  where ([e1',e2'],a') = accEseqs ef a [e1,e2]
accEseq (pf,ef) a (Set es) = (Set es',a') where (es',a') = accEseqs ef a es
accEseq (pf,ef) a (Setc tt qs pr e) = (Setc tt qs pr' e',a'')
 where (pr',a') = pf a pr
       (e',a'') = ef a' e
accEseq (pf,ef) a (Seq es) = (Seq es',a') where (es',a') = accEseqs ef a es
accEseq (pf,ef) a (Seqc tt qs pr e) = (Seqc tt qs pr' e',a'')
 where (pr',a') = pf a pr
       (e',a'') = ef a' e
accEseq (pf,ef) a (Map drs) = (Map drs',a') where (drs',a') = accEseqm ef a drs
accEseq (pf,ef) a (Cond pc et ee) = (Cond pc' et' ee',a'')
  where (pc',a') = pf a pc
        ([et',ee'],a'') = accEseqs ef a [et,ee]
accEseq (pf,ef) a (Build s es) = (Build s es',a') where (es',a') = accEseqs ef a es
accEseq (pf,ef) a (The tt qs pr) = (The tt qs pr',a')
  where (pr',a') = pf a pr
accEseq (pf,ef) a (Eabs tt qs e) = (Eabs tt qs e',a') where (e',a') = ef a e
accEseq (pf,ef) a (Esub e sub) = (Esub e' sub',a'')
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

debugPshow (Pfocus fpr)
 = "FOCUSSED-PRED"
   ++ hdr 1 ++ dbgPshow 2 fpr

debugPshow pr = dbgPshow 0 pr

debugEshow  =  dbgEshow 0

debugTshow  =  dbgTshow 0

debugLshow (LangSpec les ss)
 =  "LANGSPEC"
    ++ concat (map (dbgLshow 3) les)
    ++ concat (map (dbgSSshow 1) ss)

debugAshow (pr,sc)
 = "ASSERTION"
    ++ dbgPshow 3 pr
    ++ dbgSCshow 1 sc

hdr i  = '\n':(replicate i ' ')

dbgPshow i  TRUE     = hdr i ++ "TRUE"
dbgPshow i  FALSE    = hdr i ++ "FALSE"
dbgPshow i  (Obs e)  = hdr i ++ "OBS " ++ dbgEshow (i+1) e
dbgPshow i  (Defd e) = hdr i ++ "DEFD " ++ dbgEshow (i+1) e
dbgPshow i  (TypeOf e t) = hdr i ++ "TYPEOF " ++ dbgEshow (i+1) e ++ dbgTshow (i+1) t
dbgPshow i  (Lang s p les ss)
  = hdr i ++ "LANG " ++ s ++ " "++show p
             ++ concat (map (dbgLshow (i+1)) les)
             ++ concat (map (dbgSSshow (i+1)) ss)
dbgPshow i  (Not pr) = hdr i ++ "NOT" ++ dbgPshow (i+1) pr
dbgPshow i  (And prs)
  = hdr i ++ "AND"++concat (map (dbgPshow (i+1)) prs)
dbgPshow i  (Or prs)
  = hdr i ++ "OR"++concat (map (dbgPshow (i+1)) prs)
dbgPshow i  (NDC pr1 pr2)
  = hdr i ++ "NDC"++dbgPshow (i+1) pr1++dbgPshow (i+1) pr2
dbgPshow i  (Imp pr1 pr2)
  = hdr i ++ "IMP"++dbgPshow (i+1) pr1++dbgPshow (i+1) pr2
dbgPshow i  (RfdBy pr1 pr2)
  = hdr i ++ "RFDBY"++dbgPshow (i+1) pr1++dbgPshow (i+1) pr2
dbgPshow i  (Eqv pr1 pr2)
  = hdr i ++ "EQV"++dbgPshow (i+1) pr1++dbgPshow (i+1) pr2
dbgPshow i  (If prc prt pre)
  = hdr i ++ "IF"++dbgPshow (i+1) prc++dbgPshow (i+1) prt++dbgPshow (i+1) pre
dbgPshow i  (Forall tt qs pr)
  = hdr i ++ "FORALL "++show tt++' ':dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Exists tt qs pr)
  = hdr i ++ "EXISTS "++show tt++' ':dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Exists1 tt qs pr)
  = hdr i ++ "EXISTS1 "++show tt++' ':dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Univ tt pr) = hdr i ++ "UNIV " ++ show tt++' ':dbgPshow (i+1) pr
dbgPshow i  (Sub pr sub) = hdr i ++ "SUB" ++ dbgESshow (i+1) sub++dbgPshow (i+1) pr
dbgPshow i  (Psub pr sub) = hdr i ++ "PSUB" ++ dbgPSshow (i+1) sub++dbgPshow (i+1) pr
dbgPshow i  (Pvar r) = hdr i ++ "PVAR '"++dbgRshow (Gen r)++"'"
dbgPshow i  (Ppabs qs pr)
  = hdr i ++ "PPABS "++dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Peabs qs pr)
  = hdr i ++ "PEABS "++dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Papp prf pra)
  = hdr i ++ "PAPP"++dbgPshow (i+1) prf++dbgPshow (i+1) pra
dbgPshow i  (Psapp pr spr)
  = hdr i ++ "PSAPP"++dbgPshow (i+1) pr++dbgPSetshow (i+1) spr
dbgPshow i  (Psin pr spr)
  = hdr i ++ "PSIN"++dbgPshow (i+1) pr++dbgPSetshow (i+1) spr
dbgPshow i  (Pforall qs pr)
  = hdr i ++ "PFORALL "++dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Pexists qs pr)
  = hdr i ++ "PEXISTS "++dbgQSshow (i+1) qs++dbgPshow (i+1) pr
dbgPshow i  (Pfocus fpr)
 = hdr i ++ "PFOCUS" ++ dbgPshow (i+1) fpr
dbgPshow i (Perror msg) = "PERROR '" ++ msg ++ "'"
-- dbgPshow i pr = "??PWHAT??"

dbgPSetshow i (PSName nm) = hdr i ++ "PSNAME '"++nm++"'"
dbgPSetshow i (PSet prs)
 = hdr i ++ "PSET"++concat (map (dbgPshow (i+1)) prs)
dbgPSetshow i (PSetC qs pr1 pr2)
 = hdr i ++ "PSETC "++dbgQSshow (i+1) qs++" "
   ++ dbgPshow (i+1) pr1 ++ dbgPshow (i+1) pr2
dbgPSetshow i (PSetU s1 s2)
 = hdr i ++ "PSETU" ++ dbgPSetshow (i+1) s1 ++ dbgPSetshow (i+1) s2


dbgLshow i (LVar g)    = hdr i ++ "LVAR " ++ dbgGshow g
dbgLshow i (LType t)   = hdr i ++ "LTYPE" ++ dbgTshow (i+1) t
dbgLshow i (LExpr e)   = hdr i ++ "LEXPR" ++ dbgEshow (i+1) e
dbgLshow i (LPred pr)  = hdr i ++ "LPRED" ++ dbgPshow (i+1) pr
dbgLshow i (LList les) = hdr i ++ "LLIST" ++ concat (map (dbgLshow (i+1)) les)

dbgGshow (Std s) = "STD: " ++ s
dbgGshow (Lst s) = "LST: " ++ s

dbgSSshow i SSNull      = hdr i ++ "SSNULL"
dbgSSshow i (SSTok s)   = hdr i ++ "SSTOK "  ++ s
dbgSSshow i (SSSep s)   = hdr i ++ "SSSEP "  ++ s

dbgEshow i T               = hdr i ++ "T"
dbgEshow i F               = hdr i ++ "F"
dbgEshow i (Num n)         = hdr i ++ "NUM "++show n
dbgEshow i (Var v)         = hdr i ++ "VAR " ++ dbgVshow v
dbgEshow i (Prod es)
  = hdr i ++ "PROD" ++ concat(map (dbgEshow (i+1)) es)
dbgEshow i (App s e)       = hdr i ++ "APP "++s++dbgEshow (i+1) e
dbgEshow i (Bin s p e1 e2)
 = hdr i ++ "BIN "++show p++" "++s ++dbgEshow (i+1) e1++dbgEshow (i+1) e2
dbgEshow i (Equal e1 e2)
 = hdr i ++ "EQUAL"++dbgEshow (i+1) e1++dbgEshow (i+1) e2
dbgEshow i (Set es)
  = hdr i ++ "SET" ++ concat(map (dbgEshow (i+1)) es)
dbgEshow i (Setc tt qs pr e)
  = hdr i ++ "SETC " ++ show tt ++ ' ':dbgQSshow (i+1) qs ++ dbgPshow (i+1) pr++ dbgEshow (i+1) e
dbgEshow i (Seq es)
  = hdr i ++ "SEQ" ++ concat(map (dbgEshow (i+1)) es)
dbgEshow i (Seqc tt qs pr e)
  = hdr i ++ "SEQC " ++ show tt ++ ' ':dbgQSshow (i+1) qs ++ dbgPshow (i+1) pr++ dbgEshow (i+1) e
dbgEshow i (Map es) = hdr i ++ "MAP" ++ concat(map (dbgMshow (i + 1)) es)
dbgEshow i (Cond pc et ee)
 = hdr i ++ "COND"++dbgPshow (i+1) pc++dbgEshow (i+1) et++dbgEshow (i+1) ee
dbgEshow i (Build s es)
  = hdr i ++ "BUILD "++s ++ concat(map (dbgEshow (i+1)) es)
dbgEshow i (The tt x pr)
  = hdr i ++ "THE "++show tt ++ " "++dbgVshow x++dbgPshow (i+1) pr
dbgEshow i (Evar e) = hdr i ++ "EVAR " ++ dbgVshow e
dbgEshow i (Eabs tt qs e) = hdr i ++ "EABS "++show tt++' ':dbgQSshow (i+1) qs ++ dbgEshow (i+1) e
dbgEshow i (Esub e sub) = hdr i ++ "ESUB "++dbgESshow (i+1) sub ++ dbgEshow (i+1) e
dbgEshow i (Eerror s) = hdr i ++ "EERROR "++s
dbgEshow i (EPred p)
 = hdr i ++ "EPRED" ++ dbgPshow (i+1) p
dbgEshow i (Efocus ef)
 = hdr i ++ "EFOCUS" ++ dbgEshow (i+1) ef

-- Code to show map domain and range

dbgDshow NoDecor = "NODECOR"
dbgDshow Pre = "PRE"
dbgDshow Post = "POST"
dbgDshow (Subscript s) = "SSCRPT:"++s
dbgDshow Scrpt = "SCRIPT"

dbgRshow (Gen (Std s)) = "STD "++s
dbgRshow (Gen (Lst s)) = "LST "++s
dbgRshow (Rsv OBS rs)  = "OBS"++' ':(concat $ intersperse ":" $ map (dbgRshow . Gen) rs)
dbgRshow (Rsv MDL rs)  = "MDL"++' ':(concat $ intersperse ":" $ map (dbgRshow . Gen) rs)
dbgRshow (Rsv SCR rs)  = "SCR"++' ':(concat $ intersperse ":" $ map (dbgRshow . Gen) rs)

dbgVshow (r,d,s) = dbgRshow r
                    ++ ' ':dbgDshow d
                    ++ " \"" ++ s ++ "\""

dbgVSshow vs = "<"
               ++ (concat $ intersperse ">, <" $ map dbgVshow vs)
               ++ ">"

debugQSshow :: QVars -> String
debugQSshow = dbgQSshow 0

dbgQSshow i (Q [])  = hdr i ++ "QVARS(empty)"
dbgQSshow i (Q qs)
 = hdr i ++ "QVARS:"
   ++ (concat $ map ( (hdr (i+1) ++) . dbgVshow ) qs)


dbgMshow i (x,y) = hdr i ++ "DOM" ++ dbgEshow (i+1) x ++ hdr i ++ "RNG" ++ dbgEshow (i+1) y

dbgESshow :: Int -> ESubst -> String
dbgESshow i (Substn sub)
  = hdr i ++ "E-SUBSTN" ++ dbgSshow dbgVshow dbgEshow (i+1) sub

dbgPSshow :: Int -> PSubst -> String
dbgPSshow i (Substn sub)
  = hdr i ++ "P-SUBSTN" ++ dbgSshow (dbgRshow . Gen) dbgPshow (i+2) sub

dbgSshow :: (v -> String) -> (Int -> a -> String) -> Int -> [(v,a)]
         -> String
dbgSshow shv shth i  [] = ""
dbgSshow shv shth i ((v,thing):rest)
 = hdr i ++ shv v ++ "  |->" ++ shth (i+3) thing
   ++ dbgSshow shv shth i rest

dbgTshow i Tarb = hdr i ++ "TARB"
dbgTshow i (Tvar s) = hdr i ++ "TVAR "++s
dbgTshow i (Tset t) = hdr i ++ "TSET" ++ dbgTshow (i+1) t
dbgTshow i (Tseq t) = hdr i ++ "TSEQ" ++ dbgTshow (i+1) t
dbgTshow i (Tseqp t) = hdr i ++ "TSEQP" ++ dbgTshow (i+1) t
dbgTshow i (Tprod ts) = hdr i ++ "TPROD" ++ concat(map (dbgTshow (i+1)) ts)
dbgTshow i (Tfree s cs) = hdr i ++ "TFREE "++s ++ concat(map (dbgFshow (i+1)) cs)
dbgTshow i (Tfun t1 t2) = hdr i ++ "TFUN" ++ dbgTshow (i+1) t1 ++ dbgTshow (i+1) t2
dbgTshow i (Tpfun t1 t2) = hdr i ++ "TPFUN" ++ dbgTshow (i+1) t1 ++ dbgTshow (i+1) t2
dbgTshow i (Tmap t1 t2) = hdr i ++ "TMAP" ++ dbgTshow (i+1) t1 ++ dbgTshow (i+1) t2
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
 deriving (Eq,Ord)

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
--predParts (Pvar (Std s)) = ("Pvar-"++show s,[],[],[],[])
--predParts (Pvar (Lst s)) = ("Pvar-"++show s++[listVarFlag],[],[],[],[])
predParts (Pvar r) = ("Pvar-"++rootString (Gen r),[],[],[],[])
predParts (Obs e) = ("Obs",[],[e],[],[])
predParts (Defd e) = ("Defd",[],[e],[],[])
predParts (TypeOf e t) = ("TypeOf",[],[e],[],[t])
predParts (Not pr) = ("Not",[pr],[],[],[])
predParts (And prs) = ("And",prs,[],[],[])
predParts (Or prs) = ("Or",prs,[],[],[])
predParts (NDC pr1 pr2) = ("NDC",[pr1,pr2],[],[],[])
predParts (Imp pr1 pr2) = ("Imp",[pr1,pr2],[],[],[])
predParts (RfdBy pr1 pr2) = ("RfdBy",[pr1,pr2],[],[],[])
predParts (Eqv pr1 pr2) = ("Eqv",[pr1,pr2],[],[],[])
predParts (Lang s p les ss) = langParts s les
predParts (If prc prt pre) = ("If",[prc,prt,pre],[],[],[])
predParts (Forall tt qs pr) = ("Forall",[pr],[],[qs],[])
predParts (Exists tt qs pr) = ("Exists",[pr],[],[qs],[])
predParts (Exists1 tt qs pr) = ("Exists1",[pr],[],[qs],[])
predParts (Univ tt pr) = ("Univ",[pr],[],[],[])

predParts (Sub (Obs e) sub@(Substn ssub))
   = ( "(e)Sub"
     , []
     , [Esub e sub]
     , [Q $ map fst ssub]
     , []
     )
predParts (Sub pr (Substn ssub))
   = ( "Sub"
     , [pr]
     , map snd ssub
     , [Q $ map fst ssub]
     , []
     )

predParts (Psub pr (Substn ssub))
   = ( "Sub"
     , pr:(map snd ssub)
     , []
     , [Q $ map (rootAsVar . Gen . fst) ssub]
     , []
     )
predParts (Ppabs s pr) = ("Ppabs",[pr],[],[],[])
predParts (Papp prf pra) = ("Papp",[prf,pra],[],[],[])
predParts (Psapp pr spr) = ("Psapp",[pr],[],[],[])
predParts (Psin pr spr) = ("Psin",[pr],[],[],[])
predParts (Pforall pvs pr) = ("Pforall",[pr],[],[],[])
predParts (Pexists pvs pr) = ("Pexists",[pr],[],[],[])
predParts (Peabs s pr) = ("Peabs",[pr],[],[],[])
predParts (Pfocus prf) = ("Pfocus",[prf],[],[],[])
predParts _ = ("pred",[],[],[],[])

langParts s les = ("Lang-"++s,prs,es,[],ts)
 where
  (prs,es,ts) = langp [] [] [] les
  langp srp se st [] = (reverse srp,reverse se,reverse st)
  langp srp se st ((LVar g):les) = langp srp (Var (Gen g,Scrpt,"\""):se) st les
  langp srp se st ((LType t):les)      = langp srp se     (t:st) les
  langp srp se st ((LExpr e):les)      = langp srp (e:se)     st les
  langp srp se st ((LPred pr):les)     = langp (pr:srp) se    st les
  langp srp se st ((LList les'):les)   = langp srp    se      st (les'++les)

predNPart  = fst5 . predParts
predPParts = snd5 . predParts
predEParts = thd5 . predParts
predQParts = frt5 . predParts
predTParts = fth5 . predParts
\end{code}

Generally we pull out expressions using \texttt{predParts},
and collecting top-level expressions before those
in sub-predicates.
The exception is the \texttt{Lang} construct were we take expressions
in a linear pass through the language elements
\begin{code}
exprsOf (Lang _ _ les _)
 = lesExprs [] les
 where
   lesExprs srpxe []             =  reverse srpxe
   lesExprs srpxe (le:les)       =  lesExprs (leExprs srpxe le) les
   leExprs srpxe (LVar g)        =  (Var (Gen g,Scrpt,"\""):srpxe)
   leExprs srpxe (LType _)       =  srpxe
   leExprs srpxe (LExpr e)       =  (e:srpxe)
   leExprs srpxe (LPred pr)      =  reverse (exprsOf pr) ++ srpxe
   leExprs srpxe (LList les')    =  reverse (lesExprs [] les') ++ srpxe
   leExprs srpxe (LCount les')   =  reverse (lesExprs [] les') ++ srpxe
exprsOf pr
 = let (_,prs,es,_,_) = predParts pr
   in es ++ (concat $ map exprsOf prs)
\end{code}

\begin{code}
exprParts :: Expr -> (String,[Pred],[Expr],[QVars])
exprParts T                  = ("T",[],[],[])
exprParts F                  = ("F",[],[],[])
exprParts (Num _)            = ("Num",[],[],[])
exprParts (Var (_,_,s))      = ("Var:"++s,[],[],[])
exprParts (Prod es)          = ("Prod",[],es,[])
exprParts (App s e)          = ("App",[],[e],[])
exprParts (Bin s i e1 e2)    = ("Bin",[],[e1,e2],[])
exprParts (Equal e1 e2)      = ("Equal",[],[e1,e2],[])
exprParts (Set es)           = ("Set",[],es,[])
exprParts (Setc tt qs pr e)  = ("Setc",[pr],[e],[qs])
exprParts (Seq es)           = ("Seq",[],es,[])
exprParts (Seqc tt qs pr e)  = ("Seqc",[pr],[e],[qs])
exprParts (Map drs)          = ("Map",[],(uncurry (++) (unzip drs)),[])
exprParts (Cond pc et ee)    = ("Cond",[pc],[et,ee],[])
exprParts (Build s es)       = ("Build",[],es,[])
exprParts (The tt x pr)      = ("The",[pr],[],[Q [x]])
exprParts (Evar (_,_,s))     = ("EVar:"++s,[],[],[])
exprParts (Eabs tt qs e)     = ("Eabs",[],[e],[qs])
exprParts (Esub e (Substn ssub))
  = ( "Esub"
    , []
    , e:(map snd ssub)
    , [Q $ map fst ssub]
    )
exprParts (EPred p) = ("Epred",[p],[],[])
exprParts (Efocus ef) = ("Efocus",[],[ef],[])
exprParts _ = ("expr",[],[],[])

exprNPart  = fst4 . exprParts
exprPParts = snd4 . exprParts
exprEParts = thd4 . exprParts
exprQParts = frt4 . exprParts
\end{code}

Generally we pull out predicates using \texttt{exprParts},
and collecting top-level predicates before those
in sub-expressions.
The exception is the \texttt{Lang} construct were we take expressions
in a linear pass through the language elements
\begin{code}

predsOf e
 = let (_,prs,es,_) = exprParts e
   in prs ++ (concat $ map predsOf es)

\end{code}

Extracting the language components is useful
\begin{code}
exprLang :: Expr -> [String]
exprLang (Prod es)       = exprsLang es
exprLang (App s e)       = exprLang e
exprLang (Bin s i e1 e2) = exprsLang [e1,e2]
exprLang (Equal e1 e2)   = exprsLang [e1,e2]
exprLang (Set es)        = exprsLang es
exprLang (Setc tt qs pr e)  = predLang pr `mrgnorm` exprLang e
exprLang (Seq es)        = exprsLang es
exprLang (Seqc tt qs pr e)  = predLang pr `mrgnorm` exprLang e
exprLang (Map drs)       = exprsLang (de++re) where (de,re)=unzip drs
exprLang (Cond pc et ee) = predLang pc `mrgnorm` exprsLang [et,ee]
exprLang (Build s es)    = exprsLang es
exprLang (The tt qs pr)     = predLang pr
exprLang (Eabs tt qs e)     = exprLang e
exprLang (Esub e sub)    = exprLang e `mrgnorm` subLang exprsLang sub
exprLang (EPred p)     = predLang p
exprLang (Efocus ef)     = exprLang ef
exprLang e               = []

exprsLang [] = []
exprsLang (e:es) = exprLang e `mrgnorm` exprsLang es

subLang slang (Substn ssub) = slang (map snd ssub)

predLang :: Pred -> [String]
predLang (Obs e)            = exprLang e
predLang (Defd e)           = exprLang e
predLang (TypeOf e t)       = exprLang e
predLang (Not pr)              = predLang pr
predLang (And prs)             = predsLang prs
predLang (Or prs)              = predsLang prs
predLang (Imp pr1 pr2)         = predsLang [pr1,pr2]
predLang (Eqv pr1 pr2)         = predsLang [pr1,pr2]
predLang (Forall tt qs pr)        = predLang pr
predLang (Exists tt qs pr)        = predLang pr
predLang (Exists1 tt qs pr)       = predLang pr
predLang (Univ tt pr)             = predLang pr
predLang (Sub pr sub)          = predLang pr `mrgnorm` subLang exprsLang sub
predLang (If prc prt pre)      = predsLang [prc,prt,pre]
predLang (NDC pr1 pr2)         = predsLang [pr1,pr2]
predLang (RfdBy pr1 pr2)       = predsLang [pr1,pr2]
predLang (Lang s p les ss)     = insnorm s (langsLang les)
predLang (Peabs s pr)          = predLang pr
predLang (Ppabs s pr)          = predLang pr
predLang (Papp prf pra)        = predsLang [prf,pra]
predLang (Psapp pr spr)        = predLang pr `mrgnorm` psetLang spr
predLang (Psin pr spr)         = predLang pr `mrgnorm` psetLang spr
predLang (Pforall pvs pr)      = predLang pr
predLang (Pexists pvs pr)      = predLang pr
predLang (Psub pr sub)         = predLang pr `mrgnorm` subLang predsLang sub
predLang (Pfocus prf)          = predLang prf
predLang pr                    = []

predsLang [] = []
predsLang (pr:prs) = predLang pr `mrgnorm` predsLang prs

psetLang (PSet prs) = predsLang prs
psetLang (PSetC _ pr1 pr2) = predsLang [pr1,pr2]
psetLang (PSetU s1 s2) = psetLang s1 `mrgnorm` psetLang s2
psetLang _ = []

langLang :: LElem -> [String]
langLang (LExpr e)    = exprLang e
langLang (LPred pr)   = predLang pr
langLang (LList les)  = langsLang les
langLang (LCount les) = langsLang les
langLang le           = []

langsLang [] = []
langsLang (le:les) = langLang le `mrgnorm` langsLang les
\end{code}



\subsubsection{Pvar table building}

Building tables from \texttt{Pvar}-value lists:
\begin{code}
plupdate :: Trie t -> [(Pred, t)] -> Trie t
plupdate = foldr mkpentry
mkpentry (Pvar (Std f),t) trie = tupdate f t trie
mkpentry (Pvar (Lst f),t) trie = tupdate (f++"$") t trie
mkpentry _          trie = trie
\end{code}
