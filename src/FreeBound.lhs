\section{Free and Bound Variables}

\begin{code}
module FreeBound where
import Tables
import Datatypes
import DataText
import Utilities
import MatchTypes
import Matching
import Instantiate

import Data.List
import Data.Maybe
\end{code}

In non-pattern predicates and expressions,
we have three classes of variables:
\begin{enumerate}
  \item observation variables in expressions (\texttt{Var})
  \item meta-variables denoting entire expressions
      (\texttt{Evar})
  \item meta-variables denoting whole predicates
      (\texttt{Pvar})
\end{enumerate}

We provide three functions that return free variables of the
various classes.
These functions have two accumulation lists, the first
(\texttt{bs})
being the
binding variables encountered in getting to the current point,
whilst the second (\texttt{fs}) is the free variables found to
date.


Also adding in quantifier variables to a bindings
list will be handy:
\begin{code}
bs +|+ qs = bs ++ getqovars qs
\end{code}

Stripping predicates, expressions and types from a language
construct
\begin{code}
lesTypes :: [LElem] -> [Type]
lesTypes = concat . map leTypes

leTypes :: LElem -> [Type]
leTypes (LType pr) = [pr]
leTypes (LList les) = lesTypes les
leTypes (LCount les) = lesTypes les
leTypes _ = []


lesExprs :: [LElem] -> [Expr]
lesExprs = concat . map leExprs

leExprs :: LElem -> [Expr]
leExprs (LExpr pr) = [pr]
leExprs (LList les) = lesExprs les
leExprs (LCount les) = lesExprs les
leExprs _ = []

lesPreds :: [LElem] -> [Pred]
lesPreds = concat . map lePreds

lePreds :: LElem -> [Pred]
lePreds (LPred pr) = [pr]
lePreds (LList les) = lesPreds les
lePreds (LCount les) = lesPreds les
lePreds _ = []
\end{code}



\newpage
\subsection{Free Observation Variables (Theory)}

\input{doc/FreeBound-ObsVar-Theory}

\newpage
\subsection{Set Expressions(Code)}

We reprise the set expression syntax:
\begin{eqnarray*}
   s \in S &::=& \setof{\vec v,\lstvec q}
\\ &|& E
\\ &|& s \setminus s
\\ &|&  \bigcup \setof{\vec s}
\\ &|&  m \sthen s
\\ &|&  m \ssthen \lst r\setminus \setof{\vec v,\lstvec q}
\\ &|&  \lst r
\\ m \in Mmbr  & ::= & v \in s | \lst q \in s  | \bigwedge (m_1,\ldots,m_n)
\end{eqnarray*}

The actual representation we use is re-factored to
support normalisation:
\begin{eqnarray*}
   a \in Atm &::=& \setof{\vec v,\lstvec q}
               | E \setminus \setof{\vec v,\lstvec q}
               | \lst r \setminus \setof{\vec v,\lstvec q}
\\ c \in CndSet &::=& a
                    | \bigwedge(m,\ldots,m) \sthen c
                    | m \ssthen \lst r \setminus \setof{\vec v,\lstvec q}
\\ m \in Mmbr &::=& v \in c | \lst q \in c
\\ s \in S &::=& \bigcup \setof{\vec c}
\end{eqnarray*}

First, we introduce datatypes to represent free-variable
set-expression (normal) forms.

First, atomic sets:
\begin{eqnarray*}
  a \in A &::=& \setof{\vec v,\lstvec q}
| E \setminus \setof{\vec v,\lstvec q}
| \lst r \setminus \setof{\vec v,\lstvec q}
\end{eqnarray*}

\begin{code}
data AtomicSet
 = Enum [Variable]  -- Enumeration
 | NameE String [Variable] -- Evar name, with subtraction enumeration
 | NameP String [Variable] -- Pvar name, with subtraction enumeration
 | NameQ Variable [Variable] -- Qvar name, with subtraction enumeration
 deriving (Eq,Ord)

instance Show AtomicSet where
  show (Enum vs) = showFVEnum vs
  show (NameE enm []) = enm
  show (NameE enm as) = enm ++ "\\" ++ showFVEnum as
  show (NameP pnm []) = pnm
  show (NameP pnm as) = pnm ++ "\\" ++ showFVEnum as
  show (NameQ pnm []) = showVar pnm
  show (NameQ pnm as) = showVar pnm ++ "\\" ++ showFVEnum as

showFVName nm = "fv."++nm
--showFVEnum xs =  "{" ++ (concat (intersperse "," xs)) ++ "}"
showFVEnum xs =  concat (intersperse "," $ map showVar xs)
\end{code}

\newpage
Conditionals:
\begin{eqnarray*}
  c \in CndSet &::=&
   a
   | \bigwedge(m,\ldots,m) \sthen c
   |  m \ssthen \lst r \setminus \setof{\vec v,\lstvec q}
\end{eqnarray*}
\begin{code}
data CondSet
 = Atom AtomicSet
 | CondSet [MmbrShp] CondSet
 | QCondSet MmbrShp Variable [Variable]
 | BadCondSet String
 deriving (Eq,Ord)

instance Show CondSet where
 show (Atom set) = show set
 show (CondSet [] set) = show set
 show (CondSet conds set)
  = "(" ++(concat $ intersperse "/\\" $ map show conds)
     ++ " => " ++ show set ++ ")"
 show (QCondSet cond r vs)
  = "(" ++ show cond ++ " =>> " ++ showVar r ++ showvs vs++")"
  where showvs [] = ""
        showvs vs = "\\"++showFVEnum vs
 show (BadCondSet msg) = "bad-FVC("++msg++")"
\end{code}

Membership:
\begin{eqnarray*}
m \in Mmbr &::=& v \in c | \lst q \in c
\end{eqnarray*}
\begin{code}
data MmbrShp
 = MmbrShp Variable CondSet -- with no subtraction enumeration (?)
 deriving (Eq,Ord)

instance Show MmbrShp where
  show (MmbrShp a set) = showVar a ++ ".in." ++ show set
\end{code}


Unions:
\begin{eqnarray*}
 s \in S &::=& \bigcup \setof{\vec c}
\end{eqnarray*}
\begin{code}
data FVSetExpr
 = FVSet [CondSet]
 | BadFVSet String
 deriving (Eq,Ord)

instance Show FVSetExpr where
 show (FVSet [])  = "Closed"
 show (FVSet css) = concat $ intersperse " U " $ map show css
 show (BadFVSet msg) = "bad-FV("++msg++")"

fvClosed = FVSet []
\end{code}

\newpage

We now define builder functions that match our set-expression
language,
but which normalise on-the-fly.
\begin{code}
atomNull = Enum []
condSetNull = Atom atomNull
fvsNull = FVSet []
\end{code}

First, the atomic cases:
\begin{eqnarray*}
   s &=& \bigcup( \top \sthen s )
\end{eqnarray*}
\begin{code}
fvsEnum :: [Variable] -> FVSetExpr
fvsEnum as = fvsAtomic (Enum (lnorm as))

fvsNameE :: String -> FVSetExpr
fvsNameE enm = fvsAtomic (NameE enm [])

fvsNameP :: String -> FVSetExpr
fvsNameP pnm = fvsAtomic (NameP pnm [])

fvsNameQ :: Variable -> FVSetExpr
fvsNameQ qnm = fvsAtomic (NameQ qnm [])

fvsAtomic :: AtomicSet -> FVSetExpr
fvsAtomic a = FVSet [Atom a]

nullAtom (Enum []) = True
nullAtom _         = False
\end{code}

\newpage
$s \setminus \setof{a_i}$ becomes  $s$ \verb"`fvsDiff`"
$\setof{a_i}$.
\begin{eqnarray*}
\\ \bigcup( s_i ) \setminus \setof{ a_i }
   &=&
   \bigcup( s_i \setminus \setof{ a_i} )
\\ (m \sthen s) \setminus \setof{a_i} &=& m \sthen (s \setminus
\setof{a_i})
\\ (s \setminus \setof{ a_i} ) \setminus \setof{ a_j }
   &=&
   s \setminus \setof{ a_i, a_j }
\\ \setof{ a_i } \setminus \setof{ a_j }
   &=& \setof{ a_k }, \quad a_k \in a_i, a_k \notin a_j
\\ m \sthen \setof{} &=& \setof{}
\end{eqnarray*}
\begin{code}
fvsDiff :: FVSetExpr -> [Variable] -> FVSetExpr

fvsDiff bad@(BadFVSet _) _ = bad

fvsDiff (FVSet condsets) as
 = FVSet $ mergeAtomic $ filter nonnullCondSet  $ map (csDiff $ lnorm as) condsets

nonnullCondSet (Atom atom)             = not (nullAtom atom)
nonnullCondSet (CondSet _ (Atom atom)) = not (nullAtom atom)
nonnullCondSet _                       = True

csDiff :: [Variable] -> CondSet -> CondSet
csDiff as (Atom atom) = Atom (asDiff as atom)
csDiff as (CondSet setconds (Atom atom))
 | nullAtom atom'  =  condSetNull
 | otherwise       =  CondSet setconds $ Atom atom'
 where atom' = (asDiff as atom)
csDiff as (CondSet setconds subcond) =
  case csDiff as subcond of
    (Atom atom') | nullAtom atom'  ->  condSetNull
    subcond'                       ->  CondSet setconds subcond'
csDiff as (QCondSet setconds r vs)
 | r `elem` as  =  condSetNull
 | otherwise    =  QCondSet setconds r $ lnorm (vs++as)
csDiff _ cs@(BadCondSet _) = cs

-- do we hardwire the fact that E and P are obsvar healthy ?
-- or should it be a side-condition?
asDiff :: [Variable] -> AtomicSet -> AtomicSet
asDiff as (Enum vs) = Enum (vs \\ as)
asDiff as (NameE enm as1) = NameE enm (asDiffNorm (as++as1))
asDiff as (NameP pnm as1) = NameP pnm (asDiffNorm (as++as1))
asDiff as (NameQ qnm as1) = NameQ qnm (lnorm (as++as1))

asDiffNorm = filter (not.isLstV) . lnorm

mergeAtomic :: [CondSet] -> [CondSet]
mergeAtomic [] = []
mergeAtomic [cs] = [cs]

mergeAtomic (CondSet [] (Atom (Enum xs)):CondSet [] (Atom (Enum ys)):css)
 = mergeAtomic (CondSet [] (Atom (Enum (lnorm (xs++ys)))):css)

mergeAtomic (CondSet [] (Atom (NameE enm1 as1)):CondSet [] (Atom (NameE enm2 as2)):css)
 | enm1 == enm2  =   mergeAtomic (CondSet [] (Atom (NameE enm1 (lnorm (as1 `intersect` as2)))):css)

mergeAtomic (CondSet [] (Atom (NameP pnm1 as1)):CondSet [] (Atom (NameP pnm2 as2)):css)
 | pnm1 == pnm2  =   mergeAtomic (CondSet [] (Atom (NameP pnm1 (lnorm (as1 `intersect` as2)))):css)

mergeAtomic (CondSet [] (Atom (NameQ qnm1 as1)):CondSet [] (Atom (NameQ qnm2 as2)):css)
 | qnm1 == qnm2  =   mergeAtomic (CondSet [] (Atom (NameQ qnm1 (lnorm (as1 `intersect` as2)))):css)

mergeAtomic (cs:css) = cs : mergeAtomic css
\end{code}

\newpage
$ \bigcup ( s_i )$ becomes \verb"fvsUnion [" $s_i$ \verb"]".
\begin{code}
fvsUnion :: [FVSetExpr] -> FVSetExpr
fvsUnion fvsets
 | null bad = FVSet css'
 | otherwise = head bad
 where
   (good,bad) = partition isgood fvsets
   isgood (BadFVSet _) = False
   isgood _            = True
   strip (FVSet cs) = cs
   css = map strip good
   css' = fvsUNorm css

fvsUNorm :: [[CondSet]] -> [CondSet]
fvsUNorm css = mergeAtomic $ fvsSubsume $ foldr mrgnorm [] css

fvsSubsume :: [CondSet] -> [CondSet]
fvsSubsume [] = []
fvsSubsume (condset:condsets)
  = condset : fvsSubsume (csSubsume condset condsets)
\end{code}


We say that $c_1$ ``subsumes'' $c_2$ if, for all $\rho$
we have $\sem{c_1}_\rho \supseteq \sem{c_2}_\rho$.
We write code that walks down a list of $c$ comparing them
to a reference one, and dropping any subsumed by that reference:
\begin{code}
csSubsume :: CondSet -> [CondSet] -> [CondSet]
csSubsume c0 cs = filter (not . csSubsume' c0) cs

csSubsume' :: CondSet -> CondSet -> Bool
csSubsume' c (Atom (Enum [])) = True
\end{code}

Rules for Atom subsumption:
\begin{eqnarray*}
   vs \supseteq us &\equiv&  us \subseteq vs
\\ E\setminus vs \supseteq F\setminus us &\equiv& E=F \land vs \subseteq us
\\ \lst r\setminus vs \supseteq \lst q\setminus us &\equiv& \lst r=\lst q \land vs \subseteq us
\\ a \supseteq {} \land\!ms \sthen c &\impliedby& a \supseteq c
\end{eqnarray*}
\begin{code}
csSubsume' a@(Atom _) (CondSet _ c) = csSubsume' a c
csSubsume' (Atom (Enum vs)) (Atom (Enum us)) = us `subsetOf` vs
csSubsume' (Atom (NameE m vs)) (Atom (NameE n us)) = m==n && vs `subsetOf` us
csSubsume' (Atom (NameP m vs)) (Atom (NameP n us)) = m==n && vs `subsetOf` us
csSubsume' (Atom (NameQ m vs)) (Atom (NameQ n us)) = m==n && vs `subsetOf` us
\end{code}

Rules for $\sthen$ subsumption:
\begin{eqnarray*}
   {}\land\!ms \sthen c \supseteq \land  {}\!ns \sthen d
   &\equiv& (\land\!ns \implies \land\!ms) \land c \supseteq d
\end{eqnarray*}
\begin{code}
csSubsume' (CondSet ms c) (CondSet ns d) = msSubsume ms ns && csSubsume' c d
\end{code}

\newpage
Rules for $\ssthen$ subsumption:
\begin{eqnarray*}
   m \ssthen \lst r \setminus vs \supseteq n \ssthen \lst q \setminus us
   &\equiv& (n\implies m) \land \lst r = \lst q \land vs \subseteq us
\end{eqnarray*}
\begin{code}
csSubsume' (QCondSet m r vs) (QCondSet n q us)
 = r==q && vs `subsetOf` us && msSubsume [m] [n]

csSubsume' (BadCondSet _) (BadCondSet _) = True -- one error is enough

csSubsume' _ _ = False
\end{code}

Membership subsumption:
\begin{eqnarray*}
   \bigwedge_i(n_i) \implies \bigwedge_j(m_j)
   &\equiv&
   \forall j @ \exists i @ n_i \implies m_j
\\ v \in c \impliedby u \in d    &\equiv& u=v \land d \subseteq c
\end{eqnarray*}
\begin{code}
--  want/\ ns => /\ms
msSubsume ms ns  = all (msSubsume' ns) ms

msSubsume' ns m = any (mSubsume m) ns

mSubsume (MmbrShp v c) (MmbrShp u d) = u==v && csSubsume' c d
\end{code}


\newpage
$ v \in s_1 \sthen s_2 $ becomes $(v,s_1)$ \verb"`fvsCond`" $s_2$.

\begin{eqnarray*}\textstyle
   v \in \bigcup_i (m_i \sthen s_i) \sthen \bigcup_j (n_j \sthen t_j)
   &=& \textstyle \bigcup_{i,j} \left( v \in (m_i \sthen s_i) \sthen (n_j \sthen t_j) \right)
\\ v \in (m_i \sthen s_i) \sthen (n_j \sthen t_j) &=& {}\land(m_i,v \in s_i, n_j) \sthen t_j
\\ v \in (m_i \sthen s_i) \sthen (n_j \ssthen \lst r_j) &=& {}\land(m_i,v \in s_i) \sthen (n_j \ssthen \lst r_j)
\\ v \in (m_i \ssthen \lst r_i) \sthen (n_j \sthen t_j) &=& stet
\\ v \in (m_i \ssthen \lst r_i) \sthen (n_j \ssthen \lst r_j) &=& stet
\\ \bigwedge( m_i, v \in \setof{ a_i} ) \sthen s
  &=& \setof{}, \qquad \mbox{if }v \notin \setof{a_i}
\\&=& \bigwedge( m_i ) \sthen s, \qquad \mbox{if } v \in \setof{a_i}
\end{eqnarray*}
Here we use $stet$ to say that, while there might be transformations possible,
we don't do them.
\begin{code}
fvsCond :: (Variable,FVSetExpr) -> FVSetExpr -> FVSetExpr

fvsCond (_,bad@(BadFVSet _)) _  =  bad
fvsCond _     bad@(BadFVSet _)  =  bad

fvsCond (a,FVSet mcondsets) (FVSet ncondsets)
 = FVSet (fvsUNorm (map (csCondOuter (a,ncondsets)) mcondsets))

csCondOuter :: (Variable,[CondSet]) -> CondSet -> [CondSet]
csCondOuter (a,ncondsets) mcondset
 = filter nonnullCondSet (map (csCondInner a mcondset) ncondsets)

csCondInner :: Variable -> CondSet -> CondSet -> CondSet
csCondInner a (CondSet ms s) (CondSet ns t)     = CondSet ((MmbrShp a s):(ms++ns)) t
csCondInner a (CondSet ms s) q@(QCondSet _ _ _) = CondSet ((MmbrShp a s):ms) q
csCondInner a mcondset ncondset                 = CondSet [MmbrShp a mcondset] ncondset


-- = simplifyCondSet atom [] (lnorm ((MmbrShp ma matom):msetconds++setconds))

-- csQCondInner :: [MmbrShp] -> Variable -> Variable -> CondSet -> CondSet
-- csQCondInner setconds ma r (CondSet msetconds matom)
--  = simplifyCondSet (NameQ r []) [] (lnorm ((MmbrShp ma matom):msetconds++setconds))

-- simplifyCondSet :: AtomicSet -> [MmbrShp] -> [MmbrShp] -> CondSet
-- simplifyCondSet atom sdnoc [] = CondSet (reverse sdnoc) atom
-- simplifyCondSet atom sdnoc ((MmbrShp a (Enum as)):rest)
--  | a `elem` as  = simplifyCondSet atom sdnoc rest
--  | otherwise = CondSet [] (Enum [])
-- simplifyCondSet atom sdnoc (cond:rest) = simplifyCondSet atom (cond:sdnoc) rest
\end{code}


\newpage
$ \lst q \in s \ssthen \lst r \setminus vs$ becomes $(\lst q,s)$ \verb"`fvsQCond`" $(\lst r,vs)$.

\begin{eqnarray*}\textstyle
   \lst q \in \bigcup_i (m_i \sthen s_i) \ssthen \lst r
   &=& \textstyle \bigcup_i \left( \lst q \in (m_i \sthen s_i) \ssthen \lst r \right)
\\ \lst q \in (m_i \sthen s_i) \ssthen \lst r &=& ??
\\ \lst q \in (m_i \ssthen \lst r_i) \ssthen \lst r &=& ??
\\ \bigwedge( m_i, \lst q \in \setof{ a_i} ) \ssthen \lst r
  &=& \setof{}, \qquad \mbox{if }\lst q \not\subseteq \setof{a_i}
\\&=& \bigwedge( m_i ) \ssthen \lst r, \qquad \mbox{if } v \in \setof{a_i}
\end{eqnarray*}
Here we use $stet$ to say that, while there might be transformations possible,
we don't do them.

\begin{code}
fvsQCond :: (Variable,FVSetExpr) -> (Variable,[Variable]) -> FVSetExpr

fvsQCond (_,bad@(BadFVSet _)) _  =  bad
fvsQCond (q,FVSet mcondsets) (r,vs)
 = FVSet $ map (csQCondOuter q r vs) mcondsets

csQCondOuter q r vs mcondset = QCondSet (MmbrShp q mcondset) r vs
\end{code}





\newpage
\subsection{Free Observation Variables (Code)}

Computing free variables for our example language:
\begin{eqnarray*}
   \fv(x) &\defs& \setof x
\\ \fv(e_1~e_2) &\defs& \bigcup( \fv e_1,\fv e_2 )
\\ \fv(\lambda \vec x,\lstvec q @ e) &\defs& (\fv e) \setminus \setof{\vec x,\lstvec q}
\\ \fv(E) &\defs& E
\\ \fv (e[\vec f,\lstvec r/\vec x,\lstvec q])
   &\defs&
   \fv(e)\setminus \setof{\vec x,\lstvec q}
\\ && {} \cup
   \bigcup_i
   \setof{
     x_i \in \fv(e) \sthen \fv(f_i)
   }
\\ && {} \cup
   \bigcup_j
   \setof{
     \lst q_j \in \fv(e) \ssthen \lst r_j
   }
\end{eqnarray*}
We can now define functions to return free-variable information
as set-expressions.


Expressions:
\begin{code}
exprFVSet :: MatchContext -> Expr -> FVSetExpr
exprFVSet mctxt (Var s)         = fvsEnum [s]
exprFVSet mctxt (App s es)       = exprsFVSet mctxt es
exprFVSet mctxt (Equal e1 e2)   = exprsFVSet mctxt [e1,e2]
exprFVSet mctxt (The tt x pr)      = predFVSet mctxt pr `fvsDiff` [x]
exprFVSet mctxt (Eabs tt qs e)     = exprFVSet mctxt e
                                        `fvsDiff` getqvars qs
-- exprFVSet mctxt (Evar s) = fvsNameE $ varKey s -- REVIEW
exprFVSet mctxt (Esub e sub)    = esubFVSet mctxt
                                          (exprFVSet mctxt e)
                                          sub
exprFVSet mctxt (Efocus ef)     = exprFVSet mctxt ef
exprFVSet mctxt _               = fvsNull

exprsFVSet :: MatchContext -> [Expr] -> FVSetExpr
exprsFVSet mctxt = fvsUnion . map (exprFVSet mctxt)
\end{code}

\newpage
Substitutions:
\begin{eqnarray*}
   \fv (e[\vec f,\lstvec r/\vec x,\lstvec q])
   &\defs&
   \fv(e)\setminus \setof{\vec x,\lstvec q}
\\ && {} \cup
   \bigcup_i
   \setof{
     x_i \in \fv(e) \sthen \fv(f_i)
   }
\\ && {} \cup
   \bigcup_j
   \setof{
     \lst q_j \in \fv(e) \ssthen \lst r_j
   }
\end{eqnarray*}
\begin{code}
esubFVSet :: MatchContext -> FVSetExpr -> ESubst -> FVSetExpr
esubFVSet mctxt fvbase (Substn sub)
 = fvsUnion ((fvbase `fvsDiff` (xs++qs)):(map insidef ssub++map insider msub))
 where
   (msub,ssub) = partition (isLstV . fst) sub
   xs = map fst ssub
   qs = map fst msub
   insidef (x,f) = (x,fvbase) `fvsCond` (exprFVSet mctxt f)
   insider (q,Var r) = (q,fvbase) `fvsQCond` (r,[])
   insider (q,e) = error ("esubFVSet.insider fails on "++show e)

psubFVSet :: MatchContext -> FVSetExpr -> PSubst -> FVSetExpr
psubFVSet mctxt fvbase (Substn sub)
 = fvsUnion ((fvbase `fvsDiff` xs):(map insidef sub))
 where
   xs = map (rootVar . Gen . fst) sub
   insidef (x,f) = (rootVar $ Gen x,fvbase) `fvsCond` (predFVSet mctxt f)
\end{code}

We need a \texttt{MatchContext} so that we can look up any
user-defined
language construct definitions to expand their definitions
in order to determine free variables.
To avoid infinite loops given (mutually) recursive
language definitions, we keep track of constructs
expanded so far, only allowing one translation per construct at
present.

Predicates are as expected, except that \texttt{Pvar} $\_UNINT$
(uninterpreted)
returns a null set result:
\begin{code}
predFVSet :: MatchContext -> Pred -> FVSetExpr

predFVSet mctxt (Pvar r)
 | s == nameUNINT  =  fvsNull
 | otherwise       =  fvsNameP s
 where s = show r

predFVSet mctxt (Obs e)            = exprFVSet mctxt e
predFVSet mctxt (Defd e)            = exprFVSet mctxt e
predFVSet mctxt (TypeOf e t)        = exprFVSet mctxt e
predFVSet mctxt (Not pr)              = predFVSet mctxt pr
predFVSet mctxt (And prs)             = predsFVSet mctxt prs
predFVSet mctxt (Or prs)              = predsFVSet mctxt prs
predFVSet mctxt (Imp pr1 pr2)         = predsFVSet mctxt [pr1,pr2]
predFVSet mctxt (Eqv pr1 pr2)         = predsFVSet mctxt [pr1,pr2]
predFVSet mctxt (NDC pr1 pr2)         = predsFVSet mctxt [pr1,pr2]
predFVSet mctxt (Papp pr1 pr2)        = predsFVSet mctxt [pr1,pr2]

predFVSet mctxt (Psapp pr spr)        = fvsUnion [ predFVSet mctxt pr
                                                 , psetFVSet mctxt spr ]
predFVSet mctxt (Psin pr spr)         = fvsUnion [ predFVSet mctxt pr
                                                 , psetFVSet mctxt spr ]

predFVSet mctxt (If prc prt pre)      = predsFVSet mctxt [prc,prt,pre]
predFVSet mctxt (Forall _ qs pr)        = predFVSet mctxt pr
                                              `fvsDiff` getqvars qs
predFVSet mctxt (Exists _ qs pr)        = predFVSet mctxt pr
                                           `fvsDiff` getqvars qs
predFVSet mctxt (Exists1 _ qs pr)       = predFVSet mctxt pr
                                              `fvsDiff` getqvars qs
predFVSet mctxt (Sub pr sub)          = esubFVSet mctxt
                                              (predFVSet mctxt pr) sub
predFVSet mctxt (Psub pr sub)         = predFVSet mctxt pr
predFVSet mctxt (Peabs qs pr)          = predFVSet mctxt pr
predFVSet mctxt (Ppabs qs pr)          = predFVSet mctxt pr
predFVSet mctxt (Pfocus prf)          = predFVSet mctxt prf
predFVSet mctxt lang@(Lang _ _ _ _)  = langFVSet mctxt lang

predFVSet mctxt _                     = fvsNull

predsFVSet :: MatchContext -> [Pred] -> FVSetExpr
predsFVSet mctxt prs = fvsUnion $ map (predFVSet mctxt) prs

psetFVSet mctxt (PSet prs)        = predsFVSet mctxt prs
psetFVSet mctxt (PSetC _ pr1 pr2) = predsFVSet mctxt [pr1,pr2]
psetFVSet mctxt (PSetU s1 s2)     = fvsUnion [ psetFVSet mctxt s1
                                             , psetFVSet mctxt s2 ]
psetFVSet mctxt _                 = fvsNull
\end{code}

Language constructs:
\begin{code}
langFVerr nm msg = ("User construct `"++nm++"` "++msg)

langFVSet :: MatchContext -> Pred -> FVSetExpr
langFVSet mctxt lang@(Lang nm _ _ _)
 = case tslookup (langDefns mctxt) nm of
     Nothing  ->  BadFVSet (langFVerr nm "not defined")
     Just ldefs
      ->  case ldefsMatch mctxt lang ldefs of
        Just expandedPr  ->  predFVSet mctxt expandedPr
        Nothing  ->  BadFVSet
                      $ langFVerr nm
                         ("defn. matching ("++show lang++") not found")

langFVSet _ pr = BadFVSet ("??? Bad Call -- langFVSet _ _"++show pr)
\end{code}

Given a list of language definitions (lhs/rhs pairs)
we match a given construct against
the lhs sides,
failing if none match,
otherwise returning the rhs with the bindings
from the first successful match.
\begin{code}
ldefsMatch :: MatchContext -> Pred -> [LangDefn] -> Maybe Pred
ldefsMatch _ _ [] = Nothing
ldefsMatch mctxt lang ((lhs,rhs):ldefs)
 = case pMatch (LC mctxt Bnil Bnil [] [] [] []) noBinding lang lhs of
     Nothing          ->  ldefsMatch mctxt lang ldefs
     Just (bnds,_,_)  ->  Just  $ instantiatePred mctxt bnds rhs
\end{code}



\newpage
\subsection{Free Observation Variables (old Code)}

The following code should now be deprecated,
as it simply returns an enumeration of set variables,
hence is inaccurate in the presence of both meta-variables and
explicit substitutions.
However it is useful when applying a match to identify
which unbound variables need to be instantiated.

Note that using a \texttt{MatchContext} here results in known
variables
being removed from the free variable list,
and so general use should pass in \texttt{nullMatchContext}.
A non-null context should only be used when trying to
complete matches in the prover.
\begin{code}
exprFreeOVars :: MatchContext -> Expr -> [Variable]
exprFreeOVars mctxt = lnorm . efreeovars mctxt [] []
predFreeOVars  :: MatchContext -> Pred -> [Variable]
predFreeOVars mctxt = lnorm . pfreeovars mctxt [] []
exprsFreeOVars mctxt = lnorm . seq2s (efreeovars mctxt) [] []
predsFreeOVars mctxt = lnorm . seq2s (pfreeovars mctxt) [] []
\end{code}

For variables, we only return those that are not ``known'':
\begin{code}
efreeovars :: MatchContext -> [Variable] -> [Variable] -> Expr -> [Variable]
efreeovars mctxt bs fs (Var v)
 | v `elem` bs  =  fs
 | isJust sobs  =  fs
 | isJust skon  =  fs
 | otherwise    =  (v:fs)
 where
   vtxt = varKey v
   sobs = tspfxlookup (knownObs mctxt) vtxt
   skon = tspfxlookup (knownConsts mctxt) vtxt
\end{code}

The rest is mainly recursive boilerplate...
\begin{code}
efreeovars mctxt bs fs (Eabs _ qs e)     =  efreeovars mctxt (bs+|+qs) fs e

efreeovars mctxt bs fs (Esub e sub)
 = let efs = exprFreeOVars mctxt e
   in sfreevars (efreeovars mctxt) bs fs efs (qvunzip sub)

efreeovars mctxt bs fs (App s es)
 = seq2s (efreeovars mctxt) bs fs es
efreeovars mctxt bs fs (Equal e1 e2)   = seq2s (efreeovars mctxt) bs fs [e1,e2]
efreeovars mctxt bs fs (The _ x pr)  = pfreeovars mctxt (x:bs) fs pr

efreeovars mctxt bs fs (Efocus ef)     = efreeovars mctxt bs fs ef

efreeovars mctxt  _ fs _ = fs
\end{code}

When checking a variable to see if it is known,
we need to check its root if decorated.
We keep this simple, if a root is known, so are all possible decorations
of it, even if such decorations do not appear explicitly in the
observation variable tables.
\begin{code}
tspfxlookup [] _ = (fail "Nothing")
tspfxlookup (trie:tries) s
 | subtrie == tnil  =  tspfxlookup tries s
 | otherwise        =  return subtrie
 where
   subtrie = pfxSubTrie s trie
\end{code}

Now, do the same for predicates:
\begin{code}
pfreeovars :: MatchContext -> [Variable] -> [Variable] -> Pred -> [Variable]
pfreeovars mctxt bs fs (Forall _ qs pr)
                          = pfreeovars mctxt (bs+|+qs) fs pr
pfreeovars mctxt bs fs (Exists _ qs pr)
                          = pfreeovars mctxt (bs+|+qs) fs pr
pfreeovars mctxt bs fs (Exists1 _ qs pr)
                          = pfreeovars mctxt (bs+|+qs) fs pr
pfreeovars mctxt bs fs (Univ _ pr) = []

pfreeovars mctxt bs fs (Sub pr sub)
 = let prfs = predFreeOVars mctxt pr in
       sfreevars (efreeovars mctxt) bs fs prfs (qvunzip sub)

pfreeovars mctxt bs fs (Psub pr sub)
 = let prfs = predFreeOVars mctxt pr in
       sfreevars (pfreeovars mctxt) bs fs prfs (qvunzipWith (rootVar . Gen) sub)

pfreeovars mctxt bs fs (Obs e) = efreeovars mctxt bs fs e
pfreeovars mctxt bs fs (Defd e) = efreeovars mctxt bs fs e
pfreeovars mctxt bs fs (TypeOf e t) = efreeovars mctxt bs fs e
pfreeovars mctxt bs fs (Not pr) = pfreeovars mctxt bs fs pr
pfreeovars mctxt bs fs (And prs) = seq2s (pfreeovars mctxt) bs fs prs
pfreeovars mctxt bs fs (Or prs) = seq2s (pfreeovars mctxt) bs fs prs
pfreeovars mctxt bs fs (NDC pr1 pr2) = seq2s (pfreeovars mctxt) bs fs [pr1,pr2]
pfreeovars mctxt bs fs (Imp pr1 pr2) = seq2s (pfreeovars mctxt) bs fs [pr1,pr2]
pfreeovars mctxt bs fs (RfdBy pr1 pr2) = []
pfreeovars mctxt bs fs (Eqv pr1 pr2) = seq2s (pfreeovars mctxt) bs fs [pr1,pr2]
pfreeovars mctxt bs fs (Lang _ _ _ _) = []  -- n.s., fv not defined !
pfreeovars mctxt bs fs (If prc prt pre) = seq2s (pfreeovars mctxt) bs fs [prc,prt,pre]
pfreeovars mctxt bs fs (Peabs s pr) = pfreeovars mctxt bs fs pr
pfreeovars mctxt bs fs (Ppabs s pr) = pfreeovars mctxt bs fs pr

-- these are almost certainly incorrect
pfreeovars mctxt bs fs (Papp prf pra) = seq2s (pfreeovars mctxt) bs fs [prf,pra]
pfreeovars mctxt bs fs (Pforall pvs pr) = pfreeovars mctxt bs fs pr
pfreeovars mctxt bs fs (Pexists pvs pr) = pfreeovars mctxt bs fs pr

pfreeovars mctxt bs fs (Pfocus prf)     = pfreeovars mctxt bs fs prf -- ????

pfreeovars mctxt bs fs _ = fs
\end{code}

This fudge has now been superseded by a proper set-expression
based treatment
of free variable analysis described earlier in this section.
\textit{
Substitution needs special handling.
Consider the substitution:
\begin{eqnarray*}
   && P [ e_i / x_i ], i \in 1 \ldots n
\end{eqnarray*}
Then the free variables of this are defined as
\begin{eqnarray*}
  FV(P[e_i/x_i])
  &\defs&
  (FV(P) \setminus \setof{x_i}_{i=1}^n)
  \cup
  \bigcup_{i=1}^n \setof{ FV(e_i) | x_i \in FV(P) }
\end{eqnarray*}
However, if $P$ contains any meta-variables
then we can't establish the truth in general of $x_i \in
FV(P)$,
so we act conservatively, and do it for all $i$.
Having first established the free variables (\texttt{bodyfs}) of
the
entity into which the substitutions are being made,
we remove all the target variables in the substitution,
and then add in the free variables of all substitution
expressions.
}
\begin{code}
sfreevars :: ([Variable] -> [Variable] -> a -> [Variable])
          -> [Variable] -> [Variable] -> [Variable] -> ([a],[Variable])
          -> [Variable]
sfreevars freevars bs fs bodyfs (es,vs)
 = svars bs (fs++(bodyfs \\ vs)) (zip vs es)
 where
   svars bs fs'  [] = fs' \\ bs
   svars bs fs' ((v,e):ves) =  svars bs (fs'++freevars bs fs e) ves
\end{code}

\subsection{Free Expression meta-Variables}

\begin{code}
exprFreeEVars mctxt = lnorm . efreeevars mctxt [] []
predFreeEVars mctxt = lnorm . pfreeevars mctxt [] []
exprsFreeEVars mctxt = lnorm . seq2s (efreeevars mctxt) [] []
predsFreeEVars mctxt = lnorm . seq2s (pfreeevars mctxt) [] []
\end{code}

\begin{code}
-- efreeevars mctxt bs fs (Evar s)  -- REVIEW
-- | s `elem` bs  =  fs
-- | otherwise    =  (s:fs)

efreeevars mctxt bs fs (Esub e sub)
 = let efs = efreeevars mctxt [] [] e in
       sfreevars (efreeevars mctxt) bs fs efs (qvunzip sub)

efreeevars mctxt bs fs (App s es)
 = seq2s (efreeevars mctxt) bs fs es
efreeevars mctxt bs fs (Equal e1 e2)
 = seq2s (efreeevars mctxt) bs fs [e1,e2]
efreeevars mctxt bs fs (The _ qs pr)
 = pfreeevars mctxt bs fs pr
efreeevars mctxt bs fs (Eabs _ (Q qs) e)
 = efreeevars mctxt (bs++qs) fs e
efreeevars mctxt bs fs (Efocus ef)
 = efreeevars mctxt bs fs ef -- ????

efreeevars mctxt  _ fs _ = fs

pfreeevars mctxt bs fs (Sub pr sub)
 = let prfs = pfreeevars mctxt [] [] pr in
       sfreevars (efreeevars mctxt) bs fs prfs (qvunzip sub)

pfreeevars mctxt bs fs (Psub pr sub)
 = let prfs = pfreeevars mctxt [] [] pr in
       sfreevars (pfreeevars mctxt) bs fs prfs (qvunzipWith (rootVar . Gen) sub)

pfreeevars mctxt bs fs (Obs e) = efreeevars mctxt bs fs e
pfreeevars mctxt bs fs (Defd e) = efreeevars mctxt bs fs e
pfreeevars mctxt bs fs (TypeOf e t) = efreeevars mctxt bs fs e
pfreeevars mctxt bs fs (Not pr) = pfreeevars mctxt bs fs pr
pfreeevars mctxt bs fs (And prs) = seq2s (pfreeevars mctxt) bs fs prs
pfreeevars mctxt bs fs (Or prs) = seq2s (pfreeevars mctxt) bs fs prs
pfreeevars mctxt bs fs (NDC pr1 pr2) = seq2s (pfreeevars mctxt) bs fs [pr1,pr2]
pfreeevars mctxt bs fs (Imp pr1 pr2) = seq2s (pfreeevars mctxt) bs fs [pr1,pr2]
pfreeevars mctxt bs fs (RfdBy pr1 pr2) = seq2s (pfreeevars mctxt) bs fs [pr1,pr2]
pfreeevars mctxt bs fs (Eqv pr1 pr2) = seq2s (pfreeevars mctxt) bs fs [pr1,pr2]
pfreeevars mctxt bs fs (Lang _ _ les _) = seq2s (pfreeevars mctxt) bs fs (lesPreds les)
pfreeevars mctxt bs fs (If prc prt pre) = seq2s (pfreeevars mctxt) bs fs [prc,prt,pre]
pfreeevars mctxt bs fs (Forall _ qs pr) = pfreeevars mctxt bs fs pr
pfreeevars mctxt bs fs (Exists _ qs pr) = pfreeevars mctxt bs fs pr
pfreeevars mctxt bs fs (Exists1 _ qs pr) = pfreeevars mctxt bs fs pr
pfreeevars mctxt bs fs (Peabs qs pr) = pfreeevars mctxt bs fs pr
pfreeevars mctxt bs fs (Univ _ pr) = pfreeevars mctxt bs fs pr
pfreeevars mctxt bs fs (Ppabs _ pr) = pfreeevars mctxt bs fs pr

-- almost certainly incorrect
pfreeevars mctxt bs fs (Papp prf pra) = seq2s (pfreeevars mctxt) bs fs [prf,pra]

pfreeevars mctxt bs fs (Pfocus prf)     = pfreeevars mctxt bs fs prf -- ????

pfreeevars mctxt  _ fs _ = fs
\end{code}

\subsection{Free Observation and Expression Variables}

Sometimes it is useful to treat both \texttt{Var} and
\texttt{Evar} as the same:
\begin{code}
exprFreeVars mctxt e
           = lnorm (efreeovars mctxt [] [] e ++ efreeevars mctxt
           [] [] e)
predFreeVars mctxt pr
           = lnorm (pfreeovars mctxt [] [] pr ++ pfreeevars
           mctxt [] [] pr)
\end{code}
(This assumes a usage where their string values do not overlap,
 which should be the case in general)

\subsection{Free Predicate meta-Variables}

\begin{code}
exprFreePVars :: MatchContext -> Expr -> [Variable]
exprFreePVars mctxt  = lnorm . efreepvars mctxt [] []
exprsFreePVars :: MatchContext -> [Expr] -> [Variable]
exprsFreePVars mctxt = lnorm . seq2s (efreepvars mctxt) [] []

predFreePVars :: MatchContext -> Pred -> [Variable]
predFreePVars mctxt  = lnorm . pfreepvars mctxt [] []
predsFreePVars :: MatchContext -> [Pred] -> [Variable]
predsFreePVars mctxt = lnorm . seq2s (pfreepvars mctxt) [] []


efreepvars mctxt bs fs (Esub e sub)
 = let efs = efreeovars mctxt [] [] e in
       sfreevars (efreepvars mctxt) bs fs efs (qvunzip sub)

efreepvars mctxt bs fs (App s es) = seq2s (efreepvars mctxt) bs fs es
efreepvars mctxt bs fs (Equal e1 e2)
 = seq2s (efreepvars mctxt) bs fs [e1,e2]
efreepvars mctxt bs fs (The _ qs pr)
 = pfreepvars mctxt bs fs pr
efreepvars mctxt bs fs (Eabs _ qs e)
 = efreepvars mctxt bs fs e
efreepvars mctxt bs fs (Efocus ef)
 = efreepvars mctxt bs fs ef -- ????

efreepvars mctxt  _ fs _ = fs

pfreepvars mctxt bs fs (Pvar s)
 | v `elem` bs  =  fs
 | otherwise    =  v:fs
 where v = rootVar $ Gen s

pfreepvars mctxt bs fs (Ppabs (Q pvs) pr) = pfreepvars mctxt (pvs++bs) fs pr

pfreepvars mctxt bs fs (Sub pr sub)
 = let prfs = pfreepvars mctxt [] [] pr
   in sfreevars (efreepvars mctxt) bs fs prfs (qvunzip sub)

pfreepvars mctxt bs fs (Psub pr sub)
 = let prfs = pfreepvars mctxt [] [] pr
   in sfreevars (pfreepvars mctxt) bs fs prfs (qvunzipWith (rootVar . Gen) sub)

pfreepvars mctxt bs fs (Obs e) = efreepvars mctxt bs fs e
pfreepvars mctxt bs fs (Defd e) = efreepvars mctxt bs fs e
pfreepvars mctxt bs fs (TypeOf e t) = efreepvars mctxt bs fs e
pfreepvars mctxt bs fs (Not pr) = pfreepvars mctxt bs fs pr
pfreepvars mctxt bs fs (And prs) = seq2s (pfreepvars mctxt) bs fs prs
pfreepvars mctxt bs fs (Or prs) = seq2s (pfreepvars mctxt) bs fs prs
pfreepvars mctxt bs fs (NDC pr1 pr2) = seq2s (pfreepvars mctxt) bs fs [pr1,pr2]
pfreepvars mctxt bs fs (Imp pr1 pr2) = seq2s (pfreepvars mctxt) bs fs [pr1,pr2]
pfreepvars mctxt bs fs (RfdBy pr1 pr2) = seq2s (pfreepvars mctxt) bs fs [pr1,pr2]
pfreepvars mctxt bs fs (Eqv pr1 pr2) = seq2s (pfreepvars mctxt) bs fs [pr1,pr2]
pfreepvars mctxt bs fs (Lang _ _ les _) = seq2s (pfreepvars mctxt) bs fs (lesPreds les)
pfreepvars mctxt bs fs (If prc prt pre) = seq2s (pfreepvars mctxt) bs fs [prc,prt,pre]
pfreepvars mctxt bs fs (Forall _ qs pr) = pfreepvars mctxt bs fs pr
pfreepvars mctxt bs fs (Exists _ qs pr) = pfreepvars mctxt bs fs pr
pfreepvars mctxt bs fs (Exists1 _ qs pr) = pfreepvars mctxt bs fs pr
pfreepvars mctxt bs fs (Univ _ pr) = pfreepvars mctxt bs fs pr
pfreepvars mctxt bs fs (Peabs _ pr) = pfreepvars mctxt bs fs pr

pfreepvars mctxt bs fs (Papp prf pra) = seq2s (pfreepvars mctxt) bs fs [prf,pra]

pfreepvars mctxt bs fs (Pforall (Q pvs) pr) = pfreepvars mctxt (pvs++bs) fs pr
pfreepvars mctxt bs fs (Pexists (Q pvs) pr) = pfreepvars mctxt (pvs++bs) fs pr

pfreepvars mctxt bs fs (Pfocus prf)     = pfreepvars mctxt bs fs prf -- ????

pfreepvars mctxt  _ fs _ = fs
\end{code}



\subsection{Getting All Variables of some Kind}

Sometimes we just want all the variables of some kind mentioned in a
construct,
free or bound.
In so doing, we need to note if they occur in a ``general'' context
(can represent both variables or expressions over same)
or if they are found were their only interpretation can be as variables.
This latter case occurs if a variable occurs in a quantifier list,
or as the target of a substitution.
\begin{code}
data VContext = Vonly | VorT deriving (Eq,Ord,Show)
\end{code}
We will produce normalised lists of variable/context pairs
and will want to fuse same variables with different context markings
\begin{code}
vcMerge :: Eq a =>  [(a,VContext)] -> [(a,VContext)] -- assume lnormed
vcMerge [] = []
vcMerge [av] = [av]
vcMerge (av1@(a,v1):brest@((b,_):rest))
 | a == b     =  av1:vcMerge rest  -- (a,Vonly):(a,VorT):rest
 | otherwise  =  av1:vcMerge brest
\end{code}

\subsubsection{Getting All Pred/Expr Metavariables}~

\begin{code}
predAllPVars :: Pred -> [(GenRoot,VContext)]
exprAllPVars :: Expr -> [(GenRoot,VContext)]

allPVarsFold = ( ([],predAllPVars,id,concat)
               , ([],exprAllPVars,id,concat) )

predAllPVars (Pvar r)            =  [(r,VorT)]
predAllPVars (Pforall (Q ps) pr) =  lnorm  (map qPVar ps ++ predAllPVars pr)
predAllPVars (Pexists (Q ps) pr) =  lnorm  (map qPVar ps ++ predAllPVars pr)
predAllPVars (Ppabs (Q ps) pr)   =  lnorm  (map qPVar ps ++ predAllPVars pr)
predAllPVars (Psub pr psub)      =  lnorm  (predAllPVars pr ++ psubPVars psub)
predAllPVars pr                  =  lnorm $ foldP allPVarsFold pr

qPVar pv = (varGenRoot pv,Vonly)

exprAllPVars e = lnorm $ foldE allPVarsFold e

psubPVars :: PSubst -> [(GenRoot,VContext)]
psubPVars = substVars predAllPVars id

substVars :: (Ord v) => (a -> [(v,VContext)]) -> (u -> v) -> Substn u a
          -> [(v,VContext)]
substVars ovars toV (Substn sub)
 = lnorm $ concat $ map subvars sub
 where subvars (v,a) = (toV v,Vonly) : ovars a
\end{code}

\subsubsection{Getting All Pred/Expr Observation Variables}~

\begin{code}
predAllOVars :: Pred -> [(Variable,VContext)]
exprAllOVars :: Expr -> [(Variable,VContext)]

allOVarsFold = ( ([],predAllOVars,id,concat)
               , ([],exprAllOVars,id,concat) )

predAllOVars (Forall _ (Q vs) p2)  = lnorm (map qOVar vs ++ predAllOVars p2)
predAllOVars (Exists _ (Q vs) p2)  = lnorm (map qOVar vs ++ predAllOVars p2)
predAllOVars (Exists1 _ (Q vs) p2) = lnorm (map qOVar vs ++ predAllOVars p2)
predAllOVars (Peabs (Q vs) pr)     = lnorm (map qOVar vs ++ predAllOVars pr)
predAllOVars (Sub pr esub)         = lnorm (predAllOVars pr ++ esubOVars esub)
predAllOVars (Psub pr psub)        = lnorm (predAllOVars pr ++ psubOVars psub)
predAllOVars pr                    = lnorm $ foldP allOVarsFold pr

qOVar ov = (ov,Vonly)

exprAllOVars (Var s) = [(s,VorT)]
exprAllOVars (App s es)  -- ignore s for now
 = concat $ map exprAllOVars es
exprAllOVars (The _ x p2) = lnorm ([(x,Vonly)] ++ predAllOVars p2)
exprAllOVars (Eabs _ (Q vs) e)  =  lnorm (map qOVar vs ++ exprAllOVars e)
exprAllOVars (Esub e esub) = lnorm (exprAllOVars e ++ esubOVars esub)
exprAllOVars e = lnorm $ foldE allOVarsFold e


esubOVars :: ESubst -> [(Variable,VContext)]
esubOVars  =  substVars exprAllOVars id

psubOVars :: PSubst -> [(Variable,VContext)]
psubOVars  =  substVars predAllOVars (rootVar . Gen)
\end{code}


\subsubsection{Getting All Pred/Expr Type Variables }

Type variables only occur here in a general context - no type-var quantifiers
\begin{code}
predAllTVars :: Pred -> [TVar]
exprAllTVars :: Expr -> [TVar]

allTVarsFold = ( ([],predAllTVars,id,concat)
               , ([],exprAllTVars,id,concat) )

predAllTVars (TypeOf e t)  =  typeAllTVars t ++ exprAllTVars e
predAllTVars pr = lnorm $ foldP allTVarsFold pr

exprAllTVars e = lnorm $ foldE allTVarsFold e

typeAllTVars :: Type -> [TVar]
typeAllTVars (Tvar tv)     = [tv]
typeAllTVars (TApp _ ts)  = lnorm $ concat $ map typeAllTVars ts
typeAllTVars (Tfree _ ccs)
  = lnorm $ concat $ map (concat . (map typeAllTVars . snd)) ccs
typeAllTVars (Tfun t1 t2)  = lnorm (typeAllTVars t1 ++ typeAllTVars t2)
typeAllTVars _             = []
\end{code}



\subsection{Forcing Induction Variables}

When matching against an induction axiom
with a designated induction variable,
we need to ensure that any free \texttt{Evar} that matches the
induction variable
is forced to a \texttt{Var}.

\textbf{Note:}
\emph{we also need to ensure that name-capture is avoided !}
\begin{code}
forcePredInductionVar :: Variable -> Pred -> Pred
forcePredInductionVar ivar pr@(Peabs qs@(Q [evar]) pbody)
 | evar == ivar  =  pr     -- not free below, so ignore
 | otherwise     =  Peabs qs (forcePredInductionVar ivar pbody)
forcePredInductionVar ivar pr
 = mapP (forcePredInductionVar ivar, forceExprInductionVar ivar) pr

forceExprInductionVar :: Variable -> Expr -> Expr
forceExprInductionVar ivar e
 = mapE (forcePredInductionVar ivar, forceExprInductionVar ivar) e
\end{code}
