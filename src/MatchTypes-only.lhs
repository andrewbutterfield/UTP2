\section{Match Types}

\begin{code}
module MatchTypes where
import Tables
import Datatypes
\end{code}

A binding object represents the sum type $T+V+V^*+T^*$:
\begin{code}
data BObj v t
 = TO t       -- Std, Regular not bound
 | VO v       -- Std, Irregular
 | VSO [v]    -- Lst, Quantifier, Subst-Target
 | TSO [t]    -- Lst, Subst-Replace, 2-Place

\end{code}

We define a sub-binding as:
\begin{code}
type SBind v t = Trie (BObj v t)
\end{code}

\begin{code}
type GPBind = SBind GenRoot Pred
type VEBind = SBind Variable Expr
type TTBind = SBind TVar Type
\end{code}

We now define the overall binding as a triple of sub-bindings,
one each for predicates, expressions and types:
\begin{code}
type Binding = (GPBind, VEBind, TTBind)
\end{code}



Some matches, to do with \texttt{QVars}, have to be deferred for
post-processing that requires free-variable information,
as well using side-conditions as hints.
\begin{code}
type QVarMatchToDo = ([Variable],[Variable]) -- (test,pattern)
\end{code}

\begin{code}
type LocalContext
 = ( TypeTables, TypeTables   -- test,pattern
     , [TTTag], [TTTag]         -- test,pattern
     , [Variable], [Variable]   -- test,pattern
     )

type SubstMatchToDo v a
 = ( [(v,a)]  -- test substitution pairs
   , [(v,a)]  -- pattern substitution pairs
   , LocalContext
   )

type ESubstMatchToDo = SubstMatchToDo Variable Expr
\end{code}

A match-result is bindings with lists of deferred \texttt{QVar} and \texttt{Substn}
matches.
\begin{code}
type MatchResult = (Binding,[QVarMatchToDo],[ESubstMatchToDo])
\end{code}

A match-outcome either fails,
or returns a binding with deferred \texttt{QVars} and \texttt{ESubst} matches.
\begin{code}
type MatchOutcome = Maybe MatchResult
\end{code}

\newpage

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
\end{code}

We want to be able to rank based on match-type,
level of trust, as well as the bindings and replacement predicates that are part
of a successful match.
\begin{code}
type LawMatch = (MatchType,Provenance,Binding,SideCond,[Pred])
\end{code}

In addition, in order to handle user-defined language constructs properly,
we need a mapping from construct names to lists
of definitions, each represented as a lhs/rhs predicate pair.
\begin{code}
type LangDefn = (Pred,Pred)
\end{code}

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
\end{code}


We use lists to represent the explicit bijection and sets
\begin{code}
type ExplBij = [(Variable, Variable)]  -- ordered, unique
type ImplBij = ([Variable],[Variable])  -- both ordered, unique
type BIJ = ( ExplBij, ImplBij )
\end{code}
