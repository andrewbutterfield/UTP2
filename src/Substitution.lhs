\section{Substitution}

\begin{code}
module Substitution where
import Tables
import Datatypes
import DataText
import Flatten
import Focus
import MatchTypes
import Matching
import AlphaSubs
import FreeBound
import Types
import SideConditions
import Heuristics
import Utilities
import DSL
import Data.List
import Data.Maybe
import Debug.Trace
\end{code}

Here we collect a variety of built-in substitution manipulations
that can be applied the focus of a goal predicate.


\subsection{Substitution Intro}

We basically have substitutions with two parts:
individual expression-per-variable replacements ($e_i/x_i$) on the one hand,
and multiple expression-per-(list)-variable replacements ($\lst f_j/\lst y_j$),
on the other hand:
$$
  [
    e_1,\ldots,e_k,~\lst f_{k+1},\ldots,\lst f_{k+\ell}
  /
    x_1,\ldots,x_k ~,~ \lst y_1, \ldots \lst y_\ell
  ]
$$
The substitution list-variables ($\lst y_j$)
denote a list (zero or more) of underlying individual variables ($x_i$).
For this to work, each $\lst f_j$ is itself a list-variable,
that denotes a list of expressions.

The denotation of a list-variable is given by a context,
and is of the form of a list of individual variables. A denotation,
in a given context can be partial, if we are subtracting a set $S$
whose contents aren't all known observation variables.

Given that list-variables denote a list of individual variables,
there is a well-formedness condition that needs to be satisfied.
The substitution element
$$
  \lst f / \lst y
$$
is well-formed if
$\lst f$ is itself a list-variable whose denotation has the
size as that of $\lst y$.
We can always compare list-variables for size,
regardless of what is known.

\newpage
\subsection{Normalising Substitution}

We define a substitution normalisation process
transforming
$$
[\lst f/\lst y]
\qquad
\textbf{where}
\qquad
\sem{\lst f}=\seqof{v_1,\ldots,v_n}
\quad
\textbf{and}
\quad
\sem{\lst y}=\seqof{y_1,\ldots,x_n}
$$
into
$$[\texttt{Var}~v_1,\ldots,\texttt{Var}~v_n,\lst f/x_1,\ldots,x_n,\lst y]$$
where the denotation of  $\lst f$ and $\lst y$
are $v_1,\ldots,v_n$ and  $x_1,\ldots,x_n$ respectively.
It fails if the substitution is not well-formed.
So for example, given that $\sem{\lst{Var}} = \setof{x,y,x}$,
the normalisation of
 $[\lst{Var}'/\lst{Var}]$
results in
  $[x',y',z',\lst{Var}'/x,y,x,\lst{Var}]$.
This is adding in redundancy, but makes performing substitutions easier.
\begin{code}
normaliseSubstn :: MatchContext -> ESubst -> Maybe ESubst
normaliseSubstn mctxt (Substn sub)
 = do msubs' <- sequence $ map checkMulti msub
      let ssubx = concat $ map expandM msub
      return $ Substn (ssubx ++ ssub ++ concat msubs')
 where

   (msub,ssub) = partition (isLstV . fst) sub

   checkMulti :: (Variable,Expr) -> Maybe [(Variable,Expr)]
   checkMulti sublet@(y,Var f)
    | consistent y f  =  Just [sublet]
   checkMulti _ = Nothing

   -- for now we expect the same root
   consistent (yr,yd,_) (fr,fd,_)  =  yr == fr

   expandM :: (Variable,Expr) -> [(Variable,Expr)]
   expandM (y,Var f)
    | null tsubs && null rsubs && tlen == rlen
       =  zip tgtsem (map mkEVar repsem)
    | otherwise
       =  []
    where
      (tgtsem,tsubs) = lVarDenote mctxt y
      (repsem,rsubs) = lVarDenote mctxt f
      tlen = length tgtsem
      rlen = length repsem
\end{code}


\newpage
\subsection{The Extended Lambda Calculus}

\input{doc/Extended-Lambda-Calculus}


\newpage
\subsection{Applying Substitutions}

\input{doc/Manipulation-Subst-Apply}


\subsubsection{Non-substitutable (n.s.) constructs}

Most of the ``language constructs'' (a.k.a. ``\texttt{Lang}'') are non-substitutable,
with almost the sole exception of the conditional.
Substitutions into these can only be performed after they have been
expanded out using their semantics-defining predicates.
Examples of such n.s. constructs include:
$$ p;q \qquad x:=e \qquad c*p \qquad pre \vdash post \qquad a \then P$$

\subsubsection{Determine Substitution Scope}
\begin{eqnarray*}
  dss~B~\sigma
  &\defs&
     {}\LET \sigma' = \sigma \setminus B \IN (\sigma',\fv(\ran~\sigma'))
\end{eqnarray*}
\begin{code}
detSubsScope :: [Variable] -> [(Variable,Expr)] -> ([(Variable,Expr)],[Variable])
detSubsScope bvars subslist = (subslist',freevars')
 where
   (subslist',freevars') = dss [] [] subslist

   dss sbus fvs [] = (reverse sbus, sort fvs)
   dss sbus fvs ((x,e):subl)
     | x `elem` bvars  =  dss sbus  fvs  subl
     | otherwise       =  dss sbus' fvs' subl
     where
       sbus' = (x,e):sbus
       fvs' = (exprFreeOVars nullMatchContext e) ++ fvs
\end{code}

\newpage
\subsubsection{Avoid Variable Capture}

\begin{eqnarray*}
  avc~F_s~F_e~B
  &\defs&
     {}\LET (B_F,B_C) = (B \setminus F_s, B \cap F_s) \IN {}
\\&& {}\LET \alpha :\in N_C \bij B_C \IN (B_F \cup N_C,\alpha)
\\&& {}\WHERE N_C \cap F_e = \emptyset \land F_s \subseteq F_e
\end{eqnarray*}
\begin{code}
avoidVarCapture :: [Variable] -> [Variable] -> [Variable] -> ([Variable],Maybe ESubst)
avoidVarCapture subfree efree bvars = (bvars',alphasub')
 where
   (bvars',alphasub') = avc 0 [] [] bvars

   avc _ sravn alfa [] = (reverse sravn,mksub alfa)
   avc i sravn alfa (bv@(r,_,_):bvars)
    | bv `elem` subfree  =  avc i' (nv':sravn) ((bv,nv'):alfa) bvars
    | otherwise          =  avc i  (bv:sravn)  alfa            bvars
    where
      (nv',i') = fresh r (varLess bv) efree i

   mksub [] = Nothing
   mksub alfa = Just $ Substn $ map lift alfa

   lift (v,x) = (v,Var x)

   fresh r s ss i
     = if v' `elem` ss  then fresh r s ss (i+1) else (v',i+1)
     where
      v' = mkVar r (Subscript $ show i) s
\end{code}
To link the two phases we need to be able to extend
the free variable list, maintaining order:
\begin{eqnarray*}
  extvs~F_n~F_s
  &\defs& F_n \cup F_s
\end{eqnarray*}
\begin{code}
extendOrdVars :: Ord t => [t] -> [t] -> [t]
-- we assume the 2nd argument is ordered, but not the first
extendOrdVars [] vars           =  vars
extendOrdVars (newv:rest) vars  =  extendOrdVars rest (insnorm newv vars)
\end{code}

\newpage
\subsubsection{Binder Substitution}

We now put all the pieces together,
with the free variable extension passed in as a function parameter
\begin{eqnarray*}
  bsb~B~fext~\sigma
  &\defs&
     \LET (\sigma',F_s) = dss~B~\sigma \IN
\\&& \LET F_x = fext~(F_s \cup B) \IN
\\&& \LET (N',\alpha') = avc~F_s~F_x~B \IN
\\&& (N',\alpha,\sigma')
\end{eqnarray*}
\begin{code}
binderSubstnBits :: QVars
                 -> ([Variable]->[Variable])
                 -> [(Variable,Expr)]
                 -> ( QVars        -- result (poss. alpha-renamed) qvars
                    , Maybe ESubst -- alpha-renaming, if required
                    , ESubst       -- revised substitution
                    )
binderSubstnBits vars fext subslist
 = ( vars', alpha', Substn subslist' )
 where
   (subslist',subfree') = detSubsScope vars subslist
   xfree' = fext (extendOrdVars vars subfree')
   (vars',alpha') = avoidVarCapture subfree' xfree' vars
\end{code}

\subsubsection{Substitution-list Manipulation}

We want to be able to remove a list of target-vars from a substitution-list,
useful for the \textsc{bnd} and \textsc{fre} cases above.
\begin{code}
maskvars :: Eq v => [v] -> [(e,v)] -> [(e,v)]
maskvars [] subs = subs
maskvars (v:vs) subs
 = maskvars vs (lrem v subs)
 where
    lrem v [] = []
    lrem v ((e,x):xs) | v==x  =  lrem v xs
                      | otherwise  =  ((e,x):lrem v xs)
\end{code}

Or do the opposite, for the \textsc{cap} case.
\begin{code}
onlyvars :: Eq v => [v] -> [(e,v)] -> [(e,v)]
onlyvars vs [] = []
onlyvars vs (s@(e,x):ss) | x `elem` vs  =  s:(onlyvars vs ss)
                         | otherwise    =  onlyvars vs ss
\end{code}

\newpage
\subsubsection{Generating fresh variables}

Given a string-list,
produce something not in that list:
\begin{code}
freshIn :: [String] -> String
freshIn ss = genf 0
 where genf i
         | n `elem` ss  =  genf (i+1)
         | otherwise    =  n
         where n = ('N':(show i))
\end{code}
Proof that this terminates is an interesting exercise
(what is the well-founded relation?).

We can also do this multiple times:
\begin{code}
mfreshIn :: [String] -> Int -> [String]
mfreshIn ss k = mgenf [] 0 k
 where
   mgenf ns i 0 = ns
   mgenf ns i k
    | n `elem` ss  =  mgenf ns     (i+1) k
    | otherwise    =  mgenf (n:ns) (i+1) (k-1)
    where n = ('N':(show i))
\end{code}
Can a proof of \texttt{genf}'s termination be re-used
to assist in proving termination of \texttt{mgenf}?

This code is only used in \texttt{Pvar} substitutions.

\subsubsection{Observation Substitution}

Straight variable substitution for both
single and multiple q-variables.
\begin{code}
type VSubst = Substn Variable ListVar Variable

qvarOSub :: MatchContext -> VSubst -> QVars -> QVars
qvarOSub mctxt (Substn sub) vs = map (areplace sub) vs
\end{code}


\newpage
\subsubsection{Meta-Variable Substitution}

We also need to add cases to handle explicit meta-variables,
where we assume explicit side-conditions regarding
their free variables may be present.
In the context of a side-condition $C$,
we get the following behaviour:
\begin{eqnarray*}
  M[r/x]
  &\defs&
  \left\{
  \begin{array}{ll}
    M, & C \implies x \mbox{ not free in } M \\
    M[r/x], & \mbox{otherwise}
  \end{array}
  \right.
\end{eqnarray*}
Note that $C$ may not mention $M$,
or what it says is too weak to rule out the potential
presence of $x$ in any expansion of $M$.

Given a side-condition in single-MV normal-form
and a (normalised) list of variables,
it is useful to be able determine which variables
are definitely not free in the corresponding meta-variable.
\begin{code}
keepFree :: [(Variable, t)] -> Variable -> Trie SCSingle -> [(Variable, t)]
keepFree sublist var varSCs
 = case tvlookup varSCs var of
          Nothing  ->  sublist
          Just scsngl  ->  filter (keepSub scsngl) sublist

keepSub :: SCSingle -> (Variable,t) -> Bool
keepSub (SCSingle isCond msetsc) sub@(x,_)
 | isCond && not (isPreVariable x)  =  False
 | otherwise
    = case msetsc of
        Nothing                 ->  True
        (Just (SCequal vs))     ->  x `elem` vs
        (Just (SCsub supvs))    ->  x `elem` supvs
        (Just (SCdisj disjvs))  ->  not (x `elem` disjvs)
\end{code}

Now, given a normalised side-condition,
a meta-variable and a substitution-list
remove substitutions targetting variables we can show will not be free:
\begin{code}
keepFreeInE :: [(Variable, t)] -> Variable -> SCNF -> [(Variable, t)]
keepFreeInE sublist evar (SCNFcond _ evars _)
                                        =  keepFree sublist evar evars
keepFreeInE sublist _    _              =  sublist

keepFreeInP :: [(Variable, t)] -> Root -> SCNF -> [(Variable, t)]
keepFreeInP sublist pvar (SCNFcond _ _ pvars)
                                        =  keepFree sublist (rootVar pvar) pvars
keepFreeInP sublist _    _              =  sublist
\end{code}
\textbf{Question}:
\emph{ if a variable is fresh, how does this influence the above?}



\subsubsection{Expression Substitution}
\label{Manip.Expr.Subst}

\begin{code}
exprOSub :: MatchContext -> SideCond -> ESubst -> Expr -> (Expr,ChgMrk)
exprOSub mctxt sc subs e
 = case normaliseSubstn mctxt subs of
    Nothing  ->  (e,NoChg)
    Just subs'  ->  exprONSub' mctxt sc subs' e

exprONSub :: MatchContext -> SideCond -> ESubst -> Expr -> Expr
exprONSub mctxt sc subs e = fst $ exprONSub' mctxt sc subs e

exprONSub' :: MatchContext -> SideCond -> ESubst -> Expr -> (Expr,ChgMrk)
exprONSub' mctxt sc subs@(Substn subslist) e
 = eOS e
 where
  (msubslist,ssubslist) = partition (isLstV . fst) subslist
  scnf = normaliseSC sc
\end{code}
\begin{eqnarray*}
   k[r/x] &\defs& k
\end{eqnarray*}
\begin{code}
  eOS e@(Num _) = (e,NoChg)
\end{code}
\begin{eqnarray*}
   v[r/x] &\defs& r \cond{x=v} v
\\ v\sigma &\defs& \sigma(v) \cond{v \in \sigma} v
\\ (M\!\!\dagger\!\!\setminus S)
   [~M\!\!\ddagger\!\!\setminus S ~/~ M\!\!\dagger\!\!\setminus S~]
    &\defs&
    M\!\!\ddagger\!\!\setminus S
\\ v\!\dagger [~M\!\ddagger ~/~ M\!\dagger]
   &\defs&
   v\!\ddagger \cond{v \in \sem M} v\!\dagger
\\ E[r/x]
  &\defs&
  \left\{
  \begin{array}{lr}
    E, & x \mbox{ not free in } E \\
    E[r/x], & x \mbox{ free in } E
  \end{array}
  \right.
\end{eqnarray*}
\begin{code}
  eOS e@(Var v)
   | isLstV v
       =  ( case alookupOrd msubslist v of
             Just v'@(Var r)  ->  v' -- UNSOUND ?? root/S/decor ignored
             _               ->  e
          , Chgd )

   | isEVar v
      = let freesl = keepFreeInE ssubslist v scnf
        in if null freesl
            then (e,Chgd)
            else (ESub e (Substn (freesl++msubslist)),Chgd)

   | otherwise
       =  ( case alookupOrd ssubslist v of
             Just r   ->  r
             Nothing  ->  e
          , Chgd )
\end{code}
\begin{eqnarray*}
   (e_1~e_2)[r/x] &\defs& (e_1[r/x])~(e_2[r/x])
\\ (e_1~e_2)\sigma &\defs& (e_1\sigma)(e_2\sigma)
\end{eqnarray*}
\begin{code}
  eOS (App s es) = (App s (fst $ chgmap eOS es),Chgd)
\end{code}
\newpage
THIS NEEDS TO REFLECT THAT GENERAL ABSTRACTIONS HAVE MANY BODIES
\begin{eqnarray*}
   (\lambda B @ e)\sigma &\defs& \lambda N' @ (e~\alpha)\sigma'
\\&& \WHERE (N',\alpha,\sigma') = bsb~B~(extvs (\fv e))~\sigma
\end{eqnarray*}
\begin{code}
  eOS ae@(Abs nm _ bvars es)
   = case alfa' of
       Nothing    ->  ( Abs nm 0 nvars'
                         $ map (exprONSub mctxt sc subs') es
                      , Chgd )
       (Just alf) ->  ( Abs nm 0 nvars'
                         $ map ( exprONSub mctxt sc subs'
                               . exprONSub mctxt sc alf) es
                      , Chgd )
   where
     (nvars',alfa',subs') = binderSubstnBits bvars fext subslist
     fext = extendOrdVars
              $ concat $ map (exprFreeOVars nullMatchContext) es

\end{code}
\begin{eqnarray*}
   (e~\sigma_1)\sigma_2 &\defs& e(\sigma_1 ; \sigma_2)
\end{eqnarray*}
\begin{code}
-- not currently implemented
--   eOS (Esub e sub)
--    = (exprONSub mctxt sc subc e,Chgd)
--    where subc = substnComp (exprONSub mctxt sc)
--                             eNonTrivSub sub subs
\end{code}

Anything else is left untouched.
\begin{code}
  eOS e               = (ESub e subs,NoChg)

emsg_sub_focus    = "exprONSub mctxt-of-Efocus"
\end{code}

\newpage
\subsubsection{Predicate Substitution}
\label{Manip.Pred.Subst}

\textbf{TODO: }
We first look at meta-variables and see if either they
can be instantiated, or they are substituting for each
in a conforming manner, in which case we proceed.

\begin{code}
subFocus mctxt sc fpr
 = case getPFocus fpr of
    Sub pr subs
      -> let (pr',chgd)  =  predOSub mctxt sc subs pr
         in case chgd of
              Chgd  ->  (repPFocus pr' fpr,chgd)
              _     ->  (fpr,chgd)
    _ -> (fpr,NoChg)

predOSub :: MatchContext -> SideCond -> ESubst -> Pred -> (Pred,ChgMrk)
predOSub mctxt sc subs pr
 = case normaliseSubstn mctxt subs of
    Nothing  ->  (pr,NoChg)
    Just subs'  ->  predONSub' mctxt sc subs' pr

predONSub mctxt sc subs pr = fst $ predONSub' mctxt sc subs pr

predONSub' mctxt sc subs@(Substn sublist) pr
 = pOS pr
 where
  (pr',chg) = pOS pr
  (msubslist,ssubslist) = partition (isLstV . fst) sublist
  subslist = (ssubslist,msubslist)
  scnf = normaliseSC sc
\end{code}

\begin{eqnarray*}
   k[r/x] &\defs& k
\end{eqnarray*}
\begin{code}
  pOS TRUE = (TRUE,Chgd)
  pOS FALSE = (FALSE,Chgd)
\end{code}
\begin{eqnarray*}
  P[r/x]
  &\defs&
  \left\{
  \begin{array}{lr}
    P, & x \mbox{ not free in } P \\
    P[r/x], & x \mbox{ free in } P
  \end{array}
  \right.
\end{eqnarray*}
\begin{code}
  pOS pv@(PVar p)
   | null freesl  =  (pv,Chgd)
   | otherwise    =  (Sub pv (Substn freesl),Chgd)
   where
     freesl = keepFreeInP sublist (varRoot p) scnf
\end{code}
\newpage
\begin{eqnarray*}
   (\texttt{C}~p_1,\ldots,p_m,e_1,\ldots,e_n)[r/x]
   &\defs&
   (\texttt{C}~p_1[r/x],\ldots,p_m[r/x],e_1[r/x],\ldots,e_n[r/x])
\end{eqnarray*}
\begin{code}
-- Lang and RfdBy are not substitutable
  pOS (PExpr e) = (pExpr e',chg)
   where (e',chg) = exprONSub' mctxt sc subs e
  pOS (TypeOf e t) = (TypeOf e' t,chg)
   where (e',chg) = exprONSub' mctxt sc subs e
  pOS (PApp nm prs) = (PApp nm (fst $ chgmap pOS prs),Chgd)
\end{code}
\newpage
\begin{eqnarray*}
  (\forall B @ p)\sigma
  &\defs&
  \forall N' @ (p~\alpha)\sigma'
\\&& \WHERE (N',\alpha,\sigma') = bsb~B~(extvs(\fv p))~\sigma
\end{eqnarray*}
\begin{code}
  pOS qpr@(PAbs nm _ bvars prs)
   = case alfa' of
       Nothing     ->  ( PAbs nm 0 nvars'
                           $ map (predONSub mctxt sc subs') prs
                       , Chgd )
       (Just alf)  ->  ( PAbs nm 0 nvars'
                          $ map ( predONSub mctxt sc subs'
                                  . predONSub mctxt sc alf ) prs
                       , Chgd )
   where
     (nvars',alfa',subs') = binderSubstnBits bvars fexts sublist
     fexts = extendOrdVars
              $ concat $ map (predFreeOVars nullMatchContext) prs
\end{code}
\newpage
\begin{eqnarray*}
   (p~\sigma_1)\sigma_2 &\defs& p(\sigma_1 ; \sigma_2)
\end{eqnarray*}
\begin{code}
-- not implemented at present
--   pOS (Sub pr sub)
--    = (predONSub mctxt sc subc pr,Chgd)
--    where
--       subc = substnComp (exprONSub mctxt sc)
--                         eNonTrivSub sub subs
\end{code}
\begin{code}
  pOS pr  = (Sub pr subs,NoChg)

pmsg_free_capture = "free-capture-problem-NYI"
pmsg_sub_focus   = "predONSub-of-focus"
\end{code}


\subsubsection{Substitution Composition}

We implement substitution composition
as a binary operator on substitutions,
which is safe provided the substitution mechanism
avoids free variable capture.
If substitutions are viewed as maps $\sigma : Substn = Var \pfun Expr$,
then we define it as:
\begin{eqnarray*}
   \_ ; \_ &:& Substn \times Substn \fun Substn
\\ \sigma_1 ; \sigma_2
   &\defs&
   \sigma_2 \override ((id \pfun \lambda e @ e[\sigma_2])\sigma_1)
\end{eqnarray*}
\begin{code}
substnComp :: Ord v
           => (Substn v e -> e -> e)           -- substitution application
           -> ((v,e) -> Bool)                  -- identifies non-trivial subs
           -> (Substn v e) -> (Substn v e) -> (Substn v e)
substnComp sapp nontriv (Substn sub1) sbst2@(Substn sub2)
 = Substn $ filter nontriv sub'
 where
   sub' = sub2 `aloverride` mapsnd (sapp sbst2) sub1
\end{code}

We give some pre-canned non-trivial substitution predicates:
\begin{code}
eNonTrivSub (t,(Var r))  =  t /= r
eNonTrivSub  _           =  True

prNonTrivSub (t,(PExpr (Var r)))  =  t /= r
prNonTrivSub  _                   =  True
\end{code}


\subsubsection{Predicate/Expression Substitution}

This substitution replaces
free occurrences of predicate meta-variable \texttt x
by predicate \texttt r:
\begin{code}
exprPSub :: Pred -> GenRoot -> Expr -> Expr
exprPSub r g e
 = ePS e
 where
  ePS (App s es)        = App s (map ePS es)
  ePS (Abs nm tt ss es) = Abs nm 0 ss (map ePS es)
  ePS (EPred pr)        = ePred $ predPSub r g pr
  ePS (ESub e sub)      = ESub (ePS e) sub
  ePS e                 = e
\end{code}

\newpage
As does this:
\begin{code}
predPSub :: Pred -> GenRoot -> Pred -> Pred
predPSub r g pr
 = pPS pr
 where
  fpvr = predFreePVars nullMatchContext r
  pPS pv@(PVar s)         = if s==genRootAsVar g then r else pv
  pPS (PExpr e)           = pExpr (exprPSub r g e)
  pPS (TypeOf e t)        = TypeOf (exprPSub r g e) t
  pPS (PApp nm prs)       = PApp nm (map pPS prs)
  pPS (PAbs nm tt ss prs) = PAbs nm 0 ss (map pPS prs)
  pPS (Sub pr sub)        = Sub (pPS pr) sub
  pPS pr                  = pr

closed = qvars []
\end{code}


\newpage
\subsubsection{$\alpha$-substitution}

Let $\alpha$ denote a variable-substitution,
i.e. a mapping from variables to variables.
The substitution
$$
  (\forall \vec x @ P)_\alpha
$$
is well defined if
\begin{enumerate}
  \item $\alpha$ must be injective:
    $$ \#(\dom~\alpha) = \#(\ran~\alpha)$$
  \item $\alpha$ only maps from variables in $\vec x$:
    $$ \dom~\alpha \subseteq \vec x$$
  \item
    $\alpha$ only maps to fresh variables:
    $$ \ran~\alpha \DISJ (\vec v \union \fv.P)$$
\end{enumerate}
Given the above conditions, it is defined as follows:
$$
 (\forall \vec x @ P)_\alpha
 ~\defs~
 (\forall \vec x[\alpha] @ P[\alpha])
$$
\newpage
\begin{code}
predASub :: MatchContext -> SideCond -> VSubst -> Pred -> Pred
predASub mctxt sc vsubs@(Substn sub) pr
 = pAS pr
 where

  fvset = reduceFVSetExpr (normaliseSC sc) (predFVSet mctxt pr)

  esubs = mapSub Var vsubs

  alphaOk :: VSubst -> QVars -> Pred -> Bool
  alphaOk (Substn sub) qvs pr
   | not $ null $ dupsOf sdom    =  False
   | not $ null $ dupsOf sran    =  False
   | length sdom /= length sran  =  False
   | not (sdom `subsetOf` qvec)  =  False
   | otherwise                   =  True
   where
    (sdom,sran) = unzip sub
    qvec = getqvars qvs
    ranset = fvsEnum sran
    prset = fvsUnion [fvsEnum qvec,fvset]

  pAS qpr@(PAbs nm _ qvs prs) | all (alphaOk vsubs qvs) prs
    =  PAbs nm 0 (qvarOSub mctxt vsubs qvs)
                 (map (predONSub mctxt sc esubs) prs)

  pAS pr  = pr

pmsg_alphaNYI = "alpha-substitution-NYI"
\end{code}
