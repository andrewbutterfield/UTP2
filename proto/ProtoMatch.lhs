\section{Match Prototyping}

\begin{code}
{-# OPTIONS_GHC -XOverlappingInstances #-}
{-# OPTIONS_GHC -XFlexibleInstances #-}
module ProtoMatch where
import Data.List
import Data.Maybe
import Utilities
import Tables
\end{code}

We prototype matching here.

\newpage
\subsection{Expressions}


We first define our expression syntax,
which has been has been chosen to throw up every feature of the full \UTP2 logic,
except for variable decorations.

\subsubsection{Data Declarations}

\begin{eqnarray*}
   x_\circ,y_\circ \in V_\circ && \mbox{---Standard Variables}
\\ \lst x,\lst y \in V_\$  && \mbox{---Generic List-Variables}
\\ xs,ys \in VS &::=& (V_\circ | V_\$)^* \qquad \mbox{Lists of Std/Generic-List Variables}
\\ R\less{xs} \in (V_R \times VS)  && \mbox{---Reserved List-Variable}
\\ \ell \in L &::=& \lst x | R\less{xs} \qquad \mbox{List-Variables}
\\ x,y \in V &::=& x_\circ | \ell \qquad \mbox{Variables}
\\ \nu \in V^* && \mbox{---Variable Lists}
\end{eqnarray*}
\begin{code}
data Var
 = Std String
 | Lst String
 | Rsv String [Var] -- no Rsv in var list !
 deriving (Eq, Ord)

newtype VarList = VL [Var] deriving (Eq,Ord)
\end{code}

\begin{eqnarray*}
   E \in MV && \mbox{Expr Meta-Variable}
\\ k \in K && \mbox{Constants/Literals}
\\ e \in EX &::=& k
\\ &|& x_\circ
\\ &|& E
\\ &|& e = e
\\ &|& e\land e\land \ldots \land e
\\ &|& e(e,\ldots,e)
\\ &|& \lambda \nu @ e
\\ &|& e
        [ x_{\circ1} \rby e_1, \ldots, x_{\circ m}\rby e_m,
          \ell_{t1} \rby \ell_{r1}, \ldots, \ell_{tn} \rby \ell_{rn}
        ], \qquad m+n \geq 1
\\ &|& \exists \nu @ e
\end{eqnarray*}
\begin{code}
data Expr
 = Const Int
 | Var Var
 | MVar String
 | Eq Expr Expr
 | And [Expr]
 | App Expr [Expr]
 | Lam VarList Expr
 | Sub Expr Substn
 | Exists VarList Expr
 -- sentinel for deferred matches
 | Wild
 deriving (Eq,Ord)

type Substn = [(Var,Expr)]
\end{code}

\newpage
\subsubsection{Show Instances}

We define Show instances that use indentation for clarity.

Variables:
\begin{code}
instance Show Var where
  show (Std s) = s
  show (Lst ell) = ell
  show (Rsv r []) = r
  show (Rsv r less) = r ++ '\\' : seplist ":" less

seplist sep []     = ""
seplist sep [x]    = show x
seplist sep (x:xs) = show x ++ sep ++ seplist sep xs
\end{code}

Variable Lists
\begin{code}
instance Show VarList where
  show (VL vars) = seplist "," vars
\end{code}

Expressions:
\begin{code}
instance Show Expr where

  show (Const n) = show n
  show (Var v)  = show v
  show (MVar e)  = e

  show (Eq e1 e2) = '(' : show e1 ++ " = " ++ show e2 ++ ")"

  show (And es) = "AND {" ++ seplist ", " es ++ "}"

  show (App f es) = show f ++ '(' : seplist ", " es ++ ")"

  show (Lam vl e) = "(Lm "++show vl++" @ " ++ show e ++ ")"

  show (Sub e ves) = show e ++ '[' : seplist ", " ves ++ "]"

  show (Exists vl e)  = "(Ex "++show vl++" @ " ++ show e ++ ")"

  show Wild  = "_"
\end{code}

\subsubsection{Support Code}

\begin{code}
isStd (Std _) = True
isStd _       = False

isLst (Lst _) = True
isLst _       = False

isRsv (Rsv _ _) = True
isRsv _         = False

dropE :: Expr -> Var
dropE (Var v) = v
dropE e = error ("dropE: "++show e++" is not a Var")
\end{code}

\newpage
\subsubsection{Test Values}

Variables:
\begin{code}
[u,v,w,x,y,z] = map Std ["u","v","w","x","y","z"]
[us,vs,xs,ys,zs,es,fs] = map Lst ["u$","v$","x$","y$","v$","e$","f$"]
r = Rsv "R" []
rless less = Rsv "R" less
\end{code}

Some builders:
\begin{code}
lam vl e = Lam (VL vl) e
exists vl e = Exists (VL vl) e
var s = Var $ Std s
lvar ell = Var $ Lst ell
rvar r less = Var $ Rsv r less
\end{code}

Expressions:
\begin{code}
[e,f,g] = ["E","F","G"]
[zero,one,two,three] = map Const $[0..3]
[vu,vv,vw,vx,vy,vz] =  map Var [u,v,w,x,y,z]
[vus,vvs,vxs,vys,vzs,ves,vfs] =  map Var [us,vs,xs,ys,zs,es,fs]
[me,mf,mg,mp] = map MVar [e,f,g,"P"]
rR = Var r
rRless = Var . rless



facx = App (var "fac") [vx]
inc = lam [x] $ App (var "plus") [vx,one]
[equv,eqwx]  = [ Eq vu vv, Eq vw vx ]
andeq = And [equv,eqwx]
vvals = [(u,zero),(v,one),(w,two),(x,three)]
nsub = Sub andeq vvals
e42 = exists [x] $ Eq vx $ Const 42
\end{code}


From \texttt{src/TODO.txt} (suitably modified):
\begin{code}
aandb = And [MVar "A",MVar "B"]
anyxp = exists [x] mp
anyxsp = exists [xs] mp
anyxsysp = exists [xs,ys] mp
anyxysp = exists [x,ys] mp
anyrp = exists [r] mp
anyrvp = exists [rless [v]] mp
anyrvsp = exists [rless [vs]] mp
anyrxp = exists [rless [x]] mp
eqrr = Eq rR rR
eqrurvs = Eq (rRless [us,vs]) (rRless [us,vs])
eqrv = Eq (rRless [v]) (rRless [v])
eqrvs= Eq (rRless [vs]) (rRless [vs])
eqrx = Eq (rRless [x]) (rRless [x])
eqxsrv = Eq vxs (rRless [v])
eqxses = Eq vxs ves
eqxsr = Eq vxs rR
eqxsru = Eq vxs (rRless [us])
eqrusvs = Eq (rRless [us,vs]) (rRless [us,vs])
sube4u = Sub mp [(u,me)]
subes4us = Sub mp [(us,ves)]
subef4uv = Sub mp [(u,me),(v,mf)]
subefs4uvs = Sub mp [(u,me),(vs,vfs)]
subr4r = Sub mp [(r,rR)]
\end{code}

\newpage
\subsection{Side-Conditions}

We have a simple side-condition language:
\begin{eqnarray*}
   a \in A &::=& v \in E | v \notin E
\\ s \in SC &::=& false | true | a | a \land \ldots \land a
\end{eqnarray*}
Clearly, $(\ldots \land v\in E \land \ldots \land v \notin E \land \ldots)$
simplifies to $false$.

\subsubsection{Data Declarations}

\begin{code}
data AtmSC = In Var String | Out Var String deriving (Eq)

data SCond
 = SCfalse
 | SCand [AtmSC]
 deriving (Eq, Ord)

-- want an ordering that puts Ins and Outs with the same variable together
-- makes it easy to spot contradictions
instance Ord AtmSC where
  compare (In  v1 e1) (In  v2 e2) = compare (v1,e1) (v2,e2)
  compare (Out v1 e1) (Out v2 e2) = compare (v1,e1) (v2,e2)
  compare (In  v1 e1) (Out v2 e2)
   | v1 <  v2  =  LT
   | v1 >  v2  =  GT
   | otherwise  =  LT
  compare (Out v1 e1) (In  v2 e2)
   | v1 <  v2  =  LT
   | v1 >  v2  =  GT
   | otherwise  =  GT
\end{code}

\subsubsection{Show Instances}

\begin{code}
instance Show AtmSC where
  show (In v e) = show v ++ " in " ++ e
  show (Out v e) = show v ++ " notin " ++ e

instance Show SCond where
  show SCfalse = "false"
  show (SCand []) = "true"
  show (SCand [a]) = show a
  show (SCand as) = '[' : seplist "; " as ++ "]"
\end{code}

\subsubsection{Test Values}

Builder code:
\begin{code}
true = SCand []

scand  = sccheck [] . sort

sccheck sev []   = SCand $ reverse sev
sccheck sev [ve] = SCand $ reverse (ve:sev)
sccheck sev (In v1 e1:Out v2 e2:ves)
 | v1 == v2 && e1 == e2  =  SCfalse
sccheck sev (ve:ves) = sccheck (ve:sev) ves
\end{code}

\newpage
\subsection{Theory Context}

\def\O{\mathcal{O}}
We consider a simplified theory context that has two forms
of ``known'' variables:
those defined as equal to some expression,
and those designated as observations.
\begin{eqnarray*}
   \kappa \in Known &=& V_\circ \pfun EX
\\ \O \in Obs &=& \power V_\circ
\end{eqnarray*}

\subsubsection{Data Declarations}

\begin{code}
data ThCtxt
 = ThCtxt
    { obs :: [Var]
    , known :: Trie Expr
    }
\end{code}

\subsubsection{Show Instances}

\begin{code}
instance Show ThCtxt where
  show (ThCtxt vs ktrie)
    = unlines [showObs vs,"Known:",show ktrie]

showObs vs = "Obs =  "++seplist ", " vs
\end{code}

\subsubsection{Test Values}

We have $x$, $y$ and $z$ as observables,
and the most important question ($q$) and answer ($a$)
as known:
\begin{code}
q6by9 = App (var "*") [Const 6, Const 9]

a42 = Const 42

thctxt = ThCtxt [x,y,z] $ lbuild [("q",q6by9),("a",a42)]
\end{code}

\newpage
\subsection{Match Bindings}

A successful match outcome has every pattern variable bound
to a corresponding part of the test.

\subsubsection{Data Declarations}

A successful match binds
regular and meta- variables to expressions,
and list-variables to expression sets or duplicate-free lists:
\def\Dom{\fn{Dom}}
\begin{eqnarray*}
   \beta_\circ &:& V_\circ \pfun E
\\ \beta_\$     &:& V_\$ \pfun (\power E + E^*_!)
\\ \beta,(\beta_\circ,\beta_*) \in \mathcal B
   &=& (V_\circ \pfun E)\times(V_\$ \pfun (\power E + E^*_!))
\\ \Dom(\beta_\circ,\beta_\$) &=& \dom \beta_\circ \cup \dom \beta_\$
\end{eqnarray*}
\begin{code}
data Binds
 = Bind
    { stdbind :: Trie Expr
    , lstbind :: Trie [Expr]
    }
\end{code}


\subsubsection{Show Instances}

\begin{code}
instance Show Binds where
  show (Bind stdb lstb) = unlines ["Std:", show stdb, "Lst:", show lstb]
\end{code}

\subsubsection{Supporting Code}

An empty binding:
\begin{code}
noBinds = Bind tnil tnil
\end{code}

Next, general variable lookup  $\beta(v)$:
\begin{code}
vlkp :: Binds -> Var -> Maybe [Expr]
vlkp binds (Std v) = fmap sngl $ tlookup (stdbind binds) v
vlkp binds (Lst v) = tlookup (lstbind binds) v
vlkp binds      r  = tlookup (lstbind binds) $ show r
\end{code}
and general variable update $\beta \override \maplet v {es}$
\begin{code}
vupd :: Binds -> Var -> [Expr] -> Binds
vupd binds (Std v) [e] = binds{stdbind = tupdate v e $ stdbind binds}
vupd binds (Lst v)  es = binds{lstbind = tupdate v es $ lstbind binds}
vupd binds      r   es = binds{lstbind = tupdate (show r) es $ lstbind binds}
\end{code}

Now, specific ways to create a single binding $\maplet v {es}$:
\begin{code}
vbind :: Var -> Expr -> Binds
vbind v e = vupd noBinds v [e]

vsbind :: Var -> [Expr] -> Binds
vsbind v es = vupd noBinds v es
\end{code}


Another useful function is one that binds
a list of (unique) \texttt{Lst} variables to null:
\begin{code}
vsnulls :: [Var] -> Binds
vsnulls lvs = Bind tnil $ lbuild $ map tonull lvs
 where tonull lv = (show lv,[])
\end{code}

Code to merge two bindings $\beta_1 \sqcup \beta_2$:
\begin{code}
mtglue t1 t2
 = case t1 `tglue` t2 of
    Nothing -> fail "conflicting entries"
    Just t  -> return t

bmrg :: Monad m => Binds -> Binds -> m Binds
bmrg (Bind stdb1 lstb1) (Bind stdb2 lstb2)
 = do stdb' <- stdb1 `mtglue` stdb2
      lstb' <- lstb1 `mtglue` lstb2
      return $ Bind stdb' lstb'
\end{code}

Merging a binding with a list of same
\begin{code}
lbmrg :: Monad m => Binds -> [Binds] -> m Binds
bind0 `lbmrg` [] = return bind0
bind0 `lbmrg` (bind1:binds)
 = do bind1' <- bind0 `bmrg` bind1
      bind1' `lbmrg` binds
\end{code}

A common case is \texttt{Var}-\texttt{Var} matching:
\begin{code}
vvbind :: (Var, Var) -> Binds
vvbind (pv, tv) = vbind pv (Var tv)

vvbinds :: Monad m => [(Var, Var)] -> m Binds
vvbinds vvs = noBinds `lbmrg` (map vvbind vvs)
\end{code}


Code to ``concat-merge'' $\beta_1 \uplus \beta_2$, so that conflicts for list variables
result in both lists being merged.
\begin{code}
mcat es1 es2 = Just (es1 ++ es2)

mtcat t1 t2
 = case tmmerge mcat t1 t2 of
    Nothing -> fail "conflicting entries"
    Just t  -> return t

bcat :: Monad m => Binds -> Binds -> m Binds
bcat (Bind stdb1 lstb1) (Bind stdb2 lstb2)
 = do stdb' <- stdb1 `mtglue` stdb2
      lstb' <- lstb1 `mtcat` lstb2
      return $ Bind stdb' lstb'
\end{code}

\newpage
\subsection{Deferred Matches}

When matching variable lists in quantifiers, or variable/expression
pairs in substitutions, order is not important, so we get a number
of potential matches. We defer the matching of these until all the
structural matching has been done, on order to have the maximum
information available to select out those matches.

For lambda variable-lists, order is important, but we still can get
a number of possible matches---so for deferred variable-list matching
we need to note if ordering is important.


\subsubsection{Data Declarations}


An unresolved variable-list match relates a given pair of variable lists,
or variable-sets
We maintain a set of these.
\begin{eqnarray*}
   vl \in DVL &=& \power(V^* \cross V^*)
\\ vs \in DVS &=& \power(\power V \cross \power V)
\end{eqnarray*}
\begin{code}
-- we want lists before sets.
-- data VLType = VSeq | Set deriving (Eq,Ord,Show)

-- we merge representations, see DefMtchs below
-- type VLPair = (VLType,([Var],[Var]))
--
-- data VLToDo =  VToDo { unVToDo :: [VLPair] }
\end{code}
In general these only come from binding quantifier binding lists,
so we assume they are all bound.

An unresolved substitution-list match relates
a given pair of substitution lists.
We maintain a set of these.
However we also need to record the bound-variables in each case
as substitutions are not binders.
\begin{eqnarray*}
   ds \in DS
   &=&
   \power(
     (\power V \times (V\times E)^*)
     \cross
     (\power V \times (V\times E)^*)
   )
\end{eqnarray*}
\begin{code}
-- data SubToDo
--   = SToDo { unSToDo :: [ ( ([Var],[(Var,Expr)])
--                          , ([Var],[(Var,Expr)]) ) ] }
\end{code}

\newpage
We have three kinds of defferred match collections:
variable-lists ($DVL$);
variables-sets ($DVS$);
and substitutions ($DS$).
The list/set distinction is important,
but in order to simplify the treatment, we shall merge them all into
a single deferred matches ($DMS$) component.
A deferred match is a pair of tuples,
each containing a set of bound variables, and a set/list
of variable/expression pairs.
\begin{eqnarray*}
   DSM &=& \power V \times \power(V\times E)
\\ DLM &=& \power V \times (V\times E)^*
\\ DCM  &=&  (DSM \times DSM) | (DLM \times DLM)
\\ DM &=& \power DCM
\\ dms \in DMS &=& \power DM
\end{eqnarray*}
We represent the variable set/lists by pairing them with a special sentinel
expression value
that denotes a wildcard ($\wild$)
that matches anything with no binding.

We represent both sets and lists as sequences, using \texttt{DType} to flag which
\begin{code}
data DType = VSeq | VSet | VESet deriving (Eq,Ord,Show)
data VEItem = VE { vOf :: Var
                 , eOf :: Expr
                 }  deriving (Eq, Ord)
type DItem = ( [Var]     -- bound variables
             , [VEItem]  -- DSM or DLM
             )
data DCM
 = DCM { dtyp  :: DType
       , defpat :: DItem
       , deftst :: DItem
       }
 deriving (Eq, Ord)
data DefMtchs = DMS { unDMS :: [DCM] }
\end{code}

\subsubsection{Show Instances}

\begin{code}
instance Show VEItem where
  show (VE v Wild) = show v
  show (VE v e) = "("++show v++", "++show e++")"
instance Show DCM where
  show dcm =    show (dtyp dcm)
             ++ ": P=" ++ show (defpat dcm)
             ++ ", T=" ++ show (deftst dcm)
instance Show DefMtchs where
  show (DMS dcms)
   | null dcms  =  "None."
   | otherwise  =  unlines (map show dcms)
\end{code}

\subsubsection{Supporting Code}


Next, the empty deferred choices:
\begin{code}
noDMS = DMS []
\end{code}

We provide ways to build deferred lists,
sorting them if ordering need not be preserved.
\begin{code}
v2vitem :: Var -> VEItem
v2vitem v       =  VE v Wild

ve2vitem :: (Var,Expr) -> VEItem
ve2vitem (v,e)  =  VE v e

vl2ditem, vs2ditem :: [Var] -> DItem
vl2ditem vl = ( vl, map v2vitem vl )
vs2ditem vs = ( vs, map v2vitem $ sort vs )

setVSPair, seqVLPair :: [Var] -> [Var] -> DCM
setVSPair vs1 vs2 =  DCM VSet (vs2ditem vs1) (vs2ditem vs2)
seqVLPair vl1 vl2 =  DCM VSeq (vl2ditem vl1) (vl2ditem vl2)

subVVEPair :: ([Var],[(Var,Expr)]) -> ([Var],[(Var,Expr)]) -> DCM
subVVEPair (bv1,ves1) (bv2,ves2)
   = DCM VESet (bv1,map ve2vitem $ sort ves1)
               (bv2,map ve2vitem $ sort ves2)
\end{code}

Useful to be able to add an pair to an existing deferred list:
\begin{code}
addPair pair l1 l2 defList
 = DMS $ sort $ (pair l1 l2 : unDMS defList)

addSetVL = addPair setVSPair
addSeqVL = addPair seqVLPair
addSubsL = addPair subVVEPair
\end{code}

We need ways to merge deferred lists $\nu_1 \cup \nu_2$,
$\sigma_1 \cup \sigma_2$:
\begin{code}
mrgDM l1 l2  = DMS $ lnorm (unDMS l1 ++ unDMS l2)
\end{code}


\newpage
\subsection{Intermediate Match Result}

An intermediate match result combines bindings and deferred matches

\subsubsection{Data Declarations}

\[
  \Xi = (\beta,\nu,\sigma)
\]
---often written as $\beta \deferred \nu,\sigma$.
\begin{code}
data IMResult
 = IMR {  binds :: Binds
       ,  mtodo :: DefMtchs
       }
\end{code}

\subsubsection{Show Instances}

\begin{code}
instance Show IMResult where
  show imr
    = unlines [ show $ binds imr
              , "Deferred : " ++ show (mtodo imr)
              ]
\end{code}

\subsubsection{Support Code}

An empty result:
\begin{code}
noIMR = IMR noBinds noDMS
\end{code}


We need to merge intermediate match results $\Xi_1 \sqcup \Xi_2$
\begin{eqnarray*}
   (\beta_1,\nu_1,\sigma_1)
   \sqcup
   (\beta_1,\nu_1,\sigma_1)
   &=&
   (\beta_1\sqcup\beta_2,\nu_1\cup\nu_2,\sigma_1\cup\sigma_2)
\end{eqnarray*}
\begin{code}
imrMrg :: Monad m => IMResult -> IMResult -> m IMResult
imrMrg imr1 imr2
 = do binds' <- binds imr1 `bmrg` binds imr2
      let mtodo' = mrgDM (mtodo imr1) (mtodo imr2)
      return IMR { binds = binds'
                 , mtodo = mtodo'
                 }
\end{code}

Sometimes we want to use ``concat-merge'' $\Xi_1 \uplus \Xi_2$:
\begin{code}
imrCat :: Monad m => IMResult -> IMResult -> m IMResult
imrCat imr1 imr2
 = do binds' <- binds imr1 `bcat` binds imr2
      let mtodo' = mrgDM (mtodo imr1) (mtodo imr2)
      return IMR { binds = binds'
                 , mtodo = mtodo'
                 }
\end{code}




\newpage
\subsection{Match Context}

The match context consists of a general context%
---the theory context---%
coupled with the side-conditions specific to the pattern and test expression
involved.

\subsubsection{Data Declarations}

\begin{code}
data MCtxt
 = MCtxt
    { mObs :: [Var]
    , mKnown :: Trie Expr
    , tSC :: SCond
    , pSC :: SCond
    }
\end{code}

\subsubsection{Show Instances}

\begin{code}
instance Show MCtxt where
 show (MCtxt ovs ktrie psc tsc)
  = unlines
     [ showObs ovs
     , "Known:"
     , show ktrie
     , "Test S.C. : " ++ show tsc
     , "Patn S.C. : " ++ show psc
     ]
\end{code}

\subsubsection{Test Values}

\begin{code}
mctxt = mkMCtxt thctxt true true
\end{code}

\subsubsection{Support}

First, a quick builder to combine two side-conditions
with a theory context:
\begin{code}
mkMCtxt thctxt tsc psc
 = MCtxt
     { mObs = obs thctxt
     , mKnown = known thctxt
     , tSC = tsc
     , pSC = psc
     }
\end{code}

A predicate to test if a variable is unknown
\begin{code}
isUnknown mctxt v
 = case tlookup (mKnown mctxt) (show v) of
    Just _  ->  False
    _       ->  not (v `elem` mObs mctxt)
\end{code}

\newpage
\subsection{Reserved Variable Denotations}

Computing the denotation of a reserved variable:
\begin{eqnarray*}
   \sem{R\less{vs}}_\Gamma
   &=&
   (\O \setminus vs) \ominus (vs \setminus \O)
\end{eqnarray*}
\begin{code}
rsvDenote mctxt _ less
 = let o = mObs mctxt in ( o \\ less, less \\ o )
\end{code}

Here we interpret $\sem{R\less{vs}} = V \ominus X$ as stating the following:
\begin{itemize}
  \item $V$ is a set of zero or more observation variables that could
   belong to $\sem{R\less{vs}}$.
  \item $X$ is a set of zero or more unknown standard variables
   or list variables (but not reserved). The final semantics of $R$
   depends on how the variables in $X$ can be bound to observation variables.
\end{itemize}
Given a binding $\varsigma$ that maps unknown and list-variables to observation variables,
we can compute a final semantics as follows,
where we take $vs=os\cat us$ as a partitioning of $vs$
into observation variables ($os$) and unknown and list-variables $us$.
Noting that $os \subseteq \O$ and $us \not\!\cap \O$,
we calculate as follows:
\begin{eqnarray*}
   \sem{R\less{vs}}_\varsigma
   &=& (\O \setminus vs) \ominus \varsigma(vs \setminus \O)
\\ &=& (\O \setminus os \cat us) \ominus \varsigma(os \cat us \setminus \O)
\\ &=& (\O \setminus os) \ominus \varsigma(us)
\\ &=& (\O \setminus os) \setminus \varsigma(us)
\\ &=& (\O \setminus (os \cup \varsigma(us))
\end{eqnarray*}

We state here some important simplifying%
\footnote{simplifying for pattern matching, that is.}
principles,
given $R\less{vs}$, $vs=os\cat us$, and its semantics $V \ominus X$
\begin{itemize}
  \item any variable occurs at most once in $vs$
  \item all the variables in $vs$ should match distinct variables in $V$
    \begin{itemize}
       \item all the standard variables in $us$ should match distinct variables in $V$
           \[ x \neq y \implies \varsigma(x) \neq \varsigma(y) \]
       \item the list variables in $us$ should match disjoint sets of variables in $V$
           \[ \lst x \neq \lst y \implies \varsigma(\lst x) \not\!\cap~ \varsigma(\lst y) \]
    \end{itemize}
\end{itemize}
So the total number of standard variables in $vs$ (observation or unknown)
must be less than the cardinality of $\sem{R}$.

\newpage
\subsubsection{Analysis}

It is worth taking a look at the nature of $\sem{R\less{vs}}$,
for various values of $vs$ and possible $\varsigma$. We assume that the observation variables
are $x, y, z$ and unknown variables include $u, v, w$.
The following table shows some possibilities, that cover most of the known use cases:
\[
\begin{array}{|l|r@{~\ominus~}l|l|c|}
  \hline
  r & \sem r = X & V & \varsigma & \sem{r}_\varsigma
\\\hline
  \hline
  R & \setof{x,y,z} & \setof{} & \_ & \setof{x,y,z} ~{}^1
\\\hline
  R\less x & \setof{y,z} & \setof{} & \_ & \setof{y,z} ~{}^1
\\\hline
  R\less{x:y} & \setof{z} & \setof{} & \_ & \setof{z} ~{}^1
\\\hline
  R\less{x:y:z} & \setof{} & \setof{} & \_ & \setof{} ~{}^1
\\\hline
  \hline
  R\less u & \setof{x,y,z} & \setof{u} & u \to x & \setof{y,z} ~{}^3
\\\hline
  R\less{u:v} & \setof{x,y,z} & \setof{u,v} & u\to x, v\to y & \setof{z} ~{}^3
\\\hline
  R\less{u:v:w} & \setof{x,y,z} & \setof{u,v,w} & u\to x, v\to y, w\to z & \setof{}
\\\hline
  \hline
  R\less{x:u} & \setof{y,z} & \setof{u} & u \to y & \setof{z} ~{}^2
\\\hline
  R\less{x:u:v} & \setof{y,z} & \setof{u,v} & u\to y, v\to z & \setof{} ~{}^2
\\\hline
  R\less{x:y:u} & \setof{z} & \setof{u} & u\to z & \setof{}
\\\hline
  \hline
                 &     \multicolumn{2}{|c|}{}     & \lst u\to \setof{}      & \setof{x,y,z}
\\R\less{\lst u} & \setof{x,y,z} & \setof{\lst u} & \lst u\to \setof{x}     & \setof{y,z} ~{}^3
\\               &     \multicolumn{2}{|c|}{}     & \lst u\to \setof{x,y}   & \setof{z} ~{}^3
\\               &     \multicolumn{2}{|c|}{}     & \lst u\to \setof{x,y,z} & \setof{}
\\\hline
                   &    \multicolumn{2}{|c|}{}    & \lst x\to \setof{}    & \setof{y,z}
\\R\less{x:\lst x} & \setof{y,z} & \setof{\lst x} & \lst x\to \setof{y}   & \setof{z} ~{}^2
\\                 &    \multicolumn{2}{|c|}{}    & \lst x\to \setof{y,z} & \setof{}
\\\hline
                        &        \multicolumn{2}{|c|}{}         & \lst u\to \setof{}, \lst v \to \setof{}      &  \setof{x,y,z}
\\                      &        \multicolumn{2}{|c|}{}         & \lst u\to \setof{x}, \lst v \to \setof{}     &  \setof{y,z} ~{}^3
\\R\less{\lst u:\lst v} & \setof{x,y,z} & \setof{\lst u,\lst v} & \lst u\to \setof{x}, \lst v \to \setof{z}    &  \setof{y} ~{}^3
\\                      &        \multicolumn{2}{|c|}{}         & \lst u\to \setof{x,y}, \lst v \to \setof{z}  &  \setof{}
\\                      &        \multicolumn{2}{|c|}{}         & \lst u\to \setof{x,y,z}, \lst v \to \setof{} &  \setof{}
\\\hline
  \hline
  \multicolumn{4}{l}{}
\\\multicolumn{4}{l}{{}^1\mbox{ $\varsigma$ immaterial}}
\\\multicolumn{4}{l}{{}^2\mbox{ one of 2 outcomes}}
\\\multicolumn{4}{l}{{}^3\mbox{ one of 3 outcomes}}
\end{array}
\]

A few laws seem to emerge from considering the above
\begin{eqnarray*}
\sem{r} = V \ominus X &\implies& \sem{r}_\varsigma \subseteq V
\end{eqnarray*}
If no list-variables are present in $vs$, then
\begin{eqnarray*}
\#\sem{R\less{vs}}_\varsigma &=& \#\sem{R} - len(vs)
\end{eqnarray*}
If any list-variables are present in $vs$, then we get
\begin{eqnarray*}
\#\sem{R\less{vs}}_\varsigma &\leq& \#\sem{R} - len(vs)
\end{eqnarray*}

We can summarise as follows, where $os$ are observables,
$us$ are standard unknowns,
and $\lst{}s$ are list variables:
\[\begin{array}{rcccc}
   \sem{R\less{os:us:\lst{}s}}
   &=&
   (\sem{R}\setminus os) &\ominus& (us \cup \lst{}s)
\\ &&  V &\ominus& (X1 \cup XS)
\end{array}\]
We find that
\begin{eqnarray}
   \#\sem{R\less{os:us:\lst{}s}}_\varsigma
   &\leq&
  \#\sem{R} - \#(os \cup \lst{}s)
  \label{eq:rsv-den-cardinality}
\end{eqnarray}
with the inequality being equality if $\lst{}s$ is empty.
A solution is any subset of $\sem{R}\setminus{os}$
that satisfies inequation (\ref{eq:rsv-den-cardinality}).

In terms of the denotation sets:
\begin{eqnarray*}
  V \ominus (X1\cup XS) &=& \sem{R\less{os:us:\lst{}s}}
\\ D &=& \#\sem{R\less{os:us:\lst{}s}}_\varsigma
\\ D &\subseteq& V
\\ \#D &\leq& \#V - \#X1
\end{eqnarray*}


A key point to keep in mind during pattern-matching is that the value
of $\varsigma$ is unknown at match time, and that certain choices for it
are consistent with a succesful match, while others are not, depending on the reserved variable's context
in the test expression as a whole.
The matcher has to somehow make its best guess.


\newpage
\subsection{Variable Conditioning}\label{ssec:Var:Cond}

In order to simplify matching we make the following assumptions
about variables in both pattern and test expressions.
\begin{itemize}
  \item All bound variables are disjoint from all free unknown variables
  \item All bound variables are disjoint from all known non-observation variables
   \\ (we allow observation variables to occur in quantifier lists).
  \item Any two distinct binding constructs,
        where one is nested inside the other,
     must have disjoint variables
\end{itemize}
Any expression that does not satisfy the above conditions can be transformed
into one that does using $\alpha$-renaming.

We do not enforce these conditions or provide facilities to so transform
expressions in this prototype module.

\newpage
\subsection{Matching Top-Level}

The top level matcher sets up the contexts,
and then invokes each stage of the matching process.
We pass in an empty match result to start,
and merge in new bindings as we proceed,
with the aim of ensuring we fail as soon as possible.
\begin{code}
topMatch :: (Functor m, Monad m)
      => ThCtxt   -- theory context
      -> SCond   -- test sidecondition
      -> Expr    -- test expresssion
      -> SCond   -- pattern sidecondition
      -> Expr    -- pattern expression
      -> m (IMResult, IMResult)
topMatch thctxt tsc texpr psc pexpr
 = match (mkMCtxt thctxt tsc psc) noIMR [] texpr [] pexpr

type Match m = MCtxt     -- match context
               -> IMResult  --  result so far
               -> [Var]     -- test bound variables
               -> Expr      -- test expresssion
               -> [Var]     -- pattern bound variables
               -> Expr      -- pattern expression
               -> m (IMResult, IMResult)

match :: (Functor m, Monad m) => Match m
match mctxt imr0 tbvs texpr pbvs pexpr
 = do imres <- eMatch mctxt imr0 tbvs texpr pbvs pexpr
      if null $ unDMS $ mtodo imres
       then return (imres, imres)
       else do fmres <- fMatch mctxt (binds imres) (unDMS $ mtodo imres)
               return (imres, fmres)
\end{code}

\newpage
\subsection{Structural Matching}

We are now in a position to define the first phase,
that performs structural matching of a test expression against a pattern.
This either fails, or returns a binding, along with any deferred matches.
We use an initially empty collection of bindings and deferred matches
as an accumulating parameter.

We write the binding of pattern variables $x$ and $y$
to test expression $e$ and $f$ respectively, as
\[
 x \to e, y \to f
\]
and we use $\theta$ to denote the empty map.

Given a set $P$ of pattern variables, and a set $T$
of test objects, we might want to construct a binding
of all variables in $P$ that precisely covers all objects in $T$.

We write
\[
 P \to^D T
\]
to describe the resulting binding, in the case that there is only
one way to construct it---it is deterministic.
We use the notation
\[
  P \to^N T
\]
to describe a deferred match $(P,T)$, in the case that there
is more than one way to construct the bindings---it is non-deterministic.

As we both specify and implement matching as a recursive descent
through both pattern and test abstract syntax, we need to track,
at each stage, what binder are currently in scope.
So we need to keep track of bound variables.

Given:
\begin{itemize}
  \item a matching context $\Gamma$ identifying $(\kappa,\O,sc_t,sc_p)$
    \begin{itemize}
      \item known variables ($\kappa$)
      \item observation variables $(\O)$
      \item test side-condition ($sc_t$) and
      \item pattern side-condition ($sc_p$);
    \end{itemize}
  \item a test expression $t$,
  \item a list of bound test variables $B_t$,
  \item a pattern expression $p$,
  \item a list of bound pattern variables $B_p$,
  \item a match result $\Xi$ containing $\beta \deferred \nu,\sigma$
    \begin{itemize}
      \item a match binding $\beta$,
      \item deferred variable-list matches $\nu$, and
      \item deferred substitution-list matches $\sigma$.
    \end{itemize}
\end{itemize}
we write
\[
  \Gamma
  \wefind (t,B_t) \matches (p,B_p)
  \withbind \Xi
\]
or
\[
  (\kappa,\O,sc_t,sc_p)
  \wefind (t,B_t) \matches (p,B_p)
  \withbind \beta \deferred \nu,\sigma
\]
to say that
\begin{quote}
``in match context $\Gamma=(\kappa,\O,sc_t,sc_p)$, we can match test $(t,B_t)$
 against pattern $(p,B_p)$,
yielding a result $\Xi$ with binding $\beta$, and deferred matches $\nu$ and $\sigma$''.
\end{quote}

We also write
\[
  \Gamma
  \wefind P \to^D T
\]
to mean
\begin{quote}
``in match context $\Gamma$,
  there is only one way to construct a binding of all variables in $P$
  that precisely covers all variables in $T$
  yielding a result $\Xi$ with binding $\beta = P \to T$, and empty deferred matches''.
\end{quote}
and
\[
  \Gamma
  \wefind P \to^N T
\]
to mean
\begin{quote}
``in match context $\Gamma$,
  there is more than one way to construct a binding of all variables in $P$
  that precisely covers all variables in $T$
  yielding a result $\Xi$ with an empty binding $P \to T$,
  and empty deferred $\sigma$,
  but with $\nu=\setof{(P,T)}$''.
\end{quote}
The general case where we are checking for either of the above
is written as
\[
  \Gamma
  \wefind P \to^? T
\]


We will have a number of different structural matchers,
which we distinguish by a subscript on $\matches$, as follows:

\begin{tabular}{|c|c|c|l|l|}
  \hline
  symbol & patn & test & function & page
  \\\hline
   $\matches_e$ & \texttt{Expr} & \texttt{Expr} & \texttt{eMatch}
   & \pageref{code:eMatch}
  \\\hline
   $\matches_v$ & \texttt{Var}  & \texttt{Var} & \texttt{vMatch}
   & \pageref{code:vMatch}
  \\\hline
   $\matches_\ell$ & \texttt{Var} & \texttt{[Var]} & \texttt{lstVMatch}
   & \pageref{code:lstVMatch}
  \\\hline
   $\matches_\ast$ & \texttt{[Var]} & \texttt{[Var]} & \texttt{vSeqMatch}
   & \pageref{code:vSeqMatch}
  \\\hline
   $\matches_\power$ & \setof{\texttt{Var}} & \setof{\texttt{Var}} & \texttt{vSetMatch}
   & \pageref{code:vSetMatch}
  \\\hline
   $\matches_s$ & \texttt{Substn} & \texttt{Substn} & \texttt{subMatch}
   & \pageref{code:subMatch}
  \\\hline
   $\matches_{es}$ & \texttt{Var} & \texttt{[Expr]} & \texttt{vesMatch}
   & \pageref{code:vesMatch}
  \\\hline
\end{tabular}

\newpage
\subsection{Call Graph}

We finish with a diagram showing the call graph for \texttt{eMatch}

\includegraphics{proto/eMatch-calls.eps}


Here we note if any call may defer matches, and if so, are they
between sets or sequences of variables, and are the variables
free or bound.

Code Page table:

\begin{tabular}{|l|r|}
  \hline
  Function & Page
  \\\hline
  \texttt{eMatch} & \pageref{code:eMatch}
  \\\hline
  \texttt{esMatch} & \pageref{code:esMatch}
  \\\hline
  \texttt{vMatch} & \pageref{code:vMatch}
  \\\hline
  \texttt{lstVMatch} & \pageref{code:lstVMatch}
  \\\hline
  \texttt{uvsMatch} & \pageref{code:uvsMatch}
  \\\hline
  \texttt{vSetMatch} & \pageref{code:vSetMatch}
  \\\hline
  \texttt{vSeqMatch} & \pageref{code:vSeqMatch}
  \\\hline
  \texttt{subMatch} & \pageref{code:subMatch}
  \\\hline
\end{tabular}

\newpage
\subsubsection{Expression Matching}

We start with $\matches_e$ implemented by \texttt{eMatch}:
\label{code:eMatch}
\begin{code}
eMatch :: (Functor m, Monad m)
       => MCtxt    -- match context
       -> IMResult -- result so far
       -> [Var]    -- test bound variables
       -> Expr     -- test expresssion
       -> [Var]    -- pattern bound variables
       -> Expr     -- pattern expression
       -> m IMResult
\end{code}

\paragraph{Wildcard Pattern}~

The wildcard matches anything, with no bindings
\[
  \Gamma
  \wefind (\wild,\_) \matches_e (e,\_)
  \withbind \theta \deferred \emptyset,\emptyset
\]
\begin{code}
eMatch _ imr _ _ _ Wild  =  return imr
\end{code}

\paragraph{Constant Pattern}~

Constants match themselves, with no bindings
\[
  \Gamma
  \wefind (k,\_) \matches_e (k,\_)
  \withbind \theta \deferred \emptyset,\emptyset
\]
\begin{code}
eMatch _ imr _ (Const ti) _ (Const pi)
 | ti == pi   =  return imr
 | otherwise  =  fail "mismatched constants"
\end{code}

\paragraph{Variable Pattern}~

If we have both pattern and test as variables,
we hand over to a variable matcher
\[
  \inferrule{%
  \Gamma
  \wefind (v,B_t) \matches_v (u,B_p)
  \withbind \beta \deferred \nu, \sigma
  }%
  {%
  \Gamma
  \wefind (v,B_t) \matches_e (u,B_p)
  \withbind \beta \deferred \nu, \sigma
  }
\]
\begin{code}
eMatch mctxt imr tbvs (Var tv) pbvs (Var pv)
 = vMatch mctxt imr tbvs tv pbvs pv
\end{code}

We normally only expect \texttt{Std} variables in general expressions.
List or reserved variables occur
 in variable lists (\texttt{Lam},\texttt{Sub},\texttt{Exists})
and in equalities, where both sides have to be list variables.

If a pattern variable is being matched against
an expression, and it is either an observation variable, non-standard, or bound,
then the match fails:
\begin{code}
eMatch mctxt imr tbvs te pbvs (Var pv)
 | not $ isStd pv       = fail "non-std variable cannot match expression"
 | pv `elem` pbvs       = fail "bound std variable cannot match expression"
 | pv `elem` mObs mctxt = fail "observational variable cannot match expression"
\end{code}

\textbf{ASSERTION}%
---%
\verb"isStd pv && not(pv `elem` pbvs) && not(pv `elem` mObs mctxt)"

A standard variable matches an arbitrary expression,
if it is not bound, not an observable, and not known:
\[
  \inferrule{%
    v_\circ \notin \kappa,\O,B_p
  }%
  {%
  (\kappa,\O,\_,\_)
  \wefind (e,\_) \matches_e (v_\circ,B_p)
  \withbind v_\circ \to e \deferred \emptyset,\emptyset
  }
\]
A standard variable matches its definition,
if it is not bound, not an observable, but is known:
\[
  \inferrule{%
    \kappa(v_\circ) = e \quad v_\circ \notin \O,B_p
  }%
  {%
  (\kappa,\O,\_,\_)
  \wefind (e,\_) \matches_e (v_\circ,B_p)
  \withbind v_\circ \to e \deferred \emptyset,\emptyset
  }
\]
\begin{code}
eMatch mctxt imr tbvs te pbvs (Var pv@(Std pstr))
 = case tlookup (mKnown mctxt) pstr of
    Nothing -> imr `imrMrg` IMR (vbind pv te) noDMS
    Just pe
      | pe == te   ->  imr `imrMrg` IMR (vbind pv te) noDMS
      | otherwise  ->  fail "known std variable can only match own definition"
\end{code}

\paragraph{Meta-Variable Pattern}~

We do not have meta-variable bindings in this prototype language,
so we simply treat these as unknown unbound variables,
matching any expression
\[
  \Gamma
  \wefind (e,\_) \matches_e (E,B_p)
  \withbind E \to e \deferred \emptyset,\emptyset
\]
Note that we assume here that meta-variables
and variables share the same name space.
\begin{code}
eMatch mctxt imr tbvs te pbvs (MVar mstr)
 = imr `imrMrg` IMR (vbind (Std mstr) te) noDMS
\end{code}

\paragraph{Equality Pattern}~

This is the place where non-\texttt{Std} variables may occur
provided they are the sole occupants of both the left-hand and right hand
components.
Then pattern
\[
  \ell_1 = \ell_2
\]
matches
\[
  x_1 = y_1 \land \ldots \land x_n = y_n
\]
for $n \geq 1$, with bindings
\begin{eqnarray*}
   \ell_1 &\to& x_1,\ldots,x_n
\\ \ell_2 &\to& y_1,\ldots,y_n
\end{eqnarray*}
If either $\ell$ is (not) bound then
all the variables they match must be (not) bound. Note that the bound status
of $\ell_1$ and $\ell_2$ can be different (this is a common use-case).

The either of the above variables are reserved, then additional constraints
apply: see later.

The case for generic list variables when $n=1$ is simplest
\[
  \inferrule{%
    \Gamma \wefind (x_i,B_t) \matches_v (\lst{u}_i,B_p) \withbind \Phi_i,
    \qquad i\in 1,2
  }%
  {%
  \Gamma
  \wefind (x_1=x_2,B_t) \matches_e (\lst{u}_1=\lst{u}_2,B_p)
  \withbind \Phi_1 \sqcup \Phi_2
  }
\]
\begin{code}
eMatch mctxt imr tbvs (Eq (Var x1) (Var x2)) pbvs (Eq (Var ell1) (Var ell2))
 = do imr1 <- vMatch mctxt imr  tbvs x1 pbvs ell1
      imr2 <- vMatch mctxt imr1 tbvs x2 pbvs ell2
      return imr2
\end{code}

For $n > 1$ (plus a degenerate form of $n=1$)
the rule is
\[
  \inferrule{%
    \Gamma \wefind
      (\seqof{x_1,\ldots,x_n},B_t) \matches_\ell (\lst{u}_1,B_p) \withbind \Phi_1
      \quad
      (\seqof{y_1,\ldots,y_n},B_t) \matches_\ell (\lst{u}_2,B_p) \withbind \Phi_2
  }%
  {%
  \Gamma
  \wefind (x_1 = y_1 \land \ldots \land x_n = y_n,B_t)
   \matches_e (\lst{u}_1=\lst{u}_2,B_p)
  \withbind \Phi_1 \sqcup \Phi_2
  }
\]
We simply split the equalites up and match the two
resulting variable-lists seperately. We then merge the two resulting bindings.
\begin{code}
eMatch mctxt imr tbvs (And tes) pbvs (Eq (Var ell1) (Var ell2))
 | null tes   =  fail "l$ = l$ must match at least one variable equality"
 | otherwise
   =  do (tvs1,tvs2) <- splitEqualityVars tes
         imr1 <- lstVMatch mctxt imr  tbvs tvs1 pbvs ell1
         imr2 <- lstVMatch mctxt imr1 tbvs tvs2 pbvs ell2
         return imr2
 where
   splitEqualityVars [] = return ([],[])
   splitEqualityVars  (Eq (Var v1) (Var v2) : es)
    = do (vs1,vs2) <- splitEqualityVars es
         return (v1:vs1, v2:vs2)
   splitEqualityVars _ = fail "l$=l$ can only match variable equalities"
\end{code}


Apart from the special cases above,
we can treat most of the rest of matching as
a straightforward recursive structural recursive walkthrough.
\[
  \inferrule{%
    \Gamma \wefind (f_i,B_t) \matches_e (e_i,B_p) \withbind \Phi_i,
    \qquad i\in 1,2
  }%
  {%
  \Gamma
  \wefind (f_1 = f_2,B_t) \matches_e (e_1=e_2,B_p)
  \withbind \Phi_1 \sqcup \Phi_2
  }
\]

\begin{code}
eMatch mctxt imr tbvs (Eq te1 te2) pbvs (Eq pe1 pe2)
 = do imr1 <- eMatch mctxt imr  tbvs te1 pbvs pe1
      imr2 <- eMatch mctxt imr1 tbvs te2 pbvs pe2
      return imr2
\end{code}

\paragraph{And Pattern}~
\[
  \inferrule{%
    \Gamma \wefind (f_i,B_t) \matches_e (e_i,B_p) \withbind \Phi_i,
    \qquad i\in 1,\ldots,n
  }%
  {%
  \Gamma
  \wefind (\bigwedge(f_1,\ldots,f_n),B_t) \matches_e (\bigwedge(e_1,\ldots,e_n),B_p)
  \withbind \bigsqcup \Phi_i
  }
\]
\begin{code}
eMatch mctxt imr tbvs (And tes) pbvs (And pes)
                                         = esMatch mctxt imr tbvs tes pbvs pes
\end{code}

\paragraph{App Pattern}~
\[
  \inferrule{%
    \Gamma \wefind (f_i,B_t) \matches_e (e_i,B_p) \withbind \Phi_i,
    \qquad i\in 0,\ldots,n
  }%
  {%
  \Gamma
  \wefind (f_0(f_1,\ldots,f_n),B_t) \matches_e (e_0(e_1,\ldots,e_n),B_p)
  \withbind \bigsqcup \Phi_i
  }
\]
\begin{code}
eMatch mctxt imr tbvs (App te tes) pbvs (App pe pes)
                               = esMatch mctxt imr tbvs (te:tes) pbvs (pe:pes)
\end{code}

\paragraph{Lam Pattern}~
\[
  \inferrule{%
    \Gamma \wefind (f,B_t) \matches_e (e,B_p) \withbind \Phi_1
    \qquad
    \Gamma \wefind \nu_t \matches_\ast \nu_p
    \withbind \Phi_2
  }%
  {%
  \Gamma
  \wefind (\lambda \nu_t @ f,B_t) \matches_e (\lambda \nu_p @ e,B_p)
  \withbind \Phi_1 \sqcup \Phi_2
  }
\]
\begin{code}
eMatch mctxt imr tbvs (Lam (VL tvl) te) pbvs (Lam (VL pvl) pe)
 = do imrb <- eMatch mctxt imr tbvs te pbvs pe
      vSeqMatch mctxt imrb tvl pvl
\end{code}


\paragraph{Exists Pattern}~
\[
  \inferrule{%
    \Gamma \wefind (f,B_t) \matches_e (e,B_p) \withbind \Phi_1
    \qquad
    \Gamma \wefind \nu_t \matches_\power \nu_p
    \withbind \Phi_2
  }%
  {%
  \Gamma
  \wefind (\exists \nu_t @ f,B_t) \matches_e (\exists \nu_p @ e,B_p)
  \withbind \Phi_1 \sqcup \Phi_2
  }
\]
\begin{code}
eMatch mctxt imr tbvs (Exists (VL tvl) te) pbvs (Exists (VL pvl) pe)
 = do imrb <- eMatch mctxt imr tbvs te pbvs pe
      vSetMatch mctxt imrb (lnorm tvl) (lnorm pvl)
\end{code}


\paragraph{Unimplemented cases}~

\begin{code}
eMatch mctxt imr tbvs (Sub te tsubs) pbvs (Sub pe psubs)
 = do imrb <- eMatch mctxt imr tbvs te pbvs pe
      subMatch mctxt imr tbvs tsubs pbvs psubs
\end{code}

All other cases fail:
\begin{code}
eMatch _ _ _ _ _ _ = fail "Structural mis-match"
\end{code}

\newpage
\subsubsection{Expression List Matching}

We simply work along two lists of expressions,
matching corresponding expressions:
\label{code:esMatch}
\begin{code}
esMatch :: (Functor m, Monad m)
        => MCtxt    -- match context
        -> IMResult -- result so far
        -> [Var]    -- test bound variables
        -> [Expr]   -- test expresssions
        -> [Var]    -- pattern bound variables
        -> [Expr]   -- pattern expression
        -> m IMResult

esMatch mctxt imr0 tbvs tes pbvs pes
 = esmatch imr0 tes pes
 where
   esmatch imr []       []        =  return imr
   esmatch _   []       (pe:pes)  =  fail "too many pattern expressions"
   esmatch _   (te:tes) []        =  fail "too many test expressions"
   esmatch imr (te:tes) (pe:pes)
     = do imr' <- eMatch mctxt imr tbvs te pbvs pe
          esmatch imr' tes pes
\end{code}

\newpage
\subsection{Variable Matching}

\subsubsection{Single Variable Matching}

We continue with $\matches_v$ implemented by \texttt{vMatch}:
\label{code:vMatch}
\begin{code}
vMatch :: Monad m
       => MCtxt    -- match context
       -> IMResult -- result so far
       -> [Var]    -- test bound variables
       -> Var      -- test variable
       -> [Var]    -- pattern bound variables
       -> Var      -- pattern variable
       -> m IMResult
\end{code}

\paragraph{Standard Variable Pattern}~

An observation variable (standard) only matches itself, with no binding
(like a constant), provided it hasn't been bound:
\[
  \inferrule{%
    u_\circ \in \O \quad u_\circ \notin B_p
  }%
  {%
  (\_,\O,\_,\_)
  \wefind (u_\circ,\_) \matches_v (u_\circ,B_p)
  \withbind \theta \deferred \emptyset,\emptyset
  }
\]
If bound, it matches anything bound:
\[
  \inferrule{%
    u_\circ \in \O \quad u_\circ \in B_p \quad v_\circ \in B_t
  }%
  {%
  (\_,\O,\_,\_)
  \wefind (v_\circ,B_t) \matches_v (u_\circ,B_p)
  \withbind u_\circ \to v_\circ \deferred \emptyset,\emptyset
  }
\]
\begin{code}
vMatch mctxt imr tbvs tv pbvs pv@(Std _)
 | pv `elem` mObs mctxt
   = if pv `elem` pbvs && tv `elem` tbvs
     then imr `imrMrg` IMR (vbind pv (Var tv)) noDMS
     else if pv == tv
          then return imr
          else fail "observation variable only matches self"
\end{code}
\textbf{Note}%
---%
\textsf{the case of an observation variable being bound should not occur
if patterns have been conditioned properly, using $\alpha$-renaming
to avoid such clashes.}

A standard bound variable can match any standard bound variable
\[
  \inferrule{%
    u_\circ \in B_p \quad v_\circ \in B_t
  }%
  {%
  \Gamma
  \wefind (v_\circ,B_t) \matches_v (u_\circ,B_p)
  \withbind u_\circ \to v_\circ \deferred \emptyset,\emptyset
  }
\]
\begin{code}
vMatch mctxt imr tbvs tv@(Std _) pbvs pv@(Std _)
 |  pv `elem` pbvs  &&  tv `elem` tbvs
    = imr `imrMrg` IMR (vbind pv (Var tv)) noDMS
\end{code}

A standard unknown, unbound variable can match any unbound standard
variable:
\[
  \inferrule{%
    u_\circ \notin \kappa,\O,B_p \quad v_\circ \notin B_t
  }%
  {%
  (\kappa,\O,\_,\_)
  \wefind (v_\circ,B_t) \matches_v (u_\circ,B_p)
  \withbind u_\circ \to v_\circ \deferred \emptyset,\emptyset
  }
\]
\begin{code}
vMatch mctxt imr tbvs tv@(Std _) pbvs pv@(Std _)
 | isUnknown mctxt pv
   && not ( pv `elem` pbvs )
   && not ( tv `elem` tbvs )
    = imr `imrMrg` IMR (vbind pv (Var tv)) noDMS
 | otherwise  =  fail "no remaing std-variable match possibilities"
\end{code}

\paragraph{List Variable Pattern}~

A generic list variable that is (not) bound matches
any variable that is (not) bound.
\[
  \inferrule{%
    \lst u \notin B_p \quad x \notin B_t
  }%
  {%
  \Gamma
  \wefind (x,B_t) \matches_v (\lst u,B_p)
  \withbind \lst u \to \seqof x \deferred \emptyset,\emptyset
  }
\]
\[
  \inferrule{%
    \lst u \in B_p \quad x \in B_t
  }%
  {%
  \Gamma
  \wefind (x,B_t) \matches_v (\lst u,B_p)
  \withbind \lst u \to \seqof x \deferred \emptyset,\emptyset
  }
\]
\begin{code}
vMatch mctxt imr tbvs tv pbvs pv@(Lst _)
 | pbound && tbound || not( pbound || tbound )
    = imr `imrMrg` IMR (vbind pv (Var tv)) noDMS
 | otherwise  =  fail "list-variable boundeness mismatch"
 where
   (pbound,tbound) = (pv `elem` pbvs, tv `elem` tbvs)
\end{code}

\paragraph{Reserved Variable Pattern}~

We will consider matching a pattern reserved variable $r$
against an arbitrary test variable $v$ on a case-by-case basis:

\subparagraph{Rsv to Std}

A reserved variable $r$ matches a single \texttt{Std} variable $x_\circ$
only when
what we know about its denotation ensures that it can represent exactly one
variable, and the given one to boot.

In a general setting, matching text $\std x$ against pattern $r$
succeeds if, given that $\sem{r} = V \ominus X$,
we can show that $x_\circ \in V$ and that we can
construct a binding $X \to V\setminus\setof{\std x}$.
\[
  \inferrule{%
     \sem{r}_\Gamma = V \ominus X
     \qquad
     \std x \in V
     \qquad
     \Gamma \wefind X \to^D (V\setminus\setof{\std x})
  }%
  {%
  \Gamma
  \wefind (\std x,B_t) \matches_v (r,B_p)
  \withbind r \to \seqof{\std x}, X \to (V\setminus\setof{\std x})
            \deferred \emptyset,\emptyset
  }
\]
\[
  \inferrule{%
     \sem{r}_\Gamma = V \ominus X
     \qquad
     \std x \in V
     \qquad
     \Gamma \wefind X \to^N (V\setminus\setof{\std x})
  }%
  {%
  \Gamma
  \wefind (\std x,B_t) \matches_v (r,B_p)
  \withbind r \to \seqof{\std x}
            \deferred \setof{(X,V\setminus\setof{\std x})},\emptyset
  }
\]
provided $r \notin B_p \land \std x \notin B_t \lor r \in B_p \land \std x \in B_t$.
\begin{code}
vMatch mctxt imr tbvs tv@(Std _) pbvs pv@(Rsv r less)
 | not (tv `elem` mObs mctxt)
    =  fail "rsv can only single-match an observation variable"
 | pbound && not tbound || not pbound && tbound
    =  fail "rsv-variable boundedness mismatch"
 | not (tv `elem` pV)
    = fail "test variable not in reserve denotation"
 | otherwise
    = do imrX <- uvsMatch setVSPair mctxt imr (pV\\[tv]) pX
         imrX `imrMrg` IMR (vbind pv (Var tv)) noDMS
 where
  (pbound,tbound) = (pv `elem` pbvs, tv `elem` tbvs)
  (pV,pX) = rsvDenote mctxt r less
\end{code}

\newpage
\subparagraph{Rsv to Rsv}

In general $\sem r$ has the form $V \ominus X$,
where $V$ is a set of observation variables,
and $X$ is a set of unknown standard variables and list variables.
So we can view matching a test reserved variable
against a pattern reserved variable
as guided by their denotations (``$\matches_d$''):
\[
 V_t \ominus X_t  \matches_d V_p \ominus X_p
\]
A key principle here is that the correctness of the match cannot depend
on any variable in $X_t$
satisfying some constraint about its `future' value.
This rules out,
for example, the match $R\less{x:u} \matches_v R\less{x:y}$,
or in denotational terms:
$
   \setof{y,z} \ominus \setof u \matches_d \setof z \ominus \emptyset.
$
The reason is that such a match carries a future commitment for test $u$
to have the `value' $y$, and we cannot represent this, nor is it reasonable
for us to develop such%
\footnote{I think this could also lead to unsoundness,
but this hasn't been checked at present}%
.
In particular, if $V_t$ has variables not present in $V_p$,
then the match must fail because otherwise we would need
to impose such a commitment on variables in $X_t$.
However, $V_p$ may contain variables not in $V_t$ so long
as we can find something in $X_p$ to bind to them.
In summary, it must always be possible to construct a binding
from $X_p$ to cover $X_t \cup (V_p \setminus V_t)$.

The following summarises the requirements, in denotational terms,
for a succesful match:
\begin{eqnarray*}
   V_t &\subseteq& V_p
\\ \Gamma
   &\wefind&
   X_p  \to^? X_t \cup (V_p \setminus V_t)
\end{eqnarray*}
\begin{code}
vMatch mctxt imr tbvs tv@(Rsv tr tless) pbvs pv@(Rsv pr pless)
 | not (tV `issubset` pV) = fail "test Rsv observables not covered"
 | otherwise
    = do imr' <- uvsMatch setVSPair mctxt imr ((pV\\tV) ++ tX) pX
         imr' `imrMrg` IMR (vbind pv $ Var tv) noDMS
 where
   (pV,pX) = rsvDenote mctxt pr pless
   (tV,tX) = rsvDenote mctxt tr tless
\end{code}

\subparagraph{Rsv to Lst}

Any match between test $\lst u$ and pattern $r$ involves
the kind of `future' commitment mentioned above, and so is not allowed.
\begin{code}
vMatch _ _ _ _ _ _ = fail "Rsv pattern cannot match Lst variable"
\end{code}

\newpage
\subsubsection{List Variable Matching}

We continue with $\matches_\ell$ implemented by \texttt{lstVMatch}:
\label{code:lstVMatch}
\begin{code}
type LVMatch m = MCtxt  -- match context
                 -> IMResult
                 -> [Var]  -- test bound variables
                 -> [Var]  -- test variables
                 -> [Var]  -- pattern bound variables
                 -> Var    -- pattern variable
                 -> m IMResult

lstVMatch :: (Functor m, Monad m) => LVMatch m
\end{code}

\paragraph{List Variable Pattern}~

Provided all the test variables are (not) bound and the pattern variable
is (not) bound we simply succeed and return the binding.
\[
  \inferrule{%
    \lst u \notin B_p \quad xs \not{\!\cap} B_t
  }%
  {%
  \Gamma
  \wefind (xs,B_t) \matches_\ell (\lst u,B_p)
  \withbind \maplet {\lst u} {xs} \deferred \emptyset,\emptyset
  }
\]
\[
  \inferrule{%
    \lst u \in B_p \quad xs \subseteq B_t
  }%
  {%
  \Gamma
  \wefind (x,B_t) \matches_\ell (\lst u,B_p)
  \withbind \maplet {\lst u} {xs} \deferred \emptyset,\emptyset
  }
\]
\begin{code}
lstVMatch mctxt imr tbvs tvs pbvs pv@(Lst _)
 | pbound && tbound || not( pbound || tbound )
    = fmap (dbg "LSTV(1)") $ imr `imrMrg` IMR (vsbind pv (map Var tvs)) noDMS
 | otherwise  =  fail "no remaining lst-variable list-match possibilities"
 where
   (pbound,tbound) = (pv `elem` pbvs, lnorm tvs `issubset` tbvs)
\end{code}


\paragraph{Reserved Variable Pattern}~

Provided all the test variables are (not) bound and the pattern variable
is (not) bound we simply proceed to try to match.

We note the need to avoid requiring unknown or list variables
to be forced to commit to some value, as discussed in the Rsv vs Rsv matching
earlier. However we do note that sometimes we can match in this case where
the test is a list of variables, without implying any such commitment.
Consider matching either test $u,R\less u$ or test $\lst u,R\less{\lst u}$
against pattern $R$. This is permissible, because in netiher case does it
force either $u$ or $\lst u$ to have any specific value, as both tests above
denote same thing as $R$ for any ultimate assignment of $u$ and $\lst u$
to observable values.

Our first step is to normalise a list of variables so that any occurence of
a variable in the list both in its own right, and as part of a reserved variable
subtraction list, is effectively ``cancelled out'' by removing both.

Then we attempt to compute an overall ``denotation'' for these
as follows:
\begin{itemize}
  \item We collect all non-reserved variables into $S$
        and compute the denotations of all the reserved variables.
  \item For every denotation $V \ominus X$,
        if any variables in $V$ are also found in $S$,
        then we must check if we can
        map an appropriate subset of $X$ to those variables:
   \begin{itemize}
     \item If we cannot, the variable list is ill-formed, and so the
           pattern match fails
     \item If we can, we remove those variables involved in the mapping
           from $V$ and $X$ as appropriate.
   \end{itemize}
  \item We fuse $S$ with the remaining $V$, and fuse the $X$s to get
        an overall denotation.
\end{itemize}
One we have this overall denotation, we match it against the pattern
variable, in precisely the same fashion used by \texttt{vMatch}
with both reserved test and pattern variables.

In effect, we have a partial function $\sem\_^*$
that takes a list of reserved variables, and returns an overall  denotation
\[
  \inferrule{%
    \lst u \notin B_p
    \quad
    xs \not{\!\cap} B_t
    \quad
    \sem{xs}^* = (V_t \ominus X_t)
    \quad
    (V_t \ominus X_t) \matches_d \sem r
  }%
  {%
  \Gamma
  \wefind (xs,B_t) \matches_\ell (r,B_p)
  \withbind \maplet {r} {xs}  \deferred \emptyset,\emptyset
  }
\]
\[
  \inferrule{%
    \lst u \in B_p
    \quad xs \subseteq B_t
    \quad
    \sem{xs}^* = (V_t \ominus X_t)
    \quad
    (V_t \ominus X_t) \matches_d \sem r
  }%
  {%
  \Gamma
  \wefind (x,B_t) \matches_\ell (r,B_p)
  \withbind \maplet {r} {xs}  \deferred \emptyset,\emptyset
  }
\]
\begin{code}
lstVMatch mctxt imr tbvs tvs pbvs pv@(Rsv pr pless)
 | not (pbound && tbound) && ( pbound || tbound )
    =  fail "no remaining rsv-variable list-match possibilities"
 | otherwise
    = do (tV,tX) <- fmap (dbg "LSTV(2)") $ bindContingentDenotes toth trsv
         if tV `issubset` pV
          then do imr2 <- uvsMatch setVSPair mctxt imr ((pV\\tV) ++ tX) pX
                  imr2 `imrMrg` IMR (vsbind pv $ map Var tvs) noDMS
          else fail "test list observables not covered"

 where
   (pbound,tbound) = (pv `elem` pbvs, tvs `issubset` tbvs)
   (trsv,toth) = normLess $ partition isRsv $ lnorm tvs
   (pV,pX) = rsvDenote mctxt pr pless

   normLess :: ([Var],[Var]) -> ([Var],[Var])
   normLess (trsv,toth) = normless [] toth trsv

   normless vsrt toth [] = (vsrt,toth)
   normless vsrt toth (Rsv r less : rest)
    = let (r',toth') = nless r less toth
      in normless (r':vsrt) toth' rest

   nless r less toth = (Rsv r (less\\toth), toth\\less)

   bindContingentDenotes :: (Functor m, Monad m) => [Var] -> [Var]
     -> m ([Var],[Var])
   bindContingentDenotes  toth trsv
     = do m <- sequence $ map (bindContingentDenote toth) trsv
          return $ fuse toth m

   bindContingentDenote :: Monad m => [Var] -> Var -> m ([Var],[Var])
   bindContingentDenote toth (Rsv r less)
    | null ovl   =  return (v,x)
    | otherwise
       = do us <- getbinders ovl x
            return (v \\ ovl, x\\us)
    where
      (v,x) = rsvDenote mctxt r less
      ovl = v `intersect` toth

   getbinders :: Monad m => [Var] -> [Var] -> m ([Var])
   getbinders [] [] = return []
   getbinders vs [] = fail "ill-condition Rsv var-list (null)"
   -- greedy !
   getbinders vs (vls@(Lst _):_) = return [vls]
   getbinders (v:vs) (u@(Std _):us)
     = do us' <- getbinders vs us
          return (u:us')
   getbinders _ _ = fail "ill-conditioned Rsv var-list (non-null)"

   fuse :: [Var] -> [([Var],[Var])] ->  ([Var], [Var])
   fuse toth dens = (toth++concat vs, concat xs) where (vs,xs) = unzip dens
\end{code}


All other cases fail:
\begin{code}
lstVMatch _ _ _ tvs _ pv = fail ( "List-Variable mis-match "
                                  ++ show pv
                                  ++ " |-> "
                                  ++ show tvs )
\end{code}

\newpage
\subsection{KOULR Matching}\label{ssec:KOULR}

We are going to describe our general approach to matching set or lists
of variables as being KOULR (Known; Observables; Unknown; List; Reserved) Matching.

Given a set (list) of variables $V$
we can immediately partition it based on the kind of variable:
Standard ($S$), List ($L$) or Reserved ($R$):
\[
  V = S \sqcup L \sqcup R
\]
Here we use $\sqcup$ to denote the union of two \emph{disjoint} sets%
\footnote{
So $A = B \sqcup C$ actually
means $A = B \cup C ~~\land~~ A \cap C = \emptyset$.
}%
.

The standard variables can be partitioned into those that are
Known ($K$), Observable ($O$), and Unknown ($U$).
\[
  S = K \sqcup O \sqcup U
\]
The observable, unknown, list and reserved variables can also occur
 as free ($V^f$) or bound ($V^b$).
\[
  V = V^f \sqcup V^b
\]

If we take the Variable Conditioning principles in \S\ref{ssec:Var:Cond}
into account then we can draw the following table:

\[
\begin{array}{|c|c|c|}
  \hline
    & \emph{free} & \emph{bound}
  \\\hline
  K & K^f & \emptyset
  \\\hline
  O & O^f & O^b
  \\\hline
  U & U^f & U^b
  \\\hline
  L & L^f & L^b
  \\\hline
  R & R^f & R^b
  \\\hline
\end{array}
\]

We can write a function that performs the above classification
and computes the size of each component to boot:
\begin{code}
classifyVars :: MCtxt
             -> [Var]  -- bound variables
             -> [Var]  -- our variable list
             -> ( (Int,[Var] )  --  K
                , (Int,[Var] )  --  O^f
                , (Int,[Var] )  --  O^b
                , (Int,[Var] )  --  U^f
                , (Int,[Var] )  --  U^b
                , (Int,[Var] )  --  L^f
                , (Int,[Var] )  --  L^b
                , (Int,[Var] )  --  R^f
                , (Int,[Var] )  --  R^b
                )
classifyVars mctxt bvs vs = error "classifyVars NYI"
\end{code}

\newpage

We now consider the case of matching a set (list) of pattern variables $V_P$
against a set (list) of test variables $V_T$, broken down into its KOULR classifications:
\[
\begin{array}{|c|c|c|}
  \hline
  K_T & K^f_T & \emptyset
  \\\hline
  O_T & O^f_T & O^b_T
  \\\hline
  U_T & U^f_T & U^b_T
  \\\hline
  L_T & L^f_T & L^b_T
  \\\hline
  R_T & R^f_T & R^b_T
  \\\hline
\end{array}
\quad
\matches_\power\!\!(\matches_\ast)
\quad
\begin{array}{|c|c|c|}
  \hline
  K_P & K^f_P & \emptyset
  \\\hline
  O_P & O^f_P & O^b_P
  \\\hline
  U_P & U^f_P & U^b_P
  \\\hline
  L_P & L^f_P & L^b_P
  \\\hline
  R_P & R^f_P & R^b_P
  \\\hline
\end{array}
\]

We now discuss restrictions on what matches are possible.

\begin{itemize}
  \item every Standard Pattern Variable must match exactly
      one (distinct) Standard Test Variable.
      \\$\#S_P \leq \#S_T$
      \begin{itemize}
        \item a Known or Observable Pattern Variable can only
          match itself (modulo bound observable subscripts%
          \footnote{
            Not pertinent here in \texttt{ProtoMatch},
            but relevant in the full \UTP2 system.
          }
          ).
          \\$K_P \subseteq K_T ~\land O_P \subseteq O_T$.
        \item
          Free Standard Unknown Pattern Variables
          can only match Known and Free
            Observable or Unknown Test Variables.
          \\$\#U^f_P \leq \#S^f_T$
        \item
          Bound Standard Unknown Pattern Variables
          can only match Bound
            Unknown Test Variables.
          \\$\#U^b_P \leq \#U^b_T$
       \end{itemize}
  \item every Standard Test Variable must be matched by exactly
      one Pattern Variable.
      \\$\#S_P < \#S_T \implies \#L_P + \#R_P > 0$
  \item every List Test Variable must be matched by
      some List Pattern Variable.
      \\$\#L_T > 0 \implies \#L_P  > 0$
  \item every Reserved Pattern Variable
      can only match Test Standard and Reserved Variables.
      If we disallow degenerate%
      \footnote{
      A reserved variable $r$ is \emph{degenerate}
      if $\sem{r}_\beta = \emptyset$
      for any $\beta$.
      }
      Reserved variables,
      then we must satisfy:
      \\$\#R_P > n \implies (\#S_T-\#S_P) + \#R_T > n$
\end{itemize}
The collection of properties shown above are collectively referred
to as the \emph{KOULR Conditions}, and we expect it to be satisfied by
all deferred matches. There is no point deferring this check,
as we prefer to fail early.

Note that if $\#S_P = \#S_T > 0$ then we can split our matching
problem into two independent parts:
\[
  S_T \matches_\power S_P
  \qquad
  L_T\sqcup R_T \matches_\power L_P\sqcup R_P
\]
This is because there will need to be a 1-1 binding between
$S_P$ and $S_T$ which completes them, so no bindings for the
list and reserved pattern variables will
involve the standard test variables.

We can write a function that takes classified variables
and checks the KOULR Condition:
\begin{code}
satisfiesKOULR :: ( (Int,[Var] )  --  K
                  , (Int,[Var] )  --  O^f
                  , (Int,[Var] )  --  O^b
                  , (Int,[Var] )  --  U^f
                  , (Int,[Var] )  --  U^b
                  , (Int,[Var] )  --  L^f
                  , (Int,[Var] )  --  L^b
                  , (Int,[Var] )  --  R^f
                  , (Int,[Var] )  --  R^b
                  )
               -> Bool
satisfiesKOULR _ = error "satisfiesKOULR NYI"
\end{code}

\newpage
\subsection{Unknown Variable-VSet Matching}


We carry on with both $P \to^D T$ and $P \to^N T$,
implemented as \texttt{uvsMatch}:
\label{code:uvsMatch}
\begin{code}
uvsMatch :: Monad m
         => ([Var] -> [Var] -> DCM) -- set/seq context
         -> MCtxt                   -- match context
         -> IMResult                -- match so far
         -> [Var]                   -- test variables
         -> [Var]                   -- pattern unknown (std,list) variables
         -> m IMResult
\end{code}

We are trying to check:
\[
 (\kappa,\_,\_,\_) \wefind
  P \to^D T
  \quad
  \textbf{or}
  \quad
  P \to^N T
\]

\subsubsection{Phase 1}

The first phase involves checking, for every $p \in P$,
if it is already bound: $p \to t$.
If so, and $t$ is in $T$, we remove both from $P$ and $T$ respectively,
otherwise we fail. If $p$ is not bound to anything, then it is left in $P$
and we move onto the next pattern variables.

\begin{code}
uvsMatch mkpair mctxt imr tvs pvs
  = do (tvs',pvs') <- remBound tvs [] pvs
       uvsMatch' mkpair imr (lnorm tvs') (lnorm pvs')
  where
    remBound tvs svp [] = return (tvs,svp)
    remBound tvs svp (pv:pvs)
     = case vlkp (binds imr) pv of
         Nothing             ->  remBound tvs (pv:svp) pvs
         Just [(Var tv)]
            | tv `elem` tvs  ->  remBound (tvs\\[tv]) svp pvs
         _      -> fail "pattern-var bound to other than denotation test-var"
\end{code}

\subsubsection{Phase 2}

We are checking
\[
 \_ \wefind
  P \to^D T
  \quad
  \textbf{or}
  \quad
  P \to^N T
\]
where we know no variable in $P$ is already bound.
\begin{code}
uvsMatch' :: Monad m
         => ([Var] -> [Var] -> DCM) -- set/seq context
         -> IMResult                -- match so far
         -> [Var]                   -- test variables
         -> [Var]                   -- pattern unknown, unbound (std,list) variables
         -> m IMResult
\end{code}
We tackle this on a case by case basis

\paragraph{No Pattern Variables}~

As long as there are no test variables, we are OK:

\[
  \_ \wefind \nil ~\to^D~ \nil
  \withbind \theta
\]
\begin{code}
uvsMatch' mkpair imr tvs []
 | null tvs  =  return imr
 | otherwise  =  fail "no pattern-vars to match the test-vars"
\end{code}

\paragraph{Single List-Variable to Any}~

\[
  \_ \wefind \lst p ~\to^D~ T
  \withbind \lst p \to T
\]
\begin{code}
uvsMatch' mkpair imr tvs [pv@(Lst _)]
 = do imr `imrMrg` IMR (vsbind pv (map Var tvs)) noDMS
\end{code}

\paragraph{Single Std, many Lst to Single Std }~

\[
  \_ \wefind p_\circ,\lst q,\ldots,\lst r ~~\to^D~~ t_\circ
  \withbind
  p_\circ \to t_\circ, \lst q \to \nil, \ldots , \lst r \to \nil
\]
\begin{code}
uvsMatch' mkpair imr [tv@(Std _)] (pv@(Std _):pvs)
 | all isLst pvs
    = do imrPVs <- imr `imrMrg` IMR (vsnulls pvs) noDMS
         imrPVs `imrMrg` IMR (vbind pv (Var tv)) noDMS
\end{code}

\paragraph{Many Lst to Empty test}~

\[
  \_ \wefind \lst q,\ldots,\lst r ~~\to^D~~ \emptyset
  \withbind
  \lst q \to \nil, \ldots , \lst r \to \nil
\]
\begin{code}
uvsMatch' mkpair imr [] pvs
 | all isLst pvs
    = imr `imrMrg` IMR (vsnulls pvs) noDMS
\end{code}

\paragraph{The General Case}

We can find at least one binding if the number of std-variables
in set $P$ are fewer than those in set $T$, but we have to defer it.
\[
  \_ \wefind P_\circ\cup\lst P ~~\to^N~~ T_\circ \cup \lst T
  \withbind
  \setof{(P_\circ\cup\lst P,T_\circ \cup \lst T)}
\]
provided
\begin{eqnarray*}
   \#P_\circ \leq \#T_\circ
\\ \#P_\circ < \#T_\circ & \implies & \#\lst P > 0
\\ \#\lst T > 0 & \implies & \#\lst P > 0
\end{eqnarray*}
\textbf{To Be Implemented}: \emph{We note that if $\#\std P = \#\std T$ then we can split
the deferrals into disjoint vars: std-only, lst-only.}
\begin{code}
uvsMatch' mkpair imr tvs pvs
  | pslen > tslen                         =  fail "too many std pattern-vars"
  | pllen == 0 && (pslen < tslen || tllen > 0)
                                          =  fail "not enough lst pattern vars"
  | otherwise
     = imr `imrMrg` IMR noBinds (DMS [mkpair pvs tvs] )
  where
   (pstd,plst) = partition isStd pvs
   (tstd,tlst) = partition isStd tvs
   pslen = length pstd
   tslen = length tstd
   pllen = length plst
   tllen = length tlst
\end{code}



\newpage
\subsection{Variable Sequence Matching}

We want to infer the following:
\[
    \Gamma \wefind \nu_t \matches_\ast \nu_p \withbind \Phi
\]
We don't need to know what the current bound variables are for either
pattern or test, as these variables are all binding occurences.

Having reserved variables in lambda-lists
makes very little sense, with no obvious use-cases, and would require too much
in the way of ordering conventions, so is not supported here.

The main problem with implementing this is determining,
for every generic list-variable in the pattern, the number of variables
with which it should associated.

We do a preliminary analysis of both pattern and target in order to rule out infeasible matches.
This analysis centres around identifying runs of standard and list variables
in order to determine if matching can be done.
The fact that order matters reduces the degree of non-determinism to a considerable
degree.

\newpage
\subsubsection{Abstracting Variable Sequences}

Given a variable sequence, we can abstract by determining the run-lengths
of sub-sequences that alternate between standard and list variables
(Here we use a convention that we always start with the length of a list-variable run):
\begin{eqnarray*}
   \lst a,\lst b, u,v, \lst c, x, \lst d,\lst e, y,z
   &\mapsto&   2, 2, 1, 1, 2, 2
\\ \lst a,\lst b, u,v, \lst c, x, \lst d,\lst e, y,z, \lst f
   &\mapsto& 2, 2, 1, 1, 2, 2, 1
\\ u,v, \lst c, x, \lst d,\lst e, y,z, \lst f
   &\mapsto& 0, 2, 1, 1, 2, 2, 1
\end{eqnarray*}
The runs of standard variables can only match a corresponding sub-sequence of the same kind of variable, while runs of list-variables can match zero of more of any kind of variable. We can therefore represent all non-zero list-variable runs by zeros, and omitting leading or trailing zeros to indicate lack of initial or final list-variable runs.
\begin{eqnarray*}
   2, 2, 1, 1, 2, 2 &\mapsto&  0,2,0,1,0,2
\\ 2, 2, 1, 1, 2, 2, 1 &\mapsto& 0,2,0,1,0,2,0
\\ 0, 2, 1, 1, 2, 2, 1 &\mapsto&  2,0,1,0,2,0
\end{eqnarray*}
We don't need all those alternating zeros, so we come up with an abstraction of three parts:
\begin{itemize}
  \item A leading digit (0 or 1) to indicate if the list starts with list-variables.
  \item A sequence of non-zero positive numbers indicating the lengths of maximal runs of standard variables, in order.
  \item A trailing digit (0 or 1) to indicate if the list ends with list-variables.
\end{itemize}
\begin{eqnarray*}
   0,2,0,1,0,2   &\mapsto&  1 \quad 2,1,2 \quad 0
\\ 0,2,0,1,0,2,0 &\mapsto&  1 \quad 2,1,2 \quad 1
\\ 2,0,1,0,2,0   &\mapsto&  0 \quad 2,1,2 \quad 1
\end{eqnarray*}
Reprising from start to finish:
\begin{eqnarray*}
   \lst a,\lst b, u,v, \lst c, x, \lst d,\lst e, y,z
   &\mapsto&   1 \quad 2,1,2 \quad 0
\\ \lst a,\lst b, u,v, \lst c, x, \lst d,\lst e, y,z, \lst f
   &\mapsto& 1 \quad 2,1,2 \quad 1
\\ u,v, \lst c, x, \lst d,\lst e, y,z, \lst f
   &\mapsto& 0 \quad 2,1,2 \quad 1
\end{eqnarray*}

\newpage

\paragraph{Code: }
We need to keep track of the relevant subsequences,
so our code first extracts those,
and then constructs the above abstraction,
with links to the subsequences.
\begin{code}
-- ==========================================================================
vTypePartition :: [Var] -> [[Var]]
-- we split list into maximal run of varsof the same type (std/lst)
-- we always start and end with lst vars, which means the first and last
-- run lists may be empty. The rest will all be non-empty.
vTypePartition vs
 = vDoingLst [] [] vs
 where
  vDoingLst parts lvs [] = reverse (reverse lvs:parts)
  vDoingLst parts lvs (v:vs)
   | isLst v    =  vDoingLst parts (v:lvs) vs
   | otherwise  =  vDoingStd (reverse lvs:parts) [v] vs
  vDoingStd parts svs [] = reverse ([]:reverse svs:parts)
  vDoingStd parts svs (v:vs)
   | isStd v    =  vDoingStd parts (v:svs) vs
   | otherwise  =  vDoingLst (reverse svs:parts) [v] vs
-- vs = concat $ vTypePartition vs

vSeqAbs :: [[Var]] -> (Bool, [Int], Bool)
-- we only expect to apply this to outputs from vTypePartition
vSeqAbs [[]]  =  (False,[],False)
vSeqAbs [_]   =  (True,[],True)
vSeqAbs vts
 = let
    (lftlst:rest1) = vts
    (rhtlst:rest2) = reverse rest1
   in ( not $ null lftlst
      , map length $ drop2nd $ reverse rest2
      , not $ null rhtlst )
 where
   drop2nd [] = []
   drop2nd [x] = [x]
   drop2nd (x:y:zs) = x:drop2nd zs
\end{code}
It is worth noting the forms that the outputs take
 of both \texttt{vTypePartition} and \texttt{vSeqAbs},
 particulary in simple cases:
\[
\begin{array}{ccc}
  \texttt{vs} & \texttt{vTypePartition} & \texttt{vSeqAbs}
\\\hline
  \texttt{[]} & \texttt{[[]]} & \texttt{(False,[],False)}
\\
  \texttt{[x]} & \texttt{[[],[x],[]]} & \texttt{(False,[1],False)}
\\
  \texttt{[xs]} & \texttt{[[xs]]} & \texttt{(True,[],True)}
\\
  \texttt{[x,xs]} & \texttt{[[],[x],[xs]]} & \texttt{(False,[1],True)}
\\
  \texttt{[xs,x]} & \texttt{[[xs],[x],[]]} & \texttt{(True,[1],False)}
\\
  \texttt{[xs,x,xs]} & \texttt{[[xs],[x],[xs]]} & \texttt{(True,[1],True)}
\\
  \texttt{[x,xs,x]} & \texttt{[[],[x],[xs],[x],[]]} & \texttt{(False,[1,1],False)}
\\\hline
\end{array}
\]
Here \texttt{x} and \texttt{xs} are standard and list variables respectively.
If we replace any \texttt{x} above by a sequence of same,
or similarly for \texttt{xs},
then the only changes is that the \texttt{1}s become the length
of the corresponding \texttt{x}-sequence.

\newpage
\subsubsection{Abstracted Sequence Judgements}
We can make a lot of quick judgments about the possibility of matching
using this abstraction, as well as breaking the problem into subsequences
that can either be discharged, or deferred.
Consider the following pair of abstractions, the top one being a pattern,
the lower a test:
\begin{eqnarray*}
   \ell_p \qquad p_1 , \ldots, & p_i & ,\ldots, p_m \qquad r_p
\\ \ell_t \qquad t_1 , \ldots, & t_j & ,\ldots, t_n \qquad r_t
\end{eqnarray*}
If \emph{any} of  following conditions hold, then \emph{no} match is possible:
\begin{description}
  \item[$\lnot\ell_p \land \ell_t$ : ]~\\
    There are no leftmost list variables in the pattern
    to match the leftmost list variables in the test
  \item[$\lnot r_p \land r_t$ : ]~\\
    There are no rightmost list variables in the pattern
    to match the rightmost list variables in the test
  \item[$m < n$ : ]~\\
    The pattern has too few runs, and cannot match all of the list-variables
    in between the test standard variable runs.
  \item[$\sum p_i > \sum t_j$ : ]~\\
    There are not enough standard variables in the test
    to be matched by standard variables in the pattern.
\end{description}
We can summarise by saying the following is
a necessary, but not sufficient, condition for a match to be possible:
\[
  (\ell_p \implies \ell_t)
  \land
  (r_p \implies r_t)
  \land
  (m \geq n)
  \land
  \sum p_i \leq \sum t_j
\]
In addtion, for a match to be possible,
there must exist a total, injective,
strictly monotonic increasing function
\[
  f : \setof{1,\ldots,m} \fun \setof{1,\ldots,n}
\]
such that, if $j = f(i)$, we have $p_i \leq t_j$
and either:
\begin{description}
  \item[$p_i = t_j$ : ]~\\
      we have a precise match of the corresponding standard pattern and list variables, or
  \item[$p_i < t_j$ : ]~\\
      and provided there is at least one list pattern variable on either the left or right of the $p_i$, we can  match them against a contiguous subsequence of the $t_j$.
\end{description}
In the second case above, the only way in which we cannot find such a list variable is if there are none,
so our abstract pattern has the form $0 \quad p \quad 0$.
In this case the only tests we can match must also have exactly the same abstract form: $0 \quad t \quad 0$, where $t=p$.

We can identify a number of situations where we can say a little more about
the nature of $f$:
\begin{description}
  \item[$m=n$ : ]
    then $f(i)=i$, for all $i$.
  \item[$\lnot\ell_p$ : ]
    then $f(1)=1$.
  \item[$\lnot r_p$ : ]
    then $f(m)=n$.
\end{description}


\newpage
\subsubsection{\texttt{vSeqMatch} code}
\label{code:vSeqMatch}
\begin{code}
vSeqMatch :: (Functor m, Monad m)
          => MCtxt      -- match context
          -> IMResult   -- match so far
          -> [Var]      -- test (std,list) variables
          -> [Var]      -- pattern (std,list) variables
          -> m IMResult

-- we deal with simple cases directly
-- [] -> [[]] -> (False,[],False)
vSeqMatch mctxt imr0 tvl []
 | null tvl  =  return imr0  -- trivial match
 | otherwise  =  fail "null-sequence can only match a null-sequence"

vSeqMatch mctxt imr0 tvl@[tv] pvl@[pv] = vMatch mctxt imr0 tvl tv pvl pv

-- [x]  -> [[],[x],[]] -> (False,[1],False)
-- [xs] ->    [[xs]]   -> (True,[],True)
vSeqMatch mctxt imr0 tvl pvl@[pv] = lstVMatch mctxt imr0 tvl tvl pvl pv

vSeqMatch mctxt imr0 tvl pvl
 | not lp && lt  =  fail "leftmost std patn var cannot match test lst var"
 | not rp && rt  =  fail "rightmost std patn var cannot match test lst var"
 | n > m         =  fail "too many std test runs to match"
 | psum > tsum   =  fail "not enough std vars to match"
 | otherwise     =  vSeqAbsMatch mctxt imr0 tvl pvl tvts pvts tabs pabs
 where
   (tvts,pvts) = (vTypePartition tvl, vTypePartition pvl)
   tabs@(lt,ts,rt) = vSeqAbs tvts
   pabs@(lp,ps,rp) = vSeqAbs pvts
   (m,n) = (length ps, length ts)
   (psum,tsum) = (sum ps, sum ts)
\end{code}

\newpage
We have a globally viable match, now let's get local
\begin{code}
vSeqAbsMatch :: (Functor m, Monad m)
             => MCtxt             -- match context
             -> IMResult          -- match so far
             -> [Var]             -- test variable list
             -> [Var]             -- pattern variable list
             -> [[Var]]           -- test variables (partitioned)
             -> [[Var]]           -- pattern variables (partitioned)
             -> (Bool,[Int],Bool) -- test variable abstraction
             -> (Bool,[Int],Bool) -- pattern variable abstraction
             -> m IMResult
\end{code}

An interesting sub-class is those abstractions of the form
\begin{eqnarray*}
   \ell_p & p_1 & r_p
\\ \ell_t & t_1 & r_t
\end{eqnarray*}
i.e., those were we have all standard variables together,
with the possibility of some list variables at either end.

We can handle a number of cases.

\paragraph{Case 1: $0~~p~~0$}
\begin{eqnarray*}
   0 & p_1 & 0
\\ 0 & t_1 & 0
\end{eqnarray*}
Succeeds with a precise binding, if $p_1 = t_1$, otherwise fails:
\begin{code}
vSeqAbsMatch mctxt imr0 tvl pvl tvts pvts
             (False, [n], False) (False, [m], False)
 | n == m  =  do binds1 <- vvbinds $ zip pvl tvl
                 imr0 `imrMrg` IMR binds1 noDMS
 | otherwise  =  fail "too few pattern vars"
\end{code}

\paragraph{Case 2: $1~~p~~1$}
\begin{eqnarray*}
   1 & p_1 & 1
\\ \ell_t & t_1 & r_t
\end{eqnarray*}
Succeeds with a precise binding, if $p_1 = t_1$
plus trying to match the lefthand and righthand list variables.
If $p_1 < t_1$ then we defer.
\begin{code}
vSeqAbsMatch mctxt imr0 tvl pvl [tllst,tstd,trlst] [pllst,pstd,prlst]
             (_, [n], _) (True, [m], True)
 | n == m
   = do binds1 <- vvbinds $ zip pstd tstd
        imr1 <- imr0 `imrMrg` IMR binds1 noDMS
        imr2 <- uvsMatch seqVLPair mctxt imr1 tllst pllst
        uvsMatch seqVLPair mctxt imr2 trlst prlst
 | otherwise  -- n > m
   = imr0 `imrMrg` IMR noBinds (DMS [seqVLPair pvl tvl])
\end{code}

\paragraph{Case 2: $0~~p~~1$}
\begin{eqnarray*}
   0 & p_1 & 1
\\ 0 & t_1 & r_t
\end{eqnarray*}
We match $p_1$ against left end of $t_1$, and then match the rest.
\begin{code}
vSeqAbsMatch mctxt imr0 tvl pvl [[],tstd,tlst] [[],pstd,plst]
             (False, [n], _) (False, [m], True)
 = do binds1 <- vvbinds $ zip pstd tfirst
      imr1 <- imr0 `imrMrg` IMR binds1 noDMS
      uvsMatch seqVLPair mctxt imr1 (trest++tlst) plst
 where (tfirst,trest) = splitAt m tstd
\end{code}

\paragraph{Case 2: $1~~p~~0$}
\begin{eqnarray*}
   0 & p_1 & 1
\\ 0 & t_1 & r_t
\end{eqnarray*}
We match $p_1$ against right end of $t_1$, and then match the rest.
\begin{code}
vSeqAbsMatch mctxt imr0 tvl pvl [tlst,tstd,[]] [plst,pstd,[]]
             (_, [n], False) (True, [m], False)
 = do binds1 <- vvbinds $ zip pstd tlast
      imr1 <- imr0 `imrMrg` IMR binds1 noDMS
      uvsMatch seqVLPair mctxt imr1 (tlst++trest) plst
 where (trest,tlast) = splitAt (n-m) tstd
\end{code}

Any other case, we just defer the whole lot\ldots
\begin{code}
vSeqAbsMatch mctxt imr0 tvl pvl tvts pvts tabs pabs
 = imr0 `imrMrg` IMR noBinds (DMS [seqVLPair pvl tvl])
\end{code}
~


\newpage
\subsection{Variable VSet Matching}

We want to infer the following:
\[
    \Gamma \wefind \nu_t \matches_\power \nu_p \withbind \Phi
\]
Unlike the $\matches_\ast$ case above,
here ordering is not significant.
The best we can do here is
look at a few simple cases where matching is forced,
and defer the rest.
\label{code:vSetMatch}
\begin{code}
vSetMatch :: (Functor m, Monad m)
          => MCtxt      -- match context
          -> IMResult   -- match so far
          -> [Var]      -- test (std,list) variables (normalised)
          -> [Var]      -- pattern (std,list) variables (normalised)
          -> m IMResult

-- all null
vSetMatch mctxt imr []  []  = return imr

-- std vs std
vSetMatch mctxt imr [tv@(Std _)] [pv@(Std _)]
  = imr `imrMrg` IMR (vbind pv $ Var tv) noDMS

-- lst vs anything
vSetMatch mctxt imr tvs [pv@(Lst _)]
  = imr `imrMrg` IMR (vsbind pv $ map Var tvs) noDMS

-- rsv vs anything
vSetMatch mctxt imr tvs [pv@(Rsv _ _)]
  = lstVMatch mctxt imr tvs tvs [pv] pv
\end{code}
In any other case, do basic sanity checking, then defer.
\begin{eqnarray*}
  & \inferrule
     {\Gamma \wefind
       \qquad
         v_1,\ldots v_a \matches_\power u_1,\ldots u_a
         \withbind \Phi_1
         \quad
         \lst m_1,\ldots, \lst m_b \matches_\power \lst n_1,\ldots,\lst n_c
         \withbind \Phi_2
     }
     {\Gamma \wefind
         v_1,\ldots v_a,\lst m_1,\ldots,\lst m_b
         \matches_\power
         u_1,\ldots u_a,\lst n_1,\ldots,\lst n_c
         \withbind \Phi_1 \sqcup \Phi_2}
\\ & \inferrule
     {a \leq b \land ( a < b \implies c > 0)}
     {\Gamma \wefind
         v_1,\ldots v_a,\lst m_1,\ldots,\lst m_c
         \matches_\power
         u_1,\ldots u_b,\lst n_1,\ldots,\lst n_d
      \withbind \Phi}
\end{eqnarray*}
\begin{code}
vSetMatch mctxt imr tvl pvl
 = case compare tlen plen of
     LT  ->  fail "more std-vars in pattern than test"
     EQ  ->  imr `imrMrg` -- exact std match, so seperate from list-vars
              IMR noBinds (DMS [setVSPair pstd tstd, setVSPair plst tlst])
     GT  ->  if null plst
             then fail "no pattern lst-vars to handle test std surplus"
             else imr `imrMrg`
                   IMR noBinds (DMS [setVSPair pvl tvl])
 where
   (pstd,plst) =  partition isStd pvl
   plen = length pstd
   (tstd,tlst) =  partition isStd tvl
   tlen = length tstd
\end{code}


\newpage
\subsection{Substitution Matching}

We treat a substitution as a set of expression-variable pairs,
so the matching treatment is very similar to that of \texttt{vSetMatch}.
\[
    \Gamma \wefind [e_t/v_t] \matches_s [e_p/v_p] \withbind \Phi
\]
The sanity checking done before deferral takes the variable lists,
and subjects them to the same sanity check as done in \texttt{vSetMatch}.

\label{code:subMatch}
\begin{code}
subMatch :: (Functor m, Monad m)
         => MCtxt  -- match context
         -> IMResult
         -> [Var]  -- test bound variables
         -> Substn -- test substitution
         -> [Var]  -- pattern bound variables
         -> Substn -- pattern substitution
         -> m IMResult

-- all null
subMatch mctxt imr tbvs [] pbvs []  =  return imr

-- single vs single
subMatch mctxt imr tbvs [(tv,te)] pbvs [(pv,pe)]
 = do imrv <- vMatch mctxt imr tbvs tv pbvs pv
      eMatch mctxt imrv tbvs te pbvs pe

-- list vs anything
subMatch mctxt imr tbvs tsubs pbvs [(pv@(Lst _),pe@(Var pev@(Lst _)))]
 = do imrv <- lstVMatch mctxt imr tbvs tvs pbvs pv
      vesMatch mctxt imrv tbvs tes pbvs pev
 where (tvs,tes) = unzip tsubs

-- rsv vs any variables
subMatch mctxt imr tbvs tsubs pbvs [(pv@(Rsv _ _),pe@(Var pev@(Rsv _ _)))]
 = do imrv <- lstVMatch mctxt imr tbvs tvs pbvs pv
      lstVMatch mctxt imrv tbvs tevs pbvs pev
 where
  (tvs,tes) = unzip tsubs
  tevs = map dropE tes
\end{code}
For deferred matches, the sanity checking just looks at the
target variables in the substitutions.
\begin{code}
subMatch mctxt imr tbvs tsub pbvs psub
 = case compare tlen plen of
    LT ->  fail "more std-vars in pattern targets than test"
    EQ ->  imr `imrMrg` -- exact std match, so seperate from list-vars
               IMR noBinds
                 (DMS [ subVVEPair (pbvs,pstd) (tbvs,tstd)
                      , subVVEPair (pbvs,plst) (tbvs,tlst) ])
    GT ->  if null plst
           then fail "no pattern target lst-vars to handle test std surplus"
           else imr `imrMrg`
                    IMR noBinds (DMS [subVVEPair (pbvs,psub) (tbvs,tsub)])
 where
   (pstd,plst) =  partition (isStd . fst) psub
   plen = length pstd
   (tstd,tlst) =  partition (isStd . fst) tsub
   tlen = length tstd
\end{code}

\newpage
\subsection{Expr-List Matching}

\[
    \Gamma \wefind \seqof{e_1,\ldots,e_n}_t \matches_{es} \lst p
    \withbind \lst p \to \seqof{e_1,\ldots,e_n}_t
\]

\label{code:vesMatch}
\begin{code}
vesMatch :: (Functor m, Monad m)
         => MCtxt  -- match context
         -> IMResult
         -> [Var]  -- test bound variables
         -> [Expr] -- test expression-list
         -> [Var]  -- pattern bound variables
         -> Var    -- pattern variable
         -> m IMResult

vesMatch mctxt imr tbvs tes pbvs pv
 = imr `imrMrg` IMR (vsbind pv tes) noDMS
\end{code}

\newpage
\subsection{Finalising Deferred Matches}

We have completed structural matching,
and at this stage have some stuff defferred until
a more complete picture of the required bindings can be built.
We now attempt to resolve these,
using a sequences of passes over the data.
\begin{code}
fMatch :: (Functor m, Monad m)
      => MCtxt   -- match context
      -> Binds   -- bindings so far
      -> [DCM]   -- deferred matches
      -> m IMResult
fMatch mctxt bnds todo
 = do (bnds1,todo1) <- fMatchP1 mctxt bnds todo
      return $ IMR bnds1 $ DMS todo1
\end{code}

\subsubsection{Finalising: 1st Pass}

In our first pass we simply take the bindings so far,
and run over the deferred matches to update and simplify them.
\begin{code}
fMatchP1 :: (Functor m, Monad m)
      => MCtxt   -- match context
      -> Binds   -- bindings so far
      -> [DCM]   -- deferred matches
      -> m (Binds, [DCM])
fMatchP1 mctxt bnds todo
 = do res <- sequence $ map (bindApply mctxt bnds) todo
      let (bndss,mtodos) = unzip res
      return (head bndss, catMaybes mtodos)
\end{code}
When we apply a binding to a  deffered set match,
we simply check every deferred pattern variable
to see if it has been bound elsewhere.
If not, we skip it, but if so, we see can we find what it is bound to
in the deferred target variables.
If we do find them, we remove them from the deferred set,
otherwise we fail.
We can define the following overloaded functions:
\begin{description}
  \item[in] returns true if $v$ is in $P$, with $i$ set to location.
  \item[inside] returns true if $\beta(v)$ is contained (appropriately)
   inside $T$.
  \item[$\rhd$] returns just the sub-part of $T$ identified by $\beta(v)$.
  \item[$\matches$] matches $T\rhd\beta(v)$ against $P(v)$.
  \item[$\ntriangleright$] denotes $T$ with the removal of the sub-part identified
  by $\beta(v)$.
\end{description}
We now give three concrete versions of each of these:

\paragraph{Implementing ``in''}~

\begin{code}
inVS, inVL, inVES :: Var -> DItem -> (Bool, Int)
inVS v (_,ves) = invs 0 v ves
 where
  invs _ _ []  =  (False, undefined)
  invs i v (VE x _:rest)
   | v == x  =  (True, i)
   | otherwise  =  invs (i+1) v rest

inVL  = inVS
inVES = inVS
\end{code}

\paragraph{Implementing ``inside'', $\rhd$, $\ntriangleright$}~

Here we fold in the implementation of both $\rhd$ and $\ntriangleright$
as well.
\begin{code}
insideVS, insideVL, insideVES
 :: [Var]        -- binding result
 -> DItem        -- test set or sequence
 -> ( Bool       -- true if "inside"
    , [VEItem]   -- part of test found  |>
    , DItem      -- test remainder  |/>
    )

insideVS vs (bvs,ves)
  = (vs `issubset` map vOf ves, inside, (bvs, outside))
  where (inside,outside) = partition (elemVS vs) ves

elemVS vs (VE v _) = v `elem` vs

insideVL  vs (bvs,ves)
 = case locateSubSeqBy sameV vs ves of
    Nothing  ->  (False, undefined, undefined)
    (Just (before,middle,after))  ->  (True, middle, (bvs, before++after))

sameV v (VE x _)  =  v == x

insideVES = insideVS
\end{code}

\begin{code}
matchVS, matchVL, matchVES :: (Functor m, Monad m) => Match m

matchVS _ imr _ _ _ _  =  return (imr, imr)
matchVL                =  match
matchVES               =  matchVS

lvmatchVS, lvmatchVL, lvmatchVES :: (Functor m, Monad m) => LVMatch m

lvmatchVS _ imr _ _ _ _  =  return imr
lvmatchVL                =  lstVMatch
lvmatchVES               =  lvmatchVS
\end{code}

And we use them....
\begin{code}
bindApply :: (Functor m, Monad m)
          => MCtxt  -- match context
          -> Binds  -- bindings so far
          -> DCM    -- deferred match
          -> m (Binds, Maybe DCM)
bindApply mctxt bnds (DCM VSet pat tst)
 = bndApp mctxt VSet  inVS  insideVS  matchVS  lvmatchVS  bnds pat tst
bindApply mctxt bnds (DCM VSeq pat tst)
 = bndApp mctxt VSeq  inVL  insideVL  matchVL  lvmatchVL  bnds pat tst
bindApply mctxt bnds (DCM VESet pat tst)
 = bndApp mctxt VESet inVES insideVES matchVES lvmatchVES bnds pat tst
\end{code}

\newpage

We can illustrate the process using
the following imperative(!) pseudo-code:
\begin{eqnarray*}
   bindApply_{\langle in,inside,\rhd,\matches,\ntriangleright\rangle }(\beta,P,T)
   &\defs
   & \forall v \in \beta  \textbf{ do}
\\&& \quad \textbf{if } v \textrm{ in } P
\\&& \quad \textbf{then if } \beta(v) \textrm{ inside } T
\\&& \quad ~~~~~\textbf{then } \beta \leftarrowtail \pi_2(T \rhd \beta(v)) \matches P(v)
\\&& \quad ~~~~~\textbf{~~~~~ } (P,T) := (P \ntriangleright v,T\ntriangleright\beta(v))
\\&& \quad ~~~~~\textbf{else } FAIL
\\&& \quad \textbf{else } Skip
\end{eqnarray*}
Here $x \leftarrowtail m$ is like $x := m$,
but propagates any failure from $m$.
When we are not dealing with $(V \times E)$, but just with $V$,
then the line invoking matching to update $\beta$ is superfluous.

\begin{code}
bndApp :: (Functor m, Monad m)
       => MCtxt
       -> DType
       -> (Var -> DItem -> (Bool, Int))
       -> ([Var] -> DItem -> ( Bool, [VEItem], DItem))
       -> Match m
       -> LVMatch m
       -> Binds
       -> DItem
       -> DItem
       -> m (Binds, Maybe DCM)
bndApp mctxt dt isin inside mtch lvmtch bnds pat tst
 = bApp bnds pat tst $ bFlatten bnds
 where

   bFlatten :: Binds -> [(Var,[Expr])]
   bFlatten (Bind std lst)
     = mapfst Std (mapsnd sngl (flattenTrie std))
       ++
       mapfst Lst (flattenTrie lst)

   bApp bnds pat tst [] = bEnd bnds pat tst

   bApp bnds pat@(pbvs,pves) tst@(tbvs,_) ((v,bes):rest)
    = let (ok1,i) = v `isin` pat
      in if ok1
       then
        do ves <- toVar [] bes
           let (ok2,tes,trest) = ves `inside` tst
            in if ok2
             then do bnds' <- bAppMatch mtch lvmtch
                                        tbvs (map eOf tes)
                                        pbvs (eOf (pves!!i))
                     bnds'' <- bnds `bmrg` bnds'
                     bApp bnds'' (pat `less` v) trest (rest++bFlatten bnds')
             else fail "defferred now inconsistent"
       else bApp bnds pat tst (rest)

   bEnd _ (_,[]) (_,_:_) = fail "dangling deferred test bits"
   bEnd bnds pat@(pbvs,pves) tst@(tbvs,tves)
    = if null pves && null tves
      then return (bnds, Nothing)
      else return (bnds, Just $ DCM dt pat tst)

   toVar sev [] = return $ reverse sev
   toVar sev (Var v:rest) = toVar (v:sev) rest
   toVar _ _ = fail "Deferred variable not mapped to variable"

   bAppMatch mtch lvmtch tbvs tes pbvs (Var pv@(Lst _))
    = do tvs <- toVar [] tes
         (IMR bnds deff) <- lvmtch mctxt (IMR noBinds noDMS) tbvs tvs pbvs pv
         if null $ unDMS deff
          then return bnds
          else fail "can't handle nested vs/v deferrals at present"

   bAppMatch mtch lvmtch tbvs [te] pbvs pe
    = do (_,IMR bnds deff) <- mtch mctxt (IMR noBinds noDMS) tbvs te pbvs pe
         if null $ unDMS deff
          then return bnds
          else fail "can't handle nested e/e deferrals at present"

   bAppMatch _ _ _ _ _ _
    = fail "Deferred substn wasn't expr |-> expr or var |-> [var]"

   (vs,ves) `less` v  = (vs,filter (not . sameV v) ves)

-- end bndApp
\end{code}

\newpage
\subsection{New SubSection}

\subsubsection{Data Declarations}

\subsubsection{Show Instances}

\subsubsection{Support Code}

\subsubsection{Test Values}


\newpage
\subsection{Testing}

A match tester with true sideconditions and test candidate last:
\begin{code}
mtest patn test
 = topMatch thctxt true test true patn
\end{code}
We need to run these tests (in \texttt{Either} monad, not exception)
so we can see error/fail messages
\begin{code}
instance Monad (Either String) where
  return = Right
  Left  l >>= _ = Left l
  Right r >>= k = k r
  fail = Left . ("FAILURE : "++) . (++ " !!!")
\end{code}
Now an (expected) outcome indicator:
\begin{code}
data Outcome
 = NoMatch
 | Binding
 | DeferIt
 | DOCHECK
 deriving Show
\end{code}
and code to compare expected an actual:
\begin{code}
checkOutcome :: Outcome -> (IMResult, IMResult) -> String
checkOutcome NoMatch _ = "EXPECTED MATCH FAIL!!"
checkOutcome Binding (imr,_)
 | not $ null $ unDMS $ mtodo imr = "DEFERRED BINDINGS NOT EXPECTED"
checkOutcome DeferIt (imr,_)
 | null $ unDMS $ mtodo imr = "DEFERRED BINDINGS EXPECTED"
checkOutcome DOCHECK (imr,_)
 | null $ unDMS $ mtodo imr = "PLEASE CHECK CAREFULLY"
checkOutcome _ _ = "As Expected"
\end{code}

\newpage
\subsubsection{Reserved Variable Tests}

Now a collection of Rsv/Rsv matches:
\begin{code}
rrTests
 = [ -- (OK?, pat, tst)
     (Binding , [],   [])
   , (NoMatch , [],   [x])
   , (NoMatch , [],   [u])
   , (NoMatch , [],   [us])
   , (NoMatch , [x],  [])
   , (Binding , [x],  [x])
   , (NoMatch , [x],  [y])
   , (NoMatch , [x],  [u])
   , (NoMatch , [x],  [us])
   , (NoMatch , [u],  [])
   , (Binding , [u],  [x])
   , (Binding , [u],  [y])
   , (Binding , [u],  [u])
   , (Binding , [u],  [v])
   , (NoMatch , [u],  [x,y])
   , (NoMatch , [u],  [us])
   , (Binding , [us], [])
   , (Binding , [us], [x])
   , (Binding , [us], [y])
   , (Binding , [us], [u])
   , (Binding , [us], [v])
   , (Binding , [us], [x,y])
   , (Binding , [us], [us])
   , (Binding , [us], [vs])
   , (Binding , [us], [x,ys])
   , (Binding , [us], [x,y,z])
   , (Binding , [x,us], [x,y,z])
   , (Binding , [x,us], [x])
   , (Binding , [x,us], [x,vs])
   , (DeferIt , [us,vs], [x,vs])
   , (DeferIt , [xs,ys], [us,vs])
   , (NoMatch , [x,us], [vs])
   , (NoMatch , [x,us], [y,vs])
   , (Binding , [x,us], [x,y])
   ]
\end{code}

\begin{code}
runRRTests rrtests
 = unlines $ concat $ map runRRTest rrtests

runRRTest (expOutcome,pless,tless)
 = "\n\n====================="
   : (show tv ++ " t=.=p " ++ show pv ++ "    ?" ++ show expOutcome)
   : "-------"
   :
   case tres of
     Left msg  -> [msg]
     Right (imr, fmr)
       -> checkOutcome expOutcome (imr, fmr)
          : lines ( show imr
                   ++ "\nAfter Finalisation:\n"
                   ++ show fmr )
 where
   pv = rless pless
   tv = rless tless
   tres :: Either String (IMResult, IMResult)
   tres = mtest (Var pv) $ Var tv

rrtests = putStrLn $ runRRTests rrTests
\end{code}

\newpage
\subsubsection{Substitution Tests}

Now a collection of Substn/Substn matches:
\begin{code}
ssTests
 = [ -- (OK?, pat, tst)
     (Binding , [],   [])
   , (Binding , [(v,one)], [(v,one)])
   , (Binding , [(v,one)], [(u,one)])
   , (NoMatch , [(v,one)], [(v,two)])
   , (Binding , [(v,Var u)], [(u,one)])
   , (Binding , [(v,Var u)], [(u,two)])
   , (Binding , [(v,Var u)], [(u,q6by9)])
   , (Binding , [(vs,Var us)], [(vs,Var us)])
   , (Binding , [(vs,Var us)], [(vs,Var us),(xs,Var ys)])
   , (Binding , [(vs,Var us)], [(v,Var u),(x,Var y)])
   , (Binding , [(vs,Var us)], [(v,q6by9),(x,a42)])
   , (DeferIt , [(us,Var es),(vs,Var fs)], [(xs,Var zs)])
   , (NoMatch , [(u,one),(v,two)], [(xs,Var zs)])
   , (DeferIt , [(u,one),(us,Var es),(vs,Var fs)], [(v,two),(xs,Var zs)])
   , (DeferIt , [(us,Var es),(vs,Var fs)], [(v,two),(xs,Var zs)])
   , (NoMatch , [(u,one),(us,Var es),(vs,Var fs)], [(xs,Var zs)])
   ]
\end{code}

\begin{code}
runSSTests sstests
 = unlines $ concat $ map runSSTest sstests

runSSTest (expOutcome,psub,tsub)
 = "\n====================="
   : (show tsub ++ " t=.=p " ++ show psub ++ "    ?" ++ show expOutcome)
   : "-------"
   :
   case tres of
     Left msg  -> [msg]
     Right (imr, fmr)
        -> checkOutcome expOutcome (imr, fmr)
           : lines ( show imr
                   ++ "\nAfter Finalisation:\n"
                   ++ show fmr )
 where
   tres :: Either String (IMResult, IMResult)
   tres = mtest (Sub (Const 1) psub) $ Sub (Const 1) tsub

sstests = putStrLn $ runSSTests ssTests
\end{code}

\newpage
\subsubsection{Lambda Tests}

Now a collection of Matches designed to test variable sequence matching
\begin{code}
vvTests -- this is Seq-oriented, need to have Set-oriented version.
 = [ -- (OK?, bind, pat, tst)
     (Binding , [], [],   [])
   , (NoMatch , [], [v], [])
   , (NoMatch , [], [], [u])
   , (Binding , [], [v], [u])
   , (NoMatch , [], [v,vs], [])
   , (Binding , [], [v,vs], [u])
   , (NoMatch , [], [v,vs], [us])
   , (NoMatch , [], [v,vs], [us,u])
   , (Binding , [], [v,vs], [u,x,us])
   , (DeferIt , [], [v,us,vs], [u,x,us])
   , (DeferIt , [(v,u)], [v,us,vs], [u,x,us])
   , (NoMatch , [(v,x)], [v,us,vs], [u,x,us])
   , (DeferIt , [], [us,v,vs], [u,x,us])
   , (DeferIt , [(v,u)], [us,v,vs], [u,x,us])
   , (DeferIt , [(v,x)], [us,v,vs], [u,x,us])
   ]
\end{code}

\begin{code}
runVVTests vvtests
 = unlines $ concat $ map runVVTest vvtests

runVVTest (expOutcome,bnds,pvars,tvars)
 = "\n\n====================="
   : show bnds
   : "|-"
   : (show tvars ++ " =t.p= " ++ show pvars)
   : ("\n-------" ++ "    ?" ++ show expOutcome)
   :
   case tres of
     Left msg  -> [msg]
     Right (imr, fmr)
        -> checkOutcome expOutcome (imr, fmr)
           : lines ( show imr
                   ++ "\nAfter Finalisation:\n"
                   ++ show fmr )
 where
   binds = foldl boverride noBinds $ map vvbind bnds
   (Bind s1 l1) `boverride` (Bind s2 l2)
                              = Bind (s1 `toverride` s2) (l1 `toverride` l2)
   tres :: Either String (IMResult, IMResult)
   tres = match mctxt
                (IMR binds noDMS)
                []
                (Lam (VL tvars) (Const 1))
                []
                (Lam (VL pvars) (Const 1))

vvtests = putStrLn $ runVVTests vvTests
\end{code}

\newpage
\subsubsection{Deferral Tests}

Testing the deferred match handling
\begin{code}
ddTestsP1
 = [ -- (OK?, bind, [DCM])
     (Binding , [], [],   [])
   , (NoMatch , [], [v], [])
   , (NoMatch , [], [], [u])
   , (NoMatch , [], [v], [u])
   , (NoMatch , [], [v,vs], [])
   , (Binding , [], [v,vs], [u])
   , (NoMatch , [], [v,vs], [us])
   , (NoMatch , [], [v,vs], [us,u])
   , (Binding , [], [v,vs], [u,x,us])
   , (DeferIt , [], [v,us,vs], [u,x,us])
   , (DOCHECK , [], [us,v,vs], [u,x,us])
   ]
\end{code}
\newpage
\subsection{Main Program}

Here we simply printout the name of all the tests:
\begin{code}
main
 = do putStrLn "rrtests -- matching Rsv vs Rsv"
      putStrLn "sstests -- matching Substn vs Substn"
      putStrLn "vvtests -- matching Lam vs Lam"
\end{code}

\newpage
\section{Old Deprecated Stuff}

\subsection{Match Resolution}

We need to define
the notions of compatibility between match outcomes ($\Mcong$),
what it means to merge ($\Mmerge$) the same,
and provide a mechanism to resolve $(\Mresolve)$ them.
In addition, given variable-lists we have a quick check
to see if they are ``matchable'' ($\Mmatchable$).

\subsubsection{Variable List Matchability}

A pattern variable list $\nu$ is matchable with a test list $\rho$
if there is some context in which we can construct a disjoint
binding of all variables
in $\nu$ to all variables in $\rho$.
Regular variables in $\nu$ must match regular variables in $\rho$,
so the number of these in the latter must be at least the number in the former.
If $\nu$ has no list variables, then neither can $\rho$ have any,
and their lengths must be equal.
If $\nu$ and $\rho$ have different lengths,
or $\rho$ has any list-variables, then $\nu$ must contain at least one list-variable.

We can write any non-empty variable list in the form:
$$
x_{\circ1},\ldots,x_{\circ m},\lst x_1,\ldots,\lst x_n \qquad m+n\geq 1
$$
without loss of generality
\begin{eqnarray*}
   \Mmatchable &:& V^* \times V^* \fun \Bool
\\ \lefteqn{
      \seqof{x_{\circ1},\ldots,x_{\circ m},\lst x_1,\ldots,\lst x_n}
      \Mmatchable
      \seqof{y_{\circ1},\ldots,y_{\circ k},\lst y_1,\ldots,\lst y_\ell}
   }
\\ &=& k \geq m
\\ &\land& n=0 \implies \ell=0
\\ &\land& m>0 \implies n > 0
\\ &\land& (k+\ell) \neq (m+n) \implies n > 0
\end{eqnarray*}
If this predicate is true, one possible binding is
$x_{\circ i} \to \lst y_i$, for $i \in 1\ldots m$,
and if $n>0$,
then $\lst x_1 \to \seqof{y_{\circ m+1},\ldots,y_{\circ k},\lst y_1,\ldots,\lst y_\ell}$
and $\lst x_j \to \nil$, for $ j \in 2\ldots n$.
However the binding that results depends on the broader context,
and there is a large number%
\footnote{
Hard to give a formula,
but bigger than
$\frac{k!}{(k-m)!} \cdot \frac{(k+\ell-m)!}{((k+\ell-m)\ominus n)!}$,
where $a\ominus b = a-b \cond{b\leq a} 0$.
}
of potential bindings here.

\subsubsection{Match Outcome Compatibility}

Essentially two match outcomes are compatible if every variable they both
match in their bindings is bound to the same thing,
with the relaxation that a binding to a list and a set is compatible
if the list elements are precisely that set in some ordering.
\begin{eqnarray*}
   \Mcong &:& \mathcal O \times \mathcal O \fun \Bool
\\ \omega_1 \Mcong \omega_2
   &=&
   \omega_1 \Mmerge \omega_2 \neq \bot
\end{eqnarray*}
A direct definition of this is possible,
but it is simplest to define it as a successful merge%
\footnote{
 The implementation does not check in advance for compatibility,
 but rather detects it on-the-fly while trying to merge.
}%
.

\subsubsection{Merging Match Outcomes}

We have interdependencies between the three components.
For example, having $\mu(\seqof{\lst x,\lst y})=\setof{a_\circ,b_\circ}$
is not compatible with $\beta(\lst x)=\seqof{c_\circ}$.
However if we have $\beta(\lst x)=\seqof{b_\circ}$,
then we can remove the $\mu$ entry and add $\lst y \to \setof{a_\circ}$
to $\beta$.

The approach we take to merging is to proceed incrementally,
merging the three components of one, one map singleton at a time,
into the other three:
\def\SLMrg{\fn{SLMrg}}
\def\VLMrg{\fn{VLMrg}}
\def\BMrg{\fn{BMrg}}
\begin{eqnarray*}
   \Mmerge &:& \mathcal O \times \mathcal O \fun \mathcal O_\bot
\\ (\beta_1,\mu_1,\sigma_1) \Mmerge \omega_2
   &=& (\fn{VLMrg} \mu_1 \circ \VLMrg \sigma_1 \circ \BMrg \beta_1)\omega_2
\end{eqnarray*}
In the sequel, we assume that if any subcomputation yields failure ($\bot$),
then the whole computation does as well.
Everything gets drilled down to two overloaded operators:
\begin{description}
  \item[Add-Entry] $m \boxplus \maplet x e$
   \\ The mapping from $x$ to $e$ is added to $m$, provided it is consistent
    with what is already there.
  \item[Rem-Entry] $m \circleddash \maplet x e$
    \\ References in $m$ linking $x$ and $e$ are removed,
      as they have been resolved. This fails if $m$ asserts something about $x$
      that makes its link to $e$ incompatible.
\end{description}

We merge bindings first, because these are hard results that must be satisfied,
and hence most likely to trigger failure.
\def\Bmrg{\fn{Bmrg}}
\def\bmrg{\fn{bmrg}}
\begin{eqnarray*}
   \BMrg &:& \mathcal B \fun \mathcal O \fun \mathcal O_\bot
\\ \BMrg(\beta_\circ,\beta_\$)
   &\defs&
   \Bmrg \beta_\$ \circ \Bmrg \beta_\circ
\\
\\ \Bmrg &:& (( V_\circ \pfun E ) + ( V_\$ \pfun (\power E +E^*) ))
             \fun \mathcal O \fun \mathcal O_\bot
\\ \Bmrg(\theta) &\defs& \id
\\ \Bmrg(\maplet v e \sqcup \beta )
   &\defs& \bmrg(v,e) \circ \Bmrg(\beta)
\\
\\ \bmrg &:& ((V_\circ \times E) + (V_\$ \times(\power E + E^*))) \fun \mathcal O \fun \mathcal O_\bot
\\ \bmrg(v_\circ,e)(\beta,\mu,\sigma)
   &\defs&
   ( \beta\boxplus\maplet{v_\circ}e
   , \mu\circleddash\maplet{v_\circ}e
   , \sigma\circleddash\maplet{v_\circ}e
   )
\\ \bmrg(v_\$,\varsigma)(\beta,\mu,\sigma)
   &\defs&
   ( \beta\boxplus\maplet{v_\$}\varsigma
   , \mu\circleddash\maplet{v_\$}\varsigma
   , \sigma\circleddash\maplet{v_\$}\varsigma
   )
\end{eqnarray*}

We merge substitution-lists next, because these contain expression matches,
that can supply more hard bindings.
\def\slmrg{\fn{slmrg}}
\begin{eqnarray*}
   \SLMrg &:& US
             \fun \mathcal O \fun \mathcal O_\bot
\\ \SLMrg(\theta) &\defs& \id
\\ \SLMrg(\maplet s S\sqcup\sigma) &\defs& \slmrg(s,S) \circ \SLMrg(\sigma)
\\
\\ \slmrg &:& ((V \times E)^* \times \power (V\times E)^*) \fun \mathcal O \fun \mathcal O_\bot
\\ \slmrg(s,S)(\beta,\mu,\sigma)
   &\defs& \ldots
\end{eqnarray*}

We merge variable-lists last, because these benefit most from already establish hard bindings.
\def\vlmrg{\fn{vlmrg}}
\begin{eqnarray*}
   \VLMrg &:& UV
             \fun \mathcal O \fun \mathcal O_\bot
\\ \VLMrg(\theta) &\defs& \id
\\ \VLMrg(\maplet \nu S\sqcup\mu) &\defs& \vlmrg(\nu,S) \circ \VLMrg(\mu)
\\
\\ \vlmrg &:& (V^* \times \power E^*) \fun \mathcal O \fun \mathcal O_\bot
\\ \vlmrg(\nu,S)(\beta,\mu,\sigma)
   &\defs& \ldots
\end{eqnarray*}

We now define the lowest level operators.
First, extending the bindings:
\begin{eqnarray*}
   \_\boxplus\_ &:& \mathcal B \fun ((V_\circ \times E) + (V_\$ \times (\power E + E^*))) \fun \mathcal B_\bot
\\ (\beta_\circ,\beta_\$) \boxplus \maplet{v_\circ}e
   &\defs&
   \left\{
     \begin{array}{ll}
       (\beta_\circ\override\maplet{v_\circ}e,\beta_\$)
       & ,v_\circ \notin \beta_\circ \lor \beta_\circ(v_\circ)=e \\
       \bot &, \otherwise
     \end{array}
   \right.
\\ (\beta_\circ,\beta_\$) \boxplus \maplet{v_\$}\varsigma
   &\defs&
   \left\{
     \begin{array}{ll}
       (\beta_\circ,\beta_\$\override\maplet{v_\$}\varsigma)
       & ,v_\$ \notin \beta_\$ \lor \beta_\$(v_\$)=\varsigma \\
       \bot &, \otherwise
     \end{array}
   \right.
\end{eqnarray*}
Next, using a new binding to remove parts of unresolved matches:
\begin{eqnarray*}
   UV &=& V^* \fun \power E^*
\\ \_\circleddash\_ &:& UV \times ((V_\circ \times E) + (V_\$ \times (\power E + E^*))) \fun UV_\bot
\\ \theta \circleddash \maplet{v}X &\defs& \theta
\\ (\maplet \nu E \extend \mu) \circleddash \maplet{v_\circ}e
   &\defs&
   \left\{
     \begin{array}{ll}
       \maplet \nu E \extend (\mu \circleddash \maplet{v_\circ}e)
      & ,  v_\circ \notin \nu
     \\ \maplet{\nu'}{E'}  \extend (\mu \circleddash \maplet{v_\circ}e)
      & , v_\circ \in \nu \land \forall \varsigma \in E @ e \in \varsigma
     \\ \bot, \otherwise
     \end{array}
   \right.
\\ && \WHERE
\\ && \nu' = \nu \hide v_\circ
\\ && E' = \power((\_\hide e))E
\\ (\maplet \nu E \extend \mu) \circleddash \maplet{v_\$}\varsigma
   &\defs&
   \left\{
     \begin{array}{ll}
       \maplet \nu E \extend (\mu \circleddash \maplet{v_\$}\varsigma)
      & ,  v_\$ \notin \nu
     \\ \maplet{\nu'}{E'}  \extend (\mu \circleddash \maplet{v_\$}\varsigma)
      & , v_\$ \in \nu \land \forall \varsigma' \in E @ \varsigma \subseteq \varsigma'
     \\ \bot, \otherwise
     \end{array}
   \right.
\\ && \WHERE
\\ && \nu' = \nu \hide v_\$
\\ && E' = \power((\_\hide \varsigma))E
\\
\\ US &=& (V\times E)^* \fun \power (V\times E)^*
\\ \_\circleddash\_ &:& US \times ((V_\circ \times E) + (V_\$ \times (\power E + E^*))) \fun US_\bot
\\ \theta \circleddash \maplet{v}X &\defs& \theta
\\ (\maplet \varrho S \extend \sigma) \circleddash \maplet{v_\circ}e
   &\defs&
   \left\{
     \begin{array}{ll}
       \maplet \varrho S \extend (\mu \circleddash \maplet{v_\circ}e)
      & ,  v_\circ \notin \pi_1^*\varrho
     \\ \maplet{\varrho'}{S'}  \extend (\mu \circleddash \maplet{v_\circ}e)
      &
     \\ \multicolumn{2}{l}{
          , (v_\circ,f) \in \varrho
            \land
            e \in V_\circ
            \land
            \forall \varsigma \in S @
               \exists g @ (e,g) \in \varsigma \land \framebox{$f \matches g$}
        }
     \\ \bot, \otherwise
     \end{array}
   \right.
\\ && \WHERE
\\ && \varrho' = \varrho \hide (v_\circ,f)
\\ && S' = \power((\_\hide (e,\_)))S
\\ (\maplet \varrho S \extend \sigma) \circleddash \maplet{v_\$}\varsigma
   &\defs&
   \left\{
     \begin{array}{ll}
       \maplet \varrho S \extend (\mu \circleddash \maplet{v_\circ}e)
      & ,  v_\$ \notin \pi_1^*\varrho
     \\ \maplet{\varrho'}{S'}  \extend (\mu \circleddash \maplet{v_\circ}e)
      &
     \\ \multicolumn{2}{l}{
          , (v_\$,\phi) \in \varrho
            \land
            \varsigma \in V^*
            \land
            \forall \varsigma' \in S @
               \exists \varphi @ (\varsigma,\varphi) \in \varsigma' \land \framebox{$\phi \matches \varphi$}
        }
     \\ \bot, \otherwise
     \end{array}
   \right.
\\ && \WHERE
\\ && \varrho' = \varrho \hide (v_\$,\phi)
\\ && S' = \power((\_\hide (\varsigma,\_)))S
\end{eqnarray*}
The matching in the boxes has a side-effect of generating new outcomes,
which need to be merged in turn---we don't explicitly show the control/plumbing here.

\subsubsection{Resolving Match Outcomes}


\newpage
\subsection{Matching Rules}

A matching rule is a quadruple relating a match context ($D$),
a pattern expression in context ($\varepsilon_p$), a test expression-in-context ($\varepsilon_t$),
and a match outcome ($\omega$), written
$$
  D \wefind \varepsilon_p \matches \varepsilon_t \withbind \omega
$$
This is interpreted as saying that
\begin{quote}
  Pattern $\varepsilon_p$ matches test $\varepsilon_t$,
  in global context $D$, with outcome $\omega$.
\end{quote}

A key principle is that every variable in a pattern must be bound,
or recorded as unresolved, even if it matches itself.
This simplifies the process of build replacement expressions using those bindings.

We shall also assume that bound variables are $\alpha$-renamed to avoid
clashing with free variables.

In the rules that follow, we leave out global or local contexts if they are not relevant.

\subsubsection{Constant Matching}

Constants only match themselves, with no bindings required
$$
  \inferrule
   {}
   {k \matches k \withbind \Theta}
  \quad
  \LNAME{Const}
$$

\subsubsection{Variable Matching}

Known (defined, not masked by higher-level binding)
 regular variables only match themselves, but we still require a binding:
$$
  \inferrule
   {x_\circ \in D \setminus B}
   {D \wefind (x_\circ,B) \matches (x_\circ,\_)
     \withbind (x_\circ \to x_\circ,\theta,\theta)}
  \quad
  \LNAME{Known}
$$

Unknown bound regular variables only match other regular bound variables:
$$
  \inferrule
   {x_\circ \in B  \quad y_\circ \in C}
   {D \wefind (x_\circ,B) \matches (y_\circ,C)
     \withbind (x_\circ \to y_\circ,\theta,\theta)}
  \quad
  \LNAME{Bound}
$$

Unknown free regular variables match any expression%
\footnote{Of the same type, but we ignore typing issues here.}%
:
$$
  \inferrule
   {x_\circ \notin D \cup B}
   {D \wefind (x_\circ,B) \matches (e,\_)
     \withbind (x_\circ \to e,\theta,\theta)}
  \quad
  \LNAME{Free}
$$
We do not expect list-variables to appear ``naked'' as an expression,
but we will introduce another relation for these later.

\subsubsection{Application Matching}

Application requires compatible component-wise matches
$$
  \inferrule
   {e_i \matches f_i \withbind \omega_i
    \qquad
    \omega_i \Mcong \omega_j
    \qquad i,j \in 0\ldots n
   }
   {e_0(e_1,\ldots,e_n) \matches f_0(f_1,\ldots,f_n)
    \withbind \Mresolve\left(\Mmerge_i\omega_i\right) }
  \quad
  \LNAME{App}
$$

$$
  \inferrule
   {e_i \matches f_i \withbind \omega_i
    \qquad
    \omega_i \Mcong \omega_j
    \qquad i,j \in 0\ldots n
   }
   {e_1 \land \ldots \land e_n \matches f_1 \land \ldots \land f_n
    \withbind \Mresolve\left(\Mmerge_i\omega_i\right) }
  \quad
  \LNAME{And}
$$

\subsubsection{Abstraction Matching}

Abstraction requires compatible bodies, and leaves quantifier
variables unresolved in the first instance.
$$
  \inferrule
   {\nu \Mmatchable \rho
    \qquad
    (e,B\cup\nu) \matches (f,C\cup\rho) \withbind \omega
    \qquad
    \omega \Mcong  (\theta,\nu \to \seqof\rho,\theta)
   }
   {(\lambda \nu @ e,B) \matches (\lambda \rho @ f,C)
    \withbind
     \Mresolve\left(\omega \Mmerge (\theta,\nu \to \seqof\rho,\theta)\right)
    }
  \quad
  \LNAME{Abs}
$$

\subsubsection{Substitution Matching}

Substitution requires the body expressions to match,
and the substitution lists to be ``matchable'' ($\Mmatchable$)
but leaves the substitution pair matches unresolved
in the first instance
$$
  \inferrule
   {s \Mmatchable t
    \qquad
    e \matches f \withbind \omega
    \qquad
    \omega \Mcong (\theta,\theta,s \to \setof t)
   }
   {e[s] \matches f[t]
     \withbind
     \Mresolve\left(\omega \Mmerge (\theta,\theta,s \to \setof t)\right)
   }
  \quad
  \LNAME{Subst}
$$

\subsubsection{Equality Matching}

The only place where a list-variable can occur ``naked''
in an expression is when two appear, one as the lhs, the other
as the rhs, of an equality assertion.

The first case is when both pattern and test are of this form:
$$
  \inferrule
   {\lst x_1 = \lst x_2 \equiv \lst y_1 = \lst y_2}
   {\lst x_1 = \lst x_2 \matches \lst y_1 = \lst y_2
    \withbind
      (\mapof{
         \lst x_1 \to \seqof{\lst y_1}
       , \lst x_2 \to \seqof{\lst y_2}
       },\theta,\theta)
   }
  \quad
  \LNAME{LstEq}
$$

The next case is when we have a single equality with regular expressions
in the test:
$$
  \inferrule
   {}
   {\lst x_1 = \lst x_2 \matches f_1 = f_2
    \withbind
      (\mapof{
         \lst x_1 \to \seqof{f_1}
       , \lst x_2 \to \seqof{f_2}
       },\theta,\theta)
   }
  \quad
  \LNAME{LstOne}
$$

Then we can match against a conjunction of equalities:
$$
  \inferrule
   {\lst x_1 = \lst x_2
    \matches e_i = f_i
    \withbind \omega_i
    \qquad
    i \in 1\ldots n
   }
   {\lst x_1 = \lst x_2 \matches \bigwedge_i e_i = f_i
    \withbind
      (\mapof{
         \lst x_1 \to \seqof{e_1,\ldots,e_n}
       , \lst x_2 \to \seqof{f_1,\ldots,f_n}
       },\theta,\theta)
   }
  \quad
  \LNAME{LstAnd}
$$

The default is simple structural matching:
$$
  \inferrule
   {e_1 \matches f_1 \withbind \omega_1
    \qquad
    e_2 \matches f_2 \withbind \omega_2
   }
   {e_1=e_2 \matches f_1=f_2 \withbind \Mresolve(\omega_1 \Mmerge \omega_2)}
  \quad
  \LNAME{Eq}
$$

\subsubsection{Quantification Matching}

Quantification requires compatible bodies, and leaves quantifier
variables unresolved in the first instance.
$$
  \inferrule
   {\nu \Mmatchable \rho
    \qquad
    (e,B\cup\nu) \matches (f,C\cup\rho) \withbind \omega
    \qquad
    \omega \Mcong  (\theta,\nu \to \setof\rho,\theta)
   }
   {(\forall \nu @ e,B) \matches (\forall \rho @ f,C)
    \withbind
     \Mresolve\left(\omega \Mmerge (\theta,\nu \to \setof\rho,\theta)\right)
    }
  \quad
  \LNAME{ForAll}
$$

\newpage
\subsection{Code Scratchpad}

All the ways $c$ (std) \texttt{p}s can match $d$ (std) \texttt{t}s, when $d \geq c$.
\begin{code}
allStdAssignments :: Eq t => [p] -> [t] -> [([(p,t)],[t])]
allStdAssignments [] ts  = [([],ts)]
allStdAssignments _ [] = error "allStdAssignments: not enough targets!"
allStdAssignments (p:ps) ts  = concat $ map (thisStdAssignments ps p ts) ts
-- result length : d!/(d-c)!,  c=length ps, d=length ts,  d >= c

thisStdAssignments :: Eq t => [p] -> p -> [t] -> t -> [([(p,t)],[t])]
thisStdAssignments ps p ts t
 = let ts' = ts\\[t]
       res' = allStdAssignments ps ts'
   in map (addStdAssignment p t) res'

addStdAssignment :: Eq t => p -> t -> ([(p,t)],[t]) -> ([(p,t)],[t])
addStdAssignment p t (pts,ts) = ((p,t):pts,ts)
\end{code}

All the ways $f$ (list) \texttt{p}s can match zero or more of $g$ (arbitrary) \texttt{t}s.
\begin{code}
allListAssignments :: Eq t => [p] -> [t] -> [[(p,[t])]]
allListAssignments [] []  =  [[]]
allListAssignments [] _   =  []  -- discard if ts leftover
allListAssignments [p] ts = [[(p,ts)]] -- hoover up what's left
allListAssignments (p:ps) ts
               = concat $ map (thisListsAssignments p ps ts) $ subsequences ts
--- result length :  (length ps)^(length ts)  !

thisListsAssignments :: Eq t => p -> [p] -> [t] -> [t] -> [[(p,[t])]]
thisListsAssignments p ps ts sts
 = let ts' = ts \\ sts
       rest' = allListAssignments ps ts'
   in map (addListAssignment p sts) rest'

addListAssignment :: p -> [t] -> [(p,[t])] -> [(p,[t])]
addListAssignment p sts ptmap = (p,sts):ptmap
\end{code}
In effect, this code enumerates all total functions from elements of \texttt{ts}
to elements of \texttt{ps}.
