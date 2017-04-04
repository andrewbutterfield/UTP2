\section{DSL Information}

\begin{code}
module DSL where
import Utilities
import Tables
import Datatypes
import Precedences
import DataText

import Data.Char
import Text.ParserCombinators.Parsec.Expr
\end{code}

This module defines a DSL in Haskell
to make it easy to write built-in theories.

\subsection{Common Types}

\begin{code}
n_Tprod = "prod"
mkTprod ts = TApp n_Tprod ts

n_Tset = "set"
mkTset t = TApp n_Tset [t]

n_Tseq = "seq"
mkTseq t = TApp n_Tseq [t]

n_Tseqp = "seqp"
mkTseqp t = TApp n_Tseqp [t]
\end{code}

\subsection{Making Laws}
\begin{code}
mkAssertion :: SideCond -> Pred -> Assertion
mkAssertion sc pr = (pr,sc)
mkAsnSCtrue = mkAssertion SCtrue

addSCtrue (nm,pr) = (nm,(mkAsnSCtrue pr))

mkLaw :: Provenance -> Assertion -> Law
mkLaw prov ass = (ass,prov,Bnil)

mkDSLSOURCE src = mkLaw (FromSOURCE src)
dslSource = "DSL"
mkDSLLaw = mkDSLSOURCE dslSource
mkDSLSubLaw sub = mkDSLSOURCE (dslSource++':':sub)

addSOURCE  :: String -> (String,Assertion) -> (String,Law)
addSOURCE src  (nm,ass) = (nm,(mkDSLSOURCE src ass))

-- support for lifting tables from Assertion to Law
wrapProv :: Provenance -> (String,Assertion) -> (String,Law)
wrapProv prov (name,ass) = (name,(ass,prov,Bnil))
\end{code}

\subsection{Precedence Lookup}
\begin{code}
precLkp precs op
 = case alookup precs op of
    Nothing       ->  (-1)
    (Just (p,_))  ->  p
\end{code}

\newpage
\subsection{DSL: Names}


Often we want an name, variable, qvar-list and expression called ``x'' (say),
so it is worth giving a  declaration building function for this usage
\begin{code}
declNVQE :: (String -> Variable) -> String -> (String,Variable,QVars,Expr)
declNVQE mkv s = (s,v,q,e) where { v = mkv s; q =  [v]; e = Var v }

declPreNVQE,declPostNVQE,declLstNVQE,declLst'NVQE
 :: String -> (String,Variable,QVars,Expr)
declPreNVQE  = declNVQE preVar
declPostNVQE = declNVQE postVar
declLstNVQE  = declNVQE lstVar
declLst'NVQE = declNVQE lstVar'
\end{code}
The intended use is something like \texttt{(x,vx,qx,ex) = declPreNVQE "x"}.

Some useful names for things.
We used to put underscores at the start of predicate variable-names
to avoid clashes with single-character predicate names given special
meaning in theories (e.g. the $B$ predicate of the Reactive theory).
Now, we use names like $Bee$ and $Jay$ for those special predicates.
\begin{code}
nA = "A"
nB = "B"
nC = "C"
nD = "D"
nP = "P"
nQ = "Q"
nR = "R"
nS = "S"

pA = PVar $ genRootAsVar $ Std nA
pB = PVar $ genRootAsVar $ Std nB
pC = PVar $ genRootAsVar $ Std nC
pD = PVar $ genRootAsVar $ Std nD
pP = PVar $ genRootAsVar $ Std nP
pQ = PVar $ genRootAsVar $ Std nQ
pR = PVar $ genRootAsVar $ Std nR
pS = PVar $ genRootAsVar $ Std nS

x = "x"
y = "y"
z = "z"

mkEvar nm = Var $ preVar ("E_"++nm) -- REVIEW
isEvar ('E':'_':_) = True
isEvar _= False
getEvar ('E':'_':nm) = nm
getEvar e = error ("'"++e++"' is not an Evar!")

mkEVar  = mkEvar . showVar
isEVar = isEvar . showVar
getEVar = getEvar . showVar


evx = mkEvar x
evy = mkEvar y
evz = mkEvar z

n_e = "e"
e_xs = qvarr "es"
e = mkEvar n_e
\end{code}

We introduce some quantifier meta-variables:
\begin{code}
nx = varKey vx ; vx = preVar "x" ; vx' = postVar "x";  qx = qvar nx; eqx = Var $ preVar nx
nxs = varKey vxs ; vxs = lstVar "x" ; qxs =  [vxs]
qxxs =  [vx,vxs]

ny = varKey vy ; vy = preVar "y" ; vy' = postVar "y"; qy = qvar ny; eqy = Var $ preVar ny
nys = varKey vys ; vys = lstVar "y" ; qys =  [vys]
qyys =  [vy,vys]

nz = "z"; vz = preVar nz; vz' = postVar nz; qz = qvar nz; eqz = Var $ preVar nz

qxsys = mkQ [vxs,vys]

nEs = "Es" ; qEs = qvarr nEs
nFs = "Fs" ; qFs = qvarr nFs
qEsFs = qvarrs [nEs,nFs]

vP = preVar nP; qP =  [vP]
nPs = varKey vPs; vPs = lstVar "P" ; qPs =  [vPs]
nQs = varKey vQs; vQs = lstVar "Q" ; qQs =  [vQs]
qPPs =  [vP,vPs]

qPsQs = mkQ [vPs,vQs]
\end{code}

\subsection{Predicate meta-Variable Lookup}
Lookup taking a \texttt{PVar}:
\begin{code}
pVarLookup table (PVar r) = tlookup table $ show r
pVarLookup _      _         = Nothing
\end{code}


\subsection{DSL: Predicates}

\begin{code}
infixl 4 ===
p === q = mkEqv p q

n_Imp = "Imp"
mkImp p q  = PApp n_Imp [p,q]
infixr 5 ==>
p ==> q = mkImp p q

infixl 6 \/
p \/ q = mkOr [p,q]

infixl 7 /\
p /\ q = mkAnd [p,q]

n_If = "If"
mkIf c p q =  PApp n_If [c,p,q]
infixl 8 <|
p <| c = (p,c)
infixl 8 |>
(p,c) |> q = mkIf c p q

infixl 9 >>>
p >>> q = PApp compName [p, q]

n_RfdBy = "RfdBy"
mkRfdBy c s = PApp n_RfdBy [c,s]
infixl 4 |=
s |= c = mkRfdBy c s

infixl 4 =|
c =| s  =  PApp "=|" [c, s]


precsLogic
 = lbuild
     [ mk equivName   AssocLeft
     , mk impName     AssocRight
     , mk orName      AssocLeft
     , mk andName     AssocLeft
     -- , mk ndcName     AssocLeft
     -- , mk rbyName     AssocNone
     , mk psunionName AssocLeft
     , mk psinName    AssocNone
     ]
 where mk nm assoc = (nm,(opPrec 1 nm,assoc))

tBoolOp = Tfun B B
tBoolBinOp = Tfun (mkTprod [B,B]) B
t = Tvar "t"
t2 = mkTprod [t,t]
\end{code}

We give types to the binary predicate operators,
as this information is useful for parsing, etc.
\begin{code}
boolOpTypes :: Trie Type
boolOpTypes = lbuild
                [(andName,tBoolBinOp)
                ,(orName,tBoolBinOp)
                -- ,(ndcName,tBoolBinOp)
                ,(impName,tBoolBinOp)
                -- ,(rbyName,tBoolBinOp)
                ,(equivName,tBoolBinOp)
                ,(notName,tBoolOp)
                ,(equalName,Tfun t2 B)
                ,(neqName,Tfun t2 B)
                ]
\end{code}

Legacy code from when quantifiers had explicit ranges.
\begin{code}
mkAll  = mkForall
mkAny  = mkExists
mkAny1  = mkExists1
\end{code}

New code because ranges have gone
\begin{code}
rForall q r p   =  mkForall q (r ==> p)
rExists q r p   =  mkExists q (r /\ p)
rExists1 q r p  =  mkExists1 q (r /\ p)
\end{code}


\begin{code}
x_NotFreeIn_e = vx `notEfree` n_e

xNFinA = SCnotFreeIn PredM [vx] nA

nN = "N"
pN = PVar $ genRootAsVar $ Std nN
xNFinN = SCnotFreeIn PredM [vx] nN
xsNFinN = SCnotFreeIn PredM [vxs] nN

qyxs = qvarsr ["y"] "xs"
yNFinA = SCnotFreeIn PredM [vy] nA
xyNFinA = SCnotFreeIn PredM [vx,vy] nA
\end{code}

\begin{code}
bN = "b"
bv = qvar bN
bvxs = qvarsr ["b"] "xs"
bp = PExpr (Var $ preVar "b")
nbp = mkNot bp
subb p t = Sub p $ Substn [(preVar bN,t)]
\end{code}

Supporting induction:
\begin{code}
indSub e x = Substn [(x,e)]
\end{code}

\subsubsection{DSL: Predicate Abstraction/Application}

\subsubsection{Expression Variables}

\begin{code}
n_PEAbs = "PEAbs"
peAbs qvs bodyp  =  PAbs n_PEAbs 0 qvs [bodyp]

n_PEApp = "PEApp"
peApp pfun parg = PApp n_PEApp [pfun, parg]
\end{code}

\subsubsection{Predicate Variables}

\begin{code}
n_PVAbs = "PVAbs"
pvAbs pvs bodyp  =  PAbs n_PVAbs 0 pvs [bodyp]

n_PVApp = "PVApp"
pvApp pfun parg = PApp n_PVApp [pfun, parg]
\end{code}

\subsection{DSL: generic expressions}

\begin{code}
n_e1 = "e1"
e1_xs = qvarr "xs"
n_e2 = "e2"
e2_ys = qvarr "ys"
n_e3 = "e3"
e3_zs = qvarr "zs"

e1 = mkEvar n_e1
e2 = mkEvar n_e2
e3 = mkEvar n_e3

mkBin nm i e1 e2 = App ('_':nm++'_':show i) [e1,e2]

isBin ('_':rest)
 = let (nm,_i) = break (=='_') rest
   in case _i of
     ('_':i) | not (null i) && all isDigit i  ->  True
     _ -> False
isBin _ = False

-- valid only if isBin is True
getBin :: String -> (String,Int)
getBin (_:rest)
 = let (nm,_i) = break (=='_') rest
   in  (nm,read $ tail _i)
\end{code}


\subsection{DSL: Equality}

\begin{code}
precsEquality
 = lbuild
     [ (equalName, (opPrec 1 equalName,AssocNone))
     , (neqName,(opPrec 1 neqName,AssocNone))
     ]

eq m n  = mkEqual m n
ne m n  = mkBin neqName (precOf precsEquality neqName) m n

infix 5 `equal`
infix 5 `neq`

e1 `equal` e2 = PExpr (e1 `eq` e2)
e1 `neq` e2   = PExpr (e1 `ne` e2)
\end{code}

A function to build definedness predicates:
\begin{code}
n_Defd = "Defd"
mkDefd e = PApp n_Defd [PExpr e]

domOfDefn nm app dod = ("DOD-"++nm , (mkDefd app) === dod )
\end{code}

Definite description:
\begin{code}
n_The = "The"
mkThe x pr = Abs n_The 0 [x] [EPred pr]
\end{code}


\subsection{DSL: Arithmetic}

\begin{code}
precsArithmetic1 :: [(String,(Int,Assoc))]
precsArithmetic1
 = [("+",(250,AssocLeft))
   ,("-",(250,AssocLeft))
   ,("*",(260,AssocLeft))
   ,("/",(260,AssocLeft))
   ,("div",(260,AssocLeft))
   ,("mod",(260,AssocLeft))
   ]

nn = mkEvar "n"
mn = mkEvar "m"

infixl 6 `plus`
infixl 6 `minus`
infixl 7 `mul`
infixl 7 `divd`
infixl 7 `divdiv`
infixl 7 `modulo`

neg m       = App "neg" [m]
plus m n    = mkBin "+"   (precLkp precsArithmetic1 "+") m n
minus m n   = mkBin "-"   (precLkp precsArithmetic1 "-") m n
mul m n     = mkBin "*"   (precLkp precsArithmetic1 "*") m n
divd m n    = mkBin "/"   (precLkp precsArithmetic1 "/") m n
divdiv m n  = mkBin "div" (precLkp precsArithmetic1 "div") m n
modulo m n  = mkBin "mod" (precLkp precsArithmetic1 "mod") m n

tNum2 = mkTprod [Z,Z]
tArithBinOp = Tfun tNum2 Z

zero = Num 0
one = Num 1

precsArithmetic2  :: [(String,(Int,Assoc))]
precsArithmetic2
 = [("<",(240,AssocNone))
   ,("<=",(240,AssocNone))
   ,(">",(240,AssocNone))
   ,(">=",(240,AssocNone))
   ]

infix 5 `lt`
infix 5 `le`
infix 5 `gt`
infix 5 `ge`

lt m n  = mkBin "<"  (precLkp precsArithmetic2 "<") m n
le m n  = mkBin "<=" (precLkp precsArithmetic2 "<=") m n
gt m n  = mkBin ">"  (precLkp precsArithmetic2 ">") m n
ge m n  = mkBin ">=" (precLkp precsArithmetic2 ">=") m n

tArithRel = Tfun tNum2 B

infix 5 `equalZ`
infix 5 `neqZ`
m `equalZ` n = PExpr (mkEqual m n)
m `neqZ` n   = mkNot (m `equalZ` n)

lthan m n  =  PExpr (lt m n)
leq m n    =  PExpr (le m n)
gthan m n  =  PExpr (gt m n)
geq m n    =  PExpr (ge m n)
\end{code}


\subsection{DSL: Set}

\begin{code}
n_s1 = "s1"
n_s2 = "s2"
n_s3 = "s3"

s1 = mkEvar n_s1
s2 = mkEvar n_s2
s3 = mkEvar n_s3

precsSet  :: [(String,(Int,Assoc))]
precsSet
 = [ ("in",(280,AssocNone))
   , ("intsct",(270,AssocLeft))
   , ("union",(260,AssocLeft))
   , ("\\",(260,AssocLeft))
   , ("subset", (250,AssocNone))
   , ("subseteq", (250,AssocNone))
   ]

tSet = mkTset t
tSet2 = mkTprod [tSet,tSet]
tSetBinOp = Tfun tSet2 tSet
tSetRel = Tfun tSet2 B
tMmbr = mkTprod [t,tSet]

n_set = "set"
mkSet = App n_set

infix 8 `mof`
infixl 6 `unn`
infixl 7 `intsct`

mof e s      = mkBin "in"       (precLkp precsSet "in") e s
subset s t   = mkBin "subset"   (precLkp precsSet "subset") s t
subsetEq s t = mkBin "subseteq" (precLkp precsSet "subseteq") s t
unn s t      = mkBin "union"    (precLkp precsSet "union") s t
intsct s t   = mkBin "intsct"   (precLkp precsSet "intsct") s t
sdiff s t    = mkBin "\\"       (precLkp precsSet "\\") s t
card s       = App "card"     [s]
empty        = mkSet []

infix 5 `equalS`
infix 5 `neqS`

e1 `equalS` e2 = PExpr (mkEqual e1 e2)
e1 `neqS` e2   = mkNot (e1 `equalS` e2)

pmof e s = PExpr (e `mof` s)
psubset s t = PExpr (s `subset` t)
psubseteq s t = PExpr (s `subsetEq` t)
\end{code}

\subsection{DSL: Lists}

\begin{code}
precsList :: [(String,(Int,Assoc))]
precsList
 = [ (":",(260,AssocRight))
   , ("++",(250,AssocRight))
   , ("<<",(240,AssocNone))
   , ("<<=",(240,AssocNone))
   , ("--",(250,AssocLeft))
   ]

n_l1 = "l1"
n_l2 = "l2"
n_l3 = "l3"

l1 = mkEvar n_l1
l2 = mkEvar n_l2
l3 = mkEvar n_l3

n_ell = "ell"
vell = Var $ preVar n_ell
qell = qvar n_ell

tSeq = mkTseq t
tSeqp = mkTseqp t
tSeq2 = mkTprod [tSeq,tSeq]
tSeqBinOp  = Tfun tSeq2 tSeq
tSeqBinRel = Tfun tSeq2 B

n_seq = "seq" ; mkSeq = App n_seq
n_tuple = "tuple"
mkProd = App n_tuple

infixr 8 `cons`

cons e s = mkBin ":"     (precLkp precsList ":") e s
lnull s  = App "null"  [s]
hd s     = App "hd"    [s]
tl s     = App "tl"    [s]
sngll e  = mkSeq [e]
frnt s   = App "frnt"  [s]
lst s    = App "lst"   [s]
len s    = App "len"   [s]
cat s t  = mkBin "++"    (precLkp precsList "++") s t
pfx s t  = mkBin "<<="   (precLkp precsList "<<=") s t
spfx s t = mkBin "<<"    (precLkp precsList "<<") s t
ssub s t = mkBin "--"    (precLkp precsList "--") s t
ix s i   = App "ix" [s,i]
elems s  = App "elems" [s]
nil      = mkSeq []

e1 `equalL` e2 = PExpr (mkEqual e1 e2)
e1 `neqL` e2   = mkNot (e1 `equalL` e2)

plnull s = PExpr (lnull s)
ppfx s t  = PExpr (s `pfx` t)
pspfx s t = PExpr (s `spfx` t)

ss = mkEvar "s"
tt = mkEvar "t"
uu = mkEvar "u"
ii = mkEvar "i"
\end{code}

\subsection{DSL: UTP Theories}

\subsubsection{Observation Variables}


We need to associate a list of observational variables
with the \texttt{PVar}s here, which will always include $ok$ and $wait$,
so we use a special name: "\_OBS" to cover the rest.

We use Haskell classes to allow us to use one identifier
to refer to the various ways in which an observation
variable name can be used
\begin{code}
class Ok t           where   ok,              ok'                         :: t
instance Ok String   where { ok = "ok" ;      ok' = "ok'" }
instance Ok Variable where { ok = preVar ok ; ok' = postVar ok }
instance Ok Expr     where { ok = Var ok ;    ok' = Var ok' }
instance Ok Pred     where { ok = PExpr ok ;    ok' = PExpr ok' }

class Wait t           where   wait,                wait'                 :: t
instance Wait String   where { wait = "wait" ;      wait' = "wait'" }
instance Wait Variable where { wait = preVar wait ; wait' = postVar wait }
instance Wait Expr     where { wait = Var wait ;    wait' = Var wait' }
instance Wait Pred     where { wait = PExpr wait ;    wait' = PExpr wait' }
\end{code}

\subsection{Observational Variables}

We define here the observational variables peculiar to R.
\begin{code}
class State t           where   state,                 state'             :: t
instance State String   where { state = "state" ;      state' = "state'" }
instance State Variable where { state = preVar state ; state' = postVar state }
instance State Expr     where { state = Var state ;    state' = Var state' }

class Tr t           where   tr,              tr'                         :: t
instance Tr String   where { tr = "tr" ;      tr' = "tr'" }
instance Tr Variable where { tr = preVar tr ; tr' = postVar tr }
instance Tr Expr     where { tr = Var tr ;    tr' = Var tr' }

class Ref t           where   ref,               ref'                     :: t
instance Ref String   where { ref = "ref" ;      ref' = "ref'" }
instance Ref Variable where { ref = preVar ref ; ref' = postVar ref }
instance Ref Expr     where { ref = Var ref ;    ref' = Var ref' }

tEvent = Tvar "Event"
tTrace = mkTseq tEvent
tTrace2 = mkTprod[tTrace,tTrace]
tRef   = mkTset tEvent
\end{code}

\subsection{DSL: Types}

\begin{code}
precsType
 = [ ("x",(10 :: Int,AssocLeft))
   , ("->",(10,AssocRight))
   , ("-~>",(10,AssocRight))
   , ("-+>",(10,AssocRight))
   ]
\end{code}

\subsection{DSL Bits and Pieces}

Here are some incarnations of old Pred/Expr constructs now gone,
but still used, in particular  by the document text parser.
\begin{code}
n_Cond = "Cond"
mkCond p e1 e2 = App n_Cond [ePred p,e1,e2]

n_Papp = "Papp"
mkPapp pf pa = PApp n_Papp [pf, pa]

n_NDC = "NDC"
mkNDC p1 p2 = PApp n_NDC [p1,p2]
\end{code}

\subsubsection{PVar table building}

Building tables from \texttt{PVar}-value lists:
\begin{code}
plupdate :: Trie t -> [(Pred, t)] -> Trie t
plupdate = foldr mkpentry
mkpentry (PVar pv,t) trie = tupdate (varKey pv) t trie
mkpentry _          trie = trie
\end{code}
