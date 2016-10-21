\section{Match Prototyping}

\begin{code}
module ProtoMatch where
import Tables
\end{code}

\begin{code}
data Var
 = Std String
 | Lst String
 | Rsv String [Var] -- no Rsv in var list !

newtype VarList = VL [Var]
\end{code}

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

type Substn = [(Var,Expr)]
\end{code}


\begin{code}
data AtmSC = In Var String | Out Var String

data SCond
 = SCfalse
 | SCand [AtmSC]
\end{code}

\begin{code}
data ThCtxt
 = ThCtxt
    { obs :: [Var]
    , known :: Trie Expr
    }
\end{code}

\begin{code}
data Binds
 = Bind
    { stdbind :: Trie Expr
    , lstbind :: Trie [Expr]
    }
\end{code}

\begin{code}
data DType = VSeq | VSet | VESet
data VEItem = VE { vOf :: Var
                 , eOf :: Expr
                 }
type DItem = ( [Var]     -- bound variables
             , [VEItem]  -- DSM or DLM
             )
data DCM
 = DCM { dtyp  :: DType
       , defpat :: DItem
       , deftst :: DItem
       }
data DefMtchs = DMS { unDMS :: [DCM] }
\end{code}


\begin{code}
data IMResult
 = IMR {  binds :: Binds
       ,  mtodo :: DefMtchs
       }
\end{code}


\begin{code}
data MCtxt
 = MCtxt
    { mObs :: [Var]
    , mKnown :: Trie Expr
    , tSC :: SCond
    , pSC :: SCond
    }
\end{code}

\begin{code}
type Match m = MCtxt     -- match context
               -> IMResult  --  result so far
               -> [Var]     -- test bound variables
               -> Expr      -- test expresssion
               -> [Var]     -- pattern bound variables
               -> Expr      -- pattern expression
               -> m (IMResult, IMResult)
\end{code}
