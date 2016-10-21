\section{Type Matching}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
module MatchingType where
import Datatypes
\end{code}

\input{doc/Matching-Types}

\newpage

\texttt{Type} Matching
\begin{code}
tMatch :: Monad m => Type -> Type -> m [(String,Type)]

tMatch (Terror tmsg tt) (Terror pmsg pt)
 | tmsg==pmsg  =  return []
 | otherwise   =  (fail "Nothing")
tMatch (Terror msg _) pt = (fail "Nothing")

tMatch tt Tarb = return []
tMatch tt (Tvar v) = return [(v,tt)]
tMatch (Tset tt) (Tset pt) = tMatch tt pt
tMatch (Tseq tt) (Tseq pt) = tMatch tt pt
tMatch (Tseqp tt) (Tseqp pt) = tMatch tt pt
tMatch (Tprod tts) (Tprod pts) = tMatchs tts pts
tMatch (Tfree tfn tvs) (Tfree pfn pvs)
 | tfn==pfn   =  tMatchVs tvs pvs
 | otherwise  =  (fail "Nothing")
tMatch (Tfun tta ttr) (Tfun pta ptr) = tMatchs [tta,ttr] [pta,ptr]
tMatch (Tpfun tta ttr) (Tpfun pta ptr) = tMatchs [tta,ttr] [pta,ptr]
tMatch (Tmap tta ttr) (Tmap pta ptr) = tMatchs [tta,ttr] [pta,ptr]
tMatch Tenv Tenv = return []
tMatch Z Z = return []
tMatch B B = return []
tMatch _ _ = (fail "Nothing")
\end{code}

Matching lists of \texttt{Type}s
\begin{code}
tMatchs :: Monad m => [Type] -> [Type] -> m [(String,Type)]

tMatchs tts pts = tMS [] tts pts
 where
   tMS tbnds [] [] = return tbnds
   tMS tbnds (tt:tts) (pt:pts)
    = do tbnd <- tMatch tt pt
         tMS (tbnd++tbnds) tts pts
   tMS _ _ _ = (fail "Nothing")
\end{code}

Matching lists of free \texttt{Type} variants
\begin{code}
tMatchVs :: Monad m
         => [(String,[Type])] -> [(String,[Type])] -> m [(String,Type)]

tMatchVs tvs pvs = tMVS [] tvs pvs
 where
  tMVS tbnds [] [] = return tbnds
  tMVS tbnds ((tvn,tts):tvs) ((pvn,pts):pvs)
   | tvn==pvn   =  do tbnd <- tMatchs tts pts
                      tMVS (tbnd++tbnds) tvs pvs
   | otherwise  =  (fail "Nothing")
  tMVS _ _ _ = (fail "Nothing")
\end{code}
