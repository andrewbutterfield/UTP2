\section{Unification Experimental Code}

\begin{code}
module Unify where
import Data.List
import Data.Either
\end{code}

\subsection{Specification}

\input{doc/Types-Unification}

\newpage
\subsection{Implementation}

\subsubsection{Types}

Terms:
\begin{code}
type Var = String
type Fun = String
data Term = V Var | A Fun [Term] deriving (Eq,Ord)

instance Show Term where
  show (V x)     =  x
  show (A f ts)  =  f ++ "("
                      ++ (concat $ intersperse "," $ map show ts)
                      ++ ")"
                      
instance Read Term where readsPrec _ = readTerm
  
readTerm str
 = case lex str of
    [(tok,rest)]  ->  readVar tok rest
    other         ->  []
    
-- seen var token
readVar tok str
 = case lex str of
    [("(",rest)]    ->  readFun tok rest
    [(thing,rest)]  ->  [(V tok, thing++rest)]
    _               ->  []
    
-- seen fun (      expecting term or )
     
readFun fun str
 = case lex str of
    [(")",rest)]  ->  [(A fun [],rest)]
    _             ->  readArg fun [] str
    
-- seen fun ( t1 , .. , ti ,     expecting term
readArg fun ts str 
 = case readTerm str of
    [(t,rest)]  ->  readNext fun (t:ts) rest
    _           ->  []
    
-- seen fun ( t1 , .. , ti , ti+1        expecting , or )
readNext fun ts str
 = case lex str of
    [(")",rest)]  ->  [(A fun $ reverse ts,rest)]
    [(",",rest)]  ->  readArg fun ts rest
    _             ->  []
\end{code}

Equations:
\begin{code}
newtype Eqn = E (Term, Term) deriving (Eq,Ord)

instance Show Eqn where
  show (E (t1,t2)) = show t1 ++ " = " ++ show t2
  
instance Read Eqn where readsPrec _ = readEqn

readEqn str
 = case readTerm str of
    [(t1,rest)]  ->  readEq t1 rest
    _            ->  []
    
readEq t1 str
 = case lex str of
    [("=",rest)]  ->  readT2 t1 rest
    _             ->  []
    
readT2 t1 str
 = case readTerm str of
    [(t2,rest)]  ->  [(E (t1,t2),rest)]
    _            ->  []

newtype Eqns = M [Eqn] deriving (Eq,Ord)

instance Show Eqns where
  show (M eqns) = unlines $ map show eqns
  
instance Read Eqns where readsPrec _ = readEqns

readEqns str = reqnsTidy [] $ map readEqn $ lines str

reqnsTidy eqns []  =  [(M $ reverse eqns,"")]
reqnsTidy eqns (res:rest)
 = reqnsTidy (tidy res:eqns) rest
 where
   tidy [(t,"")]  = t
   tidy _         = E (V "PARSE",V "ERROR")
\end{code}

\subsubsection{Variable Sets}

\begin{code}
tvars :: Term -> [Var]
tvars (V x) = [x]
tvars (A _ ts) = tsvars ts

tsvars :: [Term] -> [Var]
tsvars ts = nub $ sort $ concat $ map tvars ts

evars :: Eqn -> [Var]
evars (E (t1,t2)) = nub $ sort $ (tvars t1 ++ tvars t2)

esvars :: [Eqn] -> [Var]
esvars eqns = nub $ sort $ concat $ map evars eqns

mvars :: Eqns -> [Var]
mvars (M eqns) = esvars eqns
\end{code}



\subsubsection{Failure}

Unification fails if either
$$
 f(s_1,\ldots,s_j)=g(t_1,\ldots,t_k) \land (j\neq k \lor f \neq g)
$$
or
$$
 x = f(s_1,\ldots,s_j) \land x \in Vars(f(s_1,\ldots,s_j))
$$
\begin{code}
bad :: Eqn -> Bool
bad (E (A f ss, A g ts))   =  f /= g || length ss /= length ts
bad (E (V x, A f ss))  =  x `elem` tsvars ss
bad (E (A f ss, V x))  =  x `elem` tsvars ss
bad _ = False
\end{code}

An equation is trivial if of the form $t=t$:
\begin{code}
triv :: Eqn -> Bool
triv (E (t1, t2))  =  t1 == t2
\end{code}

\subsubsection{Pre-processing}

We scan a set of equations removing all trivial
entries, and flagging failure if we find any bad entries,
by returning the first one found
\begin{code}
instance Monad (Either Eqn)  where
  return x = Right x
  m >>= f
   = case m of
       Left e   ->  Left e
       Right x  ->  f x

pre :: Eqns -> Either Eqn Eqns
pre (M eqns)
 = do eqns' <- chk eqns
      return $ M eqns'

chk :: [Eqn] -> Either Eqn [Eqn]
chk [] =  return []
chk (e:es)
 | triv e  =  chk es
 | bad  e  =  Left e
 | otherwise  =  do es' <- chk es
                    return $ e:es'
\end{code}
The idea is that the algorithm always checks
new equations and fails if any are bad and discards any that are trivial.


\subsubsection{Substitution}

\begin{code}
tsub :: Term -> Var -> Term -> Term
tsub trepl x target@(V y)
 | x == y     =  trepl
 | otherwise  =  target
tsub trepl x (A f ts)
 = A f $ map (tsub trepl x) ts

esub :: Term -> Var -> Eqn -> Either Eqn Eqn
esub trepl x (E (t1, t2))
 | bad e'  =  Left e'
 | otherwise  =  Right e'
 where e' = E (tsub trepl x t1, tsub trepl x t2)

essub :: Term -> Var -> [Eqn] -> Either Eqn [Eqn]
essub trepl x eqns
 = do eqns' <- sequence $ map (esub trepl x) eqns
      return $ filter (not . triv) eqns'

msub :: Term -> Var -> Eqns -> Either Eqn Eqns
msub trepl x (M eqns)
 = do eqns' <- essub trepl x eqns
      return $ M eqns'
\end{code}



\subsubsection{Unification (pre-processed)}

\begin{code}
unfy :: [Eqn] -> Either Eqn [Eqn]
unfy eqns  -- no bad or trivial equations present
 = do (changed,eqns') <- uscan False [] eqns
      if changed
       then unfy eqns'
       else return eqns'
\end{code}

Now, we need to keep explicit before and after lists as we scan!
\begin{code}
uscan :: Bool -> [Eqn]-> [Eqn] -> Either Eqn (Bool, [Eqn])
uscan changed seen [] = return (changed,seen)
uscan changed seen (E (t1, t2):todo)
 = do (chgd,seen',todo') <- ueqn seen todo t1 t2
      uscan (changed || chgd) seen' todo'
\end{code}

We have equation $t_1 = t_2$ split into its two terms:
\begin{code}
ueqn :: [Eqn]-> [Eqn] -> Term -> Term
     -> Either Eqn (Bool, [Eqn], [Eqn])
\end{code}

We now consider each clause in the algorithm (-ic specification):
\begin{itemize}
\item
$unify(M\cup\setof{t=t}) ~~\defs~~ unify(M)$
\\does not arise because we remove all trivial (i.e. reflexive)
equations at the start, and in passing.
\item
$unify(M\cup \setof{f(s_1,\ldots,s_k)=f(t_1,\ldots,t_k)} )
~~\defs~~ unify(M\cup\setof{s_1=t_1,\ldots,s_k=t_k})$
\begin{code}
ueqn seen todo (A f ss) (A g ts)
 -- we don't need to check f==g && length ss==length ts
 = do let neweqns = map E $ zip ss ts
      chkdnew <- chk neweqns
      return (True, seen, chkdnew++todo)
\end{code}
\item
$ unify(M\cup \setof{f(s_1,\ldots,s_j)=g(t_1,\ldots,t_k)} )
~~\defs~~ \bot,
   \quad f \neq g \lor j \neq k$
   \\does not arise because we fail if we find a bad equation
   at the start, and if we ever generate one (using \texttt{chk}).
\item
$ unify(M\cup \setof{f(s_1,\ldots,s_k)=x} )
~~\defs~~ unify(M\cup\setof{x=f(s_1,\ldots,s_k)})$
\begin{code}
ueqn seen todo t1@(A f ss) t2@(V x)
 = return (True, seen, E (t2,t1):todo)
\end{code}
and should immediately segue into the following case.
\item
$ unify(M\cup \setof{x=t} )
~~\defs~~ unify(M[t/x] \cup \setof{x=t}),
   \quad x \in Vars(M) \land x \notin Vars(t)$
\begin{code}
ueqn seen todo t1@(V x) t2
 | x `elem` (esvars seen ++ esvars todo) -- if false, no change
 -- no need to check x notin tvars t2
 = do seen' <- essub t2 x seen
      todo' <- essub t2 x todo
      -- no need to run chk, done on fly by essub
      return (True, E (t1,t2):seen', todo')
\end{code}
\item
$ unify(M\cup \setof{x=f(t_1,\ldots,t_k)} )
~~\defs~~ \bot,
   \quad x \in Vars(f(t_1,\ldots,t_k))$
   \\does not arise because we fail if we find a bad equation
   at the start, and if we ever generate one.
\end{itemize}
In all other cases we pass over the equation with no
change, moving it to \texttt{seen} (from \texttt{todo}).
\begin{code}
ueqn seen todo t1 t2 = return (False, E (t1, t2):seen, todo)
\end{code}


\subsubsection{Unification (top-level)}

\begin{code}
unify :: Eqns -> Either Eqn Eqns
unify m = case pre m of
           Left e          ->  Left e
           Right (M eqns)  ->  do eqns' <- unfy eqns
                                  return $ M eqns'
\end{code}

\begin{code}
funify fin fout
 = do eqns <- fmap read $ readFile fin
      case unify eqns of
        Left e  ->  writeFile fout 
                       ("Cannot unify-\n" ++ show eqns
                         ++ "\nBecause:" ++ show e)
        Right eqns'  ->  writeFile fout 
                            (show eqns ++ " has solution \n" ++ show eqns')
\end{code}


