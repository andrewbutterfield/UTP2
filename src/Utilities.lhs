\section{Utilities}

\begin{code}
{-# LANGUAGE CPP #-}
module Utilities where
import Data.Char
import Data.List hiding (stripPrefix)
import System.IO

-- GHC 7.10 future proofing
import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)
\end{code}

Debugging stuff:
\begin{code}
import System.IO.Unsafe
import Debug.Trace

dbgsh sh msg x = trace (msg++sh x) x

dbg msg x = dbgsh show msg x

cdbg p msg x
 | p x        =  dbg msg x
 | otherwise  =  x

class Dshow t where dshow :: t -> String
ddbg msg x = dbgsh dshow msg x

debug s e = unsafePerformIO $ mdebug s e
mdebug s e
  = do hPutStrLn stderr s
       return e
shdebug s e = debug (s++show e) e
\end{code}

Something to clear out GHCi to make it easier to find the top of a long list
of errors:
\begin{code}
clr = putStrLn $ unlines $ replicate 40 ""
\end{code}

\newpage
\subsection{Association Lists}

Association lists are simple lookup tables
were items are stored as key-data pairs in a simple list.
\begin{code}
type AList k d = [(k,d)]
\end{code}


\subsubsection{Lookup}

A generalisation of associative-list lookup
is where we have lists of a type that ``contains''
its own name, and we want to lookup on that name:
\begin{code}
clookup :: Eq k => (a -> k) -> (a -> b) -> [a] -> k -> Maybe b
clookup key datum [] _ = Nothing
clookup key datum (a:rest) k
 | key a == k   =  Just $ datum a
 | otherwise  =  clookup key datum rest k
\end{code}

We can build ``traditional'' association-list lookup this way.
\begin{code}
alookup :: Eq k => AList k d -> k -> Maybe d
alookup = clookup fst snd
-- alookup [] _ = Nothing
-- alookup ((ky,itm):rest) nm
--  | nm == ky   =  Just itm
--  | otherwise  =  alookup rest nm

aslookup :: Eq k => [AList k d] -> k -> Maybe d
aslookup [] _ = Nothing
aslookup (alist:alists) nm
 = case alookup alist nm of
    Nothing  ->  aslookup alists nm
    res      ->  res
\end{code}

A variant is using an association list with keys and data of
the same type to do a replacement:
\begin{code}
areplace :: Eq a => AList a a -> a -> a
areplace alist tgt
 = case alookup alist tgt of
     Nothing   ->  tgt
     Just rep  ->  rep
\end{code}

We want to lookup a list of keys in an assoc list,
and return what they are bound to, plus the remaining
keys:
\begin{code}
keysExtract :: Eq k => [k] -> AList k d -> ([d],[k])
keysExtract ks alist = ksE ks [] alist
 where
  ksE dks ds [] = (ds,ks \\ dks)
  ksE dks ds (a@(n,d):alist)
   | n `elem` ks  =  ksE (n:dks) (d:ds) alist
   | otherwise    =  ksE dks     ds     alist
\end{code}


\subsection{List normalisation}

A list is normalised when its elements
are sorted with no duplicates.
\begin{code}
lnorm :: (Eq t, Ord t) => [t] -> [t]
lnorm = map head . group . sort
\end{code}

A membership predicate can be easily built on normalised lists:
\begin{code}
x `elemn` [] = False
x `elemn` (y:ys)
 | x < y      =  False
 | x == y     =  True
 | otherwise  =  x `elemn` ys
\end{code}

A subset predicate can be easily built on normalised lists:
\begin{code}
[] `subsetOf` ys = True

xs@(x:xrest) `subsetOf` (y:yrest)
 | x < y      =  False
 | x == y     =  xrest `subsetOf` yrest
 | otherwise  =  xs `subsetOf` yrest

_ `subsetOf` _ = False
\end{code}

Sometimes we want to know if we had duplicates
(e.g. for error reporting)
\begin{code}
dupsOf xs = dups (sort xs)
 where
  dups [] = []
  dups (x:xs) = dups' [] x xs
  dups' ds c [] = ds
  dups' ds c (x:xs)
   | c == x     =  dups' (c:ds) c xs
   | otherwise  =  dups' ds x xs
\end{code}



\subsubsection{Normal insertion/merge}

\begin{code}
insnorm x [] = [x]
insnorm x us@(y:ur)
  | x < y      =  x:us
  | x == y     =  us
  | otherwise  =  y:(insnorm x ur)

mrgnorm us [] = us
mrgnorm [] vs = vs
mrgnorm us@(x:ur) vs@(y:vr)
 | x < y      =  x:(mrgnorm ur vs)
 | x > y      =  y:(mrgnorm us vr)
 | otherwise  =  y:(mrgnorm ur vr)
\end{code}

\subsection{Merging by sort}

\begin{code}
ltmerge order []                 laws2  = laws2
ltmerge order laws1              []     = laws1
ltmerge order laws1@(law1:rest1) laws2@(law2:rest2)
 = case (law1 `order` law2) of
     LT  ->  law1:(ltmerge order rest1 laws2)
     GT  ->  law2:(ltmerge order laws1 rest2)
     EQ  ->  law1:law2:(ltmerge order rest1 rest2)
\end{code}


\subsection{Association-List normalisation}

An association-list is normalised when its elements
are sorted by key with no duplicate keys.
If the keys are duplicated then which one gets chosen
is non-deterministic (the first occurrence if \texttt{sortBy} is stable).
\begin{code}
alnorm :: (Eq k, Ord k) => [(k,d)] -> [(k,d)]
alnorm = map head
         . groupBy (\a -> \b -> fst a == fst b)
         . sortBy (\a -> \b -> compare (fst a) (fst b))
\end{code}

We can also insert into a normalised association-list,
resolving with \texttt{res} if key already present:
\begin{code}
alinsnorm  _  k d [] = [(k,d)]
alinsnorm res k d kds@(kd'@(k',d'):kds')
 | k  < k'    =  (k,d):kds
 | k  > k'    =  kd':(alinsnorm res k d kds')
 | otherwise  =  (k,d `res` d'):kds'
\end{code}

Merging is also useful, with a resolution function:
\begin{code}
almrgnorm :: Ord k => (d -> d -> d) -> [(k,d)] -> [(k,d)] -> [(k,d)]
almrgnorm _ kds [] = kds
almrgnorm _ [] kds = kds
almrgnorm res kds1@(kd1@(k1,d1):rest1) kds2@(kd2@(k2,d2):rest2)
 | k1  < k2   =  kd1 : almrgnorm res rest1 kds2
 | k1  > k2   =  kd2 : almrgnorm res kds1 rest2
 | otherwise  =  (k1,d1 `res` d2) : almrgnorm res rest1 rest2

\end{code}

Override is a merge that favours the second list:
\begin{code}
aloverride :: Ord k => [(k,d)] -> [(k,d)] -> [(k,d)]
aloverride = almrgnorm (curry snd)
\end{code}

Glueing is a merge that fails if the lists are inconsistent:
\begin{code}
alglue :: (Ord k, Eq d) => [(k,d)] -> [(k,d)] -> Maybe [(k,d)]
alglue kds [] = Just kds
alglue [] kds = Just kds
alglue kds1@(kd1@(k1,d1):rest1) kds2@(kd2@(k2,d2):rest2)
 | k1  < k2   =  do restglued <- alglue rest1 kds2
                    return (kd1:restglued)
 | k1  > k2   =  do restglued <- alglue kds1 rest2
                    return (kd2:restglued)
 | d1 == d2   =  do restglued <- alglue rest1 rest2
                    return (kd1:restglued)
 | otherwise  =  Nothing
\end{code}

Also useful is restriction to/and removal of
an association-list's entries w.r.t. an normalised key list:
\begin{code}
alrem :: (Ord k) => [k] -> [(k,d)] -> [(k,d)]
alrem [] kds = kds
alrem _  []  = []
alrem ks@(k1:ks1) kds2@(kd2@(k2,d2):rest2)
 | k1  < k2   =  alrem ks1 kds2
 | k1 == k2   =  alrem ks1 rest2
 | otherwise  =  kd2:(alrem ks rest2)
\end{code}


\subsection{Looking up an ordered association list}

\begin{code}
alookupOrd :: (Eq k, Ord k) => [(k,d)] -> k -> Maybe d
alookupOrd [] k = Nothing
alookupOrd ((k',d'):rest) k
 | k' < k    =  alookupOrd rest k
 | k == k'    =  Just d'
 | otherwise  =  Nothing
\end{code}

A variant that splits the list if the item is found:
\begin{code}
alkpSplit :: (Eq k, Ord k) => [(k,d)] -> k -> (Maybe d,[(k,d)])
alkpSplit [] k = (Nothing,[])
alkpSplit kds@((k',d'):rest) k
 | k' < k    =  let (d'',rest') = alkpSplit rest k
                in (d'',(k',d'):rest')
 | k == k'    =  (Just d',rest)
 | otherwise  =  (Nothing, kds)
\end{code}


\subsection{Mapping over association lists}

\begin{code}
maparng :: (d -> e) -> [(k,d)] -> [(k,e)]
maparng f [] = []
maparng f ((k,d):rest) = (k,f d):(maparng f rest)

maparngf :: (d -> (e, Bool)) -> [(k,d)] -> [((k,e),Bool)]
maparngf f [] = []
maparngf f ((k,d):[]) = [((k,d'),dif)]
  where (d', dif) = f d
maparngf f ((k,d):rest) = ((k,d'),dif):(maparngf f rest)
  where (d', dif) = f d
\end{code}

\subsubsection{List equivalence}

We need to establish two lists are the same under a given equivalence:
\begin{code}
samelist :: (a->b->Bool) -> [a] -> [b] -> Bool
samelist eq []     []  =  True
samelist eq (x:xs) (y:ys)
 | x `eq` y   =  samelist eq xs ys
 | otherwise  =  False
samelist _  _      _   =  False
\end{code}

Similarly for the association lists:
\begin{code}
samealist :: (Eq k) => (a->b->Bool) -> [(k,a)] -> [(k,b)] -> Bool
samealist eq []     []  =  True
samealist eq ((m,x):xs) ((n,y):ys)
 | m==n && x `eq` y   =  samealist eq xs ys
 | otherwise          =  False
samealist _  _      _   =  False
\end{code}

\newpage
\subsection{List Cursors}

We want to be able to go to a position
in a list and then do something to the item at that location
(replace, delete, move up, move down).

We represent such a list cursor as two lists --- those before
the current position, reversed, and those from the current position
onwards.
\begin{code}
type Cursor t = ([t],[t])

cursor2list (erofeb,hereafter) = reverse erofeb ++ hereafter
invCursor (erofeb,[])  =  null erofeb
invCursor _            =  True

dispCursor _ (_,[])  =  "<<>>"
dispCursor sh (erofeb,(cp:after))
  =  showl erofeb ++ " <<" ++ sh cp ++ ">> " ++ showl after
  where
    showl xs = concat $ intersperse "," $ map sh xs
\end{code}

Setting the cursor (at start, at numeric position, by predicate).
\begin{code}
startCursor :: [t] -> Cursor t
startCursor xs = ([],xs)

setCursorPos :: Int -> [t] -> Maybe (Cursor t)
setCursorPos n xs = cp n [] xs
 where
    cp _ erofeb [x]          =  Just (erofeb,[x])
    cp 1 erofeb after@(x:_)  =  Just (erofeb,after)
    cp n erofeb (x:after)    =  cp (n-1) (x:erofeb) after
    cp _ erofeb after        =  Nothing

setCursor :: (t -> Bool) -> [t] -> Maybe (Cursor t)
setCursor p xs = setp [] xs
 where
    setp erofeb ha@(x:after)
      | p x  =  Just (erofeb,ha)
      | otherwise  =  setp (x:erofeb) after
    setp _ []  =  Nothing
\end{code}

Getting the current item:
\begin{code}
getCursor :: Cursor t -> Maybe t
getCursor (_,(x:_))  =  Just x
getCursor _          =  Nothing
\end{code}

In place replacement:
\begin{code}
replAtCursor :: (t -> t) -> Cursor t -> Cursor t
replAtCursor f (erofeb,x:after)  =  (erofeb,(f x):after)
replAtCursor f cur               =  cur
\end{code}

Moving an item left (subject to predicate approval):
\begin{code}
leftCursor :: (t -> Bool) -> Cursor t -> Cursor t
leftCursor p cur@(prev:erofeb,curr:after)
 | p prev  =  (erofeb,curr:prev:after)
leftCursor _ cur  =  cur
\end{code}

Moving an item right (subject to predicate approval):
\begin{code}
rightCursor :: (t -> Bool) -> Cursor t -> Cursor t
rightCursor p cur@(erofeb,curr:next:after)
 | p next  =  (next:erofeb,curr:after)
rightCursor _ cur  =  cur
\end{code}

We now define a variant that searches for an item in a list,
but where the list items have a wrapper around them.
We supply the item, an unwrap function, and the list
and get get back the list with the item removed if present,
or unaltered if not, along with item itself.
\begin{code}
extractWrapped :: Eq a => (w -> a) -> a -> [w] -> (Maybe w,[w])
extractWrapped unwrap n ws
 = extw [] n ws
 where
   extw sw _ [] = (Nothing,reverse sw)
   extw sw n (w:ws)
     | n == unwrap w  =  (Just w,revapp sw ws)
     | otherwise      =  extw (w:sw) n ws
   revapp [] ws = ws
   revapp (w:sw) ws = revapp sw (w:ws)
\end{code}


\newpage
\subsection{endo-Relations as association lists}

We would like to represent an (endo-)relation on $A$,
namely $\power(A \times A)$)
by ordered association lists representing the mapping $A \pfun \power^+ A$
(i.e. partial function from $A$ to non-empty sets of same).
\begin{code}
type ERel a = [(a,[a])]  -- fst unique, snd ordered, no dups
\end{code}

\subsubsection{Building endo-Relations}

We can have empty and singleton relations,
and merge and insert into them:
\begin{code}
mterel :: ERel a
mterel = []

snglerel :: a -> a -> ERel a
snglerel adom arng = [(adom,[arng])]

smerel :: Ord a => a -> [a] -> ERel a
smerel adom arngs = [(adom,lnorm arngs)]

inserel :: (Eq a, Ord a) => a -> a -> ERel a -> ERel a
inserel adom arng [] = [(adom,[arng])]
inserel adom arng erel@((a,as):arest)
 = case compare adom a of
     LT  ->  (adom,[arng]):erel
     GT  ->  (a,as):(inserel adom arng arest)
     EQ  ->  (a,insnorm arng as):arest

mrgerel :: (Eq a, Ord a) => ERel a -> ERel a -> ERel a
mrgerel [] erel2 = erel2
mrgerel erel1 [] = erel1
mrgerel erel1@((a1,as1):arest1) erel2@((a2,as2):arest2)
 = case compare a1 a2 of
    LT  ->  (a1,as1):(mrgerel arest1 erel2)
    GT  ->  (a2,as2):(mrgerel erel1 arest2)
    EQ  ->  (a1,as1 `mrgnorm` as2):(mrgerel arest1 arest2)
\end{code}

\subsubsection{Querying endo-Relations}

We can tailor a relation lookup, to return the empty list
if nothing is found:
\begin{code}
erlookup :: (Eq a, Ord a) => ERel a -> a -> [a]
erlookup erel a
 = case alookup erel a of
    Nothing  ->  []
    Just as  ->  as
\end{code}

Queries for domain, range and everything:
\begin{code}
ereldom,erelrng,erelelems :: (Eq a, Ord a) => ERel a -> [a]

ereldom = map fst

erelrng = foldr mrgnorm [] . map snd

erelelems erel
  = foldr mrgnorm edom erng
  where (edom,erng) = unzip erel
\end{code}

Identifying the reflexive kernel:
\begin{code}
erelrkernel :: Eq a => ERel a -> [a]
erelrkernel = concat . map rkernel
 where rkernel (a,as)
        | a `elem` as  = [a]
        | otherwise    = []
\end{code}


\subsubsection{endo-Relations Mapping}

We can map endo-functions over range,
and domain (with merged ranges if the latter function is not injective):
\begin{code}
erelrmap :: (Eq a, Ord a) => (a -> a) -> ERel a -> ERel a
erelrmap f erel = map (rmap f) erel
 where rmap f (a,as) = (a,lnorm (map f as))

ereldmap :: (Eq a, Ord a) => (a -> a) -> ERel a -> ERel a
ereldmap f erel = foldr mrgerel [] (map  (dmap f) erel)
 where dmap f (a,as) = smerel (f a) as
\end{code}


\subsubsection{endo-Relations Closures}

Reflexive closure: for all $a$ in domain or range,
add in singleton $a \mapsto a$:
\begin{code}
erelrclose :: (Eq a, Ord a) => ERel a -> ERel a
erelrclose erel = erel `mrgerel` erefrefl
 where erefrefl = concat $ map snglerelrefl $ erelelems erel

snglerelrefl :: a -> ERel a
snglerelrefl a = snglerel a a
\end{code}

Transitive closure: if $a \mapsto b$ and $b \mapsto c$
are in the relation, add in $a \mapsto c$ if not present.
\begin{code}
erelcomp :: (Eq a,Ord a) => ERel a -> ERel a -> ERel a
erelcomp erel1 erel2 = map (cmap erel2) erel1
 where
  cmap erel2 (a,as)
   = (a,foldr mrgnorm [] (map (erlookup erel2) as))

erelstep :: (Eq a,Ord a) => ERel a -> ERel a
erelstep erel = erel `mrgerel` (erel `erelcomp` erel)

ereltclose :: (Eq a,Ord a) => ERel a -> ERel a
ereltclose erel = converge (==) erelstep erel
\end{code}

\subsection{List display:line per item}

\begin{code}
shList lst
 = do putStrLn ("[[")
      shL lst
      putStrLn ("]]")
 where
   shL [] = return ()
   shL (x:xs)
    = do putStrLn (show x)
         shL xs

shNList lst
 = do putStrLn ("[[")
      shL 0 lst
      putStrLn ("]]")
 where
   shL n [] = return ()
   shL n (x:xs)
    = do putStrLn (show n ++ " : "++show x)
         shL (n+1) xs
\end{code}

\subsection{Whitespace Trimming}

\begin{code}
trim = trimtr . trimtr
trimtr "" = ""
trimtr str@(c:cs)
 | isSpace c = trimtr cs
 | otherwise = reverse str
\end{code}

\subsection{Reading Integer Number}

We read a string which may or may not denote an integer,
returning \texttt{minBound} if not:
\begin{code}
getint :: String -> Int
getint "" = minBound
getint (c:cs)
 | c == '-'   =  negate (getint cs)
 | otherwise  =  gn (digitToInt c) cs
 where
   gn n "" = n
   gn n (c:cs)
    | isDigit c  =  gn (10*n + digitToInt c) cs
    | otherwise  =  minBound

\end{code}

\subsection{Reading Natural Number}

We read a string which may or may not denote a natural number,
returning -1 if not:
\begin{code}

getnum :: String -> Int
getnum "" = (-1)
getnum (c:cs) = gn (digitToInt c) cs
 where
   gn n "" = n
   gn n (c:cs)
    | isDigit c  =  gn (10*n + digitToInt c) cs
    | otherwise  =  (-1)
\end{code}

\subsection{Control Flow}

\subsubsection{A ``switch-statement''}

This allows us to match a value \texttt{x}
against a list of predicate-function pairs \texttt{(p,f)}
returning \texttt{f x} for the first \texttt{p} that \texttt{x} satisfies,
or apply a default value function \texttt{def} if no predicate is satisfied.
\begin{code}
switch x [] def = def x
switch x ((p,f):rest) def
 | p x        =  f x
 | otherwise  =  switch x rest def

(--->) a b = (a,b)
\end{code}
The arrow-like pairing operator \texttt{--->} allows
us to write things that look ``switch-like'':
\begin{verbatim}
switch exp
  [ p1 ---> f1
  , p2 ---> f2
  , ...
  , pn ---> fn
  ]
\end{verbatim}

\subsubsection{A monadic ``continue''}

The takes a list of functions of two arguments: a boolean continue flag \texttt{cont}
and a current state \texttt{s}.
It applies each function in turn until either the boolean is false,
or a monadic fail occurs. In effect we get a monadic behaviour with
two levels of failure,
denoted by \texttt{Nothing} and \texttt{Just (False,\_)}.
\begin{code}
whlcont :: [Bool -> s -> Maybe (Bool,s)] -> Bool -> s -> Maybe (Bool,s)
whlcont []     cont s = return (cont, s)
whlcont (f:fs) cont s
 = do (cont',s') <- f cont s
      whlcont fs cont' s'

whlstart  :: [Bool -> s -> Maybe (Bool,s)] -> s -> Maybe (Bool,s)
whlstart fs s0 = whlcont fs True s0
\end{code}
We assume that each \texttt{f} satisfies the law \texttt{f False s = Just (False,s)}.

\subsubsection{``Convergence''}

\begin{code}
converge :: (a -> a -> Bool) -> (a -> a) -> a -> a
converge cvg f x
 | cvg x x'  =  x'
 | otherwise  =  converge cvg f x'
 where x' = f x
\end{code}


\subsection{Console Output}

\begin{code}
toConsole :: String -> IO ()
toConsole = putStrLn
-- toConsole s = return ()
\end{code}

\subsection{A ``Uniqueness'' Monad}

We want a monad that uses an integer seed to generate unique values,
to facilitate easy variable/name/identifier generation.
All we assume is that the seed (first) value belongs to class \texttt{Enum}.
\begin{code}
newtype Uniq a  = Uniq (Int -> (Int,a))

instance Monad Uniq where
 return x = Uniq r where r s = (s,x)
 (Uniq m) >>= f
   = Uniq mf
      where mf s = let (s1,x1) = m s in
                   let (Uniq fx) = f x1 in fx s1

-- for GHC 7.10 proofing
instance Functor Uniq where fmap = liftM
instance Applicative Uniq where
 pure  = return
 (<*>) = ap

newu = Uniq n where n s = (succ s,s)

runu s0 (Uniq mu) = snd (mu s0)
\end{code}

\newpage
\subsection{Nested Record Updating}
\label{Utilities.NRU}

Given record definitions like the following,
involving record nesting (here R1 inside R2):
\begin{verbatim}
data R1 = R1{ ..., f1 :: T1 ,... }
data R2 = R2{ ..., r1 :: R1 ,... }
\end{verbatim}
Assume we have defined record modifiers as follows
(the function arguments are important):
\begin{verbatim}
f1Setf :: (T1 -> T1) -> R1 -> R1
f1Setf f rec1 = rec1{ f1 = f (f1 rec1) }
r1Setf :: (R1 -> R1) -> R2 -> R2
r1Setf g rec2 = rec2{ r1 = g (r1 rec2) }
\end{verbatim}
Note that we visualise both functions as:
\begin{center}
\begin{tikzpicture}[>=stealth,->,shorten >=2pt,looseness=.5,auto]
 \matrix[matrix of math nodes,
         column sep={2cm,between origins},
         row sep={2cm,between origins}]
  { |(R1L)|R_1 & |(R1R)|R_1 & |(R2L)|R_2 & |(R2R)|R_2  \\
    |(T1L)|T_1 & |(T1R)|T_1 & |(r1L)|R_1 & |(r1R)|R_1  \\
  };
  \tikzstyle{every node}=[midway,auto,font=\scriptsize]
  \draw (R1L) -- node {$f_1get$}(T1L) ;
  \draw (T1L) -- node {$f$} (T1R) ;
  \draw (T1R) -- node {$f_1set$}(R1R) ;
  \draw [dashed] (R1L) -- node {$f1Setf~f$} (R1R) ;
  \draw (R2L) -- node {$r_1get$}(r1L) ;
  \draw (r1L) -- node {$g$} (r1R) ;
  \draw (r1R) -- node {$r_1set$}(R2R) ;
  \draw [dashed] (R2L) -- node {$r1Setf~g$} (R2R) ;
\end{tikzpicture}
\end{center}
We can stack these as follows:
\begin{center}
\begin{tikzpicture}[>=stealth,->,shorten >=2pt,looseness=.5,auto]
 \matrix[matrix of math nodes,
         column sep={3cm,between origins},
         row sep={2cm,between origins}]
  { |(R2L)|R_2 & |(R2R)|R_2  \\
    |(R1L)|R_1 & |(R1R)|R_1  \\
    |(T1L)|T_1 & |(T1R)|T_1  \\
  };
  \tikzstyle{every node}=[midway,auto,font=\scriptsize]
  \draw (R1L) -- node {$f_1get$}(T1L) ;
  \draw (T1L) -- node {$f$} (T1R) ;
  \draw (T1R) -- node {$f_1set$}(R1R) ;
  \draw [dashed] (R1L) -- node {$f1Setf~f$} (R1R) ;
  \draw (R2L) -- node {$r_1get$}(R1L) ;
  \draw (R1R) -- node {$r_1set$}(R2R) ;
  \draw [dashed] (R2L) -- node {$r1Setf~(f1Setf~f)$} (R2R) ;
\end{tikzpicture}
\end{center}
We find that function composition then allows us to easily
construct such ``towers'':
\begin{verbatim}
(.) :: (r1r1 -> r2r2) -> (t1t1 -> r1r1) -> t1t1 -> r2r2
\end{verbatim}
Note also that \texttt{f1Set :: T1 -> R1 -> R1}
\\can be defined
as \texttt{f1Set = f1Setf . const}



\newpage
\subsection{Bits and Bobs}


Total versions of \texttt{tail} and \texttt{init}:
\begin{code}
ttail [] = []
ttail (_:xs) = xs

tinit [] = []
tinit xs = init xs
\end{code}

Total versions of \texttt{head} and \texttt{last} (with def value supplied):
\begin{code}
thead def []   =  def
thead _ (x:_)  =  x

tlast def []   =  def
tlast _ xs     =  last xs
\end{code}

Singleton list:
\begin{code}
sngl :: a -> [a]
sngl x = [x]
\end{code}


Twisting a pair:
\begin{code}
twist :: (a,b) -> (b,a)
twist (x,y) = (y,x)
\end{code}

Mapping a pair:
\begin{code}
map2 :: (a->b) -> (a,a) -> (b,b)
map2 f (x, y) = (f x, f y)
\end{code}

Self pairwise checking:
\begin{code}
selfpairwise :: (t -> t -> Bool) -> [t] -> Bool
selfpairwise p []  =  True
selfpairwise p (x:xs) = all (p x) xs && selfpairwise p xs
\end{code}

Building a graph of a function over a list:
\begin{code}
fgraph :: (s -> t) -> [s] -> [(s,t)]
fgraph f xs = zip xs $ map f xs
\end{code}


Version of unlines that only puts newlines between strings:
\begin{code}
unlines' []      =  ""
unlines' [s]     =  s
unlines' (s:ss)  =  s ++ '\n':unlines' ss
\end{code}

\subsubsection{Accumulator Functions}

Consider a function \texttt{f} with two accumulation arguments
(\texttt{a1}, \texttt{a2}), followed
by a third active argument (\texttt{x}),
whose result is the final value of the second accumulator,
\begin{verbatim}
  f :: A1 -> A2 -> X -> A2
  f a1 a2 x = a2,  if x is "done" ...
\end{verbatim}

We want a function that works down a list of active arguments
(\texttt{xs}):
\begin{code}
seq2s :: (a -> b -> c -> b) -> a -> b -> [c] -> b
seq2s f a1 a2 [] = a2
seq2s f a1 a2 (x:xs) = seq2s f a1 (f a1 a2 x) xs
\end{code}

The first accumulator is a context that is the same for all
members
of the list.
In a similar vein, given different functions
working on different types of third argument,
we'd like to sequence those as well:
\begin{code}
seq2 :: a -> b -> (a -> b -> c -> d) -> c -> (a -> d -> e -> f) -> e -> f
seq2 a1 a2 f x g y = g a1 (f a1 a2 x) y
\end{code}

We also need to flatten explicit maps
\begin{code}
mflat :: [(t,t)] -> [t]
mflat = concat . map ( \ (a,b) -> [a,b] )
\end{code}

\subsubsection{Cross Products}

We have triples, quadruples, and quintuples,
so some destructors and pointed mappings:
\begin{code}
setfst f (a,b) = (f a,b)
setsnd g (a,b) = (a,g b)
setboth (f,g) (a,b) = (f a, g b)
mapfst f = map $ setfst f
mapsnd g = map $ setsnd g
mapboth (f,g) = map $ setboth (f,g)

fst3 (a,_,_) = a
snd3 (_,b,_) = b
thd3 (_,_,c) = c
setfst3 f (a,b,c) = (f a,b,c)
setsnd3 f (a,b,c) = (a,f b,c)
setthd3 f (a,b,c) = (a,b,f c)
putfst3 x (a,b,c) = (x,b,c)
putsnd3 x (a,b,c) = (a,x,c)
putthd3 x (a,b,c) = (a,b,x)

fst4 (a,_,_,_) = a
snd4 (_,b,_,_) = b
thd4 (_,_,c,_) = c
frt4 (_,_,_,d) = d

fst5 (a,_,_,_,_) = a
snd5 (_,b,_,_,_) = b
thd5 (_,_,c,_,_) = c
frt5 (_,_,_,d,_) = d
fth5 (_,_,_,_,e) = e
\end{code}

Conditional function application
\begin{code}
applyWhen :: (t -> Bool) -> (t -> t) -> t -> t
applyWhen p f x
 | p x        =  f x
 | otherwise  =  x
\end{code}

Showing a count:
\begin{code}
showCount root plural xs
 = show len ++ " " ++ root ++ addplural plural len
 where
   len = length xs
   addplural p 1 = ""
   addplural p _ = p
\end{code}

Outputting a list, one element per line, with indenting
\begin{code}
listLines :: Show a => Int -> [a] -> String
listLines i
 = concat . intersperse "\n" . map (nl i . show)
 where
   nl 0 s =  s
   nl i s =  ' ' : nl (i-1) s

listPut :: Show a => Int -> [a] -> IO ()
listPut i = putStrLn . listLines i
\end{code}


We are also going to find it useful to have \texttt{Either String}
as an instance of \texttt{Monad}:
\begin{code}
#if __GLASGOW_HASKELL__ < 700
instance Monad (Either String) where
  return x = Right x
  m >>= f
    = case m of
        (Left s) -> (Left s)
        (Right x) -> f x
  fail s = Left s
#endif
-- instance Functor (Either String) where
--  fmap f (Left s) = Left s
--  fmap f (Right x) = Right (f x)
\end{code}

\subsubsection{Monadic Mobility}

A lot of table code was developed with return type \texttt{Maybe x}.
We want to generalise to monads in general.
Here we provide a simple wrapper:
\begin{code}
m2m :: Monad m => Maybe t -> m t
m2m Nothing   =  nowt
m2m (Just x)  =  return x
nothing = "Nothing"
nowt :: Monad m => m t
nowt = fail nothing
\end{code}


\subsubsection{Why didn't they \ldots}

Here we put things that should have appeared in the appropriate
Haskell distribution libraries.
\begin{code}
#if __GLASGOW_HASKELL__ < 700
isLeft (Left _)   = True  -- not in Data.Either
isLeft (Right _)  = False
isRight (Left _)  = False
isRight (Right _) = True
#endif
\end{code}

List membership modulo an equivalence predicate
\begin{code}
elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy eq x [] = False
elemBy eq x (y:ys)
 | x `eq` y  =  True
 | otherwise  =  elemBy eq x ys
\end{code}

``Proper'' (partial) sequence subtraction:
\begin{code}
infixl 5 -*-

xs  -*-  [] = xs

(x:xs)  -*-  (y:ys)
  | x == y     =  xs  -*-  ys
\end{code}

A more robust version:
\begin{code}
stripPrefix [] xs = Just xs
stripPrefix (x:xs) (y:ys)
 | x == y     =  stripPrefix xs ys
 | otherwise  =  Nothing
stripPrefix _ _ = Nothing
\end{code}

Also, facilities to update parts of a pair:
\begin{code}
updfst a' (a,b) = (a',b)
updsnd b' (a,b) = (a,b')
\end{code}

The function \texttt{pinchout} removes an indexed element from a list:
\begin{code}
pinchout _ [] = []
pinchout 0 (_:xs) = xs
pinchout n (x:xs) = x : pinchout (n-1) xs
\end{code}

Checking if a list of lists forms a partition:
\begin{code}
isPartition :: Eq a => [[a]] -> Bool
isPartition [] = True
isPartition [_] = True
isPartition (xs:xss)
 = all (differentTo xs) xss && isPartition xss
 where
   xs `differentTo` ys = null (xs `intersect` ys)
\end{code}

Generic list replacement:
\begin{code}
lmreplace :: (a -> Maybe a) -> [a] -> [a]
lmreplace f [] = []
lmreplace f (x:xs)
 = case f x of
     Nothing  ->  x:(lmreplace f xs)
     Just y   ->  y:(lmreplace f xs)
\end{code}

A few set-theoretic predicates:
\begin{code}
v1 `issubset` v2 =  null ( v1 \\ v2 ) -- not in Data.List !
v1 `disjoint` v2 =  null ( v1 `intersect` v2 )
\end{code}

Totalising maximum
We compute maxima of lists, which may be empty,
so we need to totalise the Prelude version,
either by assuming positive numbers only,
or a bounded type
\begin{code}
pmaxima :: (Ord a, Num a) => [a] -> a
pmaxima  =  maximum . (0:)
bmaxima :: (Ord a,Bounded a) => [a] -> a
bmaxima  =  maximum . (minBound:)
\end{code}
