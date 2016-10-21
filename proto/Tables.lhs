\section{Tables}

\begin{code}
{-# LANGUAGE CPP #-}
module Tables where

import Data.List
import Test.QuickCheck
import Utilities
\end{code}

We implement lookup tables, indexed by strings,
using ``tries''.

\subsection{Finite Map as Binary Tree}

First a polymorphic map from keys to data,
implemented as a binary tree:
\begin{code}
data Btree k d
 = Bnil | Bleaf k d | Bbr k d (Btree k d) (Btree k d)
 deriving (Eq,Ord)

instance (Show k, Show d) => Show (Btree k d) where
  show Bnil = "NIL"
  show tree = showTree 0 tree

showTree n Bnil = ""
showTree n (Bleaf c x) = showItem n c x
showTree n (Bbr c x left right)
  = showTree n' left ++ showItem n c x ++ showTree n' right
  where n' = n+1

showItem n c x = indent n ++ show c ++ " -> " ++ show x ++ "\n"

indent 0 = " "
indent n = '.':(indent (n-1))
\end{code}

Debug printer
\begin{code}
dbgBtree _ Bnil = "Bnil"
dbgBtree dbgx (Bleaf c x) = "(Bleaf "++show c++" "++dbgx x++")"
dbgBtree dbgx (Bbr c x left right)
 = "(Bbr "++show c
   ++" "++dbgx x
   ++" "++dbgBtree dbgx left
   ++" "++dbgBtree dbgx right
   ++")"
\end{code}

Inorder traversal
\begin{code}
inorder Bnil = []
inorder (Bleaf c x) = [(c,x)]
inorder (Bbr c x left right) = inorder left ++ [(c,x)] ++ inorder right
\end{code}

We have lookup
\begin{code}
btlookup :: (Eq k,Ord k) => (Btree k d) -> k -> Maybe d
btlookup Bnil c = Nothing
btlookup (Bleaf c' v) c
 | c==c'      =  Just v
 | otherwise  =  Nothing
btlookup (Bbr c' v left right) c
 | c==c'      =  Just v
 | c<c'       =  btlookup left c
 | otherwise  =  btlookup right c

type Blookup k d = k -> Maybe d
\end{code}

and data entry, with resolution for updating:
\begin{code}
btenter :: Ord k => (t -> t -> t) -> k -> t -> Btree k t -> Btree k t
btenter res c v Bnil = Bleaf c v
btenter res c v (Bleaf c' v')
 | c==c'      =  Bleaf c' (res v' v)
 | c<c'       =  Bbr c' v' (Bleaf c v) Bnil
 | otherwise  =  Bbr c' v' Bnil (Bleaf c v)
btenter res c v (Bbr c' v' left right)
 | c==c'      =  Bbr c' (res v' v) left right
 | c<c'       =  Bbr c' v' (btenter res c v left) right
 | otherwise  =  Bbr c' v' left (btenter res c v right)
\end{code}

Update simply resolves to new value:
\begin{code}
btupdate :: Ord k => k -> t -> Btree k t -> Btree k t
btupdate = btenter ovr

ovr :: a -> b -> b
ovr _ b = b
\end{code}

``Downdate'' simply resolves to old value,
so implements a liberal form of map extension.
\begin{code}
btdowndate :: Ord k => k -> t -> Btree k t -> Btree k t
btdowndate = btenter rvo

rvo :: a -> b -> a
rvo a _ = a
\end{code}

We can also map elements of a binary tree:
\begin{code}
btmap f Bnil = Bnil
btmap f (Bleaf c v) = Bleaf c (f v)
btmap f (Bbr c v left right) = Bbr c (f v) (btmap f left) (btmap f right)
\end{code}

It is useful to have something to convert a list of key-data
association pairs into a balanced binary tree,
by sorting the association list,
and then halving it repeatedly to get each side.
For efficiency, we do our own sorting, and accumulate
the list length at the same time
\begin{code}
bbuild as = mkbalbt len asrt
 where
  asrt = sort as
  len  = length asrt
  mkbalbt 0 []      = Bnil
  mkbalbt 1 [(k,d)] = Bleaf k d
  mkbalbt n asrt    = Bbr kmid dmid left right
   where -- n >= 2
     mid = n `div` 2
     nl = mid-1
     (asl,rest) = splitAt nl asrt
     ((kmid,dmid):asr) = rest
     nr = n-(nl+1)
     left  = mkbalbt nl asl
     right = mkbalbt nr asr
\end{code}


\subsection{Tries}

A trie is a map from characters to trie-nodes
where a trie-node might have a value,
but also contains a suffix-trie.
\begin{code}
data Trie t = Trie (Maybe t) (Btree Char (Trie t)) deriving (Eq,Ord)

flattenTrie :: Trie t -> [(String, t)]
flattenTrie trie = trieFlatten "" trie

trieFlatten :: String -> Trie t -> [(String, t)]
trieFlatten prefix (Trie Nothing btree)
 = concat (map (extprefix prefix) (inorder btree))
trieFlatten prefix (Trie (Just x) btree)
  = (prefix,x):(concat (map (extprefix prefix) (inorder btree)))

extprefix prefix (c,trie) = trieFlatten (prefix++[c]) trie

-- now a variant that returns the length of the longest key
flattenTrieD :: Trie t -> (Int, [(String, t)])
flattenTrieD trie = trieFlattenD 0 "" trie

trieFlattenD d prefix (Trie Nothing btree)
 = (maximum (0:ds),concat flats)
 where
    subtrees = inorder btree
    subflatds = map (extprefixD d prefix) subtrees
    (ds,flats) = unzip subflatds -- could be empty !
trieFlattenD d prefix (Trie (Just x) btree)
  = (maximum (d:ds),(prefix,x):(concat flats))
 where
    subtrees = inorder btree
    subflatds = map (extprefixD d prefix) subtrees
    (ds,flats) = unzip subflatds

extprefixD  d prefix (c,trie) = trieFlattenD (d+1) (prefix++[c]) trie

trieShowWith :: (t -> String) -> Trie t -> [String]
trieShowWith sh = showFlatTrieWith sh "" . flattenTrieD

showFlatTrieWith sh pfx (_,[]) = ["{}"]
showFlatTrieWith sh pfx (w,alist) = flatTrieShow sh pfx w alist

flatTrieShow sh pfx w [] = []
flatTrieShow sh pfx w ((nm,val):rest)
 = (pfx ++ pad nm ++ "  |->  " ++ sh val)
   : flatTrieShow sh pfx w rest
 where pad nm = nm ++ replicate (w - length nm) ' '
\end{code}

Show instance:
\begin{code}
instance Show t => Show (Trie t) where
  showsPrec ind trie s
    = (unlines' $ showFlatTrieWith show (replicate ind ' ') (flattenTrieD trie))++s
  show = unlines' . showFlatTrieWith show "" . flattenTrieD
\end{code}

Debugging Printer
\begin{code}
dbgTrie (Trie md btree)
 = "(Trie <"++show md++"> "++dbgBtree dbgTrie btree++")"

instance Dshow a => Dshow (Trie a) where
 dshow trie
   = unlines $ map adshow $ flattenTrie trie
   where
     adshow (n,x) = n ++ " |-->\n" ++ dshow x
\end{code}

Apropos empty tries:
\begin{code}
tnil :: Trie t
tnil = Trie Nothing Bnil

isEmptyTrie :: Trie t -> Bool
isEmptyTrie (Trie Nothing Bnil)  =  True
isEmptyTrie _                    =  False
\end{code}

\subsubsection{Trie Lookup}

Trie lookup is fairly straightforward:
\begin{code}
tlookup :: Trie t -> String -> Maybe t
tlookup (Trie item _) "" = item
tlookup (Trie _ stree) (c:cs)
 = case btlookup stree c of
     Nothing      ->  Nothing
     (Just node)  ->  tlookup node cs

type Tlookup t = String -> Maybe t

tlookup' = flip tlookup
\end{code}

It can also be useful to have a total lookup
where a default value is returned if the item is not present:
\begin{code}
ttlookup :: t -> Trie t -> String -> t
ttlookup def trie item
 = case tlookup trie item of
     Nothing     ->  def
     Just thing  ->  thing
\end{code}


We can also return a match against a prefix,
also indicating what part of the string was leftover.
First, a shortest-match-wins version:
\begin{code}
pfxsrchs :: Trie t -> String -> (Maybe t,String)
pfxsrchs (Trie item _) "" = (item,"")
pfxsrchs (Trie _ stree) str@(c:cs)
 = case btlookup stree c of
     Nothing      ->  (Nothing,str)
     (Just node@(Trie item _))
       ->  case item of
             Nothing  ->  pfxsrchs node cs
             _        ->  (item,cs)
\end{code}

Next, a longest-match-wins version:
\begin{code}
pfxsrchl :: Trie t -> String -> (Maybe t,String)
pfxsrchl trie str = psrchl trie [] str
 where
psrchl (Trie item _) []    "" = (item,"")
psrchl (Trie item _) (f:_) "" = f
psrchl (Trie _ stree) fnd str@(c:cs)
 = case btlookup stree c of
     Nothing
        ->  if null fnd
             then (Nothing,str)
             else head fnd
     (Just node@(Trie item _))
       ->  case item of
             Nothing  ->  psrchl node fnd cs
             _        ->  psrchl node ((item,cs):fnd) cs
\end{code}

Finally, a version that returns all matches:
\begin{code}
pfxsrchall :: Trie t -> String -> [(Maybe t,String)]
pfxsrchall trie str = psrcha trie [] str
 where
psrcha (Trie item _) fnd "" = fnd
psrcha (Trie _ stree) fnd str@(c:cs)
 = case btlookup stree c of
     Nothing ->  fnd
     (Just node@(Trie item _))
       ->  case item of
             Nothing  ->  psrcha node fnd cs
             _        ->  psrcha node ((item,cs):fnd) cs
\end{code}

Occasionally we shall want to lookup a list of tries
(typically a context-stack),
returning the first value found:
\begin{code}
tslookup :: [Trie t] -> String -> Maybe t
tslookup [] _ = Nothing
tslookup (trie:tries) item
  = case tlookup trie item of
      Nothing    ->  tslookup tries item
      something  ->  something
\end{code}

A ``transpose'' of \texttt{tslookup} is
function \texttt{tlookupall} that looks up a list of identifiers,
returning nothing if any lookup fails:
\begin{code}
tlookupall :: Trie a -> [String] -> Maybe [a]
tlookupall trie [] = Just []
tlookupall trie (v:vs)
 = do r <- tlookup trie v
      rs <- tlookupall trie vs
      return (r:rs)
\end{code}

We can also return a sub-trie determined by a prefix:
\begin{code}
pfxSubTrie :: String -> Trie t -> Trie t
pfxSubTrie "" trie = trie
pfxSubTrie (c:cs) (Trie _ btree)
  = case btlookup btree c of
      Nothing      ->  tnil
      (Just subt)  ->  pfxSubTrie cs subt
\end{code}

and show such a tree
\begin{code}
showSubTrie pfx trie
 = showFlatTrieWith show pfx (flattenTrieD (pfxSubTrie pfx trie))
\end{code}

It can useful to get a list of either keys or data
(\texttt{flattenTrie} gives both):
\begin{code}
trieDom = map fst . flattenTrie
trieRng = map snd . flattenTrie
\end{code}


\subsubsection{Trie Entry}

Trie entry is a little involved:
\begin{code}
tenter :: (t -> t -> t) -> String -> t -> Trie t -> Trie t

tenter res "" v (Trie Nothing stree)
  = (Trie (Just v) stree)

tenter res "" v (Trie (Just v') stree)
  = (Trie (Just (res v' v)) stree)

tenter res (c:cs) v (Trie item stree)
  = case btlookup stree c of
     Nothing
      -> (Trie item (btupdate c (tenter res cs v tnil) stree))
     (Just subt)
      -> (Trie item (btupdate c (tenter res cs v subt) stree))
\end{code}

And we can update/downdate:
\begin{code}
tupdate :: String -> t -> Trie t -> Trie t
tupdate = tenter ovr

tdowndate :: String -> t -> Trie t -> Trie t
tdowndate = tenter rvo
\end{code}

Building tables from string-value lists:
\begin{code}
tsingle s v = tupdate s v tnil

lupdate = foldr mkentry
mkentry (s,v) trie = tupdate s v trie
\end{code}

and from value-string lists:
\begin{code}
lflipupdate = foldr mkflipentry
mkflipentry (v,s) trie = tupdate s v trie
\end{code}

Building from scratch:
\begin{code}
lbuild = lupdate tnil
\end{code}

Building from scratch, failing if same key occurs twice
\begin{code}
lubuild [] = return tnil
lubuild ((s,v):rest)
 = do rtrie <- lubuild rest
      case tlookup rtrie s of
        Nothing  ->  return $ tupdate s v rtrie
        Just _   ->  fail ("lubuild: key '"++s++"' occurs twice")
\end{code}

Building from scratch, for objects with their own names:
\begin{code}
lnbuild getname = lbuild . map gn where gn obj = (getname obj,obj)
\end{code}



Building from scratch, using resolution for name conflicts
\begin{code}
lrbuild res assoc = lrenter res tnil assoc
lrenter res  = foldr (mkrentry res)
mkrentry res (s,v) trie = tenter res s v trie
\end{code}

We also support the use of tries as sets:
\begin{code}
sbuild :: [String] -> Trie ()
sbuild strs = lbuild (map nullassoc strs)
 where nullassoc str = (str,())

slookup :: Trie t -> String -> Bool
slookup strie str
 = case tlookup strie str of
     Nothing   ->  False
     (Just _)  ->  True

sslookup :: [Trie t] -> String -> Bool
sslookup strie str
 = case tslookup strie str of
     Nothing   ->  False
     (Just _)  ->  True
\end{code}
It can help sometimes to have a trie dom function that returns
a set, rather than a list:
\begin{code}
trieKey :: Trie t -> Trie ()
trieKey = tmap $ const ()
\end{code}

Sometimes we want an entry function with the resolution function
able to produce failure:
\begin{code}
mtenter :: (t -> t -> Maybe t) -> String -> t -> Trie t
             -> Maybe (Trie t)

mtenter mres "" v (Trie Nothing stree)
  = return (Trie (Just v) stree)

mtenter mres "" v (Trie (Just v') stree)
  = do v'' <- mres v v'
       return (Trie (Just v'') stree)

mtenter mres (c:cs) v (Trie item stree)
  = case btlookup stree c of
     Nothing
      -> return (Trie item (btupdate c (tupdate cs v tnil) stree))
     (Just subt)
      -> do subt' <- mtenter mres cs v subt
            return (Trie item (btupdate c subt' stree))
\end{code}
A useful instance of \verb"(t -> t -> Maybe t)"
is one that checks for equality:
\begin{code}
same :: Eq t => (t -> t -> Maybe t)
x `same` y
 | x == y     =  Just x
 | otherwise  =  Nothing
\end{code}


\subsubsection{Trie Merging}

Now, an approach that uses a resolution for conflicts that may fail
resulting in the merge as whole failing:
\begin{code}
tmmerge :: (t -> t -> Maybe t) -> Trie t -> Trie t -> Maybe (Trie t)

tmmerge mmrg (Trie Nothing btree1) (Trie thing2 btree2)
 = do btree' <- btmmerge mmrg btree1 btree2
      return (Trie thing2 btree')

tmmerge mmrg (Trie thing1 btree1) (Trie Nothing btree2)
 = do btree' <- btmmerge mmrg btree1 btree2
      return (Trie thing1 btree')

tmmerge mmrg (Trie (Just obj1) btree1) (Trie (Just obj2) btree2)
 =  do obj' <- obj1 `mmrg` obj2
       btree' <- btmmerge mmrg btree1 btree2
       return (Trie (Just obj') btree')
\end{code}

Merging binary tree portions
\begin{code}
btmmerge :: (t -> t -> Maybe t) -> Btree Char (Trie t) -> Btree Char (Trie t)
             -> Maybe (Btree Char (Trie t))

btmmerge mmrg Bnil btree2 = Just btree2
btmmerge mmrg btree1 Bnil = Just btree1

btmmerge mmrg bt1@(Bleaf k1 trie1) (Bleaf k2 trie2)

 | k1 == k2   =  do trie' <- tmmerge mmrg trie1  trie2
                    return (Bleaf k1 trie')

 | k1 <  k2   =  Just (Bbr k2 trie2 bt1 Bnil)

 | otherwise  =  Just (Bbr k2 trie2 Bnil bt1)

btmmerge mmrg bt1@(Bleaf k1 trie1) (Bbr k2 trie2 left right)

 | k1 == k2   =  do trie' <- tmmerge mmrg trie1 trie2
                    return (Bbr k2 trie' left right)

 | k1 <  k2   =  do left' <- btmmerge mmrg bt1 left
                    return (Bbr k2 trie2 left' right)

 | otherwise  =  do right' <- btmmerge mmrg bt1 right
                    return (Bbr k2 trie2 left right')

btmmerge mmrg (Bbr k1 trie1 left right) bt2@(Bleaf k2 trie2)

 | k1 == k2   =  do trie' <- tmmerge mmrg trie1 trie2
                    return (Bbr k1 trie' left right)

 | k2 <  k1   =  do left' <- btmmerge mmrg left bt2
                    return (Bbr k1 trie1 left' right)

 | otherwise  =  do right' <- btmmerge mmrg right bt2
                    return (Bbr k1 trie1 left right')

btmmerge mmrg (Bbr k1 trie1 left1 right1) (Bbr k2 trie2 left2 right2)

 | k1 == k2   =  do trie' <- tmmerge mmrg trie1 trie2
                    left' <- btmmerge mmrg left1 left2
                    right' <- btmmerge mmrg right1 right2
                    return (Bbr k1 trie' left' right')

 | k1 <  k2   =  do left21 <- btmmerge mmrg (Bleaf k1 trie1) left2
                    left22 <- btmmerge mmrg left1 left21
                    let bt2' = Bbr k2 trie2 left22 right2
                    bt2'' <- btmmerge mmrg right1 bt2'
                    return bt2''

 | otherwise  =  do right21 <- btmmerge mmrg (Bleaf k1 trie1) right2
                    right22 <- btmmerge mmrg right1 right21
                    let bt2' = Bbr k2 trie2 left2 right22
                    bt2'' <- btmmerge mmrg bt2' left1
                    return bt2''
\end{code}

Also required, a (consistent) trie glueing that fails if there is
a dispute over the binding of a name
\begin{code}
tglue :: Eq t => Trie t -> Trie t -> Maybe (Trie t)
tglue t1 t2 = tmmerge trieglue t1 t2

trieglue :: Eq t => t -> t -> Maybe t
trieglue a b
    | (a == b)   =  Just a
    | otherwise  =  Nothing

tglueW :: (t -> t -> Bool) -> Trie t -> Trie t -> Maybe (Trie t)
tglueW fits t1 t2 = tmmerge (tglueWith fits) t1 t2

tglueWith :: (t -> t -> Bool) -> t -> t -> Maybe t
tglueWith fits a b
    | (a `fits` b)  =  Just a
    | otherwise   =  Nothing
\end{code}

It is useful to be able to merge two tries \emph{letting
entries in the second override the first}:
\begin{code}
tmerge :: Trie t -> Trie t -> Trie t
tmerge trie1 trie2
 = let
     (Just trie') = tmmerge later trie1 trie2
     later a b = Just b
   in trie'

toverride = tmerge -- a helpful synonym.
\end{code}


\subsubsection{Trie Deletion}

Trie deletion is less involved, if we leave the node alone,
just pointing to nothing:
\begin{code}
tblank :: String -> Trie t -> Trie t
tblank "" (Trie _ stree) = Trie Nothing stree
tblank (c:cs) trie@(Trie item stree)
 = case btlookup stree c of
     Nothing -> trie
     (Just subt) -> Trie item (btupdate c (tblank cs subt) stree)
\end{code}

\subsubsection{Trie Mapping}

It is useful to be able to map
a function over the Trie range items.
\begin{code}
tmap :: (a -> b) -> Trie a -> Trie b
tmap f (Trie v btree)
  = Trie (fmap f v) (btmap (tmap f) btree)
\end{code}

\subsubsection{Trie Inversion}

Sometimes we need to be able to invert a \texttt{Trie} mapping
(e.g. to check for injectivity):
\begin{code}
tinv :: Ord t => Trie t -> [(t,[String])]
tinv = kdsfuse . sort . map twist . flattenTrie

kdsfuse :: Eq t => [(t,String)]  -- assumed sorted
                -> [(t,[String])]
kdsfuse []       =  []
kdsfuse [(k,d)]  =  [(k,[d])]
kdsfuse (kd:kds) = kdsfuse' kd $ kdsfuse kds

kdsfuse' (k,d) [] = [(k,[d])]
kdsfuse' (k,d) kds@((k',ds'):kds')
 | k == k'    =  ((k',d:ds'):kds')
 | otherwise  =  (k,[d]):kds
\end{code}

Testing a trie for injectivity:
\begin{code}
isInjTrie :: Ord t => Trie t -> Bool
isInjTrie trie = srcCounts == [1] || null srcCounts
 where srcCounts = nub . map (length . snd) $ tinv trie
\end{code}


\newpage
\subsubsection{Maximal Munching}

Given a string \texttt{str}, and a set of strings $S$,
we want to fragment \texttt{str} by extracting out (``munching'') any occurrences
as subsequences in \texttt{str} of elements of $S$,
as well as the in-between fragments.
If $S$ contains $s_1$ and $s_2$ such that $s_1 < s_2$,
then we return any occurrence of $s_2$ as is, without splitting it down
into $s_1$ and something else (``maximal munch'').
So, for example, the maximal munch of
\texttt{aabcddbbddd}
w.r.t set
$\{\texttt{b},\texttt{d},\texttt{dd}\}$
is
$$
\langle
 \texttt{aa}
,\texttt{b}
,\texttt{c}
,\texttt{dd}
,\texttt{b}
,\texttt{b}
,\texttt{dd}
,\texttt{d}
\rangle
$$
We represent the set $S$ by a Trie (of anything).

The first function returns a maximal munch if it starts
at the beginning of the string, along with the string leftover:
\begin{code}
getStartMunch :: Trie a -> String -> (String,String)
getStartMunch trie str = gsm ("",str) "" trie str
 where

   gsm :: (String,String) -- best answer so far
          -> String       -- answer under construction (reversed)
          -> Trie a       -- current sub-Trie
          -> String       -- string remaining
          -> (String,String)

   gsm (munch,rest) _ (Trie Nothing _) ""      = (munch,rest)

   gsm (munch,rest) hcnum (Trie (Just _) _) "" = (reverse hcnum,"")

   gsm (munch,rest) hcnum (Trie Nothing btree) str@(c:cs)
    = case btlookup btree c of
        Nothing      ->  (munch,rest)
        (Just node)  ->  gsm (munch,rest) (c:hcnum) node cs

   gsm (munch,rest) hcnum (Trie (Just _) btree) str@(c:cs)
    = case btlookup btree c of
        Nothing      ->  (reverse hcnum,str)   -- done, with new munch
        (Just node)  ->  gsm (reverse hcnum,str) (c:hcnum) node cs
\end{code}

Basically we apply \texttt{getStartMunch} to our string.
If it succeeds (non-empty munch found),
then we record the munch, and then repeat.
If it fails, we note the first character as belonging to a sub-string not
in the set, and we apply \texttt{getStartMunch} to the rest of the string,
building up a list of failing characters.
When it succeeds again, the accumulated list is an `tween' fragment.
\begin{code}
maximalMunches :: Trie a -> String -> [String]
maximalMunches trie str = mm  [] "" str
 where

   mm :: [String] -- munches so far (reversed)
         -> String -- current "tween" munch (reversed)
         -> String -- string remaining
         -> [String]

   mm sechnum "" "" = reverse sechnum

   mm sechnum neewt "" = reverse (reverse neewt:sechnum)

   mm sechnum neewt str@(c:cs)
    | null munch  =  mm sechnum (c:neewt) cs
    | null neewt  =  mm (munch:sechnum) "" rest
    | otherwise   =  mm (munch:(reverse neewt):sechnum) "" rest
    where (munch,rest) = getStartMunch trie str
\end{code}

\subsection{Trie-based Replacement}

We can model a replacement translation
as a \texttt{String}-to-\texttt{String} mapping (\texttt{Trie}),
and use this to change strings.
In the event of a sub-string matching more than
one key, then the replacement with the \emph{longer} match is used.
\begin{code}
trie_repl trie str = tr [] str
 where
   tr ser [] = reverse ser
   tr ser str@(c:cs)
    = case pfxsrchl trie str of
       (Nothing,_)       ->  tr (c:ser) cs
       ((Just rep),cs')  ->  tr (rep~~ser) cs'
   []     ~~ sx  =  sx
   (c:cs) ~~ sx  =  cs ~~ (c:sx)
\end{code}



\newpage
\subsection{Rings}

We have a polymorphic ring datastructure,
that allows us to move clock-/anticlock-wise around a ring.

A ring is implemented as a pair of lists:
\begin{code}

type Ring a = ([a],[a])

\end{code}
A non-empty ring always has its second list non-empty,
and its head is the ``current'' element.
\begin{code}

invRing :: Ring a -> Bool
invRing (back,front)
 = if null front then null back else True

\end{code}

We build a ring from a list, noting the convention that the
current item is always the head of the second list:
\begin{code}

buildRing :: [a] -> Ring a
buildRing xs = ([],xs)

prop_invbuild :: [Int] -> Bool
prop_invbuild xs = invRing (buildRing xs)

-- *Tables> test prop_invbuild
-- OK, passed 100 tests.
\end{code}
Moving clockwise involves transferring the current element
to the front of the first list, and rotating all if the
second list becomes empty:
\begin{code}

rotateCW :: Ring a -> Ring a
rotateCW ring@(_,[]) = ring
rotateCW ring@(back,(curr:front))
 | null front  =  ([],reverse (curr:back))
 | otherwise   =  (curr:back,front)

prop_invcw :: Ring Int -> Property
prop_invcw r = invRing r ==> invRing (rotateCW r)

-- *Tables> test prop_invcw
-- OK, passed 100 tests.
\end{code}
Moving anti-clockwise is the reverse of the above:
\begin{code}

rotateACW :: Ring a -> Ring a
rotateACW ring@(_,[]) = ring
rotateACW ring@([],front)
 = let (prev:back) = reverse front in (back,[prev])
rotateACW ring@(prev:back,front) = (back,prev:front)

prop_invacw :: Ring Int -> Property
prop_invacw r = invRing r ==> invRing (rotateACW r)

prop_cw_o_acw :: Ring Int -> Bool
prop_cw_o_acw r = r == rotateCW (rotateACW r)

prop_acw_o_cw :: Ring Int -> Bool
prop_acw_o_cw r = r == rotateACW (rotateCW r)

-- *Tables> test prop_invacw
-- OK, passed 100 tests.
-- *Tables> test prop_cw_o_acw
-- OK, passed 100 tests.
-- *Tables> test prop_acw_o_cw
-- OK, passed 100 tests.
\end{code}
Sometimes, we shall want to convert a ring back to a list,
noting our location in it:
\begin{code}

ringToList :: Ring a -> ([a],Int)
ringToList (_   ,[]   )  =  ([],0)
ringToList (back,front)  =  (reverse back++front,(length back)+1)

\end{code}

\newpage
\subsection{Partitioned Relational Association Lists}

Functions to invert and un-invert special relation table-pairs.

We have a type $T$ and a property $std:T \fun \Bool$.
We want to maintain mappings of the form $\tau : T \pfun \power T$.
However, we want to maintain an invariant that if $std x$,
then $std y$ is true for all $y \in \tau(x)$.
We want to represent this as two tables:
\begin{eqnarray*}
   \tau_1 &:& T\!|_{std} \pfun \power(T\!|_{std})
\\ \tau_2 &:& T\!|_{\neg std} \pfun \power T
\end{eqnarray*}
However, we also want to invert these tables,
in which case the invariant now asserts that non-$std$ can only map
to non-$std$:
\begin{eqnarray*}
   \tau^{-1}_1 &:& T\!|_{std} \pfun \power T
\\ \tau^{-1}_2 &:& T\!|_{\neg std} \pfun \power (T\!|_{\neg std})
\end{eqnarray*}
\begin{code}
to :: d -> k -> (k,d)
d `to` k = (k,d)

invertTab :: (Ord k, Ord d) => [(k,[d])] -> [(d,[k])]
invertTab = invert []
 where
  invert itab []            =  itab
  invert itab ((x,as):tab)  =  invert (almrgnorm mrgnorm itab (map (to [x]) as)) tab

invertPartTabs :: (Ord k, Ord d)
            => (d -> Bool)
            ->   [(k,[d])] -> [(k,[d])]
            -> ( [(d,[k])] ,  [(d,[k])] )
invertPartTabs std sngltab multtab
 = minvertTab std (invertTab sngltab) [] multtab
 where
  minvertTab std istab imtab [] = (istab,imtab)
  minvertTab std istab imtab ((xs,avs):mtab)
   = minvertTab std istab' imtab' mtab
   where
     (as,ass) = partition std avs
     istab' = almrgnorm mrgnorm istab astoxs
     astoxs = map (to [xs]) as
     imtab' = almrgnorm mrgnorm imtab asstoxs
     asstoxs = map (to [xs]) ass

unInvertPartTabs :: (Ord d, Ord k)
            => (k -> Bool)
            -> [(d,[k])]
            -> [(d,[k])]
            -> ( [(k,[d]) ], [(k,[d])] )
unInvertPartTabs std snglitab multitab
 = muninvertTab std (invertTab multitab) [] snglitab
 where
  muninvertTab std imtab istab [] = (istab,imtab)
  muninvertTab std imtab istab ((a,xvs):stab)
   = muninvertTab std imtab' istab' stab
   where
     (xs,xss) = partition std xvs
     imtab' = almrgnorm mrgnorm imtab xstoa
     xstoa = map (to [a]) xss
     istab' = almrgnorm mrgnorm istab xsstoa
     xsstoa = map (to [a]) xs
\end{code}



\newpage
\subsection{Rooted DAGs}

We want to view theories as forming a DAG with many top
elements but all leading down to a common root (a \emph{rooted}-DAG or \textbf{rDAG}):
\begin{center}
\begin{tikzpicture}[>=stealth,->,shorten >=2pt,looseness=.5,auto]
 \matrix[matrix of nodes,
         nodes={rectangle,draw,minimum size=4mm},
         column sep={1cm,between origins},
         row sep={1cm,between origins}]
  {              &              &              & |(e)|e\ldots  \\
    |(c)|c\ldots &              & |(d)|d\ldots                 \\
                 & |(a)|a\ldots &              & |(b)|b\ldots  \\
                 &              & |(r)|r\ldots                 \\
  };
  \draw (a) -- (r) ;
  \draw (b) -- (r) ;
  \draw (c) -- (a) ;
  \draw (d) -- (a) ; \draw (d) -- (b) ;
  \draw (e) -- (d) ;
\end{tikzpicture}
\end{center}
We assume that every node has an identifier component
and is associated with some  extra data.
This could be rendered in pseudo-haskell as
\begin{verbatim}
let
  r = Root 'r' ...
  a = Node 'a' ... [r]
  b = Node 'b' ... [r]
  c = Node 'c' ... [a]
  d = Node 'd' ... [a,b]
  e = Node 'e' ... [d]
in Top [c,e]
\end{verbatim}
We shall assume that nodes contain identifiers
of type $I$, which are then associated independently with
their data using another indexing structure.
So all we implement here is
\begin{verbatim}
let
  r = Root 'r'
  a = Node 'a' [r]
  b = Node 'b' [r]
  c = Node 'c' [a]
  d = Node 'd' [a,b]
  e = Node 'e' [d]
in Top [c,e]
\end{verbatim}
\begin{center}
\begin{tikzpicture}[>=stealth,->,shorten >=2pt,looseness=.5,auto]
 \matrix[matrix of nodes,
         nodes={circle,draw,minimum size=4mm},
         column sep={1cm,between origins},
         row sep={1cm,between origins}]
  {        &        &        & |(e)|e  \\
    |(c)|c &        & |(d)|d           \\
           & |(a)|a &        & |(b)|b  \\
           &        & |(r)|r           \\
  };
  \draw (a) -- (r) ;
  \draw (b) -- (r) ;
  \draw (c) -- (a) ;
  \draw (d) -- (a) ; \draw (d) -- (b) ;
  \draw (e) -- (d) ;
\end{tikzpicture}
\end{center}
Given a node, we then want to easily produce the list of nodes
leading from it down to the root.
Also, we want the representation to be minimal w.r.t to transitivity,
i.e. if $c$ links to $a$ and $a$ links to $r$ then we do not need to
explicitly represent the link from $c$ to $r$.
This ensure that the lists described above can easily be constructed,
as we anticipate building such lists will occur frequently,
whereas changes to the rDAG will be relatively rare.

We want to construct an rDAG either by providing a root object,
or a new object with a list of objects to which it should link,
all of which must already be present, modulo some equivalence
relation.
\begin{eqnarray*}
   rDAG_{I} &\defs& \ldots
\\ root &:& I \fun rDAG_{I}
\\ add &:& I \fun \finset_1 I \fun rDAG_{I} \fun rDAG_{I}
\\ pre\_add~i~S~r &\defs& i \notin r \land \forall j \in S @ j \in r
\\ \_ \in \_ &:&   I \times rDAG_{I} \fun \Bool
\end{eqnarray*}
In addition we want to search for a object by identifier,
and return its node (as the sub-rDAG with it as the only top object):
\begin{eqnarray*}
   search &:& I \fun rDAG_{I} \fun [rDAG_{I}]
\\ i \in r &\equiv& search~i~r \neq null
\end{eqnarray*}
Given a rDAG we want to return all the paths to the root,
topologically sorted into a single list.
\begin{eqnarray*}
   stack &:& rDAG_{I} \fun I^+
\end{eqnarray*}

\newpage
\subsubsection{rDAG Datatype}

Considering all of the above we now design our datatype.

An rDAG over identifier $I$ ($rDAG_I$)
\begin{code}
data RDAG i
\end{code}
is either:
\begin{itemize}
  \item a root node, containing an element of type $I$:
\begin{code}
 = DRoot i
\end{code}
  \item
    or a non-root node, containing an element of type $I$,
    along with a non-empty list of immediate descendant rDAGs,
    and an annotation giving the length of the longest
    path to the root%
    \footnote{Simplifies topological sort}%
    .
\begin{code}
 | DNode i [RDAG i] Int
\end{code}
  \item or a list of top rDAG nodes:
\begin{code}
 | DTop [RDAG i]
\end{code}
\end{itemize}
First, a way to view rDAGs over $I$:
\begin{code}
instance Show i => Show (RDAG i) where
  show r = showRDAG 0 r

showRDAG ind (DRoot i) = "\n" ++ indent ind ++ "ROOT " ++ show i
showRDAG ind (DNode i rs h)
  = "\n" ++ indent ind ++ "Node@" ++ show h ++ " "++ show i
     ++ ( concat $ map (showRDAG (ind+1)) rs )

showRDAG ind (DTop rs)
 = unlines $ map (showRDAG ind) rs
\end{code}

An alternative look that exposes structure a bit more:
\begin{code}
showRDStruct :: Show i => RDAG i -> String
showRDStruct (DRoot i) = "\nROOT = "++show i
showRDStruct (DNode i deps h)
 = "\nNODE: "++show i++" -> "++show (map rdId deps)++", h="++show h
 ++ concat (map showRDStruct deps)
showRDStruct (DTop tops)
 = "TOP = "++show (map rdId tops) ++ concat (map showRDStruct tops)
\end{code}


\newpage
\subsubsection{rDAG Analysis}

Getting the rDAG ``top names'':
\begin{code}
rdNames :: RDAG i -> [i]
rdNames (DRoot r) = [r]
rdNames (DNode n _ _) = [n]
rdNames (DTop rs) = map rdName rs
\end{code}

Getting the rDAG ``name'' (if it has a unique top):
\begin{code}
rdName :: RDAG i -> i
rdName (DRoot r) = r
rdName (DNode n _ _) = n
rdName (DTop [r]) = rdName r
rdName (DTop _) = error "Tables.rdName: multi-DTop has no name"
\end{code}

We have a simple rDAG equivalence based on root and node names:
\begin{code}
eqvRDAG :: Eq i => RDAG i -> RDAG i -> Bool
eqvRDAG (DRoot r1) (DRoot r2) = r1 == r2
eqvRDAG (DNode r1 _ _) (DNode r2 _ _) = r1 == r2
eqvRDAG _ _ = False
\end{code}

Also, a way to extract the height:
\begin{code}
rdHeight :: RDAG i -> Int
rdHeight (DRoot _)      =  0
rdHeight (DNode _ _ h)  =  h
rdHeight (DTop tops)    =  pmaxima $ map rdHeight tops

rdHOrd :: RDAG i -> RDAG i -> Ordering
rdHOrd r1 r2 = compare (rdHeight r1) (rdHeight r2)
\end{code}


We want to search by name
and get the relevant sub-rDAG, if it exists.
We will in fact generalise to searching a list of names
to get a list of rDAGs
\begin{eqnarray*}
   search &:& I \fun rDAG_{I} \fun [rDAG_{I}]
\\ search &:& I^* \fun rDAG_{I} \fun (rDAG_{I})^*
\end{eqnarray*}
\begin{code}
rdSearch :: Eq i => [i] -> RDAG i -> [RDAG i]

rdSearch ids root@(DRoot r)
 | r `elem` ids  =  [root]
 | otherwise     =  []

rdSearch ids node@(DNode n subn _)
 | n `elem` ids  = [node]
 | otherwise     = concat $ map (rdSearch ids) subn

rdSearch ids (DTop tops)
 = nubBy eqvRDAG $ concat $ map (rdSearch ids) tops
\end{code}

\newpage
Pruning maintains transitive non-redundancy,
by eliminating any descendants whose parents are already present.
\begin{code}
rdPrune :: Eq i => [RDAG i] -> [RDAG i]
rdPrune nodes
 = prune1 nodes `intsct` (reverse $ prune1 $ reverse nodes)
 where
    intsct = intersectBy eqvRDAG

   --prune1 :: Eq i => [RDAG i] -> [RDAG i]
    prune1 [] = []
    prune1 (node:nodes)
     | notsubnode  =  node:prune1 nodes
     | otherwise   =  prune1 nodes
     where
       asubnode = rdSearch [rdName node]
       notsubnode = null $ concat $ map asubnode nodes
-- end rdPrune
\end{code}


We want to build a stacked context for a node,
which is a sequence leading from it to the root,
through all its downstream nodes,
i.e., we include all parallel paths,
and maintain  order.
\begin{eqnarray*}
   stack &:& rDAG_I \fun I^+
\end{eqnarray*}
In effect we do a topological sort of the rDAG elements whose top
is the note of concern.
We shall consider a generalisation
that returns each element tagged with its height.
\begin{eqnarray*}
   stack &:& rDAG_I \fun (\Nat \times I )^+
\end{eqnarray*}
\begin{code}
rdStack :: Eq i => RDAG i -> [(Int,i)]
rdStack r = nub $ sortBy hord $ stk r
 where stk (DRoot i)         =  [(0,i)]
       stk (DTop tops)       =  stack tops
       stk (DNode i subn h)  =  (h,i) : (stack subn)

       stack rs = concat $ map stk rs

       sameelem (_,i1) (_,i2) = i1 == i2

       hord (h1,i1) (h2,i2)
               | h1 <  h2  =  GT
               | h1 >  h2  =  LT
               | i1 == i2  =  EQ
               | otherwise =  LT -- compare i2 i1
-- end rdStack
\end{code}
Now, a stratification function
that returns lists of lists of elements at the same level:
\begin{eqnarray*}
   stratify &:& rDAG_I \fun (I^+)^+
\end{eqnarray*}
\begin{code}
rdStratify :: Eq i => RDAG i -> [[i]]
rdStratify = hstratify . rdStack

hstratify
 = reverse . hstrat (-1) [] []
 where
   hstrat _  [] ees []  =  ees
   hstrat _  es ees []  =  es:ees
   hstrat ch es ees ((h,i):rest)
    | h == ch  = hstrat ch (i:es) ees rest
    | otherwise  =  hstrat h [i] ees' rest
    where
      ees' | null es    =  ees
           | otherwise  =  (reverse es):ees

rdNamesOf :: Eq i => RDAG i -> [i]
rdNamesOf = concat . reverse . rdStratify
\end{code}

Given an identifier, and RDAG,
it would be nice to know its immediate descendants:
\begin{eqnarray*}
  desc &:& I \fun RDAG_I \fun I^*
\end{eqnarray*}
\begin{code}
rdDesc :: Eq i => i -> RDAG i -> [i]
rdDesc i rdag
           = concat
             $ map (map rdId . rdAncs)
             $ rdSearch [i] rdag

rdAncs :: RDAG i -> [RDAG i]
rdAncs (DNode _ nds _) = nds
rdAncs _ = []

rdId :: RDAG i -> i
rdId (DRoot i)      =  i
rdId (DNode i _ _)  =  i
rdId (DTop _)       =  undefined
\end{code}


Given a node id, it can be useful to know all
its relatives (ancestors and descendants).
We ensure that descendants are returned in height order,
highest first.
\begin{code}
rdAncestors i   = fst . rdRelatives i
rdDescendants i = snd . rdRelatives i

rdRelatives :: Ord i => i -> RDAG i -> ([i],[i])
rdRelatives _ (DRoot _)  = ([],[])
rdRelatives _ (DNode _ _ _)  = ([],[])
rdRelatives i (DTop tops)
 = (ancs, nub $ map snd $ reverse $ sort rawrels)
 where
   (ancs,rawrels) = relMrg $ map (relsrch i []) tops

   relMrg = foldr relmrg norel
   norel = ([],[])
   (a1,d1) `relmrg` (a2,d2) = (nub (a1++a2), (d1++d2) )

   -- relsrch from top, looking for i, recording path followed
   -- relsrch :: t -> [t] -> RDAG t -> ([t],[(Int,t)])
   relsrch i ipath (DRoot r)
    | i == r     =  (ipath,[])
    | otherwise  =  norel
   relsrch i ipath (DNode j deps _)
    | i == j     =  (ipath,concat $ map rdStack $ deps)
    | otherwise  =  relMrg $ map (relsrch i (j:ipath)) deps
   relsrch _ _ (DTop _) = norel
\end{code}

When adding new links they can always be done to/from
any non-relative node:
\begin{code}
rdNonRelatives i rdag = rdNamesOf rdag \\ (i:(ancs++descs))
 where (ancs,descs) = rdRelatives i rdag
\end{code}


\newpage
\subsubsection{rDAG Construction}

The key principle here is that every RDAG at the top-level
is represented by a \texttt{DTop} constructor (even a root-only graph).
The root-node only appears in the DTop when it is the only node
in the graph.

We have two functions, \texttt{rdAdd} and \texttt{rdExtend} designed for internal use,
that add a new node in the first case, and a link in the second,
reporting various errors.
\begin{code}
data RDAGError i
 = RDAGOK
 | RDAGErr String i
 deriving (Eq,Show)

type RDAGRes i = Either (RDAGError i) (RDAG i)
\end{code}
We define a monad instance for this
\begin{code}
-- IMPORTANT: INCOMPATIBLE LIBRARY CHANGES
-- Data.Either has a Monad instance from 7.x.x onwards
#if __GLASGOW_HASKELL__ < 700
instance Monad (Either (RDAGError i)) where
  return r = Right r
  (Left e)  >>= _   =   Left e
  (Right d) >>= f   =   f d
#endif
\end{code}


The general purpose builder function is \texttt{rdUpdate} that add nodes
and links as required, by calling \texttt{rdAdd} and \texttt{rdExtend}.


Now, the main builder functions.
\begin{code}
rdROOT :: i -> RDAG i
rdROOT i = DTop [DRoot i]
\end{code}
Code to return the root is also useful:
\begin{code}
rdGetRoot :: RDAG i -> RDAG i
rdGetRoot r@(DRoot _)         =  r
rdGetRoot (DNode _ (sn:_) _)  =  rdGetRoot sn
rdGetRoot (DTop (top:_))      =  rdGetRoot top
rdGetRoot rdag = error "rdGetRoot - can't find root"
\end{code}


\begin{eqnarray*}
   add &:& I \fun rDAG_I \fun rDAG_I
\\ pre\_add~i~r &\defs& i \notin r
\end{eqnarray*}
The code is more liberal,
but also reports back if the new node has a name clash,
or if requested names were unavailable.
This algorithm is designed to be thorough
and correct, rather than fast.
\begin{code}
rdAdd :: (Eq i,Show i) => i -> RDAG i -> RDAGRes i
rdAdd i top@(DTop tops)
 | nameclash      =  err "already present" i
 | otherwise      =  return $ DTop $ rdPrune $ add (DNode i [root] 1) tops
 where
   nameclash = not $ null $ rdSearch [i] top
   root = rdGetRoot top
   add node [DRoot _] = [node]
   add node tops      = node:tops

   err s i = Left $ RDAGErr s i

rdAdd i r = Left $ RDAGErr "Not a DTop!" i
\end{code}

\newpage
Once an element is in, we may wish to modify it
to point to other elements already present
and not a parent of oneself:
\begin{eqnarray*}
   link &:& I \fun I \fun RDAG_{I} \fun RDAG_{I}
\\ pre\_link~p~c~r &\defs& p \neq c \land p \in r \land p \neq root(r) \land c \in r \land c \notin ancs(p)
\end{eqnarray*}
\begin{code}
rdLink :: (Eq i,Show i) => i -> i -> RDAG i -> RDAGRes i
rdLink pid chid r
 | pid == chid        = err "Cannot link to itself" pid
 | null psrch         = err "Parent not present" pid
 | isroot pnode      = err "Root cannot be parent" pid
 | null chsrch        = err "Child not present" chid
 | not $ null pcsrch  = err "Child is parent" chid
 | not $ null cpsrch  = return r
 | otherwise          = return $ update pid pe newsub newh r
 where

  err s i = Left $ RDAGErr s i

  psrch = rdSearch [pid] r
  (pnode:_) = psrch

  root = rdGetRoot r
  isroot (DRoot _) = True
  isroot _ = False

  chsrch = rdSearch [chid] r
  cpsrch = rdSearch [chid] pnode
  (chnode:_) = chsrch
  pcsrch = rdSearch [pid] chnode
  (DNode pe subn ph) = pnode

  newsub = adjroot $ filter (not . isroot) (chnode:subn)
  adjroot [] = [root]
  adjroot subs = subs

  newh =  max ph (rdHeight chnode + 1)

  update tgtnm orige newsub newh r
   = u r
   where
     u (DTop tops) = DTop $ rdPrune $ (map u tops)
     u r@(DRoot _) = r
     u (DNode i sub h)
       | i == tgtnm  =  DNode orige newsub newh
       | otherwise    =  DNode i msub mh
       where
         msub = map u sub
         mh = (pmaxima $ map rdHeight msub)+1
\end{code}

\begin{code}
rdUpdate :: (Eq i,Show i) => i -> [i] -> RDAG i -> RDAGRes i
rdUpdate i deps rdag
 = case rdAdd i rdag of
    Left _  ->  dolinks i rdag deps
    Right rdag'  ->  dolinks i rdag' deps
 where
  dolinks i rdag [] = return rdag
  dolinks i rdag (dep:deps)
   = do rdag' <- rdLink i dep rdag
        dolinks i rdag' deps
\end{code}

It is also useful to output an RDAG as a list of tuples
indicating the immediate first level dependencies
of the whole graph, form the bottom upwards.
\begin{code}
rdToList :: Eq i => RDAG i -> [(i,[i])]
rdToList = map drop3rd . sortBy compare3rd . nub . rdlist
 where
  rdlist (DRoot i) = [(i,[],0)]
  rdlist (DNode i subn h)
                      = (i,map rdId subn,h):(concat $ map rdlist subn)
  rdlist (DTop tops) = concat $ map rdlist tops
  compare3rd (_,_,a) (_,_,b) = compare a b
  drop3rd (a,b,_) = (a,b)
\end{code}

The converse of this is code to construct an RDAG from
such a list of tuples:
\begin{code}
rdFromList :: (Eq i, Show i) => [(i,[i])] -> RDAGRes i
rdFromList [] = error "rdFromList: emptylist"
rdFromList ((r,[]):rest)
 = rdFrom (rdROOT r) rest
 where

  rdFrom rdag [] = return rdag

  rdFrom rdag ((n,deps):rest)
    = do rdag' <- rdUpdate n deps rdag
         rdFrom rdag' rest

rdFromList ((_,(d:_)):_) = Left $ RDAGErr "rdFromList: root has deps" d
\end{code}



Given a list of identifiers, build a linear rDAG from them
(top down):
\begin{code}
linRdFromList :: (Eq i, Show i) => [i] -> RDAGRes i
linRdFromList [] = error "linRdFromList: empty list"
linRdFromList [i] = return $ rdROOT i
linRdFromList (i:rest@(j:_))
 = do rdag <- linRdFromList rest
      rdUpdate i [j] rdag
\end{code}

\newpage
\subsubsection{rDAG Deconstruction}

Remove a top node:
\begin{code}
rdRemoveTop :: Eq i => i -> RDAG i -> RDAG i
rdRemoveTop i rdag@(DTop [DNode i' rs h])
 | i == i'  = DTop rs
rdRemoveTop i (DTop rs) = DTop (rdRem i rs)
 where
   rdRem :: Eq i => i -> [RDAG i] -> [RDAG i]
   rdRem _ [] = []
   rdRem i (r@(DNode i' rs' h):rs)
    | i == i'  =  rs'++rs
   rdRem i (r:rs)  =  r : rdRem i rs
rdRemoveTop _ rdag = rdag
\end{code}

\newpage
\subsubsection{rDAG examples}
Temporary test example (that at the start of the rDAG section):
\begin{center}
\begin{tikzpicture}[>=stealth,->,shorten >=2pt,looseness=.5,auto]
 \matrix[matrix of nodes,
         nodes={rectangle,draw,minimum size=4mm},
         column sep={1cm,between origins},
         row sep={1cm,between origins}]
  {              &              &              & |(e)|e\ldots  \\
    |(c)|c\ldots &              & |(d)|d\ldots                 \\
                 & |(a)|a\ldots &              & |(b)|b\ldots  \\
                 &              & |(r)|r\ldots                 \\
  };
  \draw (a) -- (r) ;
  \draw (b) -- (r) ;
  \draw (c) -- (a) ;
  \draw (d) -- (a) ; \draw (d) -- (b) ;
  \draw (e) -- (d) ;
\end{tikzpicture}
\end{center}
\begin{verbatim}
r = DRoot "r"
a = DNode "a" [r] 1
b = DNode "b" [r] 1
c = DNode "c" [a] 2
d = DNode "d" [a,b] 2
e = DNode "e" [d] 3
top1 = DTop [c,e]
\end{verbatim}
Another hairy example:
\begin{center}
\begin{tikzpicture}[>=stealth,->,shorten >=2pt,looseness=.5,auto]

 \matrix[matrix of nodes,
         nodes={rectangle,draw,minimum size=4mm},
         column sep={1cm,between origins},
         row sep={1cm,between origins}]
  {              & |(g)|m\ldots &               \\
    |(e)|k\ldots &              & |(f)|l\ldots  \\
    |(c)|h\ldots &              & |(d)|j\ldots  \\
    |(a)|f\ldots &              & |(b)|g\ldots  \\
                 & |(r)|r\ldots                 \\
  };
  \draw (a) -- (r) ;
  \draw (b) -- (r) ;
  \draw (c) -- (a) ;
  \draw (d) -- (b) ;
  \draw (e) -- (c) ;
  \draw (e) -- (b) ;
  \draw (f) -- (d) ;
  \draw (f) -- (a) ;
  \draw (g) -- (e) ;
  \draw (g) -- (f) ;
\end{tikzpicture}
\end{center}
\begin{verbatim}
f = DNode "f" [r] 1
g = DNode "g" [r] 1
h = DNode "h" [f] 2
j = DNode "j" [g] 2
k = DNode "k" [h,g] 3
l = DNode "l" [f,j] 3
m = DNode "m" [k,l] 4
top2 = DTop [m]
\end{verbatim}

\newpage
\subsection{Finding Pairings}

In effect, when matching $k$ un-ordered patterns ($p_i$)
against $n$ un-ordered tests ($t_j$), we get a 2-dim grid showing which
tests and pattern match:
$$
\begin{array}{c|c|c|c|}
    & t_1 & \ldots & t_n
\\\hline
 p_1 &  \beta_{11}  & \ldots   & \beta_{1n}
\\\hline
 \vdots & \vdots   & \ddots   & \vdots
\\\hline
 p_k &  \beta_{k1}  &  \ldots  & \beta_{kn}
\\\hline
\end{array}
,\qquad n \geq k
$$
where $\beta_{ij}$ can be a valid binding, or a failure indicator.
If any row has only failure indicators,
then the entire match fails.
Otherwise, we know a solution is possible,
so we then try to construct a list of valid bindings where every pattern
occurs in exactly one binding, and every test in at most one.
In effect we are trying to find a setof ($p_i,t_j$) pairings
such that each is a valid match, and every $p_i$ occurs exactly once,
and each $t_j$ at most once.

Key heuristic: choose a valid binding from a row
with fewest valid bindings.
We may have several such rows, each with more than one binding,
in which case we choose a binding with the fewest valid bindings
in \emph{its column}.

We implement this in the abstract, with a matrix of \texttt{a}s,
and a \texttt{Valuation} that maps those to integers, with 0 denoting
a fail or null outcome.
\begin{code}
type Mat a = [[a]] -- we number from 1..upwards
type Valuation a = a -> Int
type Row = Int
type Col = Int

getIx :: Int -> [a] -> a
getIx i a = a!!(i-1)
\end{code}
We have an example matrix:
$$
\begin{array}{|c|c|c|c|}
  \hline
 1 & 2 & 0 & 3
\\\hline
 0 & 4 & 5 & 0
\\\hline
 0 & 6 & 0 & 7
\\\hline
\end{array}
$$
\begin{code}
testMat = [[1,2,0,3]
          ,[0,4,5,0]
          ,[0,6,0,7]] :: [[Int]]
\end{code}
We want to be able access and remove rows and columns
\begin{code}
remIx :: Int -> [a] -> [a]
remIx i a = take (i-1) a ++ drop i a

getRow :: Mat a -> Row -> [a]
getRow m r = m!!(r-1)

remRow :: Row -> Mat a -> Mat a
remRow r m = remIx r m

getCol :: Mat a -> Col -> [a]
getCol m c = map (!!(c-1)) m

remCol :: Col -> Mat a -> Mat a
remCol c m = map (remIx c) m

showMat :: Show a => Mat a -> IO ()
showMat = putStrLn . unlines . map (concat . intersperse " , " . map show)
\end{code}
We want to compute the row and column occupancy:
$$
\begin{array}{|c|c|c|c||c}
  \hline
 1 & 2 & 0 & 3 & 3
\\\hline
 0 & 4 & 5 & 0 & 2
\\\hline
 0 & 6 & 0 & 7 & 2
\\\hline\hline
 1 & 3 & 1 & 2
\end{array}
$$
\begin{code}
pairR :: (a->b) -> a -> (a,b)
pairR f a = (a, f a)
rowOcc, colOcc  :: Mat Int -> [Int]
rowOcc m = map sum  m
colOcc m = foldr1 (zipWith (+)) m
rowNums = rowOcc testMat
colNums = colOcc testMat
\end{code}
We now need to find the rows with minimum occupancy
\begin{code}
minEntries :: Ord a => [a] -> [Int]
minEntries [] = []
minEntries (c1:cs)
 = mE c1 [1] 2 cs
 where
   mE c is _ [] = reverse is
   mE c is i (v:vs)
    | c >  v     =  mE v [i]    i' vs
    | c == v     =  mE c (i:is) i' vs
    | otherwise  =  mE c is     i' vs
    where i' = i+1
\end{code}
Given those rows, we want to find the occupied
columns with minimal occupancy, noting both row and column indices
\begin{code}
possColumns :: Mat Int -> [Row] -> [(Row,Col)]
possColumns m bestixs
  = concat $ map (mrg . pairR (cols 1 . getRow m)) bestixs
  where
    cols _ [] = []
    cols i (v:vs)
      | v == 0  =  cols i' vs
      | otherwise  =  i:cols i' vs
      where i' = i+1
    mrg (r,cs) = map (pair r) cs
    pair r c = (r,c)
\end{code}
Then for each row/column pair we find the column occupancy,
and get the minimums of those
\begin{code}
bestColOcc :: [Int]        -- occupancy of each column
           -> [(Row,Col)]  -- candidate match coordinates
           -> [(Int,(Row,Col))] -- column occupancy for each match (sorted)
bestColOcc cs = sort . map (twist . pairR (lkp cs . snd))
 where
   lkp cs c = cs!!(c-1)
\end{code}
\newpage
We can currently choose greedily, given a sorted list
\begin{code}
type PairChoice = [(Int,(Row,Col))] -> (Row,Col)

greedyRC :: PairChoice
greedyRC = snd . head
\end{code}
We put this all together as a single step
\begin{code}
findPairingStep :: Valuation a
          -> PairChoice
          -> Mat a
          -> ( (Row,Col)  -- chosen location
             ,Mat a       -- Matrix with chosen row/column removed
             )
findPairingStep eval choose  matrix
 = ( (r,c), remRow r $ remCol c matrix )
 where
   absmat = map (map eval) matrix
   bestixs = minEntries absmat
   candidates = possColumns absmat bestixs
   colocc = bestColOcc (colOcc absmat) candidates
   (r,c) = choose colocc
\end{code}
We then construct a top-level that iterates findPairingStep
until done, and then returns a list of the selected matrix entries
\begin{code}
findPairings :: Valuation a
              -> PairChoice
              -> Mat a
              -> [a]
findPairings _ _ [] = []
findPairings eval choose matrix
 = let
     ((r,c),matrix') = findPairingStep eval choose matrix
   in (getIx c $ getIx r matrix) : findPairings eval choose matrix'
\end{code}
