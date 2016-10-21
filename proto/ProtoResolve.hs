module ProtoResolve where
import Utilities

inv :: (Ord k, Ord d) => [(k,[d])] -> [(d,[k])]
inv kds = inv' [] kds

inv' dks [] = dks
inv' dks ((k,ds):kds) = inv' (inv'' dks k ds) kds

inv'' dks k [] = dks
inv'' dks k (d:ds) = inv'' (ins dks d k) k ds

img :: (Ord d, Ord k) => [(d,[k])] -> [([k],[d])]
img dks = img' [] dks

img' ksds [] = ksds
img' ksds ((d,ks):dks1) = img' (ins ksds ks d) dks1

alloc :: (Ord k, Ord d) 
      => ([k] -> [d] -> [(k,d)]) -> [([k],[d])] -> [(k,[d])]
alloc divvy ksds = fins $ concat $ map (uncurry divvy) ksds

resolve :: (Ord k, Ord d) 
        => ([k] -> [d] -> [(k,d)]) -> [(k,[d])] -> [(k,[d])]
resolve divvy  = alloc divvy . img . inv

-- allocate round-robin among the keys
rrobin :: [k] -> [d] -> [(k,d)]
rrobin keys dats
 = shr keys dats
 where
  shr  _      []     =  []
  shr []     ds      =  shr keys ds
  shr (k:ks) (d:ds)  =  (k,d):shr ks ds

-- allocate one per key with last takes all
oneall :: [k] -> [d] -> [(k,d)]
oneall _      []      =  []
oneall [k]    ds      =  map (\d->(k,d)) ds
oneall (k:ks) (d:ds)  =  (k,d):oneall ks ds

-- allocate all to first key
firstkey :: [k] -> [d] -> [(k,d)]
firstkey _     []      =  []
firstkey (k:_) ds      =  map (\d->(k,d)) ds


ins :: (Ord k, Ord d) => [(d,[k])] -> d -> k -> [(d,[k])]
ins [] d0 k0 = [(d0,[k0])]
ins dks@(hd@(d,ks):dks1) d0 k0
 | d0 < d   =  (d0,[k0]):dks
 | d0 == d  =  (d,lnorm (k0:ks)):dks1
 | otherwise  =  hd:ins dks1 d0 k0
 
fins [] = []
fins ((k,d):kds) = ins (fins kds) k d

ex1 = [ ('a',[4,5,6,7,12,13,14,15])
      , ('b',[2,3,6,7,10,11,14,15])
      , ('c',[1,3,5,7,9,11,13,15])
      ]
ex2 = [ ('a',[1,2]) 
      , ('b',[1,2])
      ]
ex3 = [ (2,"4567CDEF")
      , (1,"2367ABEF")
      , (0,"13579BDF")
      ]
ex4 = [ (1,"12") 
      , (2,"12")
      ]
ex5 = [ ('a',[4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31])
      , ('b',[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31])
      , ('c',[1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31])
      ]
ex6 = [ (3,"89ABCDEF")
      , (2,"4567CDEF")
      , (1,"2367ABEF")
      , (0,"13579BDF")
      ]
ex7 = [ ('o',"AB") ]
    
