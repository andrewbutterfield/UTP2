module Test where
import Utilities
import Data.List
import Numeric

ex = [ ('a',[4,5,6,7,12,13,14,15])
     , ('b',[2,3,6,7,10,11,14,15])
     , ('c',[1,3,5,7,9,11,13,15])
     ]
     
inv kds = inv' [] kds

inv' dks [] = dks
inv' dks ((k,ds):kds) = inv' (inv'' dks k ds) kds

inv'' dks k [] = dks
inv'' dks k (d:ds) = inv'' (ins dks d k) k ds

ins [] d0 k0 = [(d0,[k0])]
ins dks@(hd@(d,ks):dks1) d0 k0
 | d0 < d   =  (d0,[k0]):dks
 | d0 == d  =  (d,lnorm (k0:ks)):dks1
 | otherwise  =  hd:ins dks1 d0 k0
 
img dks = img' [] dks

img' ksds [] = ksds
img' ksds ((d,ks):dks1) = img' (ins ksds ks d) dks1

divvy _      []      =  []
divvy [d]    ks      =  map (\k->(d,k)) ks
divvy (d:ds) (k:ks)  =  (d,k):divvy ds ks

alloc ksds = alloc' $ concat $ map (uncurry divvy) ksds

alloc' [] = []
alloc' ((k,d):kds) = ins (alloc' kds) k d

ex2 = [ ('a',[1,2]) , ('b',[1,2]) ]

infixr 1 ==> 
b1 ==> b2  =  (not b1) || b2

rmanalysis vp   
           x1p  
           xsp 
           vt 
           x1t 
           xst
 = let
    vplesst = vp \\ vt
    vtlessp = vt \\ vp
    vpt     = vt `intersect` vp
    svp = length vp
    sx1p = length x1p
    sxsp = length xsp
    svt = length vt
    sx1t = length x1t
    sxst = length xst
    splesst = length vplesst
    stlessp = length vtlessp
    spt = length vpt
   in do putStrLn "\ninputs:"
         display "V_p" vp
         display "X1_p" x1p
         display "XS_p" xsp
         display "V_t" vt
         display "X1_t" x1t
         display "XS_t" xst
         putStrLn "\nset calcs:"
         display "V_p\\V_t" vplesst
         display "V_t\\V_p" vtlessp
         display "V_p /\\ V_t" vpt
         putStrLn "\nassertions:"

         props <- sequence
                   [ 
                     assert "X1_p <= X1_t"  
                            (sx1p <= sx1t)
                   , assert "X1_p =  X1_t /\\ XS_t >= 1 ==> XS_p >= 1"  
                            (sx1p == sx1t && sxst >= 1 ==> sxsp >= 1)
                   , assert "X1_p <  X1_t ==> XS_p >= 1"
                            (sx1p < sx1t ==> sxsp >= 1)                    
                   , assert "V_p - X1_p <=  V_p /\\ V_t"
                            (svp - sx1t <= spt)
                   ]
         if and props
          then putStrLn "\nALL OK\n"
          else putStrLn "\nWE HAVE A PROBLEM\n"
         putStrLn "Other tests - not mandatory"
         sequence [ assert "X1_p <= V_p\\V_t"
                           (sx1p <= splesst)
                  , assert "X1_p <  V_p\\V_t ==> XS_p >= 1"
                           (sx1p <= splesst ==> sxsp >= 1)
                  , assert "X1_t <= V_t\\V_p"
                           (sx1t <= stlessp)
                  , assert "X1_t <  V_t\\V_p ==> XS_t >= 1"
                           (sx1t <= stlessp ==> sxst >= 1)
                  ]
         

         putStrLn "\n\n"
 where
   display nm list
    = putStrLn (nm++" = "++show list++", |"++nm++"| = "++show (length list))
   assert descr prop
    = do putStrLn (showB prop ++ "          "++descr)
         return prop
   showB True  = "true "
   showB False = "FALSE"
   
hex n = showHex n ""

uniExample = "\8709 = A \8745 \ESC[9mA\x35e\ESC[0m"

writeUFile = writeFile "unicode.txt" uniExample

readUFile
 = do utxt <- readFile "unicode.txt"
      putStrLn utxt

-- dealing with strings using read- and show-like functions
-- results because read and show are not inverses for strings
