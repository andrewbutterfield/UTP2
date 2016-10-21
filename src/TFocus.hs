module TestFocus where

import Datatypes
import Focus

ppfp fp
 = do putStrLn $ showPFocus fp
      putStrLn ""

p = And [ Or [ FALSE
             , Obs $ Prod [ T
                          , Num 3
                          , App "f" $ Num 0
                          ]  
             ] 
        , TRUE
        , Imp (Imp FALSE TRUE) TRUE 
        ]

fp     = setPFocus          p
fp1    = downPFocus 1 fp
fp12   = downPFocus 2 fp1
fp123  = downPFocus 3 fp12
fp1231 = downPFocus 1 fp123
fp123' = upPFocus           fp1231
fp12'  = upPFocus           fp123'
fp1'   = upPFocus           fp12'
fp'    = upPFocus           fp1'

fp3   = downPFocus 3 fp
fp31  = downPFocus 1 fp3
fp311 = downPFocus 1 fp31
fp312 = downPFocus 2 fp31
fp32  = downPFocus 2 fp3

q = Imp (Imp (Pvar "P1") (Pvar "N1")) (Imp (Pvar "N2") (Pvar "P2"))
fq   = setPFocus          q
fq1  = downPFocus 1 fq
fq2  = downPFocus 2 fq
fq11 = downPFocus 1 fq1
fq12 = downPFocus 2 fq1
fq21 = downPFocus 1 fq2
fq22 = downPFocus 2 fq2

fq1'  = upPFocus fq11
fq1'' = upPFocus fq12
fq2'  = upPFocus fq21
fq2'' = upPFocus fq22

fq'    = upPFocus fq1'
fq''   = upPFocus fq1''
fq'''  = upPFocus fq2'
fq'''' = upPFocus fq2''

e = And
     [
       Obs $ Bin "<" 0              -- 1
                 (Num 0)                             -- 1.1
                 (Var "i")                           -- 1.2
     , Defd $ Equal                 -- 2
              (Num 3)                                  -- 2.1
              (Var "x")                                -- 2.2
     , TypeOf (Seq [Var "b"])                               -- 3.1
              $ Tseq B  
     , Obs $ Setc 0 (QVars ["e"] [])  -- 4
                    (Obs (Bin ">" 0 (Num 9) $ Var "e") )  -- 4.1
                    (App "sqr"                                 -- 4.2
                       $ Var "e")                              -- 4.2.1
     ]
fe  = setPFocus e
fe1 = downPFocus 1 fe
fe2 = downPFocus 2 fe
fe3 = downPFocus 3 fe
fe4 = downPFocus 4 fe
fe11 = downPFocus 1 fe1
fe12 = downPFocus 2 fe1
fe21 = downPFocus 1 fe2
fe22 = downPFocus 2 fe2
fe31 = downPFocus 1 fe3
fe32 = downPFocus 2 fe3
fe41 = downPFocus 1 fe4
fe411 = downPFocus 1 fe41
fe412 = downPFocus 2 fe41
fe42 = downPFocus 2 fe4
fe421 = downPFocus 2 fe42

f = Obs $ Bin "<" 0 
              (Num 0)    -- 1
              (Var "i")  -- 2
ff  = setPFocus f
ff1 = downPFocus 1 ff
ff2 = downPFocus 2 ff

g = Defd $ Bin "<" 0     -- 1
               (Num 0)    -- 1.1
               (Var "i")  -- 1.2
fg  = setPFocus g
fg1 = downPFocus 1 fg
fg11 = downPFocus 1 fg1
fg12 = downPFocus 2 fg1

h = TypeOf (Bin "<" 0       -- 1
                 (Num 0)     -- 1.1
                 (Var "i"))  -- 1.2
            Tarb
                
fh  = setPFocus h
fh1 = downPFocus 1 fh
fh11 = downPFocus 1 fh1
fh12 = downPFocus 2 fh1

eq = Obs $ Equal
            (Bin "+" 0 (Var "x") (Var "y") )
            (Bin "+"  0 (Var "y") (Var "x") )
feq = setPFocus eq
feq1 = downPFocus 1 feq
feq11 = downPFocus 1 feq1
feq12 = downPFocus 2 feq1
feq2 = downPFocus 2 feq
feq21 = downPFocus 1 feq2
feq22 = downPFocus 2 feq2


