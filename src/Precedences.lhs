\section{Precedences}

\begin{code}

module Precedences where
import Tables

import Text.ParserCombinators.Parsec.Expr

\end{code}

This module defines precedence information for use by the
ASCII/\LaTeX\ parsers and pretty-printers.

\subsection{Precedences}

We need to define precedences for binary operators. In general
expression operators will bind tighter than predicate
operators, with user-defined language operators in between
(e.g.):
$$\begin{array}{ccc}
  \mbox{tightest} && \mbox{loosest}
\\ {}^{}~*~+ & :=~& \refinedby~;~\lor~\land
\\ \mbox{Expr} &\mbox{Lang} & \mbox{Pred}
\end{array}$$
We define precedences over non-negative ranges:
\begin{code}

precTightest  = 1000 :: Int

precTightExpr =  290 :: Int
precMidExpr   =  250 :: Int
precLooseExpr =  210 :: Int

precTightLang =  190 :: Int
precMidLang   =  150 :: Int
precLooseLang =  110 :: Int

precTightPred =   90 :: Int
precMidPred   =   50 :: Int
precLoosePred =   10 :: Int

precLoosest   =    0 :: Int

\end{code}
\newpage
And hard code these :
\begin{code}

equalName = "="
neqName   = "/="

equivName   = "=="
impName     = "=>"
rbyName     = "|="
orName      = "\\/"
ndcName     = "|~|"
andName     = "/\\"
dsgnName    = "|-"
compName    = ";"
notName     = "~"
lcondName   = "<|"
rcondName   = "|>"
psunionName = "U"
psinName    = "IN"

exprBinGen = "E@" -- generic names for unknown expr binops
predBinGen = "P@" -- generic names for unknown pred binops
langBinGen = "L@" -- generic names for unknown language binops

hardPrecs
 = lbuild [ -- Expressions
                        -- 290
            ( exprBinGen , 280 )  -- expression application is tight
          , ( equalName  , 220 )  -- equality is fairly loose
          , ( neqName    , 220 )
                        -- 210
            -- Language
                        -- 190
          , ( langBinGen , 150 )  -- default language precedence
                        -- 110
            -- Predicates
                        --  90
          , ( notName    ,  90 )  -- negation is tight
          , ( predBinGen ,  85 )  -- predicate application is tight
          , ( psunionName,  85 )
          , ( psinName   ,  83 )
          , ( andName    ,  80 )
          , ( lcondName  ,  70 )
          , ( rcondName  ,  70 )
          , ( orName     ,  60 )
          , ( ndcName    ,  60 )
          , ( dsgnName   ,  55 )
          , ( compName   ,  50 )
          , ( rbyName    ,  40 )
          , ( impName    ,  30 )
          , ( equivName  ,  20 )  -- equivalence is loose
                        --  10
          ]

opPrec :: Int -> String -> Int
opPrec def op
  = case tlookup hardPrecs op of
      Nothing   ->  def
      (Just p)  ->  p

\end{code}

We provide tables mapping appropriate names to precedences,
types, and behaviours
\begin{code}

instance Show Assoc where
 show AssocNone = "AssocNone"
 show AssocLeft = "AssocLeft"
 show AssocRight = "AssocRight"

type Precs = (Int,Assoc)

precOf ptbl name
 = case tlookup ptbl name of
     Nothing       ->  -1
     (Just (p,_))  ->  p

\end{code}
