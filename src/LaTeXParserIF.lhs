\section{\LaTeX\ Parser Interface}

\begin{code}
module LaTeXParserIF where
import Tables
import Datatypes
import Proof
import LaTeXSetup
-- import FromZ
import Text.ParserCombinators.Parsec.Expr
\end{code}

\subsection{\LaTeX\ Parser Main}

\begin{code}
utpParser theories txt
 = readZSpec params txt
 where params = Contexttables{ prectable  = [] -- need to decide where precedence lives
                             , vartable  = [] -- need to get obs vars.
                             , typetable = map types theories
                             , predtable = map preds theories
                             , ltxtable = defaultLaTeXLayout
                             }
\end{code}

A debug parser:
\begin{code}
utpParserDebug theories txt
 = readZSpecDebug params txt
 where params = Contexttables{ prectable  = [] -- need to decide where precedence lives
                             , vartable  = [] -- need to get obs vars.
                             , typetable = map types theories
                             , predtable = map preds theories
                             , ltxtable = defaultLaTeXLayout
                             }
\end{code}

\subsection{old deprecated stuff}

\begin{code}
latexParser
 :: [Trie (Int,Assoc)] -- prec: builtin operator precedence and associativity table
    -> [Trie Type]   -- obs:  theory observation variables (set)
    -> [Trie Type]   -- typ: type-table stack
    -> [Trie Pred]   -- preds: named predicates stack
    -> String        -- file: LaTeX source file-name
    -> String        -- text: LaTeX file contents
    -> Either String Theory --  Left msg : error with message string
                                  --  Right pc : success with proof context
latexParser prec obs typ preds file text
 = readZSpec params text
 where params = Contexttables{ prectable = prec
                              , vartable=obs
                              , typetable=typ
                              , predtable=preds
                              , ltxtable=defaultLaTeXLayout
                              }
\end{code}
