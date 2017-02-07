\section{\LaTeX\ Setup}

\begin{code}
module LaTeXSetup where
import Tables
import Data.Char
import Data.List
\end{code}

This module contains definitions used by the \LaTeX\ parser and
pretty-printer, with emphasis on those aspects that are
(potentially)
user-customisable.

\subsection{Translations}

We want to be able to translate \LaTeX\ in the following situations:
\begin{itemize}
  \item to/from an internal symbolic notation
   (to support variant \LaTeX\ styles)
  \item to/from ASCII format used by \UTP2.
\end{itemize}
We give symbolic names to a \emph{lot} of \LaTeX\ tokens,
for example like \verb"=" and \verb"\fun".
This allows us to retarget to different \LaTeX\ dialects.
For example the symbol \texttt{INTEGER}, typically rendered as $\num$,
may be expressed by any one
of the following \LaTeX\ macros, depending on the style file in use:
\begin{quote}
  \verb"\num"
  ~~~~
  \verb"\integer"
  ~~~~
  \verb"\Integer"
\end{quote}
So, we can identify three ``namespaces'':
\begin{description}
  \item[ASCII] this is how symbols are rendered in the GUI
  \item[\LaTeX] the corresponding forms for \LaTeX.
  \item[Symbols] An internal symbolic (abstract) representation of these.
\end{description}
We need translations between all three, which we derive from
two base translations, from Symbol to the other two.

\newpage
\subsection{Symbols}

Symbols are special tokens that are ``built-in'' to \UTP2,
in that they have to be supported in all ASCII and \latex\ variants.
Some are also rigid, in that their translations (esp. to \latex)
are fixed and not user-customisable.
Rigidity arises for things like brackets, and Z-specific symbols
(for future extensions in the \Circus\ direction),
Fluid symbols are things like type integer as mentioned above.
We also have ``semi-rigid'' symbols associated with \UTP2,
that translate to plain text strings (no macros)
and should be left unchanged in most cases.
\begin{code}
data Symbol
 = -- rigid symbols first
   ABRDEF | ALSO | BSUP | CLOSEBRACE | CLOSEBRACKET | CLOSEPAREN
 | CLOSESET | CLOSESUB | COLON | COLONCOLONEQUALS | COMMA | DBLBACKSLASH
 | DELTA | EQUALS | ESUP | LBLOT | LDATA | LIMG | MATHMODE | OPENBRACE
 | OPENBRACKET | OPENPAREN | OPENSET | OPENSUB | PARENEND | PARENSTART
 | RBLOT | RDATA | RIMG | SETEND | SETSTART | SLASH | SUBEND | SUBSTART
 | THETA | UNDERSCORE | UNIVEND | UNIVSTART | VERT | XI
   -- semi-rigid symbols next
 | ASSUME | LAWRED | LHS2RHS | REDUCE | REDUCE2 | RHS2LHS
   -- fluid symbols last
 | AND | ASSIGN | AT | BOOL | CROSS | DEFD | DEFS | EC | ELAMBDA | ELSE
 | EQUIV | EXISTS | EXISTS1 | EXTCHOICE | FORALL | FUN | GUARD | HASTYPE
 | HIDE | HOLDS | HYPHEN | IF | IFF | IMPLIES | IN | INTCHOICE | INTEGER
 | LAMBDA | LAND | LANGLE | LET | LHD | LNOT | LOR | MAP | MAPSTO
 | MAPSTOEND | MAPSTOSTART | MU | NAMES | NDETC | NEQ | NOT | NOTIN | OBSV
 | OR | PAPP | PFALSE | PFUN | PIPE | PLAMBDA | POINT | PRE | PREQV | PRIMP
 | PROJECT | PRPMI | PTRUE | QED | QVARSEP | RANGLE | RFDBY | RHD
 | SEMICOLON | SEPPIPE | SEPSLASH | SEQ | SEQCOMP | SEQEND | SEQP | SEQSTART
 | SET | SSTPRED | STPRED | TARB | TENV | THEN | WHERE
 deriving (Eq,Ord,Enum,Show,Read)

type SymRenderTable = [(Symbol,String)]
\end{code}

\subsection{Symbol to \LaTeX\ Translation}

The following tables associating symbols and strings are currently
hardwired, but will eventually reside in configuration files.
Rigid symbols:
\begin{code}
rigidSymLTXTbl
 = [ (ABRDEF,"=="), (ALSO,"\\also"), (BSUP,"\\bsup"), (CLOSEBRACE,"}")
   , (CLOSEBRACKET,"]"), (CLOSEPAREN,")"), (CLOSESET,"\\}"), (CLOSESUB,"]")
   , (COLON,":"), (COLONCOLONEQUALS,"::="), (COMMA,","), (DBLBACKSLASH,"\\\\")
   , (DELTA,"\\Delta"), (EQUALS,"="), (ESUP,"\\esup"), (LBLOT,"\\lblot")
   , (LDATA,"\\ldata"), (LIMG,"\\limg"), (MATHMODE,"$$"), (OPENBRACE,"{")
   , (OPENBRACKET,"["), (OPENPAREN,"("), (OPENSET,"\\{"), (OPENSUB,"[")
   , (PARENEND,")"), (PARENSTART,"("), (RBLOT,"\\rblot"), (RDATA,"\\rdata")
   , (RIMG,"\\rimg"), (SETEND,"}"), (SETSTART,"{"), (SLASH,"/"), (SUBEND,"]")
   , (SUBSTART,"["), (THETA,"\\theta"), (UNDERSCORE,"_"), (UNIVEND,"]")
   , (UNIVSTART,"["), (VERT,"|"), (XI,"\\Xi")
   ]
\end{code}

Semi-rigid symbols:
\begin{code}
semiRigidSymLTXTbl
 = [ (ASSUME,"Assume, then ")
   , (LAWRED,"Reduce Law to Goal : ")
   , (LHS2RHS,"Transform left-hand side into right-hand.")
   , (REDUCE,"Reduce to True.")
   , (REDUCE2,"Reduce both sides to the same.")
   , (RHS2LHS,"Transform right-hand side into left hand.")
   ]
\end{code}

We proceed to supply default generated values for the fluid symbols,
as well as a built-in fuzz-like translation.
\begin{code}
genSymLTXTbl
 = rigidSymLTXTbl
   ++ semiRigidSymLTXTbl
   ++ map mkSymRenderEntry [AND .. WHERE]
 where
   mkSymRenderEntry sym = (sym,'\\':(map toLower (show sym)))

fuzzFluidSymLTXTbl
 = [ (AND,"\\land"), (ASSIGN,":="), (AT,"@"), (BOOL,"\\bool"), (CROSS,"\\cross")
   , (DEFD,"\\Defd"), (DEFS,"\\defs"), (EC,"\\extchoice"), (ELAMBDA,"\\elambda")
   , (ELSE,"\\ELSE"), (EQUIV,"\\equiv"), (EXISTS,"\\exists"), (EXISTS1,"\\exists1")
   , (EXTCHOICE,"\\extchoice"), (FORALL,"\\forall"), (FUN,"\\fun"), (GUARD,"\\amp")
   , (HASTYPE,":"), (HIDE,"\\hide"), (HOLDS,"::="), (HYPHEN,"-"), (IF,"\\IF")
   , (IFF,"\\iff"), (IMPLIES,"\\implies"), (IN,"\\in"), (INTCHOICE,"\\intchoice")
   , (INTEGER,"\\num"), (LAMBDA,"\\lambda"), (LAND,"\\land"), (LANGLE,"\\langle")
   , (LET,"\\LET"), (LHD,"\\lhd"), (LNOT,"\\lnot"), (LOR,"\\lor"), (MAP,"\\ffun")
   , (MAPSTO,"\\mapsto"), (MAPSTOEND,"}"), (MAPSTOSTART,"{"), (MU,"\\mu")
   , (NAMES,"\\names"), (NDETC,"\\intchoice"), (NEQ,"\\neq"), (NOT,"\\lnot")
   , (NOTIN,"\\notin"), (OBSV,"\\obs"), (OR,"\\lor"), (PAPP,"\\papp")
   , (PFALSE,"false"), (PFUN,"\\pfun"), (PIPE,"\\pipe"), (PLAMBDA,"\\plambda")
   , (POINT,"."), (PRE,"\\pre"), (PREQV,"\\EQV"), (PRIMP,"\\IMP")
   , (PROJECT,"\\project"), (PRPMI,"\\PMI"), (PTRUE,"true"), (QED,"\\qed")
   , (QVARSEP,"\\qvarsep"), (RANGLE,"\\rangle"), (RFDBY,"\\refinedby")
   , (RHD,"\\rhd"), (SEMICOLON,";"), (SEPPIPE,"|"), (SEPSLASH,"/"), (SEQ,"\\seq")
   , (SEQCOMP,"\\seqcomp"), (SEQEND,"\\rangle"), (SEQP,"\\seq1")
   , (SEQSTART,"\\langle"), (SET,"\\power"), (SSTPRED,"\\&"), (STPRED,"&&")
   , (TARB,"\\tarb"), (TENV,"\\Env"), (THEN,"\\THEN"), (WHERE,"\\where")
   ]

fuzzSymLTXTbl
 = rigidSymLTXTbl ++ semiRigidSymLTXTbl ++ fuzzFluidSymLTXTbl
\end{code}

\newpage
\subsection{Symbol to ASCII Translation}

\begin{code}
genSymAscTbl
 = map mkSymRenderEntry [ALSO .. XI]
 where
   mkSymRenderEntry sym = (sym,map toLower (show sym))

utp2SymASCTbl -- what UTP2 currently does
 = [ (ALSO,"also"), (ABRDEF,"=="), (AND,"/\\"), (ASSUME,"Assume, then")
   , (ASSIGN,":="), (AT,"@"), (BOOL,"B"), (BSUP,"."), (CLOSEBRACE,"}")
   , (CLOSEBRACKET,"]"), (CLOSEPAREN,")"), (CLOSESET,"}"), (CLOSESUB,"]")
   , (COLON,":"), (COLONCOLONEQUALS,"::="), (COMMA,","), (CROSS,"x")
   , (DBLBACKSLASH,"\\"), (DEFD,"DFD"), (DEFS,"^="), (DELTA,"Dlt"), (EC,"[]")
   , (ELAMBDA,"\\"), (ELSE,"else"), (EQUALS,"="), (EQUIV,"==="), (ESUP,".")
   , (EXISTS,"exists"), (EXISTS1,"exists1"), (EXTCHOICE,"[]"), (FORALL,"forall")
   , (FUN,"->"), (GUARD,"&"), (HASTYPE,":"), (HIDE,"\\"), (HOLDS,"::=")
   , (HYPHEN,"-"), (IF,"if"), (IFF,"<=>"), (IMPLIES,"=>"), (IN,"in")
   , (INTEGER,"Z"), (INTCHOICE,"|~|"), (LAMBDA,"\\"), (LAND,"/\\"), (LANGLE,"<")
   , (LAWRED,"Reduce Law to Goal :"), (LBLOT,"<|"), (LDATA,"<<"), (LET,"let")
   , (LHD,"<|"), (LHS2RHS,"Transform left-hand side into right-hand.")
   , (LIMG,"(|"), (LNOT,"~"), (LOR,"\\/"), (MAP,"\\ffun"), (MAPSTO,"\\mapsto")
   , (MAPSTOEND,"}"), (MAPSTOSTART,"{"), (MATHMODE,"$$"), (MU,"mu"), (NAMES,"is")
   , (NDETC,"|~|"), (NEQ,"/="), (NOT,"~"), (NOTIN,"notin"), (OBSV,"Obs")
   , (OPENBRACE,"{"), (OPENBRACKET,"["), (OPENPAREN,"("), (OPENSET,"{")
   , (OPENSUB,"["), (OR,"\\/"), (PAPP,"App"), (PARENEND,")"), (PARENSTART,"(")
   , (PFALSE,"false"), (PFUN,"pfun"), (PIPE,"|"), (PLAMBDA,"\\"), (POINT,".")
   , (PRE,"pre"), (PROJECT,"project"), (PREQV,"=="), (PRIMP,"=>"), (PRPMI,"=<")
   , (PTRUE,"true"), (QED,"Qed."), (QVARSEP,"qvarsep"), (RANGLE,">")
   , (RBLOT,"|>"), (RDATA,">>"), (REDUCE,"Reduce to True.")
   , (REDUCE2,"Reduce both sides to the same."), (RFDBY,"|="), (RHD,"|>")
   , (RHS2LHS,"Transform right-hand side into left hand."), (RIMG,"|)")
   , (SEMICOLON,";"), (SEPPIPE,"|"), (SEPSLASH,"/"), (SEQ,"seq"), (SEQCOMP,";")
   , (SEQP,"seq1"), (SEQEND,">"), (SEQSTART,"<"), (SET,"set"), (SETEND,"}")
   , (SETSTART,"{"), (SLASH,"/"), (SSTPRED,"&"), (STPRED,"&&"), (SUBEND,"]")
   , (SUBSTART,"["), (TARB,"Tarb"), (TENV,"Env"), (THEN,"then"), (THETA,"theta")
   , (UNDERSCORE,"_"), (UNIVEND,"]"), (UNIVSTART,"["), (VERT,"|")
   , (WHERE,"where"), (XI,"Xi")
   ]
\end{code}

\newpage
\subsection{Specifying \LaTeX\ Layout}

The \texttt{LaTeXLayout} structure
holds the parameters that are need for pretty printing/parsing
\begin{code}
data LaTeXLayout
  = LaTeXLayout { lineLength  :: Int
                , indentLength  :: Int
                , wantBindings  :: Bool
                -- translation functions
                , ltx2sym :: String -> Maybe Symbol
                , sym2ltx :: Symbol -> Maybe String
                , asc2sym :: String -> Maybe Symbol
                , sym2asc :: Symbol -> Maybe String
                , asc2ltx :: String -> Maybe String
                , ltx2asc :: String -> Maybe String
                -- corresponding tables (for viewing/editing)
                , symAltx :: SymRenderTable
                , symAasc :: SymRenderTable
                , ascAltx :: [(String,String)]
                }
\end{code}

The translation tables are built from
the symbol-string association lists mentioned
above, plus extra \latex-ASCII translations supplied
by the user (usually via definitions in theories).
\begin{code}
mkLaTeXLayout ll il wb asymltx asymasc aascltx
  = LaTeXLayout { lineLength = ll
                , indentLength = il
                , wantBindings = wb
                , ltx2sym = tlookup  ltx2symt
                , sym2ltx = btlookup sym2ltxt
                , asc2sym = tlookup  asc2symt
                , sym2asc = btlookup sym2asct
                , asc2ltx = tlookup  asc2ltxt
                , ltx2asc = tlookup  ltx2asct
                , symAltx = asymltx
                , symAasc = asymasc
                , ascAltx = aascltx
                }
  where
    ltx2symt = lbuild (map twist asymltx)
    sym2ltxt = bbuild asymltx
    asc2symt = lbuild (map twist asymasc)
    sym2asct = bbuild asymasc
    asc2ltxt = lbuild aasc2ltx
    ltx2asct = lbuild altx2asc

    aasc2ltx = (merge (sort asymasc) (sort asymltx)) ++ aascltx
    altx2asc = map twist aasc2ltx

    twist (a,b) = (b,a)
    merge [] _ = []
    merge _ [] = []
    merge s2a@((s1,asc):ascrest) s2l@((s2,ltx):ltxrest)
     | s1 < s2    =  merge ascrest s2l
     | s1 > s2    =  merge s2a ltxrest
     | otherwise  =  (asc,ltx):(merge ascrest ltxrest)
\end{code}


The default \LaTeX\ layout
\begin{code}
defaultLaTeXLayout len ind showbind
   = mkLaTeXLayout len ind showbind
           fuzzSymLTXTbl utp2SymASCTbl asciiLaTeXMapping
\end{code}

The table \texttt{laTeXRefToMathMap} holds the
translations for certain short sequences for printing part of the inferences.
\TODO{
 These tables should be loadable from/saveable to a configuration file,
 and modifiable from within the user interface.
}
\begin{code}
laTeXRefToMathMap
 = [( "$"   , "\\$" )
   ,( "/\\" , "$\\land$" )
   ,( "\\/" , "$\\lor$" )
   ,( "=="  , "$\\equiv$" )
   ,( "=~="  , "$\\nequiv$" )
   ,( "=/="  , "$\\nequiv$" )
   ,( "=>"  , "$\\implies$" )
   ,( "<|"  , "$\\lhd$" )
   ,( "|>"  , "$\\rhd$" )
   ,( "~"  , "$\\lnot$" )
   ]
\end{code}

The \texttt{asciiLaTeXMapping} maps ASCII names to their \LaTeX\ equivalents.
Note that some of these are non-standard and require the use of a \UTP2-specific
style file (\texttt{saoithin.sty}).
\begin{code}
asciiLaTeXMapping
 = [("neq","//=")

   ,("times","*")
   ,("div","/")
   ,("leq","<=")
   ,("geq",">=")

   ,("setminus","\\")
   ,("in","in")
   ,("cup","union")
   ,("cap","intsct")

   ,("sle","<<=")
   ,("slt","<<")
   ,("sge",">>=")
   ,("sgt",">>")
   ,("cat","++")
   ,("ssub","--")
   ,("#","#")

   ,("then","->")
   ,("intchoice","|~|")
   ,("refinedby","|=")
   ,("refines","=|")
   ]
\end{code}
