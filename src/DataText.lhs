\section{Text Handling for Data Types}

\begin{code}
module DataText where
import Data.Char hiding (isSymbol)
import Data.List
import Data.Maybe
import Tables
import Datatypes
import Precedences
--import Focus
import Utilities
-- import Invariants
-- import DSL
--import Types

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error

import Control.Monad
\end{code}

We define ways to render key datatypes in textual format
that can itself be parsed.


\newpage
\subsection{Lexical Analysis}

Our basic character classes are:
\LXCHARACTERS

We have Names, Identifiers, Numerical Constants, Symbols, and White-space:
\begin{itemize}
  \item
    Names start with an alphabetic character or underscore
    and continue with zero or more alphanumerics.
    \begin{eqnarray*}
       \LXName
    \\ \LXAlfDig
    \end{eqnarray*}
  \item
    Identifiers are either General or Reserved
    \begin{eqnarray*}
          \LXIdent
    \end{eqnarray*}
  \item
    General Identifiers are Names that are followed immediately
    (no whitespace) by decorations and some extra stuff.
    Decorations indicate List-vars (\verb"$"),
    after-variables (\verb"'"),
    subscripts (\verb"_n"),
    and patterns that match both
    before and after-variables (\verb"?").
    A List-var decoration can be followed by one of the other decorations
    above.
    \begin{eqnarray*}
          \LXGen
       \\ \LXDecor
    \end{eqnarray*}
\begin{code}
chrLST = listVarFlag ; strLST = [chrLST]
chrPOST = '\'' ; strPOST = [chrPOST]
chrSUBS = '_'  ; strSUBS = [chrSUBS]
\end{code}
  \item
    Reserved Identifiers denote observation variables
    of various classes (\verb"O",\verb"M",\verb"S"),
    and these can have the decorations for
    after-variables, subscripts or \verb"?",
    and can also end with a backslash (\verb"\") followed
    by one-or more colon-separated (\verb":") Names,
    not included the reserved three.
    \begin{eqnarray*}
          \LXRsv
       \\ \LXRsvSuffix
       \\ \LXRoots
    \end{eqnarray*}
\begin{code}
chrLESS = '\\' ; strLESS = [chrLESS]
chrLSEP = ':'  ; strLSEP = [chrLSEP]
\end{code}
    This immediately induces a number of instances of \texttt{Show}:
\begin{code}
instance Show GenRoot where show = rootString . Gen
instance Show RsvRoot where show r = rootString $ Rsv r []
instance Show Root where show = rootString

instance Show Decor where
  show NoDecor        =  ""
  show Pre            =  ""
  show Post           =  strPOST
  show (Subscript s)  =  chrSUBS:s
  show Scrpt          =  "\""
\end{code}
  \item
    Numerical constants begin with a digit or minus sign (\verb"-"),
    and then followed by a sequence of digits,
    with possibly one period (\verb".") inbetween.
    \begin{eqnarray*}
      \LXNum
    \end{eqnarray*}
  \item Symbols are any contiguous sequence of non-digit,
      non-alpha, non-underscore, visible characters.
      In general the ``maximum munch'' principle applies,
      except for specified symbols which should be split-out
      from longer sequences, By default, these include
      the brackets, so that ``\verb"(("'' gives two (bracket-) symbol
      tokens, for instance.
      One exception is the backquote character (\verb"`") which
      always forms a single character token.
      \begin{eqnarray*}
         \LXSymbol
      \end{eqnarray*}
\begin{code}
chrBKQ = '`'
\end{code}
  \item White space is all invisible characters, both
      printable and un-printable.
  \item A special `comment' character
      occurring at the start of a line
      turns that whole line into a whitespace token.
\begin{code}
chrCMT = '!'
\end{code}
  \item A special `definition-separator' character
      occurring at the end of a line
      becomes a ``SEP'' token. This is used to separate
      multi-line definitions.
\begin{code}
chrSEP = '.'
\end{code}
  \item
    We also have ``key-'' versions of names and symbol tokens,
    which denote those with a special meaning or role.
\end{itemize}



\newpage
\subsubsection{Lexical Tokens}

\begin{code}
data Tok = TEOF
         | TName String  | TKey String
         | TIdent Variable
         | TNum  String
         | TSym  String  | TKSym String
         | TLQt | TSep
         | TWht  String
         deriving (Eq,Ord)

instance Show Tok where
 show TEOF                =  "EOF"
 show (TName s)           =  "N." ++ s
 show (TKey s)            =  "K." ++ s
 show (TIdent (_,_,s))    =  "I."++s
 show (TNum s)            =  "#." ++ s
 show (TSym s)            =  "S." ++ s
 show (TKSym s)           =  "KS." ++ s
 show (TWht s)            =  "W." ++ showLitString s
 show TLQt                =  "LQT"
 show TSep                =  "SEP"

showLitString s = (foldr (.) id (map showLitChar s)) ""

type Token = (SourcePos,Tok)

cShowPos pos
  = "(" ++ show (sourceLine pos)
     ++ ","
     ++ show (sourceColumn pos)
     ++ ")"

cShowToken (pos,tok)
  = show tok ++ " @ " ++ cShowPos pos

cShowToks :: [Token] -> String
cShowToks = concat . intersperse "\n" . map cShowToken

tsshow toks = concat (intersperse "  " (map tshow toks))
tshow (_,tok) = show tok

displayToks = putStrLn . unlines . map tshow
\end{code}

\newpage
\subsubsection{Lexical Scanner}

The lexical definition:

\LXCHARACTERS

First, some useful predicates:
\begin{code}
isSymb c = isPrint c && not (isSpace c)
isNewLine c = c == '\n'

isIdent c = isAlpha c || isDigit c
isSymbol c = isSymb c && not (isIdent c )
\end{code}

We define a Parsec-compliant scanner, that returns no errors
(any string lexes OK).

\LXTOKENS

\newpage
\begin{center}
\includepicture{doc/images/Identifier-Lexical-Diagram}
\end{center}
\newpage



Now, the scanner itself:
\begin{code}
scanner :: String  -- file/input-name
        -> [Char] -> [Token]

scanner name cs
  = scanroot [] zeroPos cs
  where
\end{code}

We set initial position, and provide tail-recursion-aware
token builders.
\begin{code}
    zeroPos = initialPos name

    m rcons pos txt st -- assemble a string-based token
      = (pos,rcons txt'):st
      where
       txt' = (reverse txt)

    m' rcons pos st -- assemble a string-free token
      = (pos,rcons):st
\end{code}

We dispatch on the first character to determine the token type
\begin{code}
    scanroot skot pos [] = reverse ((pos,TEOF):skot)

    scanroot skot pos (c:cs)
     | [c] `elem` [strOBS,strMDL,strSCR]
                     =  scanRsv skot pos [c] pos cs
     | isAlpha c     =  scanName skot pos' [c] pos' cs
     | c == '_'      =  scanName skot pos' [c] pos' cs
     | isDigit c     =  scanNum  skot pos' [c] pos' cs
     | c == '-'      =  scanNeg  skot pos' [c] pos' cs
     | c == '`'      =  scanroot (m' TLQt pos skot) pos' cs
     | c == chrSEP   =  scanSep skot pos cs
     | isNewLine c   =  scanNLine  skot pos' [c] pos' cs
     | isSymb c      =  scanSym  skot pos' [c] pos' cs
     | otherwise     =  scanWht  skot pos' [c] pos' cs
     where
       pos' = updatePosChar pos c
\end{code}

\newpage
\paragraph{Reserved Variable}
\begin{eqnarray*}
   \LXRsv
\end{eqnarray*}
Node \textsf{Rsv}:
Seen initial $\lit O, \lit M, \lit S$.
\begin{code}
    scanRsv skot spos kot pos []
       = scanroot ((spos,tokrsv (reverse kot)):skot) pos []
    scanRsv skot spos kot pos cs@(c:cs')
     | isAlpha c  =  scanName skot spos (c:kot) pos' cs'
     | isDigit c  =  scanName skot spos (c:kot) pos' cs'
     | c == chrSUBS   =  scanSbscrR skot spos tok "" pos' cs'
     | c == chrPOST  =  scanPostR skot spos tok pos' cs'
     | c == chrLESS  =  scanGenRoots skot spos tok (Pre,"") [] (pos,c) pos' cs'
     | otherwise  =  scanroot ((spos,tokrsv tok):skot) pos cs
     where
       pos' = updatePosChar pos c
       tok = reverse kot

    tokrsv tok = TIdent $ mkVar (stringToRoot tok) Pre   []
\end{code}

\paragraph{Reserved Decorations}

\begin{eqnarray*}
   \LXDecor
\end{eqnarray*}
Node \textsf{RsvSub}:
Seen initial $\LXRsvN~\lit\_$
\begin{code}
    scanSbscrR skot spos tok sbus pos []
       = scanroot ((spos,tokrsvsubs tok (reverse sbus)):skot) pos []
    scanSbscrR skot spos tok sbus pos cs@(c:cs')
     | isAlpha c  =  scanSbscrR skot spos tok (c:sbus) pos' cs'
     | isDigit c  =  scanSbscrR skot spos tok (c:sbus) pos' cs'
     | c == chrLESS  =  scanGenRoots skot spos tok (Subscript subs,subs) [] (pos,c) pos' cs'
     | otherwise  =  scanroot ((spos,tokrsvsubs tok subs):skot) pos cs
     where
       pos' = updatePosChar pos c
       subs = reverse sbus

    tokrsvsubs tok subs = TIdent $ mkVar (stringToRoot tok) (Subscript subs) []
\end{code}

Node \textsf{RsvPost}:
Seen initial $\LXRsvN~\lit'$.
\begin{code}
    scanPostR skot spos tok pos []
       = scanroot ((spos,tokrsvpost tok):skot) pos []
    scanPostR skot spos tok pos cs@(c:cs')
     | c == chrLESS  =  scanGenRoots skot spos tok (Post,strPOST) [] (pos,c) pos' cs'
     | otherwise  =  scanroot ((spos,tokrsvpost tok):skot) pos cs
     where
       pos' = updatePosChar pos c

    tokrsvpost tok = TIdent $ mkVar (stringToRoot tok) Post []
\end{code}


\paragraph{Reserved Subtractions}
\begin{eqnarray*}
   \LXRsvSuffix
\end{eqnarray*}
Node \textsf{RsvL}:
Seen initial $\lit O$, $\lit M$, or $\lit S$,
followed by $\LXDecorN$.
\begin{code}
    scanGenRoots skot spos tok decor stoor (pos0,c0) pos []
       = scanroot ((spos,tokrsvlnames tok decor (reverse stoor)):skot) pos0 [c0]
    scanGenRoots skot spos tok decor stoor (pos0,c0) pos cs@(c:cs')
     | isAlpha c  =  scanGenRoots' skot spos tok decor stoor [c] pos' cs'
     | otherwise  =  scanroot ((spos,tokrsvlnames tok decor roots):skot) pos0 (c0:cs)
     where
       pos' = updatePosChar pos c
       roots = reverse stoor

    tokrsvlnames tok (dcr,s) roots
       = TIdent $ mkVar (stringToRoot tok) dcr roots
\end{code}

Node \textsf{RsvLs}:
Seen initial $(\lit O | \lit M | \lit S)\LXDecorN$
followed by 1 or more $\LXAlfDigN$.
\begin{code}
    scanGenRoots' skot spos tok decor stoor eman pos []
       = scanroot ((spos,tokrsvlnames tok decor (reverse (Std (reverse eman):stoor))):skot) pos []
    scanGenRoots' skot spos tok decor stoor eman pos cs@(c:cs')
     | isAlpha c  =  scanGenRoots' skot spos tok decor stoor (c:eman) pos' cs'
     | isDigit c  =  scanGenRoots' skot spos tok decor stoor (c:eman) pos' cs'
     | c == chrLSEP   =  scanGenRoots skot spos tok decor (Std name:stoor) (pos,c) pos' cs'
     | c == chrLST   =  scanGenRoots'' skot spos tok decor (Lst name:stoor) pos' cs'
     | otherwise  =  scanroot ((spos,tokrsvlnames tok decor roots):skot) pos cs
     where
       pos' = updatePosChar pos c
       name = reverse eman
       roots = reverse (Std name:stoor)
\end{code}

Node \textsf{RsvLss}:
Seen initial $(\lit O | \lit M | \lit S)\LXDecorN$
followed by 1 or more $\LXAlfDigN$ and a $\lit\$$.
\begin{code}
    scanGenRoots'' skot spos tok decor stoor pos []
       = scanroot ((spos,tokrsvlnames tok decor (reverse stoor)):skot) pos []
    scanGenRoots'' skot spos tok decor stoor  pos cs@(c:cs')
     | c == chrLSEP   =  scanGenRoots skot spos tok decor stoor (pos,c) pos' cs'
     | otherwise  =  scanroot ((spos,tokrsvlnames tok decor roots):skot) pos cs
     where
       pos' = updatePosChar pos c
       roots = reverse stoor
\end{code}

\newpage
\paragraph{General Identifier}
\begin{eqnarray*}
   \LXGen
\\ \LXDecor
\end{eqnarray*}
Node \textsf{StdPre}:
Seen initial $\LXalphaN$ less $\setof{\lit O,\lit M,\lit S}$,
and zero or more $\LXAlfDigN$.
\begin{code}
    scanName skot spos kot pos []
       = scanroot ((spos,tokpre (reverse kot)):skot) pos []
    scanName skot spos kot pos cs@(c:cs')
     | isAlpha c  =  scanName skot spos (c:kot) pos' cs'
     | isDigit c  =  scanName skot spos (c:kot) pos' cs'
     | c == chrPOST  =  scanroot ((spos,tokpost tok):skot) pos' cs'
     | c == chrSUBS   =  scanSbscr skot spos tok "" pos' cs'
     | c == chrLST   =  scanLst skot spos tok pos' cs'
     | otherwise  =  scanroot ((spos,TName tok):skot) pos cs
     where
       pos' = updatePosChar pos c
       tok = reverse kot

    tokpre tok  = TIdent $ mkVar (stringToRoot tok) Pre   []
    tokpost tok = TIdent $ mkVar (stringToRoot tok) Post  []
\end{code}

\paragraph{Subscript}
\begin{eqnarray*}
   \LXDecor
\end{eqnarray*}
Node \textsf{StdSub}:
Seen initial $\LXNameN~\lit\_$.
\begin{code}
    scanSbscr skot spos tok sbus pos []
       = scanroot ((spos,toksubs tok (reverse sbus)):skot) pos []
    scanSbscr skot spos tok sbus pos cs@(c:cs')
     | isAlpha c  =  scanSbscr skot spos tok (c:sbus) pos' cs'
     | isDigit c  =  scanSbscr skot spos tok (c:sbus) pos' cs'
     | otherwise  =  scanroot ((spos,toksubs tok subs):skot) pos cs
     where
       pos' = updatePosChar pos c
       subs = reverse sbus

    toksubs tok subs = TIdent $ mkVar (stringToRoot tok) (Subscript subs) []
\end{code}

\paragraph{General List Variable}
\begin{eqnarray*}
   \LXGen
\end{eqnarray*}
Node \textsf{LstPre}:
Seen initial $\LXNameN~\lit\$$.
\begin{code}
    scanLst skot spos tok pos []
       = scanroot ((spos,toklst tok):skot) pos []
    scanLst skot spos tok pos cs@(c:cs')
     | c == chrSUBS  =  scanSbscrL skot spos tok "" pos' cs'
     | c == chrPOST  =  scanPost skot spos tok pos' cs'
     | otherwise  =  scanroot ((spos,toklst tok):skot) pos cs
     where
       pos' = updatePosChar pos c

    toklst tok = TIdent $ mkVar (forceLst $ tok) Pre []
\end{code}

Node \textsf{LstPost}:
Seen initial $\LXNameN~\lit\$$\lit'.
\begin{code}
    scanPost skot spos tok pos []
       = scanroot ((spos,toklstpost tok):skot) pos []
    scanPost skot spos tok pos cs@(c:cs')
     | otherwise  =  scanroot ((spos,toklstpost tok):skot) pos cs
     where
       pos' = updatePosChar pos c

    toklstpost tok = TIdent $ mkVar (forceLst tok) Post []
\end{code}


Node \textsf{LstSubscr}:
Seen initial $\LXNameN~\lit\$\lit\_$.
\begin{code}
    scanSbscrL skot spos tok sbus pos []
       = scanroot ((spos,toklstsubs tok (reverse sbus)):skot) pos []
    scanSbscrL skot spos tok sbus pos cs@(c:cs')
     | isAlpha c  =  scanSbscrL skot spos tok (c:sbus) pos' cs'
     | isDigit c  =  scanSbscrL skot spos tok (c:sbus) pos' cs'
     | otherwise  =  scanroot ((spos,toklstsubs tok subs):skot) pos cs
     where
       pos' = updatePosChar pos c
       subs = reverse sbus

    toklstsubs tok subs = TIdent $ mkVar (forceLst tok) (Subscript subs) []
\end{code}

\newpage
\paragraph{\LXNumN}
\begin{eqnarray*}
   \LXNum
\end{eqnarray*}
Seen initial `-'. If followed by whitespace, it is the binary
minus operator, otherwise it is either part of a negative
number, part of a symbol or the unary negation symbol.
\begin{code}
    scanNeg  skot spos kot pos []
       = scanroot (m TSym spos kot skot) pos []
    scanNeg skot spos kot pos cs@(c:cs')
     | isDigit c  =  scanNum skot spos (c:kot) pos' cs'
     | isAlpha c  =  scanroot skot' pos cs
     | isSymb c   =  scanSym skot spos (c:kot) pos' cs'
     | otherwise  =  scanroot (m TSym spos kot skot) pos cs
     where
       pos' = updatePosChar pos c
       skot' = m TName spos "gen" skot
\end{code}

\begin{eqnarray*}
   Num &::=& [ \mbox{`-'} ] digit^+
\end{eqnarray*}
Seen initial $-$, if present, and initial $\LXdigitN$.
\begin{code}
    scanNum  skot spos kot pos []
       = scanroot (m TNum spos kot skot) pos []
    scanNum skot spos kot pos cs@(c:cs')
     | isDigit c  =  scanNum skot spos (c:kot) pos' cs'
     | otherwise  =  scanroot (m TNum spos kot skot) pos cs
     where
       pos' = updatePosChar pos c
\end{code}

\newpage
\paragraph{\LXSymbolN}
\begin{eqnarray*}
   \LXSymbol
\end{eqnarray*}
Seen initial $\LXsymN$.
\begin{code}
    scanSym  skot spos kot pos []
       = scanroot (m TSym spos kot skot) pos []
    scanSym  skot spos kot pos cs@(c:cs')
     | isAlpha c  = scanroot (m TSym spos kot skot) pos cs
     | isDigit c  = scanroot (m TSym spos kot skot) pos cs
     | c == chrSUBS   = scanroot (m TSym spos kot skot) pos cs
     | c == '`'   = scanroot (m TSym spos kot skot) pos cs
     | isSymb c   =  scanSym skot spos (c:kot) pos' cs'
     | otherwise  =  scanroot (m TSym spos kot skot) pos cs
     where

       pos' = updatePosChar pos c
\end{code}

\newpage
\paragraph{\LXWhiteN}
\begin{eqnarray*}
  \LXWhite
\end{eqnarray*}
Seen initial $wht$.
\begin{code}
    scanWht skot spos kot pos []
       = scanroot (m TWht spos kot skot) pos []
    scanWht skot spos kot pos cs@(c:cs')
     | c == '\n'  =  scanNLine skot spos (c:kot) pos' cs'
     | isSpace c  =  scanWht skot spos (c:kot) pos' cs'
     | isPrint c  =  scanroot (m TWht spos kot skot) pos cs
     | otherwise  =  scanWht skot spos (c:kot) pos' cs'
     where
       pos' = updatePosChar pos c
\end{code}

Seen $newline$ in white-space. If immediately followed by
a comment character, we merge the following line into a whitespace token.
\begin{code}
    scanNLine skot spos kot pos []
       = scanroot (m TWht spos kot skot) pos []
    scanNLine skot spos kot pos cs@(c:cs')
     | c == chrCMT  =  scanCMT skot spos (c:kot) pos' cs'
     | otherwise    =  scanWht skot spos kot pos cs
     where
       pos' = updatePosChar pos c

    scanCMT skot spos kot pos []
     = scanroot (m TWht spos kot skot) pos []
    scanCMT skot spos kot pos (c:cs')
     | c == '\n'  =  scanNLine skot spos (c:kot) pos' cs'
     | otherwise  =  scanCMT skot spos (c:kot) pos' cs'
     where
       pos' = updatePosChar pos c
\end{code}


Seen \texttt{chrSEP} at start of a token.
If followed by a newline then it is a \texttt{TSep} token,
otherwise treat as part of a symbol.
\begin{code}
    scanSep skot pos []
     = scanroot (m TSym pos [chrSEP] skot) pos []
    scanSep skot pos cs@(c:cs')
     -- | c == '\n'  =  scanroot (m' TSep pos skot) pos cs
     | c == '\n'  =  scanNLine (m' TSep pos skot) pos' [c] pos' cs'
     | otherwise  =  scanSym skot pos [chrSEP] pos cs
     where
       pos' = updatePosChar pos c

-- end scanner

tstScan  = displayToks . scanner  "<test>"
\end{code}

An important property of this lexer is that it never produces
two consecutive white-space tokens.
$$
 \forall n,s,w_1,w_2:String @
   \lnot substring(\seqof{TWht~w_1,TWht~w_2},\pi_1(scanner~n~s))
$$



\subsubsection{Symbol-Token splitting}

Symbols found by these rules are then broken into ``maximal
munches'' using the \texttt{knownSymbols} set.
\begin{code}
symbolSplit :: Trie a -> [Token] -> [Token]
symbolSplit knownSymbols = concat . map (symSplit knownSymbols)

symSplit :: Trie a -> Token -> [Token]

symSplit known (pos,TSym stxt)
 = posmap pos munches
 where
    munches = maximalMunches known stxt
    posmap pos [] = []
    posmap pos (munch:munchies)
     = (pos,TSym munch)
           : posmap (incSourceColumn pos (length munch)) munchies

symSplit known tok = [tok]
\end{code}


\subsubsection{Token Clean-up}

We can remove whitespace tokens from list
\begin{code}
removeWhite = filter notWht

notWht (_,(TWht _)) = False
notWht _            = True
\end{code}

Sometimes it is handy to chop off trailing EOF tokens
\begin{code}
chopLastEOF [] = []
chopLastEOF [(_,TEOF)] = []
chopLastEOF (tok:toks) = tok : chopLastEOF toks
\end{code}

Combining both of the above
\begin{code}
chopWhiteEOF = filter notWhtEOF

notWhtEOF (_,TEOF)     = False
notWhtEOF (_,(TWht _)) = False
notWhtEOF _            = True
\end{code}

\newpage
\subsubsection{Variable Building \& Parsing}

We need to set the (key) string in a Variable to match its
printed form
\begin{code}
renderVar :: Root -> Decor -> String
renderVar (Gen g) d  = show g ++ show d
renderVar (Rsv r rs) d  = show r ++ show d ++ showrs rs
 where
  showrs [] = ""
  showrs rs = chrLESS : concat (intersperse strLSEP $ map show rs)

mkVar :: Root -> Decor -> [GenRoot] -> Variable
mkVar r@(Gen g) d _ = (r, d, renderVar r d)
mkVar (Rsv r _) d rs
 | any badroot rs  = badvar
 | otherwise  = (root', d, renderVar root' d)
 where
  root' = Rsv r $ lnorm rs
  badroot (Std s)  =  s `elem` [strOBS,strMDL,strSCR]
  badroot _        =  False
  badvar = predVar ("!BadGenRoots"++show rs)

mkGVar :: Decor -> GenRoot -> Variable
mkGVar d g   = (r, d, renderVar r d) where r = Gen g

mkSVar :: String -> Decor -> Variable
mkSVar s d  = (r, d, renderVar r d) where r = Gen $ Std s

mkLVar :: String -> Decor -> Variable
mkLVar l d  = (r, d, renderVar r d) where r = Gen $ Lst l

mkRVar :: RsvRoot -> [GenRoot] -> Decor -> Variable
mkRVar r subs d = (r', d, renderVar r' d) where r' = Rsv r subs

showVar :: Variable -> String
showVar (_, _, s) = s
\end{code}
Some language facilities:
\begin{code}
theLEVar :: LElem -> Variable
theLEVar (LVar g)          =  mkGVar Scrpt g
theLEVar (LExpr (Var v))   =  v
theLEVar (LExpr (Evar e))  =  e
theLEVar _                 =  error "theLEVar: not Variable"

theLEExpr :: LElem -> Expr
theLEExpr (LVar g)         =  Var $ mkGVar Scrpt g
theLEExpr (LExpr e)        =  e
theLEExpr (LPred (Obs e))  =  e
theLEExpr _                =  error "theLEExpr: not Expr"
\end{code}
We also need to parse strings into roots
    \begin{eqnarray*}
       \LXName
    \\ \LXAlfDig
    \\ \LXRoots
    \end{eqnarray*}
\begin{code}
parseRoot :: String -> Root
parseRoot "" = Gen $ Std "!null-root!"
parseRoot s@(c:cs)
 | isAlpha c  =  p1 [c] cs
 | otherwise  =  Gen $ Std ("!non-root:"++s++"!")
 where
   -- seen initial alpha, and zero or more alphanum
   p1 toor ""
    = case reverse toor of
        [c] | c == chrOBS  ->  Rsv OBS []
            | c == chrMDL  ->  Rsv MDL []
            | c == chrSCR  ->  Rsv SCR []
        root                   ->  stringToRoot root
   p1 toor str@(c:cs)
    | isAlpha c                =  p1 (c:toor) cs
    | isDigit c                =  p1 (c:toor) cs
    | c == chrLST && null cs   =  Gen $ Lst $ reverse toor
    | otherwise  =  Gen $ Std ("!non-root:"++reverse toor++str++"!")

badRoot (Gen (Std ('!':_)))  =  True
badRoot _                    =  False
\end{code}
Sometimes we just want a \texttt{GenRoot}:
\begin{code}
parseGenRoot :: String -> GenRoot
parseGenRoot s
 = case parseRoot s of
    (Gen g)  ->  g
    r@(Rsv _ _)  ->  Lst ("!non-genroot:"++show r++"!")

badGenRoot (Std ('!':_))  =  True
badGenRoot (Lst ('!':_))  =  True
badGenRoot _              =  False
\end{code}
\newpage
Parsing variables:
    \begin{eqnarray*}
       \LXName
    \\ \LXAlfDig
    \\ \LXIdent
    \\ \LXRsv
    \\ \LXRsvSuffix
    \\ \LXGen
    \\ \LXDecor
    \\ \LXRoots
    \end{eqnarray*}
\begin{code}
parseVariable :: String -> Variable
parseVariable str
 = case scanner "" str of
    []                       ->  predVar ("!NoVar<"++str++">")
    [(_,TName n), (_,TEOF)]  ->  preVar n
    [(_,TIdent v),(_,TEOF)]  ->  v
    _                        ->  predVar ("!BadVar<"++str++">")

badVariable (_, _, ('!':_))  =  True
badVariable _                =  False
\end{code}

\newpage
\subsection{Making Variables}

\begin{code}
preVar, postVar, scrptVar, lstVar, lstVar', predVar :: String -> Variable
preVar nm  = mkVar (stringToRoot nm) Pre     []
postVar nm = mkVar (stringToRoot nm) Post    []
scrptVar nm   = mkVar (stringToRoot nm) Scrpt   []
lstVar  nm = mkVar (Gen $ Lst nm) Pre     []
lstVar' nm = mkVar (Gen $ Lst nm) Post    []
predVar nm = mkVar (Gen $ Std nm) NoDecor []

subVar, lsubVar :: String -> String -> Variable
subVar s nm  = mkVar (stringToRoot nm) (Subscript s) []
lsubVar s nm = mkVar (Gen $ Lst nm) (Subscript s) []

decorVar :: Decor -> Variable -> Variable
decorVar d (r@(Gen _),_,_) = mkVar r d []
decorVar d (r@(Rsv _ rs),_,_) = mkVar r d rs

(\\\) :: Variable -> [GenRoot] -> Variable
v@(Gen _,_,_) \\\ _ =  v
(r@(Rsv _ less1),d,_) \\\ less2 =  mkVar r d (less1 `mrgnorm` less2)

qnil         =  Q []
qvar   x     =  Q [preVar x]
qvars  xs    =  mkQ $ map preVar xs
qvarr  r     =  Q [lstVar r]
qvarrs rs    =  mkQ $ map lstVar rs
qvarsr xs r  =  mkQ $ (map preVar xs) ++ [lstVar r]

rootVar :: Root -> Variable
rootVar r = mkVar r NoDecor []
\end{code}


\newpage

\input{doc/VariableKinds}

\newpage
\subsection{List-Variables}

\input{doc/ListKinds}

We adopt the following ASCII representations of these variables:

\begin{tabular}{|c|c||c|c|}
  \hline
  % after \\: \hline or \cline{col1-col2} \cline{col3-col4} ...
  $Obs$ & \verb"O" & $Obs'$ & \verb"O'" \\\hline
  $Mdl$ & \verb"M" & $Mdl'$ & \verb"M'" \\\hline
  $Scr$ & \verb"S" & $Scr'$ & \verb"S'" \\
  \hline
\end{tabular}

In effect, \texttt{O}, \texttt{S} and \texttt{M} are reserved variable roots.
\begin{code}
strLISTS = [ strOBS, strMDL, strSCR ]

obsList  =  mkVar (Rsv OBS []) Pre  []
obsList' =  mkVar (Rsv OBS []) Post []
mdlList  =  mkVar (Rsv MDL []) Pre  []
mdlList' =  mkVar (Rsv MDL []) Post []
scrList  =  mkVar (Rsv SCR []) Pre  []
scrList' =  mkVar (Rsv SCR []) Post []
\end{code}

A range of tests:
\begin{code}
-- want a test for pure reserved list, with no _m
isPureList (_, Subscript _, _)  =  False
isPureList v                    =  isRsvV v

-- want a test for subscripted reserved list
isListSub v@(_, Subscript _, _)  =  isRsvV v
isListSub _                         =  False


obslookup :: (Variable -> t) -> Trie t -> Variable -> Maybe t
obslookup wrap trie v@(_, _, s)
 = case tlookup trie s of
     Nothing | isRsvV v  ->  Just $ wrap v
             | otherwise    ->  Nothing
     res                    ->  res

nonRsvList = not . isRsvV
\end{code}

\newpage
\subsection{Generic Abstract Syntax (Type/Expr/Pred)}

We define an abstract syntax tree that covers type-expressions,
and which merges both predicates and
expressions, giving a generic Type/Expr/Pred datatype.
This is done to avoid having a syntactical ``wrapper''
for boolean-valued expressions. This requires the precedence
levels of binary operators in both to be kept in sync.

We simply assume a general expression grammar with constants,
variables, prefix-, infix- and postfix-applications, and
binding and listing constructs, that covers types, expressions
and predicates:
\begin{eqnarray*}
   c \in Constant
   &\subseteq&
   \setof{true,false,0,1,2,\ldots}
\\ v \in Variable
   &\subseteq&
   \setof{x,y,z,\lnot,\Defd,\ldots}
\\ \oplus \in Operator
   &\subseteq&
   \setof{=,:,\land,\lor,\implies,\equiv,+,-,/,\times,\ldots}
\\ Q \in Binder &\subseteq& \setof{\forall,\exists,\exists!,\lambda,\mu}
\\ d \in Decl &::=&  v | v : pe
\\ s \in Subs &::=& pe^+ // v^+
\\ e \in Elem &::=& pe | pe \mapsto pe
\\ pe \in TEP
   &::=&
   c | v | pe~pe | pe \oplus pe | pe^{pe}
\\ && | Q \vec d @ pe | e [subs] | \{ e^* \} | [ pe^* ] | pe\cond{pe} pe
\end{eqnarray*}

We then post-process this to get the appropriate \texttt{Type},
\texttt{Pred} and \texttt{Expr} structures.
We now introduce our Type/Expr/Pred (TEP) abstract syntax:
\begin{code}
data TEP
-- *predicate* TEPS
 = TEPnull          -- used for Decl of form v
 | TEPperr String
 | TEPnum Int
 | TEPname String
 | TEPvar Variable
 | TEPprefix TEP TEP
 | TEPinfix Int String TEP TEP
 | TEPpostfix TEP TEP
 | TEPfactor [TEP]
 | TEPqvars [Variable]
 | TEPbind String [Variable] TEP TEP
 | TEPsub String [TEP] [Variable]
 | TEPuniv TEP
 | TEPcond TEP TEP TEP
 | TEPcomp TEP TEP
-- * higher order stuff
 | TEPpset [TEP]
 | TEPpsetc [String] TEP TEP
-- * language TEPs
 | TEPlang String [(String,TEP)] [SynSpec]
 | TEPllist [TEP] -- should only occur inside TEPlang
-- *expression* TEPs
 | TEPeerr String
 | TEPprod [TEP]
 | TEPset [TEP]
 | TEPsetc [Variable] TEP TEP
 | TEPseq [TEP]
 | TEPseqc [Variable] TEP TEP
 | TEPmap [(TEP, TEP)]
 | TEPtype TEP -- embedding types in expr/pred world.
-- *type* TEPS
 | TEPterr String
 | TEPtprod [TEP]
 | TEPtfun TEP TEP
 | TEPtpfun TEP TEP
 | TEPtmap TEP TEP
 | TEPtset TEP
 | TEPtseq TEP
 | TEPtseqp TEP
 | TEPtfree String [(String,[TEP])]
 deriving (Eq,Ord,Show)
\end{code}

\subsubsection{Token Parsers}

We now develop the Type/Expression/Predicate (TEP) parser, by
first giving a parser that scans a single token:
\begin{code}
type TEP_Parser t = GenParser Token () t

ptoken :: (Tok -> Maybe a) -> TEP_Parser a
ptoken test
  = token showToken posToken testToken
  where
    showToken (pos,tok) = show tok
    posToken (pos,tok)  = pos
    testToken (pos,tok) = test tok
\end{code}

Now we define basic parsers on tokens,
\begin{code}
p_string :: TEP_Parser String
p_string = ptoken pname <?> "string"
 where
   pname _         =  Nothing

p_namesym :: TEP_Parser String
p_namesym = ptoken pname <?> "name or symbol"
 where
   pname (TName s)  =  Just s
   pname (TSym s)   =  Just s
   pname (TKey s)   =  Just s
   pname (TKSym s)  =  Just s
   pname _          =  Nothing

p_thenamesym :: String -> TEP_Parser ()
p_thenamesym str = ptoken pname <?> ("the-token:"++str)
 where
   pname (TName s)  =  the str s
   pname (TSym s)   =  the str s
   pname (TKey s)   =  the str s
   pname (TKSym s)  =  the str s
   pname _          =  Nothing
   the str s
    | str == s   =  Just ()
    | otherwise  =  Nothing

p_name :: TEP_Parser String
p_name = ptoken pname <?> ("name")
 where
   pname (TName s)  =  Just s
   pname _          =  Nothing

p_thename :: String -> TEP_Parser ()
p_thename name = ptoken pname <?> ("name."++name)
 where
   pname (TName s)
    | s == name  =  Just ()
   pname _       =  Nothing

p_keyword :: String -> TEP_Parser ()
p_keyword key = ptoken pkeyword <?> ("keyword."++key)
 where
   pkeyword (TKey s)
    | s == key  =  Just ()
   pkeyword _   =  Nothing

p_lquote :: TEP_Parser ()
p_lquote = ptoken plquote <?> "lquote"
 where
   plquote TLQt  =  Just ()
   plquote _     =  Nothing

p_num :: TEP_Parser Int
p_num = ptoken pnum <?> "number"
 where
   pnum (TNum s)  =  Just (read s)
   pnum _         =  Nothing

p_lbr :: String -> TEP_Parser ()
p_lbr brs = ptoken pbr <?> ("left-br."++brs)
 where
   pbr (TKSym s)
    | s == brs  =  Just ()
   pbr _        =  Nothing

p_rbr :: String -> TEP_Parser ()
p_rbr brs = ptoken pbr <?> ("right-br."++brs)
 where
   pbr (TKSym s)
    | s == brs  =  Just ()
   pbr _        =  Nothing

p_sym :: String -> TEP_Parser ()
p_sym sym = ptoken psym <?> ("symbol."++sym)
 where
   psym (TSym s)
    | s == sym    = Just ()
   psym _         =  Nothing

p_asym :: TEP_Parser String
p_asym = ptoken pasym <?> ("any-symbol")
 where
   pasym (TSym s)   =  Just s
   pasym (TKSym s)  =  Just s
   pasym _          =  Nothing

p_ksym :: String -> TEP_Parser ()
p_ksym ksym = ptoken psym <?> ("keysymbol."++ksym)
 where
   psym (TKSym s)
    | s == ksym  =  Just ()
   psym _        =  Nothing

eofile :: TEP_Parser ()
eofile = ptoken peof <?> "end-of-file"
 where
   peof TEOF  =  Just ()
   peof _     =  Nothing

whitesp :: TEP_Parser ()
whitesp = ptoken wht <?> "whitespace"
 where
   wht (TWht _)  =  Just ()
   wht _         =  Nothing

defn_sep :: TEP_Parser ()
defn_sep = ptoken ne <?> "defn-sep."
 where
   ne TSep  =  Just ()
   ne _     =  Nothing
\end{code}

We also define our own lexeme wrapper:
\begin{code}
skipWhite = whitesp <|> eofile <|> return ()

lexify p = do { x <- p; skipWhite; return x }

nametxt = lexify p_name
name = do{ n <- nametxt; return (TEPname n) }
strng = do{ n <- lexify p_string; return (TEPname n) }
nameOrKey = do{ n <- lexify p_namesym; return (TEPname n) }
thename  = lexify . p_thename
thenamesym = lexify . p_thenamesym
keyword  = lexify . p_keyword
lquote = lexify p_lquote
num = do { n <- lexify p_num; return (TEPnum n) }
sym = lexify . p_sym
asym = do{ s <- lexify p_asym; return (TEPname s) }
keysym = lexify . p_ksym
lbracket = lexify . p_lbr
rbracket = lexify . p_rbr
defnsep = lexify defn_sep
\end{code}

Next, the brackets:
\begin{code}
keyDLSQBR = "[["
keyDRSQBR = "]]"
keyDLCBR  = "{{"
keyDRCBR  = "}}"
keySTRTYP = "|:"
keyENDTYP = ":|"

[lbr,lsqbr,lcbr,ldsqbr,ldcbr,starttype]
  = map lbracket [ "(", "[", "{", keyDLSQBR, keyDLCBR, keySTRTYP ]
[rbr,rsqbr,rcbr,rdsqbr,rdcbr,endtype]
  = map rbracket [ ")", "]", "}", keyDRSQBR, keyDRCBR, keyENDTYP ]
\end{code}

Finally, special handling for variables:
\begin{code}
p_variable :: TEP_Parser Variable
p_variable = ptoken pvar <?> "variable"
 where
   pvar (TIdent v)  =  Just v
   pvar (TName s)
    | s == strOBS  =  Just (Rsv OBS [],   Pre, s)
    | s == strMDL  =  Just (Rsv MDL [],   Pre, s)
    | s == strSCR  =  Just (Rsv SCR [],   Pre, s)
    | otherwise    =  Just (Gen $ Std s,  Pre, s)
   pvar _          =  Nothing

variable = do{ v <- lexify p_variable; return $ TEPvar v }


names :: TEP_Parser [String]
names = nametxt `sepBy1` cmma
\end{code}

\subsubsection{Precedence Tables}

We need to be able to establish the fixity and precedence
levels of operators, as well as which names are keywords.

We build a \texttt{Parsec} \texttt{OperatorTable} from
precedence tables, such as in module \texttt{Builtins}. In
order for this to work, we need to ensure that the binary
predicate operators ($\land$,$\lor$,$\implies$ and $\equiv$)
are included with appropriate precedences in the tables.



First we convert the table to a sorted association list,
segmented by precedence level. The sorted operators then need
to be converted into the \texttt{Parsec} operator-table type:
\begin{code}

tepOperators precTable
 = map (map tepOperator) sortedOps
 where
  precList = flattenTrie precTable
  sortedPrec = sortBy precOrd precList
  sortedOps = segment [] [] 0 sortedPrec

precOrd (n1,(p1,_)) (n2,(p2,_)) = compare (p1,n1) (p2,n2)

segment seg segs cp []  =  seg:segs
segment seg segs cp (op@(_,(p,_)):rest)
 | cp == p    =  segment (op:seg)  segs  cp rest
 | null seg   =  segment [op] segs        p rest
 | otherwise  =  segment [op] (seg:segs)  p rest

tepOperator (name,(pr,assoc))
 = Infix (do{sym name; return (TEPinfix pr name)} <?> ("op."++name)) assoc

\end{code}




\subsubsection{Infix Precedences}

This allows us to add new infix operators on-the-fly. If 3
tokens of the form
\verb'<TName "infix/infixr/infixl" TNum integer TName/TSym/TKSym something>'
are found the operator is
added to a list of existing operators with their associativity
and precedence. The remaining tokens are parsed.

If next two tokens after a \verb'TName "infix/infixr/infixl"'
contain and integer and name/symbol respectively then we need
to add a tuple of form (String, Precs) containing information
based on the values to the first accumulator and skip on to
next tokens.

\begin{code}

checkInfix :: [(String, Precs)] -> [Token] -> [Token] -> ([(String, Precs)], [Token])
checkInfix newPrecs newToks [] = (reverse newPrecs, reverse newToks)
checkInfix newPrecs newToks ((sp, h):xs)
 = if (numName /= Nothing)
   then case h of
          (TName "infix") -> checkInfix (ntriple:newPrecs) newToks xxs -- skip past next 2 tokens
          (TName "infixr") -> checkInfix (rtriple:newPrecs) newToks xxs
          (TName "infixl") -> checkInfix (ltriple:newPrecs) newToks xxs
          _ -> checkInfix newPrecs ((sp, h):newToks) xs -- check next token

   else checkInfix newPrecs ((sp,h):newToks) xs -- check next token
 where ntriple = (name, (val, AssocNone))  -- (String, Precs)
       ltriple = (name, (val, AssocLeft))
       rtriple = (name, (val, AssocRight))
       numName = checkNum xs -- does TNum token follow name?
       (h1:h2:xxs) = xs
       Just(val, name) = numName

checkNum [] = Nothing
checkNum ((sp, (TNum num)):xs)
 = checkOp n xs -- does TName/TSym/TKSym token follow number?
         where n = read num :: Int
checkNum (h:xs)
 = Nothing

checkOp n [] = Nothing
checkOp n ((sp, (TName x)):xs)
 = Just (n, x)                    -- Just (precedence,name)
checkOp n ((sp, (TSym x)):xs)
 = Just (n, x)
checkOp n ((sp, (TKSym x)):xs)
 = Just (n, x)
checkOp n (h:xs)
 = Nothing

\end{code}








\section{Text Handling for \texttt{Type}}


\subsubsection{Type Key-tokens}
We then address those key-words and key-symbols used for type
expressions
\begin{code}
tkeyBOOL  = "B"
tkeyINT   = "Z"
tkeyENV   = "ENV"
tkeyPOWER = "P"
tkeyPROD  = "x"

te_keywords
 = [ tkeyBOOL
   , tkeyINT
   , tkeyENV
   , tkeyPOWER
   , tkeyPROD
   ]

teKeywords = sbuild te_keywords

tksymHASTYPE = ":"
tksymAT = "@"
tksymALT = "|"
tksymDOT = "."
tksymARB   = "?"
tksymFUN = "->"
tksymPFUN = "-~>"
tksymMAP = "-+>"
tksymSEQ = "*"
tksymSEQP = "+"
tksymLBR = "("
tksymRBR = ")"

te_keysymbols
 = [ tksymARB
   , tksymFUN
   , tksymPFUN
   , tksymMAP
   , tksymSEQ
   , tksymSEQP
   , tksymHASTYPE
   , tksymAT
   , tksymALT
   , tksymDOT
   , tksymLBR
   , tksymRBR
   ]

teKeysymbols = sbuild te_keysymbols
\end{code}


\subsection{Showing a \texttt{Type}}

\begin{code}
instance Show Type where
 show t = tShow 0 t

tShow p B            = tkeyBOOL
tShow p Z            = tkeyINT
tShow p (Tvar v)     = v
tShow p Tenv         = tkeyENV
tShow p (Terror s t) = "TERR(" ++ s ++ " : " ++ tShow 0 t ++ ")"
tShow p Tarb         = tksymARB
tShow p t
 | tp <= p  =  tksymLBR++tShow 0 t++tksymRBR
 | otherwise  =  showType tp t
 where tp = typeLevel t

typeLevel (Tfree _ _) = 1
typeLevel (Tfun _ _)  = 2
typeLevel (Tpfun _ _) = 2
typeLevel (Tmap _ _)  = 2
typeLevel (Tprod _)   = 2
typeLevel (Tset _)    = 4
typeLevel (Tseq _)    = 5
typeLevel (Tseqp _)   = 5

showType p (Tfree n cs) = n ++ ' ':tksymAT++ (showSep 6 showCases (' ':tksymALT) cs)++"."
showType p (Tfun d r)   = tShow (p+1) d ++ ' ':tksymFUN ++ ' ':tShow p r
showType p (Tpfun d r)  = tShow (p+1) d ++ ' ':tksymPFUN ++ ' ':tShow p r
showType p (Tmap d r)   = tShow (p+1) d ++ ' ':tksymMAP ++ ' ':tShow p r
showType p (Tprod ts)   = showSep (p+1) tShow (' ':tkeyPROD++" ") ts
showType p (Tset t)     = tkeyPOWER++' ':tShow p t
showType p (Tseq t)     = tShow p t++tksymSEQ
showType p (Tseqp t)    = tShow p t++tksymSEQP
showType p t            = tShow p t

showCases p (n,ts) = " "++n ++ " " ++ showSep p tShow " " ts
\end{code}


\subsection{Parsing a \texttt{Type}}

We want type parsing to work in an environment were tokens have
been classified for parsing expressions and predicates,
where for example, `*` is an infix operator and not a postfix one.
This means we look for tokens of any type provided they have the
correct string.

\subsubsection{Type Keywords}
First, the key-token parsers:
\begin{code}
[  tbool
 , tint
 , tenv
 , tpower
 , tprod
 ] = map thenamesym te_keywords

[  tarb
 , tfunc
 , tpfunc
 , tmapsym
 , tseqm
 , tseqpp
 , tcolon
 , tat
 , talt
 , tdot
 , tlbr
 , trbr
 ] = map thenamesym te_keysymbols
\end{code}

Now, the grammar:
\begin{eqnarray*}
  T \in Type
   &::=& \Bool
       | \Int
       | \tau
       | Env
       | T^*
       | T^+
       | \power T
       | {}
\\ &&    T \times T
       | T \ffun T
       | T \fun T
       | T \pfun T
       | {}
\\ &&    Name~TC\mbox{-list}
       | ( T )
\\ && \mbox{(tightest binding first)}
\\  TC &::=& Name~ T~ T~ \ldots~ T
\end{eqnarray*}
More formally, we go with the following grammar:
\begin{eqnarray*}
   Type & \mapsto & FunType
\\ FunType & \mapsto & ProdType [ (\litm\fun|\litm\pfun|\litm\ffun) FunType ]
\\ ProdType & \mapsto & PreType [ \litm\times ProdType ]
\\ PreType & \mapsto & \{ \litm\power \}^* PostType
\\ PostType & \mapsto & BaseType \{ \litm* | \litm+ \}^*
\\ BaseType & \mapsto & \litm? | \Bool | \Int | FreeType | \litm( Type \litm)
\\ FreeType & \mapsto & Name \{ Name \{ Type \} ^*\}^*
\end{eqnarray*}

\subsubsection{Type Parser}
\begin{code}
tepType = tepFunType

tepFunType
 = do ptyp <- tepProdType
      tepFunTypeRest ptyp

tepFunTypeRest ptyp
 = try (tepFunTypeArrow tfunc TEPtfun ptyp)
   <|> try (tepFunTypeArrow tpfunc TEPtpfun ptyp)
   <|> try (tepFunTypeArrow tmapsym TEPtmap ptyp)
   <|> return ptyp

tepFunTypeArrow tarrow tep ptyp
 = do tarrow
      ftyp <- tepFunType
      return (tep ptyp ftyp)

tepProdType
 = do typ1 <- tepPreType
      typs <- many ( do { tprod ; tepPreType } )
      if null typs
       then return typ1
       else return (TEPtprod (typ1:typs))

tepPreType
 = do power <- many tpower
      tpost <- tepPostType
      return (mkpre power tpost)
 where
   mkpre []     post  =  post
   mkpre (p:ps) post  =  TEPtset (mkpre ps post)

tepPostType
 = do btyp <- tepBaseType
      post <- many tepPostTCons
      return (mkpost btyp post)
 where
   mkpost btyp [] = btyp
   mkpost btyp (p:ps) = mkpost (p btyp) ps


tepPostTCons
 = try ( do { tseqm ; return TEPtseq  })
   <|>
   try ( do { tseqpp; return TEPtseqp })

tepBaseType
 =     try ( do { tarb  ; return (TEPname tksymARB) } )
   <|> try ( do { tbool ; return (TEPname tkeyBOOL) } )
   <|> try ( do { tint  ; return (TEPname tkeyINT)  } )
   <|> try ( do { tenv  ; return (TEPname tkeyENV)  } )
   <|> try (between tlbr trbr tepType)
   <|> try tepFreeType

tepFreeType
 = do
      (TEPvar v) <- variable
      let nm = varKey v
      let tn = (TEPname nm)
      rest <- optionMaybe tepFreeClauses
      case rest of
        Nothing -> return tn
        (Just cls) -> do tdot
                         return (TEPtfree nm cls)

tepFreeClauses
  = do tat
       tepFreeClause `sepBy` talt

tepFreeClause
 = do (TEPvar v) <- variable
      let cn = varKey v
      typs <- many tepType
      return (cn,typs)

tepTypes = tepType `sepBy1` cmma
\end{code}

\newpage
\section{Text Handling for \texttt{Pred}/\texttt{Expr}}


Pretty-printing is based on classifying syntactic
constructs into three groups:
\begin{description}
  \item[Closed]
    Items that are never bracketed, because they a are simple atomic
    items, or have brackets as part of their syntax.
  \item[Open] Items that must be enclosed in parentheses if they occur anywhere
   but at the top (loosest) level. The immediate interior of parentheses
   of bracketing of any sort is always taken as being at the loosest possible level.
  \item[Dependent]
    Items that are bracketed if their precedence level is lower than that of
    the context in which they appear. Typically these are infix operators,
    and their sub-components occur at the level of the operators own precedence.
\end{description}
\begin{code}
data SynPrecClass = SPClosed | SPOpen | SPDependent
 deriving (Eq,Show)
\end{code}


\subsubsection{\texttt{Expr} Precedences}

\begin{code}
exprPrecClass (App s e)        =  SPDependent
exprPrecClass (Bin s i e1 e2)  =  SPDependent
exprPrecClass (Equal e1 e2)    =  SPDependent
exprPrecClass (Cond pc et ee)  =  SPOpen
exprPrecClass (Build s es)     =  SPOpen
exprPrecClass (The tt qs pr)      =  SPOpen
exprPrecClass (Eabs tt qs e)      =  SPOpen
exprPrecClass (Esub e sub)     =  SPOpen
exprPrecClass (Eerror s)       =  SPOpen
exprPrecClass (EPred p)        =  predPrecClass p
exprPrecClass (Efocus ef)      =  exprPrecClass ef
exprPrecClass _                =  SPClosed

isEClosed e  =  exprPrecClass e == SPClosed     -- 11
isEOpen e    =  exprPrecClass e == SPOpen       --  7
isEDep e     =  exprPrecClass e == SPDependent  --  3

ePrec (App _ _)      =  opPrec 1 exprBinGen
ePrec (Equal _ _)    =  opPrec 1 equalName
ePrec (Bin _ p _ _)  =  p
ePrec (Efocus ef)    =  ePrec ef
ePrec _              =  1
\end{code}

\subsubsection{\texttt{Pred} Precedences}

\begin{code}
predPrecClass TRUE                   = SPClosed
predPrecClass FALSE                  = SPClosed
predPrecClass (Obs e)             = exprPrecClass e
predPrecClass (Not pr)               = SPDependent
predPrecClass (And prs)              = SPDependent
predPrecClass (Or prs)               = SPDependent
predPrecClass (NDC pr1 pr2)          = SPDependent
predPrecClass (Imp pr1 pr2)          = SPDependent
predPrecClass (RfdBy pr1 pr2)        = SPDependent
predPrecClass (Eqv pr1 pr2)          = SPDependent
predPrecClass (Lang s p les ss)
 | isBinSpec (LangSpec les ss)       = SPDependent
 | otherwise                         = SPClosed
predPrecClass (Univ tt pr)              = SPClosed
predPrecClass (Pvar s)               = SPClosed
predPrecClass (Papp prf pra)         = SPDependent
predPrecClass (Psapp pr spr)         = SPDependent
predPrecClass (Psin pr spr)          = SPDependent
predPrecClass (Pfocus fpr)           = predPrecClass fpr
predPrecClass _                      = SPOpen

isPClosed pr  =  predPrecClass pr == SPClosed     --  5
isPOpen pr    =  predPrecClass pr == SPOpen       -- 11
isPDep pr     =  predPrecClass pr == SPDependent  --  9

pPrec (Papp _ _)                =  opPrec 1 predBinGen
pPrec (Psapp _ _)               =  opPrec 1 predBinGen
pPrec (Not pr)                  =  opPrec 1 notName
pPrec (And prs)                 =  opPrec 1 andName
pPrec (Or prs)                  =  opPrec 1 orName
pPrec (NDC pr1 pr2)             =  opPrec 1 ndcName
pPrec (Imp pr1 pr2)             =  opPrec 1 impName
pPrec (RfdBy pr1 pr2)           =  opPrec 1 rbyName
pPrec (Eqv pr1 pr2)             =  opPrec 1 equivName
pPrec (Psin pr spr)             =  opPrec 1 psinName
pPrec (Lang s p les ss)         =  p
pPrec (Pfocus fpr)              =  pPrec fpr
pPrec _                         =  1
\end{code}

\subsection{Showing \texttt{Expr}}

First, expression-related lexical elements:
\begin{code}

keyTRUE     =  "TRUE"
keyFALSE    =  "FALSE"
keyTHE      =  "the"
ksymMAPLET  =  "|->"
ksymLCOND   =  "<|"
ksymRCOND   =  "|>"
ksymEABS    =   "\\\\"

\end{code}


The class function \texttt{show} is the top-level call
(also at precedence level 0),
and is never called recursively by itself.
The auxilliary function \texttt{eShow} is the one where we make
precedence 0 level recursive calls.
\begin{code}
instance Show Expr where
 show e = eShow 0 e

eShow 0 e = showExpr 0 e
eShow pouter e
 | isEClosed e       =  showExpr pouter e
 | isEOpen   e       =  "("++showExpr 0 e++")"
 | pinner <= pouter  =  "("++showExpr 0 e++")"
 | otherwise         =  showExpr pinner e
 where pinner = ePrec e

showExpr _ T = keyTRUE
showExpr _ F = keyFALSE
showExpr _ (Num i) = show i
showExpr _ (Var v) = showVar v
showExpr _ (Evar e) =  showVar e
showExpr _ (Eerror m) = "EERR(" ++ m ++")"
showExpr _ (Prod es) = "(" ++ showSep 0 showExpr "," es ++ ")"
showExpr _ (Set es) = "{" ++ showSep 0 showExpr "," es ++ "}"

showExpr _ (Setc tt qs TRUE e)
  = "{ "++ show qs ++" @ "++ showExpr 0 e ++" }"
showExpr _ (Setc tt qs pr e)
  = "{ "++ show qs ++" | "++ showPred 0 pr ++" @ "++ showExpr 0 e ++" }"

showExpr _ (Seq es) = "["++ showSep 0 showExpr "," es ++"]"
showExpr _ (Seqc tt qs pr e)
  = "["++ show qs ++"|"++ showPred 0 pr ++"@"++ showExpr 0 e ++"]"

showExpr _ (Map ees) = "{"++ showSep 0 mShow ", " ees ++"}"
showExpr p (Efocus fe) = [eFocusStart]++showExpr p fe++[eFocusEnd]
showExpr _ (Esub e s)
  | isEClosed e  =      showExpr 0 e        ++ show s
  | otherwise    = "("++showExpr 0 e ++ ")" ++ show s

showExpr p (The tt x (And [rg, pr]))
 | rg == TRUE  =  keyTHE ++ " " ++ showVar x
                         ++" @ " ++ showPred p pr
 | otherwise   =  keyTHE ++ " " ++ showVar x
                         ++ " | " ++ showPred 0 rg
                         ++" @ " ++ showPred p pr
showExpr p (The tt x pr)
 = keyTHE ++ " " ++ showVar x ++ " @ " ++ showPred p pr

showExpr p (Cond cp te ee)
 = eShow (p+1) te
   ++ " "++ksymLCOND++" " ++ pShow 0 cp ++ " "++ksymRCOND++" "
   ++ eShow (p+1) ee
showExpr p (Build n es) = n ++ " " ++ showSep (p+1) eShow " " es
showExpr p (Eabs tt qs eb)
  = ksymEABS ++ " " ++ show qs ++ " @ " ++ eShow (p+1) eb
showExpr p (App "-" es) = "-" ++ eShow (p+1) es -- special case
showExpr p e@(App v es) = v ++ " " ++ eShow (q+1) es
 where q = ePrec e
showExpr p (Bin op q e1 e2)
  = eShow q e1 ++" "++ op ++" "++ eShow q e2
showExpr p e@(Equal e1 e2)
  = eShow q e1 ++" = "++ eShow q e2
  where q = ePrec e

showExpr p (EPred pr) = showPred p pr

-- showExpr p e = "YYYYYY(showExpr of unexpected variant)YYYYY"


eFocusStart = chr 171  -- start underlining
eFocusEnd   = chr 187  -- end underlining

mShow p (e1,e2) = eShow p e1 ++ " " ++ ksymMAPLET ++ " " ++ eShow p e2
\end{code}

This is also  used by the Predicate pretty-printer
below to avoid excessive brackets around observation
variables expressions.

\subsection{Showing \texttt{Pred}}

Displaying predicates, designed to be compatible with the text
parser.
\begin{code}
keyLNOT     =  notName -- logical negation
keyFORALL   =  "forall"
keyEXISTS   =  "exists"
keyEXISTS1  =  "exists1"
keyPFORALL  =  "Forall"
keyPEXISTS  =  "Exists"
ksymPEABS   =  "\\!"
ksymPPABS   =  "!!"
keyREC      =  "rec"     -- a.k.a. "mu"
keyLQUOTE   =  "`"       -- language quotation
keyDEFD     =  "DEFD"
\end{code}
\begin{code}
instance Show Pred where
  show p                    = pShow 0 p

pShow 0 pr = showPred 0 pr
pShow pouter pr
 | isPClosed pr      =  showPred pouter pr
 | isPOpen   pr      =  "("++showPred 0 pr++")"
 | pinner <= pouter  =  "("++showPred 0 pr++")"
 | otherwise         =  showPred pinner pr
 where pinner = pPrec pr

showPred _ TRUE    = keyTRUE
showPred _ FALSE   = keyFALSE
showPred _ (Pvar pr) = show pr
showPred _ (Perror m) = "PERR(" ++ m ++")"

showPred p (Sub pr s)
  | isPClosed pr  =       showPred p pr        ++ show s
  | otherwise     =  "("++showPred 0 pr ++ ")" ++ show s

showPred p (Psub pr s)
  | isPClosed pr  =       showPred p pr        ++ show s
  | otherwise     =  "("++showPred 0 pr ++ ")" ++ show s

showPred p pr@(Obs e)  =  showExpr p e

showPred p (Defd e) = keyDEFD ++"("++show e++")"

showPred p (TypeOf e t)
 | isEClosed e  =        show e        ++ keySTRTYP++show t++keyENDTYP
 | otherwise    = "(" ++ show e ++ ")" ++ keySTRTYP++show t++keyENDTYP

showPred _ (Univ tt pr) = keyDLSQBR++" "++showPred 0 pr++" "++keyDRSQBR

showPred p pr@(Papp p1 p2) = pShow q p1 ++ " " ++ pShow (q+1) p2
 where q = pPrec pr

showPred p pr@(Psapp pr1 spr)
 = pShow q pr1 ++ " " ++ showPredSet (q+1) spr
 where q = pPrec pr

showPred p pr@(Psin pr1 spr)
 = pShow q pr1 ++ " IN " ++ showPredSet q spr
 where q = pPrec pr

showPred _ (Pforall qs pr)
 = keyPFORALL ++ " " ++ show qs ++ " @ " ++ showPred 0 pr

showPred _ (Pexists qs pr)
 = keyPEXISTS ++ " " ++ show qs ++ " @ " ++ showPred 0 pr

showPred p (Ppabs qs pr)
 = ksymPPABS ++ " " ++ show qs ++ " @ " ++ showPred 0 pr

showPred _ (Peabs qs pr)
 = ksymPEABS ++ " " ++ show qs ++ " @ " ++ showPred 0 pr

showPred p pr@(Lang s q les ss)
  | isBinSpec (LangSpec les ss) = showLang q les ss
  --  = if q <= p
  --     then "("++showLang 0 les ss++")"
  --     else showLang q les ss
  | otherwise = keyLQUOTE++showLang 0 les ss++keyLQUOTE

showPred p (Pfocus pr) = [pFocusStart]++showPred p pr++[pFocusEnd]

-- showPred p (Exists tt qs (And [rg, pr]))
--  | rg == TRUE  =  keyEXISTS ++ " " ++ show qs
--                             ++ " @ " ++ pShow p pr
--  | otherwise   =  keyEXISTS ++ " " ++ show qs
--                             ++ " | " ++ showPred 0 rg
--                             ++ " @ " ++ pShow p pr

showPred p (Exists tt qs pr)
 = keyEXISTS ++ " " ++ show qs ++ " @ " ++ pShow p pr

-- showPred p (Exists1 tt qs (And [rg, pr]))
--  | rg == TRUE  =  keyEXISTS1 ++ " " ++ show qs
--                             ++ " @ " ++ pShow p pr
--  | otherwise   =  keyEXISTS1 ++ " " ++ show qs
--                             ++ " | " ++ showPred 0 rg
--                             ++ " @ " ++ pShow p pr

showPred p (Exists1 tt qs pr)
 = keyEXISTS1 ++ " " ++ show qs ++ " @ " ++ pShow (p+1) pr

-- showPred p (Forall tt qs (Imp rg pr))
--  | rg == TRUE  =  keyFORALL ++ " " ++ show qs
--                             ++ " @ " ++ pShow p pr
--  | otherwise   =  keyFORALL ++ " " ++ show qs
--                             ++ " | " ++ showPred 0 rg
--                             ++ " @ " ++ pShow p pr

showPred p (Forall tt qs pr)
 = keyFORALL ++ " " ++ show qs ++ " @ " ++ pShow (p+1) pr

showPred p (If cp tp ep)
 = pShow (p+1) tp
   ++ " "++ksymLCOND++" " ++ showPred 0 cp ++ " "++ksymRCOND++" "
   ++ pShow (p+1) ep
showPred p pr@(Eqv p1 p2)  = pShow q p1 ++ " == " ++ pShow q p2
 where q = pPrec pr
showPred p pr@(Imp p1 p2)  = pShow q p1 ++ " => " ++ pShow q p2
 where q = pPrec pr
showPred p pr@(RfdBy p1 p2)  = pShow q p1 ++ " |= " ++ pShow q p2
 where q = pPrec pr
showPred p pr@(Not pr') = keyLNOT++pShow q pr'
 where q = pPrec pr
showPred p pr@(Or ps)   = showSep q pShow " \\/ " ps
 where q = pPrec pr
showPred p pr@(NDC p1 p2)   = pShow q p1 ++ " |~| " ++ pShow q p2
 where q = pPrec pr
showPred p pr@(And ps)  = showSep q pShow " /\\ " ps
 where q = pPrec pr

-- showPred p pr = "XXXXXX(showPred of unexpected variant)XXXXXX"
\end{code}

Special characters, used here and elsewhere:
\begin{code}
pFocusStart = chr 171
pFocusEnd   = chr 187
beginPFocus = '!'
beginEFocus = '!'
endEFocus   = '!'
endPFocus   = '!'
deepFocus   = '_'
\end{code}

Now, displaying predicate sets.
\begin{code}
instance Show PredSet where show ps = showPredSet 0 ps

showPredSet _ (PSName nm) = nm

showPredSet _ (PSet spr)
 = keyDLCBR ++ showSep 0 showPred "," spr ++ keyDRCBR

showPredSet _ (PSetC qs pr1 pr2)
 = keyDLCBR
   ++" "++show qs
   ++" | "++showPred 0 pr1
   ++" @ "++showPred 0 pr2
   ++" "++keyDRCBR

showPredSet p (PSetU s1 s2)
 | q <= p     =  "(" ++ psetu 0 ++ ")"
 | otherwise  =  psetu q
 where
   q = opPrec 1 psunionName
   psetu q = showPredSet q s1
              ++" "++psunionName++" "
              ++showPredSet q s2
\end{code}


\subsection{Parsing \texttt{Pred}/\texttt{Expr}}

\subsubsection{Pred-Expr Keywords}

We now define the keywords, most of which denote quantifiers, as
well as a parser that parses any quantifier and returns as
string the keyword
\begin{code}
pe_keywords
 = [ keyFORALL
   , keyEXISTS
   , keyEXISTS1
   , keyPFORALL
   , keyPEXISTS
   , keyREC
   , keyTHE
   ]

peKeywords = sbuild pe_keywords

[keyForall
 ,keyExists
 ,keyExists1
 ,keyPforall
 ,keyPexists
 ,keyRec
 ,keyThe
 ] = map keyword pe_keywords
\end{code}

\begin{code}
lnot = thename keyLNOT
pe_symasnames =  [keyLNOT]
\end{code}

We then address those key-symbols that are not pre-defined
binary operators:
\begin{code}
ksymESUB  = "//"   -- a.k.a. "/" in substitutions
ksymPSUB  = "///"   -- a.k.a. "/" in substitutions


pe_keysymbols
 = [ ":"
   , ","
   , "."
   , "@"
   , ksymESUB
   , ksymPSUB
   , "|"
   --, compName
   , lcondName
   , rcondName
   , ksymMAPLET
   , ksymEABS
   , ksymPPABS
   , ksymPEABS
   , scKeyCOV
   ]

[colon
 ,cmma
 ,dot
 ,atsign
 ,esubsep
 ,psubsep
 ,pipesign
 --,semicolon
 ,lcond
 ,rcond
 ,maplet
 ,elambda
 ,pplambda
 ,pelambda
 ,pcover
 ] = map keysym pe_keysymbols

semicolon = sym compName

nmsyms = tnil

pe_brackets
 = [ "("
   , "{"
   , "["
   , keyDLSQBR
   , keyDLCBR
   , keySTRTYP
   , ")"
   , "}"
   , "]"
   , keyDRSQBR
   , keyDRCBR
   , keyENDTYP
   ]

peKeysymbols = sbuild (pe_keysymbols ++ pe_brackets)
\end{code}

We have a conflict between the use of \lit/ for division, and as
the separator between expressions and variables in a
substitution --- we resolve this by doubling/tripling up the latter,
so that \lit{//} flags expression substitutions,
whereas \lit{///} indicates predicates as replacements.

We also have a conflict  with \lit{\BS} for set difference,
and using it Haskell-style to denote the lambda in
a lambda-expression. We keep the single backslash for set-difference
and use a double one (\lit{\BS\BS}) for lambdas.

We build our grammar over the following collection of basic `words':

\SNWORDS

\newpage
We define a general syntax covering both expressions
and predicates and use post-processing to disambiguate them.

\TEPSYNTAX

\newpage
We want to left-factor this grammar as much as possible.

\TEPLSYNTAX

\newpage
\subsubsection{Top-level Parser}

In \texttt{Parsec} terms,
we shall build an term parser over a basic `factor'
parser, and at the top-level look for conditionals.
\begin{eqnarray*}
   \SNTEP
   \\ \PPredExpr
\end{eqnarray*}
\begin{code}
parseTEP ptlt@(prec,_)
 = try (pCond ptlt pterm) <|> try pterm
 where
   pterm = buildExpressionParser (tepOperators prec) (tepFactor ptlt)

pCond ptlt pterm
 = do left <- pterm
      lcond
      cnd <- parseTEP ptlt
      rcond
      right <- pterm
      return $ TEPcond left cnd right
\end{code}

\newpage
\subsubsection{Parsing $\SNBinderI$}
Simple quantifier parser:
\begin{eqnarray*}
   \SNBinder
\end{eqnarray*}
\begin{code}
quant :: TEP_Parser String
quant =   (do {keyForall; return keyFORALL})
      <|> (do {keyExists; return keyEXISTS})
      <|> (do {keyExists1; return keyEXISTS1})
      <|> (do {keyPforall; return keyPFORALL})
      <|> (do {keyPexists; return keyPEXISTS})
      <|> (do {keyThe; return keyTHE})
      <|> (do {elambda; return ksymEABS})
      <|> (do {pplambda; return ksymPPABS})
      <|> (do {pelambda; return ksymPEABS})
      <|> (do {keyRec; return keyREC})
\end{code}


\subsubsection{Parsing $\LSNFactorI$}

\begin{eqnarray*}
   \LSNFactor \qquad\mbox{--- or, equivalently, }b^+
\end{eqnarray*}
\begin{code}
tepFactor ptlt = liftM mkTEPfactor $ many1 $ tepBase ptlt

mkTEPfactor [tep]  =  tep
mkTEPfactor teps   =  TEPfactor teps
\end{code}

\newpage
\subsubsection{Parsing $\LSNBaseI$}
\begin{eqnarray*}
   \LSNBase
\end{eqnarray*}
\begin{code}
tepBase ptlt@(_,lptree)
 =      try (langParse ptlt lptree)
    <|> try (tepBrExprs ptlt)
    <|> try (parseUniv ptlt)
    <|> try (parseSetMap ptlt)
    <|> try (parseListSubs ptlt)
    <|> try (parseHSet ptlt)
    <|> try (parseQuant ptlt)
    <|> try parseType
    -- <|> try name
    <|> try variable
    <|> try num
\end{code}
Parenthesised/Product expressions
\begin{eqnarray*}
   && \lit(~pe^+_,~\lit)
\end{eqnarray*}
\begin{code}
tepBrExprs ptlt = do lbr
                     p <- tepExprs ptlt
                     rbr
                     case p of
                      []   ->  return TEPnull
                      [p]  ->  return p
                      _    ->  return (TEPprod p)

tepExprs ptlt
  = (parseTEP ptlt) `sepBy1` cmma
    <?> "expressions"
\end{code}
Universal closure
\begin{eqnarray*}
   && \lit{[[}~pe~\lit{]]}
\end{eqnarray*}
\begin{code}
parseUniv ptlt = do ldsqbr
                    p <- parseTEP ptlt
                    rdsqbr
                    return (TEPuniv p)
\end{code}

\newpage
\subsubsection{Parsing Set/Map Expressions}
\begin{eqnarray*}
 && \lit\{~se
\\ \LSNSExpr
\\ \LSNSExprCont
\\ \LSNMExprCont
\end{eqnarray*}
\begin{code}
parseSetMap ptlt
  =  do lcbr
        (try (rightbr []) <|> try pe_sec <|> try scomp)
  where

    rightbr pes = do { rcbr; return (TEPset pes) }
    pe_sec = do p <- parseTEP ptlt
                (try (rightbr [p])
                 <|> try (pset [p])
                 <|> try (pmap p))
    pset pes = do cmma
                  p <- parseTEP ptlt
                  let pes'=pes++[p]
                  (try (rightbr pes') <|> pset pes')

    pmap de = do maplet
                 re <- parseTEP ptlt
                 pmap' [(de,re)]
    pmap' me = (try (mrbr me) <|> try (pmap'' me))
    mrbr me = do {rcbr; return (TEPmap me)}
    pmap'' me = do cmma
                   d <- parseTEP ptlt
                   maplet
                   r <- parseTEP ptlt
                   pmap' (me++[(d,r)])

    scomp = do (TEPqvars vs) <- parseQVars ptlt
               rng <- (try (parseRange ptlt) <|> return (TEPname "TRUE"))
               expr <- (try sexpr <|> return (TEPnull))
               rcbr
               return (TEPsetc vs rng expr)
    sexpr = do atsign
               parseTEP ptlt
\end{code}

\newpage
\subsubsection{Substitutions}

\begin{code}
instance Show (Substn Variable Expr) where
  show (Substn sub)
    = "[ "++(showSepList ',' as)++ksymESUB++showvs qv++" ]"
    where
      as = map snd sub
      qv = map fst sub
      showvs = concat . intersperse "," . map varKey

instance Show (Substn GenRoot Pred) where
  show (Substn sub)
    = "[ "++(showSepList ',' as)++ksymPSUB++showns qv++" ]"
    where
      as = map snd sub
      qv = map fst sub
      showns = concat . intersperse "," . map show
\end{code}


\subsubsection{Parsing List Expressions/Substitutions}

\begin{eqnarray*}
   \LSNLExpr
\\ \LSNLExprCont
\end{eqnarray*}
\begin{code}
parseListSubs ptlt
  =  do lsqbr
        (try (rightbr []) <|> try (pe_lec []))
  where

    rightbr pes = do { rsqbr; return (TEPseq pes) }

    pe_lec pes = do p <- parseTEP ptlt
                    ( try (rightbr (pes++[p]))
                      <|> try (elec (pes++[p]))
                      <|> try (plec (pes++[p]))
                      <|> try (pe_lec' (pes++[p])) )
    pe_lec' pes = do cmma
                     pe_lec pes

    elec pes = do esubsep
                  lec' ksymESUB pes []
    plec pes = do psubsep
                  lec' ksymPSUB pes []
\end{code}

\newpage
Parsing $~qs, ~\lit]$
\begin{code}
    -- (TEPqvars vs rs) <- parseQVars ptlt -- after q <- quant

    lec' sep pes _
     = do (TEPqvars vs) <- parseQVars ptlt
          rsqbr
          return (TEPsub sep pes vs)

    -- lec' sep pes sub = do n <- lexify p_name
    --                       ( try (rightbr' sep (pes,sub++[n]))
    --                         <|> try (lec'' sep pes (sub++[n])) )
    -- lec'' sep pes sub = do cmma
    --                        lec' sep pes sub

    -- rightbr' sep (pes,sub) = do rsqbr
    --                             return (TEPsub sep pes sub)
\end{code}

\subsubsection{Parsing Higher-Order Set Expressions}

\begin{eqnarray*}
   \LSNHExpr
\\ \LSNHExprCont
\end{eqnarray*}
\begin{code}
parseHSet ptlt
  =  do ldcbr
        (try (rightbr []) <|> try pe_sec <|> try scomp)
  where

    rightbr pes = do { rdcbr; return (TEPpset pes) }

    pe_sec = do p <- parseTEP ptlt
                (try (rightbr [p]) <|> try (pset [p]))

    pset pes = do cmma
                  p <- parseTEP ptlt
                  let pes'=pes++[p]
                  (try (rightbr pes') <|> pset pes')

    scomp = do ns <- names
               rng <- (try (parseRange ptlt) <|> return (TEPname "TRUE"))
               expr <- (try sexpr <|> return (TEPnull))
               rdcbr
               return (TEPpsetc ns rng expr)
    sexpr = do atsign
               parseTEP ptlt
\end{code}

\newpage
Quantified Predicates/Expressions
\begin{eqnarray*}
   b \in Base
   &::=& \ldots |  Q~qs~[ \lit| ~pe ]~\lit@~pe
\end{eqnarray*}
\begin{code}
parseQuant ptlt
 = do q <- quant
      (TEPqvars vs) <- parseQVars ptlt
      rng <- (try (parseRange ptlt) <|> return TEPnull)
      atsign
      pr <- parseTEP ptlt
      return (TEPbind q vs rng pr)
\end{code}

\texttt{parseRange} parses $\lit| ~pe$
\begin{code}
parseRange ptlt
 = do pipesign
      parseTEP ptlt
\end{code}

Type-expressions
\begin{eqnarray*}
\\ b \in Base
   &::=&
   \ldots | \lit{|:}~te~\lit{:|}
\end{eqnarray*}
\begin{code}
parseType
 = do starttype
      ttep <- tepType
      endtype
      return (TEPtype ttep)
\end{code}


\newpage
\subsubsection{Quantifier Variables}

We write variable lists as comma-separated.
$$
  x_1,\ldots,x_m
$$
\begin{code}
instance Show QVars where
 show (Q qs) = mkSepList ',' $ map showVar qs
\end{code}


\texttt{parseQVars} parses $qs$,
\begin{eqnarray*}
   \SNQVars
\end{eqnarray*}
\begin{code}
parseQVars ptlt
 = do vs <- (try parseQVS <|> return [])
      return (TEPqvars $ map strip vs)
 where strip (TEPvar v) = v
       strip tep = predVar ('?':show tep++"?")

parseQVS = variable `sepBy1` cmma
\end{code}

\subsubsection{Map expression parser}
\begin{code}
mapExpr ptlt = do p <- parseTEP ptlt
                  maplet
                  q <- parseTEP ptlt
                  return (p,q)
               <?> "map expression"

mapExprs ptlt
 = (mapExpr ptlt) `sepBy1` cmma
   <?> "map expressions"
\end{code}

\subsubsection{Parsing lists of Pred/Expr}

\begin{code}
parseTEPs ptlt = (parseTEP ptlt) `sepBy1` cmma
\end{code}

\newpage
\subsection{Side-Conditions}

\input{doc/SideConditions-Notation}

\begin{code}
scKeyCND = "CND"  ; scKeyCnd = "cnd"
scKeyNFI = "##"   ; scKeyNfi = "#"
scKeyTFO = "=="   ; scKeyTfo = "="
scKeyCOV = "<<"   ; scKeyCov = "<"
scKeyFRS = "FRSH" ; scKeyFrs = "frsh"
scKeyAnd = ";"
pad str = " " ++ str ++ " "
scvlist = mkSepList ',' . map varKey

instance Show SideCond where

 show SCtrue = "true"

 show (SCisCond PredM pn)  =  scKeyCND ++ " " ++ pn
 show (SCisCond m vn)      =  scKeyCnd ++ " " ++ vn

 show (SCnotFreeIn PredM vs pn)  =  pn ++ pad scKeyNFI ++ scvlist vs
 show (SCnotFreeIn m     vs vn)  =  vn ++ pad scKeyNfi  ++ scvlist vs

 show (SCareTheFreeOf PredM vs pn)  =  pn ++ pad scKeyTFO ++ scvlist vs
 show (SCareTheFreeOf m     vs vn)  =  vn ++ pad scKeyTfo  ++ scvlist vs

 show (SCcoverTheFreeOf PredM vs pn)  =  pn ++ pad scKeyCOV  ++ scvlist vs
 show (SCcoverTheFreeOf m     vs vn)  =  vn ++ pad scKeyCov   ++ scvlist vs

 show (SCfresh PredM v)  =  scKeyFRS ++ " " ++ varKey v
 show (SCfresh m     v)  =  scKeyFrs ++ " " ++ varKey v

 show (SCAnd []) = ";!"
 show (SCAnd [sc]) = ';':show sc
 show (SCAnd scs) = concat $ intersperse (pad scKeyAnd) $ (map show scs)
\end{code}

\newpage
\section{Text Handling for \texttt{Lang}}

A language specification is an interleaving
of explicit tokens with symbols denoting various language elements.
The basic language elements are variable (\texttt{V}), type (\texttt{T}),
 expression (\texttt{E}) and
predicate (\texttt{P}).
Composite language elements are lists,
built from basic elements,
followed immediately by
a multiplicity specifier: free (\texttt{*}) or linked (\texttt{\#}),
and then a separator token.
Free lists can be of any length,
whereas all linked lists must have the same length
in any instance of the language construct.
The above language elements are then interleaved
with tokens (anything else), which can be null.

A properly formed language specifier is two lists,
one of language elements (\texttt{LElem}),
the other of syntax specifiers (\texttt{SynSpec}),
which must satisfy a particular relationship.
A starting token must be supplied (which may be null --- \texttt{SSNull}),
and then for each language element in order,
the syntax-specifier list must contain either one or two
tokens:
a basic language element is followed by a single token (\texttt{SSTok});
a list element is followed by two tokens---the first denotes the list
separator (\texttt{SSSep}), the second is a following token,
as for the basic case.

\subsection{Showing a \texttt{Lang}}

We expect the two lists to be arranged as described above,
and an error message occurs if that relationship does not hold.
\begin{code}
showLang p [] [SSNull] = ""
showLang p [] [SSTok s] = s

showLang p (LList les':les) (SSNull:SSSep s':srest)
 = " " ++ showLSep p s' les' ++ " " ++ showLang p les srest
showLang p (LList les':les) (SSTok s:SSSep s':srest)
 = s ++ " " ++ showLSep p s' les' ++ " " ++ showLang p les srest

showLang p (LCount les':les) (SSNull:SSSep s':srest)
 = " " ++ showLSep p s' les' ++ " " ++ showLang p les srest
showLang p (LCount les':les) (SSTok s:SSSep s':srest)
 = s ++ " " ++ showLSep p s' les' ++ " " ++ showLang p les srest

showLang p (le:les) (SSTok s:srest)
 = s ++ " " ++ showLE p le ++ " " ++ showLang p les srest

showLang p (le:les) (SSNull:srest)
 = " " ++ showLE p le ++ " " ++ showLang p les srest

showLang p [] [] = "ILLFORMED - missing last specifier"
showLang p [] srest
 = "ILLFORMED - missing elements between"++ldisp dispSS srest
showLang p les []
 = "ILLFORMED - missing specifiers around"++ldisp dispLE les

showLang p les ss = "SHOWLANG?? "++show les++" "++show ss
\end{code}

Showing Language Elements:
\begin{code}
showLE p (LVar g) = show g
showLE p (LType t) = show t
showLE p (LExpr e) = eShow p e
showLE p (LPred pr) = pShow p pr
showLE p (LList _) = "!! Nested LList in DataText.showLE !!"
showLE p (LCount _) = "!! Nested LCount in DataText.showLE !!"

showLSep p sep [] = ""
showLSep p sep [le] = showLE p le
showLSep p sep (le:les) = showLE p le ++ sep ++ showLSep p sep les

instance Show LElem where -- not focus safe !
 showsPrec p (LVar g) = mkshows $ show g
 showsPrec p (LType t) = mkshows $ showType p t
 showsPrec p (LExpr e) = mkshows $ showExpr p e
 showsPrec p (LPred pr) = mkshows $ showPred p pr
 showsPrec p (LList les)
  = mkshows ("["++(concat $ intersperse ","  $ map (showLE p) les)++"]")
 showsPrec p (LCount les)
  = mkshows ("["++(concat $ intersperse ","  $ map (showLE p) les)++"]")

mkshows s sc = s ++ sc
\end{code}

Showing Syntax Specifications
\begin{code}
instance Show SynSpec where
 show SSNull     = ""
 show (SSTok s)  = s
 show (SSSep s)  = s

ldisp f = concat . map f

dispSS SSNull = " _"
dispSS (SSTok s) = ' ':s
dispSS (SSSep s) = ' ':s

dispLE le = ' ':(show le)
\end{code}


We want to output a \texttt{LElem}-list  and corresponding
\texttt{SynSpec}-list as a textual syntax specification:
\begin{code}
showLangSpec [] [SSNull] = ""
showLangSpec [] [SSTok s] = s

showLangSpec (LList (le:_):les) (s:SSSep sep:srest)
 = showSS s ++ " " ++showLS le ++ '*':sep ++ " " ++ showLangSpec les srest

showLangSpec (LCount (le:_):les) (s:SSSep sep:srest)
 = showSS s ++ " " ++showLS le ++ '#':sep ++ " " ++ showLangSpec les srest

showLangSpec (le:les) (s:srest)
 = showSS s ++ " " ++ showLS le ++ " " ++ showLangSpec les srest

showLangSpec les srest = "ILLFORMED-LANG("++show les++" "++show srest++")"

showSS SSNull = ""
showSS (SSTok tok) = tok
showSS (SSSep sep) = sep

lcVar   = 'V'
lcType  = 'T'
lcExpr  = 'E'
lcPred  = 'P'
lcLList = 'L'
lcCount = 'N'

lsVar   = [lcVar]
lsType  = [lcType]
lsExpr  = [lcExpr]
lsPred  = [lcPred]

lsEvar = (Gen $ Std lsExpr, NoDecor, lsExpr)

lslVar  = [lcVar, '*']
lslType = [lcType,'*']
lslExpr = [lcExpr,'*']
lslPred = [lcPred,'*']

lscVar  = [lcVar, '#']
lscType = [lcType,'#']
lscExpr = [lcExpr,'#']
lscPred = [lcPred,'#']

showLS (LVar  _ ) = lsVar
showLS (LType _ ) = lsType
showLS (LExpr _ ) = lsExpr
showLS (LPred _ ) = lsPred
showLS (LList []) = [lcType,'?']
showLS (LList (le:_)) = lcLList:showLS le
showLS (LCount []) = [lcCount,'?']
showLS (LCount (le:_)) = lcCount:showLS le
\end{code}

We need canonical forms of \texttt{LElem}s:
\begin{code}
lVarSpec  = LVar $ Std lsVar
lTypeSpec = LType (Tvar lsType)
lExprSpec = LExpr (Evar lsEvar)
lPredSpec = LPred (Pvar $ Std lsPred)
llist le = LList [le]
lcount le = LCount [le]
\end{code}

We can now given a Show instance for LangSpec:
\begin{code}
instance Show LangSpec where
  show (LangSpec les ss) = showLangSpec les ss
\end{code}

\subsection{Parsing Language Specifications}


\input{doc/Language-Specification}

\begin{code}
parseSynSpec sspec = pSS (ssToks [] sspec)
 where
\end{code}

Tokeniser \texttt{ssToks} simply splits its input at whitespace,
so tokens are maximal chunks of non-whitespace characters.
\begin{code}
   ssToks skot "" = reverse skot
   ssToks skot (c:srest)
    | isSpace c = ssToks  skot srest
    | otherwise = ssToks' skot [c] srest
   ssToks' skot kot "" = reverse (reverse kot:skot)
   ssToks' skot kot (c:srest)
    | isSpace c = ssToks (reverse kot:skot) srest
    | otherwise = ssToks' skot (c:kot) srest
\end{code}

This parser looks inside tokens,
and parses the following grammar,
where:
non-terminals are all uppercase;
terminals are single-quoted;
alternatives are separated by $|$;
$\dashv \ldots \vdash$ indicates parts packed into one token;
optional components are surrounded by $[ \ldots ]$;
and $tok$ denotes the rest or all of a token.
\begin{eqnarray*}
   BE & ::=&  \lit V | \lit T | \lit E | \lit P
\\ LS & ::=&  \lit * | \lit\#
\\ LE & ::=&  \dashv BE~[LS~tok] \vdash
\\ SS & ::=& tok~[SS''] | LE~[SS]
\\ SS'' &::=& LE~[SS]
\end{eqnarray*}
\begin{code}
   -- not seen any tokens yet
   pSS [] = Left "parseSynSpec: empty spec"

   pSS ((c:'*':sep):toks)
    | c == lcVar   =  pSS' [llist lVarSpec]  [SSSep sep,SSNull] toks
    | c == lcType  =  pSS' [llist lTypeSpec] [SSSep sep,SSNull] toks
    | c == lcExpr  =  pSS' [llist lExprSpec] [SSSep sep,SSNull] toks
    | c == lcPred  =  pSS' [llist lPredSpec] [SSSep sep,SSNull] toks

   pSS ((c:'#':sep):toks)
    | c == lcVar   =  pSS' [lcount lVarSpec]  [SSSep sep,SSNull] toks
    | c == lcType  =  pSS' [lcount lTypeSpec] [SSSep sep,SSNull] toks
    | c == lcExpr  =  pSS' [lcount lExprSpec] [SSSep sep,SSNull] toks
    | c == lcPred  =  pSS' [lcount lPredSpec] [SSSep sep,SSNull] toks

   pSS ([c]:toks)
    | c == lcVar   =  pSS' [lVarSpec]  [SSNull] toks
    | c == lcType  =  pSS' [lTypeSpec] [SSNull] toks
    | c == lcExpr  =  pSS' [lExprSpec] [SSNull] toks
    | c == lcPred  =  pSS' [lPredSpec] [SSNull] toks

   pSS (tok:toks)  = pSS'' [] [SSTok tok] toks

   -- seen VTEP token
   pSS' sel revss [] = Right (reverse sel,reverse (SSNull:revss))

   pSS' sel revss ((c:'*':sep):toks)
    | c == lcVar   =  pSS' (llist lVarSpec:sel)  (SSSep sep:revss) toks
    | c == lcType  =  pSS' (llist lTypeSpec:sel) (SSSep sep:revss) toks
    | c == lcExpr  =  pSS' (llist lExprSpec:sel) (SSSep sep:revss) toks
    | c == lcPred  =  pSS' (llist lPredSpec:sel) (SSSep sep:revss) toks

   pSS' sel revss ((c:'#':sep):toks)
    | c == lcVar   =  pSS' (lcount lVarSpec:sel)  (SSSep sep:revss) toks
    | c == lcType  =  pSS' (lcount lTypeSpec:sel) (SSSep sep:revss) toks
    | c == lcExpr  =  pSS' (lcount lExprSpec:sel) (SSSep sep:revss) toks
    | c == lcPred  =  pSS' (lcount lPredSpec:sel) (SSSep sep:revss) toks

   pSS' sel revss ([c]:toks)
    | c == lcVar   =  pSS' (lVarSpec:sel)  (SSNull:revss) toks
    | c == lcType  =  pSS' (lTypeSpec:sel) (SSNull:revss) toks
    | c == lcExpr  =  pSS' (lExprSpec:sel) (SSNull:revss) toks
    | c == lcPred  =  pSS' (lPredSpec:sel) (SSNull:revss) toks

   pSS' sel revss (tok:toks)           = pSS'' sel (SSTok tok:revss) toks

   -- seen visible token
   pSS'' sel revss []                   = Right (reverse sel,reverse revss)

   pSS'' sel revss ((c:'*':sep):toks)
    | c == lcVar   =  pSS' (llist lVarSpec:sel)  (SSSep sep:revss) toks
    | c == lcType  =  pSS' (llist lTypeSpec:sel) (SSSep sep:revss) toks
    | c == lcExpr  =  pSS' (llist lExprSpec:sel) (SSSep sep:revss) toks
    | c == lcPred  =  pSS' (llist lPredSpec:sel) (SSSep sep:revss) toks

   pSS'' sel revss ((c:'#':sep):toks)
    | c == lcVar   =  pSS' (lcount lVarSpec:sel)  (SSSep sep:revss) toks
    | c == lcType  =  pSS' (lcount lTypeSpec:sel) (SSSep sep:revss) toks
    | c == lcExpr  =  pSS' (lcount lExprSpec:sel) (SSSep sep:revss) toks
    | c == lcPred  =  pSS' (lcount lPredSpec:sel) (SSSep sep:revss) toks

   pSS'' sel revss ([c]:toks)
    | c == lcVar   =  pSS' (lVarSpec:sel)  revss toks
    | c == lcType  =  pSS' (lTypeSpec:sel) revss toks
    | c == lcExpr  =  pSS' (lExprSpec:sel) revss toks
    | c == lcPred  =  pSS' (lPredSpec:sel) revss toks

   pSS'' sel revss (tok:toks)  =  Left ( "parseSynSpec: double tokens: '"
                                         ++show (head revss)
                                         ++"' '"++tok++strPOST
                                       )
-- end parseSynSpec
\end{code}

A Parser returning a language specification:
\begin{code}
parseLangSpec spec
 = case parseSynSpec spec of
     (Left msg)        ->  Left msg
     (Right (les,ss))  ->  Right (LangSpec les ss)
\end{code}

Often we want to know if a language specification introduces
a binary operator.
A syntax specification of the form null, token, null
is binary.
\begin{code}
isBinSpec (LangSpec [_,_] [SSNull,SSTok _,SSNull])  =  True
isBinSpec ls                                        =  False

theBinOpName (LangSpec [_,_] [SSNull,SSTok oname,SSNull])  =  oname
theBinOpName _  =  "??"
\end{code}

In particular the two language elements need to be simple
(non-list).
We also expect that binary language constructs use \texttt{theBinOpName}
for the construct name as well:
\begin{code}
mkBinLang (LangSpec [_,_] ss@[SSNull,SSTok oname,SSNull]) prec left right
 = Lang oname prec [left,right] ss
mkBinLang lspec prec left right
 = Perror ("mkBinLang: lspec not binary - "++show lspec)
\end{code}

Checking a Lang construct for infixity is also useful:
\begin{code}
isInfixLang (Lang _ _ [_,_] [SSNull,SSTok _, SSNull]) = True
isInfixLang _ = False
\end{code}






\subsection{Parsing a \texttt{Lang} (User-Specified Language Construct)}

Given a collection of language specifications, we filter out
those that are infix binary (as they are already automatically handled).
With the rest we build a \emph{parsing tree}.
A node in the tree offers a list of distinct parser specifications,
whose associated parsers are tried in order.
\begin{code}
data LParseSpec
 = LPSTok String
 | LPSVar | LPSType | LPSExpr | LPSPred
 | LPSList LParseSpec String | LPSCount LParseSpec String
 | LPSNull
 deriving (Eq,Ord,Show)
\end{code}

If they all fail, the whole parse fails.
If one succeeds, its return value, if any, is noted, and then we follow
a link from that parser to another tree, if present, and recurse.
The leaves of this tree are special nodes that contain both the name and syntax specification
of the construct just successfully parsed.
\begin{code}
data LParseTree
 = LPNil
 | LPLeaf String [SynSpec]
 | LPList [(LParseSpec,LParseTree)]
 deriving (Eq,Ord)

instance Show LParseTree where
  show lpt = showLPT 0 lpt

showLPT n LPNil = indent n ++ "LP-NIL"
showLPT n (LPLeaf nm ss) = indent n ++ "LP-LEAF " ++ nm ++ " "++show ss
showLPT n (LPList lpl)
  = indent n ++ "LP-LIST("++show (length lpl)++")\n"
    ++ (concat $ map (showLPL (n+1)) $ lpl)
showLPL n (spec,lpt)
 = indent n ++ str ++ " -> \n"
   ++ showLPT (n+4) lpt
 where str = show spec
\end{code}

The parser code is straightforward:
\begin{code}

langParse ptlt lptree
 = do lquote
      tep <- tparse [] lptree
      lquote
      return tep
   <?> "invalid lang. syntax"
 where

  -- parse w.r.t to a tree
  tparse sel LPNil
   = fail "No User-Specified Language Constructs"

  tparse sel (LPLeaf name ss)
   = return $ TEPlang name (reverse sel) ss

  tparse sel (LPList lplist) = tlparse sel lplist

  -- parse w.r.t to a list of nodes
  tlparse sel [] = fail ("langParse fails after "++show (reverse sel))
  tlparse sel ((lpspec,lptnxt):lps)
   = (try $ lparse lptnxt sel lpspec)
     <|>
     (try $ tlparse sel lps)

  -- parse w.r.t a parser/continuation node
  lparse n s (LPSTok str)            =  lparse' n s (thenamesym' str)
  lparse n s LPSVar                  =  lparse' n s (mklp lsVar name)
  lparse n s LPSType                 =  lparse' n s (mklp lsType tepType)
  lparse n s LPSExpr                 =  lparse' n s (mklp lsExpr (parseTEP ptlt))
  lparse n s LPSPred                 =  lparse' n s (mklp lsPred (parseTEP ptlt))
  lparse n s (LPSList LPSVar sep)    =  lparse' n s (mklps lslVar name sep)
  lparse n s (LPSList LPSType sep)   =  lparse' n s (mklps lslType tepType sep)
  lparse n s (LPSList LPSExpr sep)   =  lparse' n s (mklps lslExpr (parseTEP ptlt) sep)
  lparse n s (LPSList LPSPred sep)   =  lparse' n s (mklps lslPred (parseTEP ptlt) sep)
  lparse n s (LPSCount LPSVar sep)   =  lparse' n s (mklps lscVar name sep)
  lparse n s (LPSCount LPSType sep)  =  lparse' n s (mklps lscType tepType sep)
  lparse n s (LPSCount LPSExpr sep)  =  lparse' n s (mklps lscExpr (parseTEP ptlt) sep)
  lparse n s (LPSCount LPSPred sep)  =  lparse' n s (mklps lscPred (parseTEP ptlt) sep)
  lparse lptnxt sel LPSNull          =  tparse sel lptnxt
  lparse _ _ lps = fail ("invalid LParseSpec:"++show lps)

  lparse' lptnxt sel lp
    = do lpres <- try lp
         case lpres of
           Nothing       ->  tparse sel lptnxt
           Just le       ->  tparse (le:sel) lptnxt

\end{code}
First we need parsers that look for the various types
of language elements (token,type,expression or predicate),
returning nothing for tokens, and a (string,TEP)-pair
identifying anything else parsed.
\begin{code}

  thenamesym' str
   = do thenamesym str
        return Nothing

  mklp str p
   = do tep <- p
        return $ Just $ (str,tep)

  mklps str p sep
   = do teps <- sepBy1 p (thenamesym sep)
        return $ Just $ (str++sep,TEPllist teps)

\end{code}

\subsection{Building A Language Parser Tree}

Given a collection of language specifications,
we need to build the corresponding \texttt{LParseTree}.
We do this by converting each specification into a (linear) tree,
and then merging them.

\subsubsection{Single Lang.-Spec. to (Linear) Tree}

Constructing a tree requires a well-formed \texttt{Lang}:
\begin{code}

lang2tree (name,LangSpec les ss) = l2t (name,ss) les ss
 where

   l2t (nm,ss) [] [SSNull] = LPLeaf nm ss
   l2t (nm,ss) [] [SSTok s] = LPList [(LPSTok s,LPLeaf nm ss)]

   l2t (nm,ss) (LList (le:_):les) (s:SSSep sep:srest)
    | s == SSNull  =  lplist
    | otherwise    =  LPList [(ss2lps s,lplist)]
    where
      subtree = l2t (nm,ss) les srest
      lplist = LPList [(LPSList (lelem2lps le) sep,subtree)]

   l2t (nm,ss) (LCount (le:_):les) (s:SSSep sep:srest)
    | s == SSNull  =  lplist
    | otherwise    =  LPList [(ss2lps s,lplist)]
    where
      subtree = l2t (nm,ss) les srest
      lplist = LPList [(LPSCount (lelem2lps le) sep,subtree)]


   l2t (nm,ss) (le:les) (s:srest)
    | s == SSNull  =  lplist
    | otherwise    =  LPList [(ss2lps s,lplist)]
    where
      subtree = l2t (nm,ss) les srest
      lplist = LPList [(lelem2lps le,subtree)]

   l2t (nm,ss) _ _ = LPList [(LPSTok ("ILLFORMED"),LPLeaf ("ILLFORMED-"++nm) ss)]

   ss2lps SSNull       =  LPSNull
   ss2lps (SSTok s)    =  LPSTok s
   ss2lps (SSSep sep)  =  LPSTok ("BADSEP-"++sep)

   lelem2lps (LVar _)   =  LPSVar
   lelem2lps (LType _)  =  LPSType
   lelem2lps (LExpr _)  =  LPSExpr
   lelem2lps (LPred _)  =  LPSPred
   lelem2lps _          =  LPSNull


\end{code}

\subsubsection{Merging Parse Trees}

Merging \texttt{LParseTree} just involves fusing \texttt{LPList} entries
so any parser specification occurs at most once.
A valid tree is not a isolated \texttt{LPLeaf}, so merging two is an error
(usually only caused if two different language constructs have identical
specifications).
\begin{code}

lptmerge LPNil lpl  =  lpl
lptmerge lpl LPNil  =  lpl

lptmerge (LPLeaf nm1 _) (LPLeaf nm2 _)
 = LPLeaf ("AMBIGUOUS-"++show nm1++"-"++show nm2) []

lptmerge lf@(LPLeaf nm ss) (LPList lpl)
 = LPList (alinsnorm (curry fst) LPSNull lf lpl)

lptmerge (LPList lpl) lf@(LPLeaf nm ss)
 = LPList (alinsnorm (curry fst) LPSNull lf lpl)

lptmerge (LPList lpl1) (LPList lpl2)
 = LPList (almrgnorm lptmerge lpl1 lpl2)

\end{code}

\subsection{Lang.-Table to Tree}
Finally, code that takes a language table and produces a parse-tree:
\begin{code}

langTable2LPTree  = langList2LPTree . trieFlatten ""

langList2LPTree langl
 = foldr lptmerge LPNil ltrees
 where
   ltrees = map lang2tree nonbins
   nonbins = filter (not . isBinSpec . snd) langl

\end{code}

\subsubsection{Extracting Key-Symbols}

We also need to extract all tokens, split into names and symbols
in language specifications
to ensure that the scanner can convert them to key-word/symbols.
\begin{code}
languageKeys lpt  =  lks ([],[]) lpt
 where

   lks ks (LPList lpts) = lsks ks lpts
   lks ks _             = ks

   lsks ks [] = ks
   lsks ks ((lps,lpt):lptrest)
     = lsks (lks (lpss ks lps) lpt) lptrest

   lpss (keys,syms) (LPSTok s)
     | issym s  =  (keys,s:syms)
     | iskey s  =  (s:keys,syms)
   lpss (keys,syms) (LPSList lps sep)
     | issym sep = lpss (keys,sep:syms) lps
     | iskey sep = lpss (sep:keys,syms) lps
     | otherwise = lpss (keys,syms) lps
   lpss (keys,syms) (LPSCount lps sep)
     | issym sep = lpss (keys,sep:syms) lps
     | iskey sep = lpss (sep:keys,syms) lps
     | otherwise = lpss (keys,syms) lps
   lpss ks _ = ks

   issym str       = all isSymbol str
   iskey ""        = False
   iskey str@(c:_) = isAlpha c && all isIdent str
\end{code}
For now we don't report errors such as tokens mixing symbols
and alphanumerics --- constructs using these will simply fail to parse.


\subsection{Text Utilities}


\subsubsection{Generating Fresh Variables}

Given a list of used variables,
and a variable  as a pattern, generate a fresh variable
based
on that pattern that is not already used:
\begin{code}
genFreshVar :: [Variable] -> Variable -> Variable
genFreshVar used patvar
 = head $ dropWhile alreadyUsed $ map (genvar patvar . show) [1..]
 where
   alreadyUsed var = var `elem` used
   genvar (r@(Gen _), _, _)       substr = mkVar r (Subscript substr) []
   genvar (r@(Rsv _ roots), _, _) substr = mkVar r (Subscript substr) roots
\end{code}

We generalise this to a list of fresh patterns:
\begin{code}
genFreshVars :: [Variable] -> [Variable] -> [(Variable,Variable)]
genFreshVars used [] = []
genFreshVars used (patvar:rest)
 = let gvar = genFreshVar used patvar
   in (patvar,gvar):genFreshVars (gvar:used) rest
\end{code}


\subsubsection{Fixing \texttt{Parsec}}

A serious omission in \texttt{Parsec} is the inability
to have a form of `\texttt{catch}', in which a failing
parse is turned into a success.
Given a parser returning \texttt{Either err stuff}
we provide a combinator taking this and a function \texttt{err -> stuff},
giving a parser that always returns (the) \texttt{Right stuff}.
\begin{verbatim}

%> catch :: (err -> stuff) -> GenParser tok st a -> GenParser tok st a
%> catch fix (Parser p)
%>  = Parser (\state->
%>      case (p state) of
%>         Consumed reply -> Consumed (mapReply reply)
%>         Empty    reply -> Empty    (mapReply reply)
%>     )
%>    where
%>      mapReply reply
%>        = case reply of
%>            Error err  ->  let ferr = fix err
%>                              in seq ferr (Ok ferr state err)
%>            ok         ->  ok

\end{verbatim}
Unfortunately this doesn't work because the internals of Parser
and Reply are not exported.

\subsubsection{Separated-List Text Display}

Simple string-list showing:
\begin{code}
mkSepList s []   =  ""
mkSepList s [x]  =  x
mkSepList s (x:xs)  =  x ++ (s:(mkSepList s xs))
\end{code}

Simple ``showable-thing'' list showing:
\begin{code}
showSepList s []   =  ""
showSepList s [x]  =  show x
showSepList s (x:xs)  =  show x ++ (s:(showSepList s xs))
\end{code}

A generic show-sep function, parameterised with precedence and
show-function:
\begin{code}
showSep p sh sep [] = ""
showSep p sh sep [t] = sh p t
showSep p sh sep (t:ts) = sh p t ++ sep ++ showSep p sh sep ts
\end{code}
