\section{\LaTeX\ Lexer}


 \subsection*{Lexical scanner for LaTeX Z specifications.}

\texttt{zlex} is the main entry point.
It is normally called like this:
\begin{verbatim}
      zlex l2s lexstate0 "input string ..."
\end{verbatim}
Here argument \texttt{l2s} is a function mapping \latex\ macros
to (\texttt{Maybe}) \texttt{Symbol}s and is usually derived from the \texttt{ltx2sym}
component of a \texttt{LaTeXLayout}.
The scanner handles operator declarations itself, and keeps
a record of what operators have been declared.

To speed up processing, simplify the parser and avoid starting
Z paragraphs within informal commentary, the scanner handles
commentary separately from the contents of Z paragraphs.
\begin{description}
  \item[TODO] provide a way of saving/returning the lexer state,
       because it contains declared operators etc.
  \item[TODO] implement \%\%cmd commands (to record declared operators).
\end{description}

\begin{code}

module LaTeXLexer
where
import EParseLib
import LaTeXSetup
import Data.Maybe
import Tables
import Data.Char

\end{code}
Lexer tokens are now declared in \texttt{LaTeXSetup},
in order to put certain translation details in one place
(Simon Dardis, Summer 2008).

The scanner has this internal state which records line numbers,
declared operators etc.  (The current column number is handled via
an explicit argument to \texttt{zlex}, because it changes so often, and
experiments show that the scanner is faster that way).
\begin{code}

data LexState = LexState{line::Int, opstrs::[String]}

incrline :: LexState ->  LexState
incrline ls = ls{line = line ls + 1}

lexstate0 :: LexState
lexstate0 = LexState{line=1, opstrs=[]}


\end{code}
\begin{code}


--   zlexc handles the 'commentary' part of Z specifications
--     It skips everything, looking only for constructs at the beginning
--     of a line that start a Z paragraph (like \begin{schema}).
--
--   zlexz is used within each Z paragraph, to generate the Z tokens.
--
-- zlexz takes a column number as argument (and lexer state and input string).
-- Columns are numbered from zero, whereas lines are numbered from one.
-- This numbering scheme matches Emacs conventions.

zlex :: (String -> Maybe Symbol) -> LexState ->  String -> [Token ZToken]
zlex = zlexc

zlexc :: (String -> Maybe Symbol) -> LexState ->  String -> [Token ZToken]
zlexc l2s ls "" = []
zlexc l2s ls ('%':'%':c:s)
  | isAlpha c = lexdirective l2s ls (c:s)
  | otherwise = zskipline l2s ls (c:s)

\end{code}
\begin{code}

zlexc l2s ls s
  | cmd == begin && head s4 == '}' = lexcmd envname
    -- it must still be commentary, so skip the whole line!
  | otherwise = zskipline l2s ls s
  where
  begin = "\\begin{"
  spacetab ' '  = True
  spacetab '\t' = True
  spacetab _    = False
  (spaces,s2) = span spacetab s
  (cmd,s3) = splitAt (length begin) s2
  (envname,s4) = span isAlpha s3
  pos = length spaces
  rest = zlexz l2s (pos + length begin + length envname + 1) ls (tail s4)
  lexcmd ename
   | knownEnv ename  =  Token (L_BEGIN ename) (line ls) pos : rest
   | otherwise       =  zskipline l2s ls s

\end{code}
We need to identify known environments:
\begin{code}

knownEnv e = e `elem` knownEnvs
knownEnvs  =     [ "theoryid"
                 , "typedefs"
                 , "consts"
                 , "exprs"
                 , "preds"
                 , "obs"
                 , "precs"
                 , "types"
                 , "alphas"
                 , "laws"
                 , "conjectures"
                 , "theorems"
                 , "zed"
                 , "syntax"
                 , "axdef"
                 , "schema"
                 , "gendef"
                 , "machine"
                 ]

\end{code}

\begin{code}

directivetable = []
  -- = ["theoryid"]
  -- = ["inop","postop","inrel","prerel","ingen","pregen","ignore"]

lexdirective l2s ls s
  | directive `elem` directivetable
    =  Token (L_THEORYID theoryN) (line ls) (length theoryN + 1)
          : zskipline l2s ls rest'
  | otherwise
      -- Ignore all unknown directives (silently!)
      -- Note: this is currently ignoring the 'type', 'tame' and
      --       'unchecked' directives.
      = zskipline l2s ls rest
  where
  (directive, rest) = span isAlpha s
  (theoryN, rest') = span isLawChar rest

\end{code}
\begin{code}

zskipline l2s ls s
  = zlexc l2s (incrline ls) (drop 1 (dropWhile (/= '\n') s))

\end{code}
\begin{code}

zlexz :: (String -> Maybe Symbol) -> Int ->  LexState ->  String
          ->  [Token ZToken]
zlexz l2s c ls ""       = []
-- various forms of whitespace
zlexz l2s c ls (' ':s)  = zlexz l2s (c+1) ls s
zlexz l2s c ls ('~':s)  = zlexz l2s (c+1) ls s
zlexz l2s c ls ('&':s)  = zlexz l2s (c+1) ls s   -- ignore Latex tabs
zlexz l2s c ls ('\r':s) = zlexz l2s (c+1) ls s   -- so that DOS files work
zlexz l2s c ls ('\t':s) = zlexz l2s ((c `div` 8 + 1)*8) ls s
zlexz l2s c ls ('\n':s) = zlexz l2s 0 (incrline ls) s  -- newline
zlexz l2s c ls ('\f':s) = zlexz l2s 0 (incrline ls) s  -- formfeed
zlexz l2s c ls ('\v':s) = zlexz l2s 0 (incrline ls) s  -- vertical tab
zlexz l2s c ls ('%':s)  = zlexz l2s 0 (incrline ls) (drop 1 (dropWhile (/= '\n') s))
zlexz l2s c ls ('\\':'!':s) = zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':',':s) = zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':':':s) = zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':';':s) = zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':' ':s) = zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':'\\':'&':'&':s) = zlexz l2s (c+4) ls s
-- LaTeX commands that start with a backslash
zlexz l2s c ls ('\\':'\\':s)
  = Token (L_SYM DBLBACKSLASH) (line ls) c : zlexz l2s (c+2) ls s
-- zlexz l2s c ls ('\\':'_':s)
--   = Token (L_SYM UNDERSCORE) (line ls) c : zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':'{':s)
  = Token (L_SYM OPENSET) (line ls) c : zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':'}':s)
  = Token (L_SYM CLOSESET) (line ls) c : zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':'#':s)
  = Token (L_WORD "\\#") (line ls) c : zlexz l2s (c+2) ls s
zlexz l2s c ls ('\\':s)
  -- A few commands can have a "_1" after them, which changes their meaning.
  -- For these commands, we call tok_1, to discard the "_1".
  -- Occurences of "_1" that are not recognised here are treated as
  -- normal decorations.  Perhaps *all* "_1" should be treated as decorations,
  -- but that is difficult at the moment, because the ones handled below
  -- generate a variety of lexical symbols.  This might become easier after
  -- operator declarations are implemented?
  | cmd=="t" && length (takeWhile isDigit s2) == 1
		  = zlexz l2s (c+3) ls (tail s2)   -- ignore \tN tabs commands
  | cmd=="quad"   = zlexz l2s (c+5) ls s2
  | cmd=="qquad"   = zlexz l2s (c+6) ls s2

\end{code}
Here we use the table \texttt{laTeXTokens} in \texttt{LaTexSetup} (Simon Dardis, Summer 2008).
We should try to make as much of this lexer dependent on such tables
(Andrew Butterfield, November 2008).
\begin{code}

  | isJust macrosym  = tok (L_SYM (fromJust macrosym))

\end{code}
The next block of tokens follows the tables of
operators in \cite[p46]{Spivey92}.
\begin{code}

  | cmd=="mapsto" = tok (L_IN_FUN 1 ('\\':cmd))
  | cmd=="upto"   = tok (L_IN_FUN 2 ('\\':cmd))
  | cmd=="cup"    = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="setminus"
		  = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="cat"    = tok (L_IN_FUN 4 ('\\':cmd))
  | cmd=="div"    = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="mod"    = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="cap"    = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="extract"= tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="filter" = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="comp"   = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="circ"   = tok (L_IN_FUN 5 ('\\':cmd))
  | cmd=="oplus"  = tok (L_IN_FUN 6 ('\\':cmd))
  | cmd=="dres"   = tok (L_IN_FUN 7 ('\\':cmd))
  | cmd=="rres"   = tok (L_IN_FUN 7 ('\\':cmd))
  | cmd=="ndres"  = tok (L_IN_FUN 7 ('\\':cmd))
  | cmd=="nrres"  = tok (L_IN_FUN 7 ('\\':cmd))

  | cmd=="inv"    = tok (L_POST_FUN ('\\':cmd))
  | cmd=="star"   = tok (L_POST_FUN ('\\':cmd))
  | cmd=="plus"   = tok (L_POST_FUN ('\\':cmd))

  | cmd=="subseteq"
		  = tok (L_IN_REL ('\\':cmd))
  | cmd=="subset" = tok (L_IN_REL ('\\':cmd))
  | cmd=="leq"    = tok (L_IN_REL ('\\':cmd))
  | cmd=="geq"    = tok (L_IN_REL ('\\':cmd))
  | cmd=="prefix" = tok (L_IN_REL ('\\':cmd))
  | cmd=="suffix" = tok (L_IN_REL ('\\':cmd))
  | cmd=="inseq"  = tok (L_IN_REL ('\\':cmd))
  | cmd=="partition"
		  = tok (L_IN_REL ('\\':cmd))

  | cmd=="disjoint"
		  = tok (L_IN_REL ('\\':cmd))

  | cmd=="rel"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="pfun"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="fun"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="pinj"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="inj"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="psurj"  = tok (L_IN_GEN ('\\':cmd))
  | cmd=="surj"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="bij"    = tok (L_IN_GEN ('\\':cmd))
  | cmd=="ffun"   = tok (L_IN_GEN ('\\':cmd))
  | cmd=="finj"   = tok (L_IN_GEN ('\\':cmd))

  | cmd=="power" && underscore1
		  = tok_1 (L_PRE_GEN ("\\power_1"))
  | cmd=="power"  = tok (L_SYM SET)      -- must come after \power_1.
  | cmd=="id"     = tok (L_PRE_GEN ('\\':cmd))
  | cmd=="finset" && underscore1
		  = tok_1 (L_PRE_GEN ("\\finset_1"))
  | cmd=="finset" = tok (L_PRE_GEN ("\\finset"))  -- must come after \finset_1
  | cmd=="seq" && underscore1
		  = tok_1 (L_PRE_GEN ("\\seq_1")) -- must come after \seq_1.
  | cmd=="seq"    = tok (L_PRE_GEN ("\\seq"))
  | cmd=="iseq"   = tok (L_PRE_GEN ('\\':cmd))

  | cmd=="end" && knownEnv stripArg  =  tokarg (L_END stripArg)

\end{code}
\Saoithin\ extension (Simon Dardis, Summer 2008)
\begin{code}

  | cmd=="propname" && vLawArg              = tokvarg (L_PROPNAME lawArg)
  | cmd=="evarname" && vName         = tokvarg (L_EVARNAME nameArg)
  | cmd=="qvar" && vName	   = tokvarg (L_QVAR nameArg)
  | cmd=="qqvar" && vName	   = tokvarg (L_QQVAR nameArg)
  | cmd=="qqvarlist" && vName	   = tokvarg (L_QQVARLIST nameArg)
  | cmd=="tvarname" && vName     = tokvarg (L_TVARNAME nameArg)
  | cmd=="tfreename" && vName     = tokvarg (L_TVARNAME nameArg)
  | cmd=="theoryNameVersion" && vLawArg     = tokvarg (L_THEORYID lawArg)

\end{code}
\begin{code}

  -- treat \\nat_1 specially, so the _1 is not a decoration.
  | cmd=="nat" && underscore1     = tok_1 (L_WORD "\\nat_1")
  | otherwise                     = tok (L_WORD ('\\':cmd))
  where
  (cmd,s2)	= span (\x -> or [isAlpha x, isDigit x, x == '_']) s
  macrosym = l2s ('\\':cmd)
  arg		= takeWhile isArgChar s2
  stripArg = stripCurl arg
  lawArg	= takeWhile isLawChar s2
  nameArg	= takeWhile isLawChar s2
  vName	= validLawArg nameArg
  vLawArg	= validLawArg lawArg
  tok t	= Token t (line ls) c : zlexz l2s (c + 1 + length cmd) ls s2
  tok_1 t	= Token t (line ls) c : zlexz l2s (c + 3 + length cmd) ls (drop 2 s2)
  tokarg t	= Token t (line ls) c : zskipline l2s ls s2  -- skip rest of line
  tokvarg t	= Token t (line ls) c : zlexz l2s (c + 1 + length cmd) ls (drop (length lawArg) s2)
  underscore1	= starts_with_underscore1 s2
  starts_with_underscore1 ('_':'1':[])  = True
  starts_with_underscore1 ('_':'1':c:_) = not (isDigit c)
  starts_with_underscore1 _             = False

\end{code}
Non-macro tokens
\begin{code}

zlexz l2s c ls s@('+':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@('-':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@('*':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@('.':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@('=':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@('<':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@('>':_) = zlexinfix l2s c ls s
zlexz l2s c ls s@(',':_) = zlexinfix l2s c ls s
zlexz l2s c ls (':':':':'=':s)
		   = Token (L_SYM COLONCOLONEQUALS) (line ls) c : zlexz l2s (c+3) ls s
zlexz l2s c ls (':':'=':s)
		   = Token (L_SYM ASSIGN)       (line ls) c : zlexz l2s (c+2) ls s
zlexz l2s c ls (':':s) = Token (L_SYM COLON)        (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls (';':s) = Token (L_SYM SEMICOLON)    (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('|':s) = Token (L_SYM VERT)         (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('@':s) = Token (L_SYM AT)           (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('/':s) = Token (L_SYM SLASH)        (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('{':s) = Token (L_SYM OPENBRACE)    (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('}':s) = Token (L_SYM CLOSEBRACE)   (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('(':s) = Token (L_SYM OPENPAREN)    (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls (')':s) = Token (L_SYM CLOSEPAREN)   (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('[':s) = Token (L_SYM OPENBRACKET)  (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls (']':s) = Token (L_SYM CLOSEBRACKET) (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('\'':s)
 = Token (L_STROKE "'") (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('?':s)
 = Token (L_STROKE "?") (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('!':s)
 = Token (L_STROKE "!") (line ls) c : zlexz l2s (c+1) ls s
zlexz l2s c ls ('"':s)
  | take 1 rest == "\"" = Token (L_GIVENVAL val) (line ls) c : toks
  | otherwise           = Token (L_ERROR "unclosed string") (line ls) c : toks
  where
  (val,rest) = span string_contents s
  string_contents '"'  = False
  string_contents '\n' = False
  string_contents _    = True
  toks = zlexz l2s (c + length val + 2) ls (drop 1 rest)
zlexz l2s c ls ('_':s)
  = if num==""
    then Token (L_ERROR "_") (line ls) c : zlexz l2s (c+1) ls s
    else Token (L_STROKE ('_':num)) (line ls) c
	 : zlexz l2s (c + 1 + length num) ls s2
  where
  (num,s2) = span isDigit s
zlexz l2s c ls (ch:s)
  | isAlpha ch = Token (tok word) (line ls) c
		 : zlexz l2s (c + length word) ls s2
  | isDigit ch = Token (L_NUMBER (read num)) (line ls) c
		 : zlexz l2s (c + length num) ls s3
  | otherwise  = Token (L_ERROR [ch]) (line ls) c
		 : zlexz l2s (c + 1) ls s
  where
  (word,s2) = span_ident (ch:s)
  (num,s3)  = span isDigit (ch:s)
  tok "true"  = (L_SYM PTRUE)
  tok "false" = (L_SYM PFALSE)
  tok w       = L_WORD w

\end{code}
Stripping curly brackets from arguments can be useful
\begin{code}

stripCurl arg = (strip '{') $ reverse $ (strip '}') $ reverse $ arg
 where strip _ "" = ""
       strip b str@(c:cs)
         | b == c     =  cs
         | otherwise  =  str

\end{code}
Spanning
\begin{code}

span_ident :: String ->  (String, String)
span_ident []           = ([],[])
span_ident ('\\':'_':s) = ('\\':'_':ys,zs)
			       where (ys,zs) = span_ident s
span_ident xs@(ch:s)
  | isAlphaNum ch  =  (ch:ys,zs)
  | otherwise      =  ([],xs)
		      where (ys,zs) = span_ident s


\end{code}
\begin{code}

zlexinfix l2s c ls s
  | op=="="    = tok (L_IN_FUN 3 op)
  | op=="=="   = tok (L_SYM ABRDEF)
  | op=="."    = tok (L_SYM POINT)
  | op==","    = tok (L_SYM COMMA)
  | op=="-"    = tok (L_SYM HYPHEN)
  | op=="+"    = tok (L_IN_FUN 4 op)
  | op=="*"    = tok (L_IN_FUN 5 op)
  | op=="<"    = tok (L_IN_REL op)
  | op=="> "    = tok (L_IN_REL op)
  | otherwise  = tok (L_WORD op)
  where
  (op,s2) = span isInfixChar s
  tok t = Token t (line ls) c : zlexz l2s (c + length op) ls s2



\end{code}
\begin{code}

isInfixChar :: Char ->  Bool
isInfixChar '+' = True
isInfixChar '-' = True
isInfixChar '*' = True
isInfixChar '.' = True
isInfixChar '=' = True
isInfixChar '<' = True
isInfixChar '>' = True
isInfixChar ',' = True
isInfixChar  _  = False

isArgChar :: Char ->  Bool
isArgChar '{' = True
isArgChar '}' = True
isArgChar c   = isAlpha c

\end{code}
\Saoithin\ extension (Simon Dardis, Summer 2008)
\begin{code}

isLawChar :: Char -> Bool
isLawChar '{' = True
isLawChar '}' = True
isLawChar '-' = True
isLawChar ':' = True
isLawChar '_' = True
isLawChar ';' = True
isLawChar '.' = True
isLawChar '$' = True
isLawChar c   = isAlphaNum c

\end{code}
\Saoithin\ extension (Simon Dardis, Summer 2008)
\begin{code}

isTheoryName :: Char -> Bool
isTheoryName '\n' = False
isTheoryName _    = True

\end{code}
\Saoithin\ extension (Simon Dardis, Summer 2008)
\begin{code}

validLawArg :: String -> Bool
--validLawArg nam
--  = (length name > 2) && ((head name) == '{') && (last name == '}')
validLawArg [] = False
validLawArg (c:cs)
 = c=='{' && vRest cs
 where
   vRest [] = False
   vRest [c] = c == '}'
   vRest (_:cs) = vRest cs

\end{code}
