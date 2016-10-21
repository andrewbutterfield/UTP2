\section{Extended Parser Library}

\subsection*{A library of 'extended' monadic parser combinators}

 These are designed to be compatible with the MONADIC PARSER COMBINATOR
 library, \texttt{ParseLib.hs} \cite{HuttonGrah1996c,journals/jfp/HuttonM98}

 However, these combinators are extended to:
\begin{enumerate}
  \item work on any kind of token stream, not just \texttt{[Char]}
  \item report error messages (with accurate line and column numbers)
  \item allow 'cuts' within grammars, to improve efficiency by
       reducing non-determinism.
        (Note: \texttt{first} and \texttt{+++}, from the original library,
               can also help to reduce non-determinism).
\end{enumerate}
 The goal is complete compatibility with the original library,
 so that you can just replace \texttt{import ParseLib} by \texttt{import EParseLib},
 and everything will work unchanged.
 However, you may want to use the additional functions of
 \texttt{EParseLib} to add cuts to your parsers and to report errors etc.
 This library exports two parser types:
\begin{verbatim}
   EParser tokens ast
   Parser ast       (= EParser Char ast)
\end{verbatim}
The \texttt{Parser} type is a special case of \texttt{EParser}, for compatibility
with the original library.
\begin{code}
module EParseLib
   (Token(..), mkToken,
    ParseResult(..), parse_error, mkParseError,
    EParser, epapply, epapplystr, cut, localizecut, --errorRecovery,
    Parser, item, tok, papply,
    (+++), sat, satm, many, many1, sepby, sepby1, chainl,
    chainl1, chainr, chainr1, ops, bracket,
    -- The remainder are only for parsing character strings.
    -- They have type: Parser ast, rather than EParser tok ast
    char, digit, lower, upper,
    letter, alphanum, string, ident, nat, int, spaces, comment, junk,
    parse, token, natural, integer, symbol, identifier
   )
where

import Data.Char
import Control.Monad

infixr 5 +++

----- The Token-with-Line-and-Column-Information type ------------

data Token t
  = Token{tokenValue::t, tokenLine::Int, tokenColumn::Int}
    deriving (Show)
    -- We avoid deriving Eq so that accidental == tests on tokens give
    -- errors.  (Usually just the tokenValue parts should be compared).

mkToken :: t ->  Int ->  Int ->  Token t
mkToken = Token

-- The EParser monad ---------------------------------------------

type ParseError = (Int, Int, String)  -- (line, column, msg)

type PossibleParseError toks = ([Token toks], String)

mkParseError :: Show toks => PossibleParseError toks ->  ParseError
mkParseError ([],msg)
  = (maxBound, 0, msg ++ " (at end of input)")
mkParseError (t:_,msg)
  = (tokenLine t, tokenColumn t, "Found "++show (tokenValue t)++", "++msg)
\end{code}

Errors with smaller line numbers are less likely to be chosen/reported.
An EOF error has \texttt{line==maxBound} because it is at the end of the input.
Alternative: could have an explicit end-of-file token, with a line number.
\begin{code}
recovery_error :: ParseError
recovery_error = (0, 0, "INTERNAL ERROR RECOVERY ERROR")

-- no_error :: PossibleParseError a
no_error = ([],"") -- the minimum error

parse_error :: [Token toks] ->  String ->  PossibleParseError toks
parse_error toks msg = (toks, msg)
\end{code}

This chooses between alternative parse errors.
It prefers errors that come later in the token stream,
then prefers errors from the rightmost? alternatives in the grammar
(because those are likely to be the error recovery actions?)

\begin{code}
choose_error :: [PossibleParseError toks] ->  PossibleParseError toks
choose_error errs
  = foldl1 latest errs
  where
  ([],"")     `latest`  e          = e
  e           `latest`  ([],"")    = e
  ([],msg)    `latest`  _          = ([],msg)  -- EOF error
  _           `latest`  ([],msg)   = ([],msg)  -- EOF error
  a@(t:_,_)   `latest`  b@(u:_,_)
    | (tokenLine t, tokenColumn t) > (tokenLine u, tokenColumn u)  =  a
    | (tokenLine t, tokenColumn t) < (tokenLine u, tokenColumn u)  =  b
    | otherwise                                                    =  b
\end{code}

\begin{code}
data ParseResult tok ast
  = ParseResult{ parses    :: [(ast, [ParseError], [Token tok])]
               , seencut   :: Bool
               , besterror :: PossibleParseError tok
               }
  deriving (Show)
\end{code}

Invariants/Semantics:
\begin{enumerate}
  \item
     Each member \texttt{(t,e,ts)} of \texttt{parses} means that \texttt{t} is a possible
     parse of the input upto \texttt{ts}.
     The parse is successful
     (without any errors) iff \texttt{e==[]}.
     Errors generally only get put into \texttt{e} by an explicit
     error recovery action, after all parses have failed.
  \item
    \texttt{seencut==True} iff the parser reached a `cut'.
      This means that the list of parses was (or may have been)
      intentionally cut short by the cut.
  \item
    \texttt{besterror} is the parse error that has the maximum line
      and column number so far.  This is the error that should be
      reported if the parse fails.  If no errors have been seen
      yet, this will be \texttt{no\_error}.
\end{enumerate}
\begin{code}
eof_parse :: ParseResult tok ast
eof_parse
  = ParseResult{parses=[],
      seencut=False,
      besterror=parse_error [] "Unexpected end of input"}

error_parse :: [Token tok] ->  ParseResult tok ast
error_parse toks
  = ParseResult{parses=[],
      seencut=False,
      besterror=parse_error toks "Syntax error"}

-- A. Butterfield, May 2009
-- we occasionally want to tailor the message rather than the almost
-- useless "Syntax Error"

error_parse_msg :: String -> [Token tok] ->  ParseResult tok ast
error_parse_msg msg toks
  = ParseResult{parses=[],
      seencut=False,
      besterror=parse_error toks msg}

newtype EParser tok ast   = P ([Token tok] ->  ParseResult tok ast)

-- a special case, for backward compatibility with ParseLib.hs
type Parser ast = EParser Char ast

--instance Functor (EParser toks) where
--   -- map         :: (a ->  b) ->  (EParser a ->  EParser b)
--   fmap f (P p)   = P (\inp ->  Parsed [(f v, out) | (v,out) <- p inp]) ??

instance Monad (EParser tok) where
  return v = P (\toks ->  ParseResult{parses=[(v,[],toks)],
                   seencut=False,
                   besterror=no_error})
  fail msg = P (\toks ->  ParseResult{parses=[],
                   seencut=False,
                   besterror=parse_error toks msg})
  (P p) >>= q
    = P (\toks
         -> let pout = p toks in
            let q2 (t,es,ts) = epapply_with_errors (q t) es ts in
            let qout = takeUntil1 seencut (map q2 (parses pout)) in
            ParseResult{ parses = concatMap parses qout
                       , seencut = seencut pout || any seencut qout
                       , besterror= choose_error
                                       (besterror pout : map besterror qout)
                       })

-- takeUntil1 is a variant of takeWhile that also includes the
-- first element for which p is true.  For example:
--
--      takeUntil1 (==4) [1,2,3,4,5]  = [1,2,3,4]
--
takeUntil1               :: (a ->  Bool) ->  [a] ->  [a]
takeUntil1 p []          =  []
takeUntil1 p (x:xs)
	    | p x       =  [x]
	    | otherwise =  x : takeUntil1 p xs

instance MonadPlus (EParser tok) where
  mzero = P (\toks ->  error_parse toks)
  (P p) `mplus` (P q)
    = P (\toks ->  choose (p toks) (q toks))
    where
    choose r@ParseResult{seencut=True} _ = r
    choose pout qout
      = ParseResult{ parses = parses pout ++ parses qout
                   , seencut = seencut pout || seencut qout
                   , besterror = choose_error [besterror pout, besterror qout]
                   }

-- Other primitive parser combinators ---------------------------------

(+++) :: EParser tok ast ->  EParser tok ast ->  EParser tok ast
p +++ q = first (p `mplus` q)

item :: EParser tok tok
item = P (\inp ->  case inp of
		       []     ->  eof_parse
		       (x:xs) ->  epapply (return (tokenValue x)) xs)

-- We define sat as a primitive in order to return correct error positions.
-- TODO: does this equal this?   No.
--     do{i<-item; guard (sat i); return i} +++ fail "Syntax Error"}

sat :: (tok ->  Bool) ->  EParser tok tok
sat p
  = P (\inp ->  case inp of
		    []     ->  eof_parse
		    (x:xs) ->  if p (tokenValue x)
			      then epapply (return (tokenValue x)) xs
			      else error_parse inp)

-- Andrew Butterfield, May 2009
-- Error messages are still very poor, despite all this effort to support them
-- The following version of sat allows a tailored error message to be added.

satm :: String -> (tok ->  Bool) ->  EParser tok tok
satm msg p
  = P (\inp ->  case inp of
		    []     ->  eof_parse
		    (x:xs) ->  if p (tokenValue x)
			      then epapply (return (tokenValue x)) xs
			      else error_parse_msg msg inp)

-- We define tok as a primitive in order to return a nicer error message.
-- Apart from the error message, tok t = sat (== t)

tok :: (Show tok,Eq tok) =>  tok ->  EParser tok tok
tok t
  = P (\inp ->  case inp of
		[]     ->  eof_parse
		(x:xs) ->  if tokenValue x == t
			  then epapply (return (tokenValue x)) xs
			  else epapply (fail ("expected " ++ show t)) inp)

first             :: EParser tok ast ->  EParser tok ast
first (P p)        = P (\inp ->  first_parse (p inp))
    where
    first_parse pout = pout{parses=take 1 (parses pout)}
\end{code}

This is equivalent to epsilon (zero), but acts like a Prolog 'cut'.
For example:
\begin{verbatim}
  do {p1;p2;cut;p3;p4}  `mplus`  do{p5;p6}
\end{verbatim}
will discard all unexplored parses from \texttt{p1} and \texttt{p2}
(and will not attempt \texttt{\{p5;p6\}}) once the cut is reached.
Note that the effect of a cut is global.
It prunes away ALL
unexplored alternatives,
right up to the top-level parser function!
\begin{code}
cut               :: EParser tok ()
cut                = P (\toks ->  ParseResult{parses=[((),[],toks)],
					     seencut=True,
					     besterror=no_error})

-- To localize the effect of a cut, use:  localizecut p.
-- This still allows the parser p to return multiple parses,
-- but once a cut is reached within p, it will stop returning parses.

localizecut :: EParser tok ast ->  EParser tok ast
localizecut (P p) = P (\toks ->  (p toks){seencut=False})

epapply :: EParser tok ast ->  [Token tok] ->  ParseResult tok ast
epapply (P p) inp = p inp

epapply_with_errors :: EParser tok ast
                       -> [ParseError]
                       -> [Token tok]
                       -> ParseResult tok ast
epapply_with_errors (P p) errs inp =
		let presult = p inp
		    adderrs (t,es,ts) = (t, errs++es, ts) in
		    presult{parses = map adderrs (parses presult)}

epapplystr :: EParser Char ast ->  String ->  ParseResult Char ast
epapplystr (P p) = p . tokenise 1 0

-- This is totally backwards compatible.
-- In practice, you will usually want to change from using papply
-- to using , except that the result contains
-- more information (errors as well as the parse results).
papply            :: Parser ast ->  [Char] ->  [(ast,[Char])]
papply p           = concatMap fix_result . parses . epapplystr p
  where
  fix_result (ast,[],toks) = [(ast, map tokenValue toks)]
  fix_result (ast,_,toks)  = []    -- discard parses with errors

tokenise :: Int ->  Int ->  [Char] ->  [Token Char]
tokenise _ _ "" = []
tokenise l c ('\n':s) = Token '\n' l c : tokenise (l+1) 0 s
tokenise l c ('\t':s) = Token '\t' l c : tokenise l ((c `div` 8 + 1)*8) s
tokenise l c (ch:s)   = Token ch l c   : tokenise l (c+1) s

---------------- Derived combinators ------------------------------

many :: EParser tok a ->  EParser tok [a]
many p = (many1 p +++ return [])

-- Because of cuts in p many can fail therefore force is not safe.
--many p             = force (many1 p +++ return [])

many1 :: EParser tok a ->  EParser tok [a]
many1 p = do {x <- p; xs <- many p; return (x:xs)}

sepby :: EParser tok a ->  EParser tok b ->  EParser tok [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

sepby1 :: EParser tok a ->  EParser tok b ->  EParser tok [a]
p `sepby1` sep = do {x <- p; xs <- many (do {sep; p}); return (x:xs)}

chainl :: EParser tok a ->  EParser tok (a ->  a ->  a) ->  a
          ->  EParser tok a
chainl p op v = (p `chainl1` op) +++ return v

chainl1:: EParser tok a ->  EParser tok (a ->  a ->  a)
          ->  EParser tok a
p `chainl1` op
 = do {x <- p; rest x}
 where rest x = do {f <- op; y <- p; rest (f x y)} +++ return x

chainr :: EParser tok a ->  EParser tok (a ->  a ->  a) ->  a
          ->  EParser tok a
chainr p op v = (p `chainr1` op) +++ return v

chainr1 :: EParser tok a ->  EParser tok (a ->  a ->  a)
           ->  EParser tok a
p `chainr1` op
 = do {x <- p; rest x}
 where
	rest x = do {f <- op; y <- p `chainr1` op; return (f x y)}
           +++ return x

ops :: [(EParser tok a, b)] ->  EParser tok b
ops xs = foldr1 (+++) [do {p; return op} | (p,op) <- xs]

bracket :: EParser tok a ->  EParser tok b ->  EParser tok c
           ->  EParser tok b
bracket open p close = do {open; x <- p; close; return x}

------- The rest of this file is identical to ParseLib.hs --------------
--------- (and defines 'Parser's rather than 'EParser's) ---------------

char              :: Char ->  Parser Char
char x             = tok x   -- Was: sat (\y ->  x == y)

digit             :: Parser Char
digit              = sat isDigit

lower             :: Parser Char
lower              = sat isLower

upper             :: Parser Char
upper              = sat isUpper

letter            :: Parser Char
letter             = sat isAlpha

alphanum          :: Parser Char
alphanum           = sat isAlphaNum

string            :: String ->  Parser String
string ""          = return ""
string (x:xs)      = do {char x; string xs; return (x:xs)}

ident             :: Parser String
ident              = do {x <- lower; xs <- many alphanum; return (x:xs)}

nat               :: Parser Int
nat                = do {x <- digit; return (digitToInt x)} `chainl1` return op
		     where
			m `op` n = 10*m + n

int               :: Parser Int
int                = do {char '-'; n <- nat; return (-n)} +++ nat

--- Lexical combinators ------------------------------------------------------

spaces            :: Parser ()
spaces             = do {many1 (sat isSpace); return ()}

comment           :: Parser ()
comment            = do {string "--"; many (sat (\x ->  x /= '\n')); return ()}

junk              :: Parser ()
junk               = do {many (spaces +++ comment); return ()}

parse             :: Parser a ->  Parser a
parse p            = do {junk; p}

token             :: Parser a ->  Parser a
token p            = do {v <- p; junk; return v}

--- Token parsers ------------------------------------------------------------

natural           :: Parser Int
natural            = token nat

integer           :: Parser Int
integer            = token int

symbol            :: String ->  Parser String
symbol xs          = token (string xs)

identifier        :: [String] ->  Parser String
identifier ks      = token (do {x <- ident; if not (elem x ks) then return x
							       else mzero})

------------------------------------------------------------------------------
\end{code}
