\section{\LaTeX\ Pretty-Printing}

\begin{code}
module LaTeXPretty where
import Utilities
import Datatypes
import MatchTypes

import Builtin
import Tables
import Proof
import Data.List
import Data.Maybe
import Text.ParserCombinators.Parsec.Expr
import DSL
import LaTeXNames
import LaTeXSetup
import Focus
\end{code}

This module supplies pretty-printing for the program.
Maintainers should be aware that \texttt{pprint\_proof},
\texttt{pprint\_context} have a relatively "deep" call graph,
where the current function will print out a
portion of a data structure and delegate the rest to others before returning the result.
As such some changes will require examination of the functions above and below
to see what is expected and returned from delegate functions,
in particular the placement of \texttt{INewLn} tokens.

Intended organisation:
external modules will simply need to call \texttt{pprint\_*} to get back a
\LaTeX\ fragment representation of the appropriate data structure,
so, for example,
\texttt{pprint\_pred} will return a \LaTeX\ fragment for the given predicate.


\subsection{The \texttt{ISeq} datatype}

Type \texttt{ISeq} is the core datatype of the pretty printer.
The structure in this code produces
a tree to be traversed in a pre-order fashion.
Two items of particular interest are the
Annote meta-\texttt{ISeq},
used to store information about a \texttt{ISeq}.
The other is the
\texttt{ITok} construction, representing tokens whose output is format dependant.
Currently it is set to write out \LaTeX\ commands for common constructs.
See \texttt{tokenToString} for the current representations.

Ideas have been drawn from \cite{PeytonJones92,wadler:prettier:FUN:03}.
\begin{code}
data ISeq =
  INil             -- nothing
  | INewLn           -- plain newline
  | IPNewLn          -- newline only for printing predicates
  | Indent Int       -- indentation level
  | INum Int           -- a number stored for later use
  | IString String     -- Basic output type
  | ITok LaTeXToken    -- Tokens of special interest
  | IConcat [ISeq]     -- a variable length sub tree
  | IAnnote [Annote] ISeq  -- for annotating ISeqs
  deriving (Show,Eq)
\end{code}

These annotations permit the tagging of \texttt{ISeq}s
so that information loss can be controlled through the use of tags
which signify where a particular branch or leaf came from,
and/or what purpose it serves, or to assist in determining
the final representation.
\begin{code}
data Annote =
    APlain   -- nothing, should never be used.
  | AInfRul  -- contains the raw text of a inference rule
  | AVar     -- observational variable name
  | AQVar    -- quantifier pattern variable
  | AEVar    -- expression meta-variable
  | APVar    -- predicate meta-variable
  | AApp     -- function application (expression)
  | APApp    -- function application (predicate)
  | ABin     -- Binary predicate operator name
  | AVE      -- Var-Expr operator name
  | AEP      -- Expr-Pred operator name
  | A3       -- Ternary Pred-Expr-Pred operator name
  | ACond    -- Structure is Cond (expr) or If (pred)
  | AJstPrd  -- Structure is [Just_n, Pred_n]
  | TypeVar  -- This is a ATyp variable
  | ASubs    -- Substitution
  | ATyp     -- Some sort of type expression
  | AName    -- The iseq we're attached to is the name of something
  | ABinds   -- ABinds for proof section.
\end{code}

Our set of tags for branches.
\begin{code}
  | ALaw     -- structure is a Law
  | AConj -- structure is a Conjecture
  | APred    -- structure is a predicate
  | AJust  -- This branch contains a justification.
  | AFPath   -- This branch contains the focus path.
  deriving (Show,Eq, Ord)
\end{code}

Datatype \texttt{LaTeXToken} enumerates tokens,
with the translations are handled separately by \texttt{tokenToString}.
The idea here is somewhat of an inverse lexer:
we produce tokens which the writer function will
later output as appropriate character sequences.
This also separates meaning from representation,
permitting the output format to changed easily.
\begin{code}
data LaTeXToken =
    P_COMMA | P_PAREN_START | P_PAREN_END| P_UNIV_START | P_UNIV_END
  | P_SUB_START | P_SUB_END| P_SET_START | P_SET_END
  | P_MAPSTO_START | P_MAPSTO_END
  | P_MAP        -- "-m->"  (A.Butterfield, Dec 08)
  | P_MAPSTO      -- "\\mapsto"
  | P_SEQ_START | P_SEQ_END | P_SEP_SLASH| P_SEP_PIPE | P_SEMICOLON
  | P_AT  | P_POINT
  | P_LDATA | P_RDATA
  | P_TRUE | P_FALSE| P_HOLDS | P_HASTYPE | P_JHASTYPE
  | P_BOOL | P_INTEGER | P_TARB | P_TENV
  | P_LAMBDA | P_IF | P_THEN  | P_ELSE | P_NOT | P_SET | P_SEQ | P_SEQP | P_EQUALS
  | P_AND | P_OR | P_NDC | P_SEQCOMP | P_EXT_CHOICE | P_INT_CHOICE | P_GUARD
  | P_EQUIV | P_IMPLIES | P_RFDBY | P_CROSS | P_FUN | P_PFUN | P_FORALL | P_EXISTS
  | P_EXISTS1 | P_PAPP | P_LHD | P_RHD | P_OBS | P_DEFD
  | P_ELAMBDA | P_PLAMBDA | P_MATHMODE
\end{code}

Proof relation tokens.
\begin{code}
  | P_PR_IMP | P_PR_EQV | P_PR_PMI
  | P_REDUCE | P_LHS2RHS | P_RHS2LHS | P_REDUCE_2 | P_LAWRED | P_ASSUME
  | P_ST_PRED | P_SST_PRED | P_QED
\end{code}

Tokens which carry specific information. These are primarily chosen with
\LaTeX\ in mind so that their information can be wrapped in a macro.
\begin{code}
  | P_MACRO String -- P_MACRO xxx   is rendered as  \xxx
  | P_QVARSEP | P_QVAR String | P_QQVARLIST String | P_QQVAR String
  | P_BEGIN String | P_END String | P_PROOFNAME String | P_EVARNAME String
  | P_THEORY_ID String Int | P_JDEFS | P_JNAMES | P_PROPNAME String
  | P_TVARNAME String | P_TFREENAME String
  deriving (Show,Eq)
\end{code}

This is our datatype to store the pretty printer state,
solely used at the moment by the \texttt{predSplit} function
to track line-position.
The \texttt{LaTeXLayout} component gives basic parameters, including
the length of a line, indentation depth and macro translations.
\begin{code}
data PPState
 = PPState{ indentl     :: Int    -- our current level of indentation.
          , linepos     :: Int    -- length of non-indentation strings
          , laTeXlayout :: LaTeXLayout
          , canIdent    :: Bool
          }

initState layout
  = PPState{ indentl = 0
           , linepos=0
           , laTeXlayout=layout
           , canIdent=True
           }

\end{code}
Using 0 for the current precedence means that the output in its entirety will be
bracketed,
which isn't really needed.
Using 1000 means the total expression should
be un-bracketed,
but the sub-predicates or expressions will be as necessary.

\subsection{Pretty-Printer Top-Levels}

Our current top-level pretty printer functions.
These functions are for external callers.
The basic design of the functions is to perform a large monolithic
transform (\texttt{toIseq\_xxxxx}) to turn all logical datatypes into an \texttt{ISeq}.

Afterwards multiple selective small transforms \cite{conf/icfp/SarkarWD04}
are applied to do postprocessing in the manner desired (\texttt{doTransforms}),
followed by a final stateful transform (\texttt{predsplit}?),
applied to break long predicates into smaller chunks.

Finally, \texttt{iDisplay} is called to render the final \texttt{ISeq} as a string.
\begin{code}
pprint_expr :: ([Trie (Int, b)],String -> Maybe String) -> Expr -> String
pprint_expr (prec,ltx2asc) expr
 = iDisplay (doTransforms pepost (toISeq_expr (prec,ltx2asc) 1000 expr))

pprint_pred :: ([Trie (Int, b)],String -> Maybe String) -> Pred -> String
pprint_pred (prec,ltx2asc) pred
  = iDisplay (doTransforms pepost (toISeq_pred (prec,ltx2asc) 1000 pred))

pepost = [ sortAnnotations
         , cleanNil
         , formatNames hasName
         , formatPredTform hasPApp
         , renderDecoration hasVar
         ]

pprint_proofcontext
  :: [Trie (Int, b)] -> LaTeXLayout -> Theory -> String
pprint_proofcontext prec layout pc
 = iDisplay (doTransforms pcpost (proofContextToISeq layout prec pc))
 where
   pcpost = pepost
            ++ [ escapeRuleNames hasInfRule
               , renderRuleSymbols layout hasInfRule
               ]
\end{code}

\newpage
\subsection{Proof Pretty-Printing}

\texttt{pprint\_proof} prints a proof.
It prints out the name, goal and steps, along
with the inference and bindings.

Here is where all post processing is hooked in.
Currently postprocessing fixes inference rules,
alters strings that need LaTeX escapes
and optionally displays the bindings depending on the parameters.
\begin{code}
pprint_proof :: [[(String,Law)]] -> [Trie (Int, b)] -> LaTeXLayout -> Proof -> String
pprint_proof hyps prec layout proof
  = iDisplay (doTransforms proofPostProcess ppTree)
  where
      l2a           = ltx2asc layout
      ppTree        = iConcat (proof_name ++ proof_goal
                               ++ proof_hyps ++ proof_details)
      proof_name    = [ IAnnote [AInfRul] (ITok (P_PROOFNAME (pname proof)))
                      , INewLn]
      proof_goal    = [ ITok (P_BEGIN "ppproof"), goalpred
                      , INewLn, ITok (P_END "ppproof"), INewLn]
      goalpred      = IAnnote [APred]
                        (iConcat [(toISeq_pred (prec,l2a) 1000 (goal proof))])
      proof_hyps = toISeq_Hyps prec layout hyps
      proof_details = toISeq_Strat (prec,l2a) (plan proof) (done proof)
      proofPostProcess
        = [ sortAnnotations
          , cleanNil
          , filterMatchBindings layout hasBinding
          , renderRuleSymbols layout hasInfRule
          , escapeRuleNames hasInfRule
          , renderDecoration hasVar
          , formatPredTform hasPApp
          , formatNames hasName
          , topSplit (initState layout)
          ]
\end{code}

We have a number of predicates on annotations:
\begin{code}
hasName anns = elem AName anns || elem APVar anns
hasPApp      = elem APApp
hasInfRule   = elem AInfRul
hasVar       = elem AVar
hasBinding   = elem ABinds
\end{code}



\subsection{\texttt{ISeq} Queries}

Ways to look at \texttt{ISeq} components,
in a safe manner.
\begin{code}
getAnnotations :: ISeq -> [Annote]
getAnnotations (IAnnote alist _) = alist
getAnnotations _                   = []

getAnnotatedISeq :: ISeq -> ISeq
getAnnotatedISeq (IAnnote _ iseq) = iseq
getAnnotatedISeq a                  = a

isAnnotatedAppend :: ISeq -> Bool
isAnnotatedAppend (IAnnote _ (IConcat _)) = True
isAnnotatedAppend _                        = False

isIString :: ISeq -> Bool
isIString (IString a) = True
isIString _           = False

isAppend :: ISeq -> Bool
isAppend (IConcat _) = True
isAppend _          = False

unpackAppend :: ISeq -> [ISeq]
unpackAppend (IConcat a) = a
unpackAppend a          = [a]
\end{code}


\subsection{\texttt{ISeq} Transformations}

The following functions all transform the \texttt{ISeq} datatype in some way.
We define a HOF that takes a list of transforms,
and applies them in the order given:
\begin{code}
doTransforms []       iseq  =  iseq
doTransforms (tf:tfs) iseq  =  doTransforms tfs (tf iseq)
\end{code}
We then collect together the top level definitions of
the various transforms available.

\subsubsection{Keep/Remove Match Bindings}

If bindings are wanted in the output, keep them,
otherwise delete them,
\begin{code}
filterMatchBindings layout apred iseq
 = if wantBindings layout
    then iseq
    else cBranchMapTD apred (const INil) iseq
\end{code}

\subsubsection{Rendering Symbols in Rule Names}

Many rule names have character sequences like
``\verb"\/"'' or ``\verb"=="''
that we'd like to see rendered as ``$\lor$'' or ``$\equiv$''.
\begin{code}
-- WILL NEED TO FIX THIS ????? Is ascAltx the right thing ?
renderRuleSymbols layout apred
 = cLeafMap apred
            (makeText .(stringTrans (ascAltx layout)))

makeText (IString txt) = IString ("\\mbox{"++txt++"}")
makeText iseq = iseq
\end{code}

\subsubsection{Escape \LaTeX-relevant chars in Rule Names}

Names may contain \LaTeX-sensitive characters
like \$ or \& that we want to preserve as-is.
\begin{code}
escapeRuleNames apred = cLeafMap apred insertLaTeXEscapes
\end{code}

\subsubsection{Rendering Variable Decorations}

Some names have a root and decoration parts.
We want to typeset these properly.
\begin{code}
renderDecoration apred = cLeafMap apred renderVarDecor

renderVarDecor (IString n) = IString (decor_AtoT n)
renderVarDecor (IAnnote anotes (IString n))
  = IAnnote anotes (IString (decor_AtoT n))
renderVarDecor iseq = iseq
\end{code}

\subsubsection{Formatting Names}

Names may contain \LaTeX-sensitive characters
like \$ or \& that we want to preserve as-is.
\begin{code}
formatNames apred = cLeafMap apred formatName

formatName (IString n) = IString (verb_AtoT_M n)
formatName (ITok (P_PROPNAME n))  -- Named IConcats become ITok PROPNAME!
  = ITok (P_PROPNAME (verb_AtoT_M n))
formatName (IAnnote anotes (IString n))
  = IAnnote anotes (IString (verb_AtoT_M n))
formatName iseq = iseq
\end{code}

\subsubsection{Formatting Predicate-Transformer Names}

Predicate transformer names become bold.
\begin{code}
formatPredTform apred = cLeafMap apred formatPTform

formatPTform (IString n) = IString (enbold n)
formatPTform (IAnnote anns (IString n))
  = IAnnote anns (IString (enbold n))
formatPTform iseq = iseq

enbold n = "\\mathbf{"++n++"}"
\end{code}




We now follow-on by describing the details of each transform.

\subsubsection{\texttt{ISeq} transform: \LaTeX\ escapes}

Function pattern to escape all \LaTeX control characters.
\begin{code}
insertLaTeXEscapes :: ISeq -> ISeq

insertLaTeXEscapes (IString a) = (IString (escLaTeX a))

insertLaTeXEscapes (ITok (P_PROOFNAME name))
  = ITok (P_PROOFNAME (escLaTeX name))

insertLaTeXEscapes (ITok (P_EVARNAME name))
  = ITok (P_EVARNAME (escLaTeX name))

insertLaTeXEscapes (ITok (P_THEORY_ID name num))
  = ITok (P_THEORY_ID (escLaTeX name) num)

insertLaTeXEscapes (ITok (P_PROPNAME name))
  = ITok (P_PROPNAME (escLaTeX name))

insertLaTeXEscapes (IConcat sl) = (IConcat (map insertLaTeXEscapes sl))

insertLaTeXEscapes (IAnnote al iseq)
  = (IAnnote al (insertLaTeXEscapes iseq))

insertLaTeXEscapes a = a
\end{code}

Function \texttt{escLaTex} uses list of search/replacement strings
\texttt{laTeXEscapes}
to remove all \LaTeX control characters.
To extend, add the tuple (\emph{substring},\emph{replacement}) to the list.
The list should be be in ascending order
with regard to the length of \emph{substring},
this generally stops the transformations being applied to
something already transformed.
\begin{code}
escLaTeX name  =  listReplace name laTeXEscapes

laTeXEscapes = [("$","\\$"),("_","\\_")]
\end{code}

\texttt{listReplace}: Takes a single string,
and list of search,replacement tuples.
The list should be organized such that earlier replacements
do not contain later search strings.
\begin{code}
listReplace :: String -> [(String, String)] -> String
listReplace orig list = foldl pairReplace orig list
\end{code}

\texttt{pairReplace}: takes an original string,
and a tuple of the search string, the new substring.
For each character in the original,
we take a substring of the original,
whose length is bounded by
the length of the search string or the length of the original string.
If the substring is equal to the search string,
we return the desired string and the result of
recursing the original with the substring removed.
Otherwise we return the character of original string
and the result of recursing the tail of the original string.
\begin{code}
pairReplace :: (Eq a) => [a] -> ([a],[a]) -> [a]
pairReplace [] (desired,replacement) = []
pairReplace searchString (desired,replacement)
 = if (take (length desired) searchString) == desired
    then replacement
         ++ pairReplace (drop (length desired) searchString)
                    (desired,replacement)
    else (head searchString)
         : (pairReplace (tail searchString) (desired, replacement))
\end{code}


\subsubsection{\texttt{ISeq} transform: clean out \texttt{INil}s}

\texttt{cleanNil} sweeps a \texttt{ISeq} tree clean of \texttt{INil} \texttt{ISeq}.
The only case where this won't work is where the
tree is an \texttt{IAnnote INil},
in which case the output will be the same as the input.
\begin{code}
cleanNil :: ISeq -> ISeq

cleanNil (IAnnote a item)  = (IAnnote a (cleanNil item))

cleanNil (IConcat list)
  = IConcat [cleanNil x | x <- list , x /= INil, not (isAnnotatedNil x)]

cleanNil a = a
\end{code}

We use a query function looking for annotated \texttt{INil}s.
\begin{code}
isAnnotatedNil :: ISeq -> Bool
isAnnotatedNil (IAnnote _ INil)   = True
isAnnotatedNil _        = False
\end{code}


\subsubsection{\texttt{ISeq} (pointed) transform: string translation}

This is a ``pointed'' rule (only changes \texttt{IString}s,
and proof-names,
with no recursive descent).
Its intended use is for inference-rule name transformation.
The first argument is a list of \texttt{(searchString, newString)} tuples.
The list of tuples should be ordered such that an early \texttt{newString}
is disjoint from a latter \texttt{searchString},
and if possible that no production inadvertently
creates a rule string with a latter \texttt{searchString}.
\begin{code}
stringTrans :: [(String, String)] -> ISeq -> ISeq
stringTrans tlist (IString rname) = IString (foldl pairReplace rname tlist)
stringTrans tlist (ITok (P_PROOFNAME name))
  = ITok (P_PROOFNAME (foldl pairReplace name tlist))
stringTrans tlist a = a
\end{code}


\subsubsection{\texttt{ISeq} transform: strip Annotations}


\texttt{stripAllAnnotations}: A post-processing function that strips all annotations from an ISeq tree. Not required in this
version of the code, as iDisplay ignores annotations. It's left here for use by future (debug) functions.
\begin{code}
stripAllAnnotations :: ISeq -> ISeq
stripAllAnnotations (IAnnote _ iseq)    = stripAllAnnotations iseq
stripAllAnnotations (IConcat a)     = IConcat (map stripAllAnnotations a)
stripAllAnnotations a         = a
\end{code}

\newpage
\subsubsection{\texttt{ISeq} transform: Predicate Splitting}

\texttt{predSplit} is a stateful transform.
It performs a pre-order traversal of the \texttt{ISeq} list of trees
passed to it.
It splits predicates by inserting predicate Newlines
and indentation tokens between the leaves.
It handles brackets '(' ')' without regards to length
to retain clarity in the output.
\texttt{INil}s are consumed by this function as they don't produce output.

Maintainers should note that this function takes and returns a list of \texttt{ISeq}s,
so input should be unpacked and repacked into \texttt{IConcat}s
for most other functions to process.
It's done this way as it makes for fairly simple case handling.
\begin{code}
predSplit :: PPState -> [ISeq] -> [ISeq]

predSplit ppstate []    = []

predSplit ppstate (a:ax)
 = case a of

    (ITok P_PAREN_START) -> a:(predSplit ppstate ax)
    (ITok P_PAREN_END) -> a:(predSplit ppstate ax)

    INil -> (predSplit ppstate ax)

    (IAnnote _ INil) -> (predSplit ppstate ax)

    (IConcat list)
      -> if linepos ppstate + iSeq_len a > lineLength (laTeXlayout ppstate)
          then (IConcat (predSplit state'i list)):(predSplit state'r ax)
          else (IConcat list):(predSplit state'c ax)

    (IAnnote al (IConcat sl))
      -> if linepos ppstate + iSeq_len a > lineLength (laTeXlayout ppstate)
          then (IAnnote al (IConcat (predSplit state'i sl)))
                : (predSplit state'r ax)
          else (IAnnote al (IConcat sl)):(predSplit state'c ax)

    a -> if linepos ppstate + iSeq_len a + nextlen
                           > lineLength (laTeXlayout ppstate)
          then [IPNewLn, Indent (indentl ppstate), a]
                ++ predSplit state'r ax
          else a:(predSplit state'c ax)

 where
  -- new line position, indent if we can.
  state'i = if canIdent ppstate
             then ppstate{ indentl = (indentl ppstate) +1
                         , linepos=0
                         , canIdent=False}
             else ppstate
  -- continue on this line
  state'c = ppstate{ linepos = (linepos ppstate) + iSeq_len a
                   , canIdent=True}
  -- new line
  state'r = ppstate{linepos=0, canIdent=True}         --
  nextlen   = if null ax then 0 else iSeq_len (head ax)
\end{code}

\texttt{iSeq\_len} gauges the length of a sum tree in characters.
\begin{code}
iSeq_len :: ISeq -> Int
iSeq_len INil              = 0
iSeq_len (Indent i)        = 4 * i
iSeq_len (IString a)       = length a
iSeq_len (ITok laTeXToken) = lenLaTeXToken laTeXToken
iSeq_len (IConcat list)    = sum (map iSeq_len list)
iSeq_len (IAnnote _ a)     = iSeq_len a
iSeq_len a                 = 1
\end{code}

Special handling for Tokens as some don't produce relevant length
regarding either because the tokens control how the output is displayed
by other applications, or change output without changing length.
\begin{code}
lenLaTeXToken (P_BEGIN _) = 0
lenLaTeXToken (P_END _) = 0
lenLaTeXToken (P_PROOFNAME _) = 0
lenLaTeXToken (P_EVARNAME a) = length a
lenLaTeXToken laTeXToken
 = if isJust tokenlu
    then (fromJust tokenlu)
    else length (tokenToString laTeXToken)
 where tokenlu = tlookup lengthTrie (tokenToString laTeXToken)
\end{code}

Table \texttt{lengthtrie}
contains the length of string outputs
whose length isn't necessarily related to the token representation,
usually because they are \LaTeX\ macros that turn into something completely
different.
\begin{eqnarray*}
   \mbox{4 `i's} & 4 & iiii
\\ \verb"\quad" & 4 & i \quad i
\\ \verb"\mapsto" & 2 & \mapsto
\\ \verb"\lambda" & 2 & \lambda
\\ \verb"\IF" & 2 & \IF
\\ \verb"\THEN" & 5 & \THEN
\\ \verb"\ELSE" & 4 & \ELSE
\\ \verb"\lnot" & 2 & \lnot
\\ \verb"\land" & 2 & \land
\\ \verb"\lor" & 2 & \lor
\\ \verb"\seqcomp" & 1 & \seqcomp
\\ \verb"\intchoice" & 2 & \intchoice
\\ \verb"\extchoice" & 2 & \extchoice
\\ \verb"\amp" & 2 & \amp
\\ \verb"\Bool" & 2 & \Bool
\\ \verb"\integer" & 2 & \integer
\\ \verb"\power" & 2 & \power
\\ \verb"\seq" & 4 & \seq
\\ \verb"\arbitarytype" & 2 & \arbitrarytype
\\ \verb"\enviromenttype" & 4 & \environmenttype
\\ \verb"\equiv" & 2 & \equiv
\\ \verb"\cross" & 2 & \cross
\\ \verb"\fun" & 3 & \fun
\\ \verb"\forall" & 2 & \forall
\\ \verb"\exists" & 2 & \exists
\\ \verb"\exists_1" & 3 & \exists_1
\\ \verb"\qed" & 3 & \qed
\\ \verb"\IMP" & 5 & \IMP{}
\\ \verb"\EQV" & 5 & \EQV{}
\\ \verb"\PMI" & 5 & \PMI{}
\end{eqnarray*}
\begin{code}
lengthTrie
 = lbuild [ ("\\mapsto",2), ("\\lambda",2), ("\\IF",2), ("\\THEN",5)
          , ("\\ELSE",4), ("\\lnot",2), ("\\land",2), ("\\lor",2)
          , ("\\seqcomp",1), ("\\intchoice",2), ("\\extchoice",2)
          , ("\\amp",2), ("\\Bool",2), ("\\integer",2), ("\\power",2)
          , ("\\seq",4), ("\\arbitarytype",2), ("\\enviromenttype",4)
          , ("\\equiv",2), ("\\cross",2), ("\\fun",3), ("\\forall",2)
          , ("\\exists",2), ("\\exists_1",3), ("\\IMP",5), ("\\EQV",5)
          , ("\\PMI",5), ("$$",0), ("&&",0), ("\\\\&&",0), ("\\qed",3) ]
\end{code}
Note that some of the entries in the above table are for (idiomatic) tokens generated
by this pretty-printer, which would not normally be considered
as (single) \LaTeX\ tokens, i.e \verb"&&" or \verb"\\&&".


\subsubsection{\texttt{ISeq} transform: split search}


\texttt{genSplitSearch} searches for Branches tagged \texttt{APred},
and performs the \texttt{predSplit} transform upon them.
Currently it assumes that non-predicate branches are within the bounds of line length.

Like \texttt{predSplit},
maintainers should note that it takes and returns a list of \texttt{ISeq} trees.
Maintainers who wish to add line-splitting functionality
for non-predicates should
simply introduce a new tag and case
in the function below,
with similar design to the \texttt{APred} case below,
with a similar function to \texttt{predSplit}
\begin{code}
genSplitSearch :: PPState -> [ISeq] -> [ISeq]

genSplitSearch state [] = []

genSplitSearch state (top:rest)
 = case top of
    (IAnnote alist (IConcat sl))
       -> if elem APred alist
           then (IAnnote alist
                     (IConcat ((IPNewLn):(predSplit state sl))))
                 : rest'
           else (IAnnote alist (IConcat (genSplitSearch state sl)))
                 : rest'
    (IConcat sublist) -> (IConcat (genSplitSearch state sublist)):rest'
    a -> a:rest'
 where rest' = genSplitSearch state rest
\end{code}

\subsubsection{\texttt{ISeq} transform: top-level split}

Top level split function,
that simply unpacks and calls \texttt{genSplitSearch}
upon the Branch,
then repacks and returns the repacked tree.
\begin{code}
topSplit laTeXlayout (IConcat a) = IConcat (genSplitSearch laTeXlayout a)
topSplit laTeXlayout a = a
\end{code}


\subsubsection{\texttt{ISeq} transform: sort annotations}

Use \texttt{sortAnnotations} to sort the annotation lists
on all the nodes of the tree.
Not strictly necessary, but greatly simplifies
the implementations of the HOFs map, filter%
\footnote{how?}.
The sort ordering used is simply that derived
from the \texttt{Annote} datatype.
\begin{code}
sortAnnotations :: ISeq -> ISeq

sortAnnotations (IAnnote alist iseq)
 = (IAnnote (sort alist) (sortAnnotations iseq))

sortAnnotations (IConcat list) = (IConcat (map sortAnnotations list))

sortAnnotations iseq = iseq
\end{code}


\subsubsection{\texttt{ISeq} transform: function map}



General predicated map functions:

\texttt{gLeafMap p f} applies the transformation \texttt{f} to
all leaves of the tree that satisfy \texttt{p}.
The predicate function \texttt{p} should be able to handle
both annotated and non-annotated leaves,
as should the transformation function \texttt{f}.
\begin{code}
gLeafMap :: (ISeq -> Bool) -> (ISeq -> ISeq) -> ISeq -> ISeq

gLeafMap p f (IConcat ls) = IConcat (map (gLeafMap p f) ls)

gLeafMap p f (IAnnote alist (IConcat ls))
 = IAnnote alist (IConcat (map (gLeafMap p f) ls))

gLeafMap p f iseq = if p iseq then f iseq else iseq
\end{code}

An obvious use is a filter that transforms matching nodes to \texttt{INil}:
\begin{code}
gLeafFilter :: (ISeq -> Bool) -> ISeq -> ISeq
gLeafFilter p = cleanNil . gLeafMap p (\x -> INil)
\end{code}


\subsubsection{\texttt{ISeq} transform: conditional leaf map}

Conditional high-order functions:
This collection of functions all take a predicate \texttt{p} that has the type:
\verb"[IAnnote] -> Bool".

\texttt{cLeafMap p f} tests all annotated non-branches
with the supplied predicate \texttt{p}.
If this returns true, we apply
the transform \texttt{f} to the \texttt{ISeq} leaf.
\begin{code}
cLeafMap :: ([Annote] -> Bool) -> (ISeq -> ISeq) -> ISeq -> ISeq

cLeafMap p f (IConcat list) = IConcat (map (cLeafMap p f) list)

cLeafMap p f (IAnnote alist (IConcat ls))
 = (IAnnote alist (IConcat (map (cLeafMap p f) ls)))

cLeafMap p f (IAnnote alist iseq)
 = if p alist
    then (IAnnote alist (f iseq))
    else (IAnnote alist (cLeafMap p f iseq))

cLeafMap p f iseq = iseq
\end{code}


\subsubsection{\texttt{ISeq} transform: leaf filter}

\texttt{cLeafFilter p}  transforms all annotated leaves that satisfy \texttt{p}
to \texttt{INil}, then sweeps the tree of\texttt{ INil}s.
\begin{code}
cleafFilter :: ([Annote] -> Bool) -> ISeq -> ISeq
cleafFilter p  = cleanNil . cLeafMap p (\x -> INil)
\end{code}


\subsubsection{\texttt{ISeq} transform: conditional map (top-down)}


Function call \texttt{cBranchMapTD p f} is a conditional map that
only applies \texttt{f} to branches when
the supplied annotation condition \texttt{p} is True.

The condition \texttt{p}
has to handle the annotated branch as-is.
This HOF hands the branch that succeeds on the annotation checking
to the supplied function without any type of unpacking.
This permits almost any type of transformation.
If the branch needs to be deleted,
the function should perform any further checking it wants,
then return \texttt{INil}.
Bear in mind that \texttt{INil}s should be swept from the
tree with \texttt{cleanNil} afterwards
to ensure the tree is as small as possible,
and that later processes can work with the assumption
that all nodes in the tree serve a purpose.
\begin{code}
cBranchMapTD :: ([Annote] -> Bool) -> (ISeq -> ISeq) -> ISeq -> ISeq

cBranchMapTD p f (IConcat sl) = IConcat (map (cBranchMapTD p f) sl)

cBranchMapTD p f (IAnnote alist (IConcat sl))
 = x''
 where
  x' = if p alist
        then f (IAnnote alist (IConcat sl))
        else (IAnnote alist (IConcat sl))
  x'' = case x' of
         (IConcat list) -> IConcat (map (cBranchMapTD p f) list)
         (IAnnote alist2 (IConcat list2))
               -> IAnnote alist (IConcat (map (cBranchMapTD p f) list2))
         a          -> a

cBranchMapTD p f a = a
\end{code}


\newpage
\section{Pretty-Printing Transformations}

\def\ppr#1{[\!\![#1]\!\!]}
\def\annote#1{\textsc{#1}}
\def\rndr#1{\underline{#1}}

We give the details of how every abstraction syntax
construct is translated.
For documentation purposes, we describe
the transformation as
$$
  \ppr{\_} : AST \fun \texttt{ISeq}
$$
and the application of annotations \texttt{ANote1} \ldots \texttt{ANotek}
as
$$
   \annote{Note1\ldots Notek}@ iseq
$$
When a pretty printing action on component $comp$ is done locally
rather than by a further call to \texttt{toIseq\_xxxx},
we designate it using
$$
  \rndr{comp} \mbox{ rather than } \ppr{comp}.
$$
Basic building blocks include \texttt{INewLn} ($nl$), \texttt{IPNewLn} ($pnl$)
and \texttt{Indent i} ($ind.i$).


\subsection{Environment Printing}

These the functions generate the following three lines
used to make \LaTeX\ proof environments:
\begin{verbatim}
 \begin{ppproof}
 \qed
 \end{pproof}
\end{verbatim}
\begin{code}
begProofEnv = [INewLn, ITok (P_BEGIN "ppproof")]
proofMark qed = if qed then [INewLn, ITok P_QED] else [INil]
endProofEnv = [INewLn, ITok (P_END "ppproof") ]
\end{code}


\subsection{Hypotheses Pretty-Printing}

\begin{code}
toISeq_Hyps _ _ [] = []
toISeq_Hyps prec layout ltbls
 = [ INewLn
   , IString "Hypotheses"
   , INewLn
   , IAnnote [ALaw]
          (pcComponentToISeq (pclawHandler prec) layout ("laws")
                     AInfRul (ITok P_JNAMES) (concat ltbls))
   ]
\end{code}


\subsection{Strategy Pretty-Printing}

Function \texttt{toISeq\_Strat} creates the pretty-printer branch
for the strategy in the proof.
It's here that the proof section printer is invoked
and its result framed with the output string describing the strategy
and the proof environment and optionally the QED token.
\begin{code}
toISeq_Strat (prec,l2a) (NoStrategy) done = [IString "No Strategy"]
\end{code}

Straigthforward ``reduce-to-True''.
This will be formatted as:
\begin{verbatim}
  Reduce to True.
  \begin{ppproof}
   proof-section-in-LaTeX
  \qed % if proof complete ("done")
  \end{ppproof}
\end{verbatim}
\begin{code}
toISeq_Strat (prec,l2a) (Reduce prfsec) done
  = [ITok P_REDUCE]++ begProofEnv
     ++ (toISeq_ProofSec (prec,l2a) prfsec) ++ proofMark done
     ++ endProofEnv
\end{code}

Convert LHS to RHS.
\begin{code}
toISeq_Strat (prec,l2a) (Lhs2Rhs prfsec) done
  = [ITok P_LHS2RHS] ++ begProofEnv
    ++ (toISeq_ProofSec (prec,l2a) prfsec) ++ proofMark done
    ++ endProofEnv
\end{code}

Convert RHS to LHS
\begin{code}
toISeq_Strat (prec,l2a) (Rhs2Lhs prfsec) done
  = [ITok P_RHS2LHS]++ begProofEnv
    ++ (toISeq_ProofSec (prec,l2a) prfsec) ++ proofMark done
    ++ endProofEnv
\end{code}

Reduce Law to Goal
\begin{code}
toISeq_Strat (prec,l2a) (LawReduce lname sc prfsec) done
  = [ITok P_LAWRED, IAnnote [AName] (IString lname)]
    ++ begProofEnv
    ++ (toISeq_ProofSec (prec,l2a) prfsec) ++ proofMark done
    ++ endProofEnv
\end{code}

Reduce both sides to same thing.
\begin{code}
toISeq_Strat (prec,l2a) (RedBoth num prfsec1 prfsec2) done
  = [ITok P_REDUCE_2]
    ++ [INewLn, IString "\\\\Reduce LHS:"] ++ begProofEnv
    ++ (toISeq_ProofSec (prec,l2a) prfsec1) ++ endProofEnv
    ++ [INewLn, IString "\\\\Reduce RHS:"] ++ begProofEnv
    ++ (toISeq_ProofSec (prec,l2a) prfsec2) ++ proofMark done
    ++ endProofEnv
\end{code}

Assumption-based strategies get simple handling
\begin{code}
toISeq_Strat (prec,l2a) (Assume cnsq prfsec) done
  = [ ITok P_ASSUME
    , INewLn
    , IString "then "
    ]
    ++ toISeq_Strat (prec,l2a) prfsec done
\end{code}

\subsection{Proof-Section Pretty-Printing}

\texttt{toISeq\_ProofSec} creates the structure of the major portion of the proof,
but delegates the arguments to \texttt{toISeq\_arg}.
\begin{eqnarray*}
  && \ppr{(pred,\seqof{arg_n,\ldots,arg_1})}
     = \ppr{arg_1} \ldots \ppr{arg_n} (\annote{Pred} @ \ppr{pred})
\end{eqnarray*}
\begin{code}
toISeq_ProofSec :: ([Trie (Int, b)],String -> Maybe String) -> ProofSection -> [ISeq]
toISeq_ProofSec (prec,l2a) (fpr, _, _, arglist)
  = (reverse (map (toISeq_proofstep (prec,l2a)) arglist)) ++ [IPNewLn,f]
  where f = IAnnote [APred] (toISeq_pred (prec,l2a) 1000 $ clearPFocus fpr)
\end{code}

\subsection{Argument Pretty-Printing}
\texttt{toISeq\_arg} handles the different types of argument types.
Currently only Justify is supported.
The section is passed onto \texttt{toISeq\_proofstep}.
\begin{eqnarray*}
  && \ppr{\texttt{Justify}~ps} = \ppr{ps}
\end{eqnarray*}
\begin{code}
toISeq_arg (prec,l2a) (Justify proofstep)
  = toISeq_proofstep (prec,l2a) proofstep
toISeq_arg (prec,l2a) a
  = iConcat [(IString ("Non-supported argument type " ++ show a))]
\end{code}

\subsection{Proof-Step Pretty-Printing}

\texttt{toISeq\_proofstep} creates the representation
of the justification and predicate.
\begin{eqnarray*}
  && \ppr{just,pred}
    = \annote{JstPrd} @
        \ppr{(\annote{Pred} @ \ppr{pred}),nl,(\annote{Just} @ \ppr{just})}
\end{eqnarray*}
\begin{code}
toISeq_proofstep (prec,l2a) (justif,pred)
  = IAnnote [AJstPrd]
      (iConcat [ iConcat [ IAnnote [APred] (toISeq_pred (prec,l2a) 1000 pred) ]
               , INewLn
               , iConcat [ IAnnote [AJust] (toISeq_just (prec,l2a) justif)]
               ])
\end{code}

\subsection{Justification Pretty-Printing}
\texttt{toISeq\_just} writes the inference rule used, focus path, and bindings.

\begin{eqnarray*}
  && \ppr{rel,path,rule,bnd}
     = \mathtt{\backslash}\ppr{rel}
             \texttt{\{}\ppr{rule}~(\annote{FPath}@\rndr{path})\texttt{\}}
        ~\ppr{bnd}
\end{eqnarray*}
\begin{code}
toISeq_just :: ([Trie (Int, b)],String -> Maybe String) -> Justification -> ISeq
toISeq_just (prec,l2a) (prfRel, fPath, inf,binding)
 = (iConcat [ applyMacro (toISeq_prfRel prfRel)
               (iConcat ([toISeq_infer (prec,l2a) inf, fPath'']))
            , toISeq_bindingTop (prec,l2a) binding
            ])
 where
   fPath' = if null fPath then [INil]
             else [ITok P_AT] ++
                  (intersperse (ITok P_POINT) (map (\x -> INum x) fPath))
   fPath'' = IAnnote [AFPath] (IConcat fPath')
   applyMacro (ITok a) item
     = iConcat[ IString ((tokenToString a) ++ "{"), item,(IString "}") ]
\end{code}

\subsection{Inference Pretty-Printing}

\texttt{toISeq\_infer}
renders the inference rule, taking care to treat those with parameters
in an appropriate way.
\begin{eqnarray*}
  && \ppr{\alpha Subs~[subs]} = \rndr{\alpha Subs}[\ppr{subs}]
\\&& \ppr{Witness~[subs]} = \rndr{Witness}[\ppr{subs}]
\\&& \ppr{Isplit~is} = \rndr{Isplit~is}
\\&& \ppr{infer} = \annote{InfRul}@ \rndr{infer}
\end{eqnarray*}
\begin{code}
toISeq_infer :: ([Trie (Int, b)],String -> Maybe String) -> Inference -> ISeq

toISeq_infer (prec,l2a) inf@(AlphaSubs esubst)
   = IConcat [ IString "$\\alpha-SUB"
             , toISeq_esubs (prec,l2a) 1000 esubst
             , IString "$" ]

toISeq_infer (prec,l2a) inf@(Witness esubst)
   = IConcat [ IString "WITNESS$"
             , toISeq_esubs (prec,l2a) 1000 esubst
             , IString "$"]

toISeq_infer (prec,l2a) inf@(ISplit ixs)
 = IConcat [IString "ISPLIT\\{",iseqs,IString "\\}"]
 where
  iseqs = IConcat (intersperse (IString ",") (map (IString . show) ixs))

toISeq_infer (prec,l2a) inf  = IAnnote [AInfRul] (IString (show inf))
\end{code}



\subsection{Bindings Pretty-Printing}

Top level function that creates a Branch for bindings.
\begin{eqnarray*}
  && \ppr{pbnd,ebnd,qbnd}
     = \annote{Binds} @ \ppr{pbnd}~\ppr{ebnd}~\ppr{qbnd}
\end{eqnarray*}
\begin{code}
toISeq_bindingTop (prec,l2a) (gpbnds, vebnds, ttbnds)
 = IAnnote [ABinds]
     (iConcat [ toISeq_binding (toISeq_pred (prec,l2a) 1000) $ justTO gpbnds
              , toISeq_binding (toISeq_expr (prec,l2a) 1000) $ justTO vebnds
              , toISeq_binding (toISeq_type (prec,l2a) 1000) $ justTO ttbnds
              , toISeq_binding toISeq_var $ justVO vebnds
              , IString "\\hbox{Lst(Bindings)NOT RENDERED}"
              ])
\end{code}

Function \texttt{toISeq\_binding} does the grunt work
in controlling the exact layout of the printing of the bindings.
\begin{eqnarray*}
  && \ppr{\seqof{k_1 \mapsto x_1,\ldots,k_n \mapsto x_n}}
     = pnl~\ppr{k_1,x_1}~pnl~\ldots~pnl~\ppr{k_n,x_n}
\end{eqnarray*}
\begin{code}
toISeq_binding transf item
 = iConcat item''
 where item'  = map (toISeq_bindingb transf) (flattenTrie item)
       item'' = if null item'
                 then item'
                 else [IPNewLn] ++ (intersperse IPNewLn item')
\end{code}

Function \texttt{toISeq\_bindingb} turns name/item pairs into the
form
\\\verb"\qquad "$\langle name\rangle$\verb" \mapsto "
\LaTeX\ representation of $\langle item\rangle$.
\begin{eqnarray*}
  && \ppr{k,x}
     = ind.2~(\annote{Var} @k)~\mapsto~\ppr{x}
\end{eqnarray*}
\begin{code}
toISeq_bindingb transf (name,item)
 = iConcat [ Indent 2, (IAnnote [AVar] (IString name))
           , ITok P_MAPSTO, transf item ]
\end{code}

\subsection{Proof-Relations Pretty-Printing}

The following are the productions for the proof relation type.
\begin{code}
toISeq_prfRel (IMP) = ITok P_PR_IMP
toISeq_prfRel (EQV) = ITok P_PR_EQV
toISeq_prfRel (PMI) = ITok P_PR_PMI
\end{code}

\subsection{Proof-Context Pretty-Printing}

Function \texttt{proofContextToISeq}
and the following functions transform a \texttt{Theory} into a \texttt{ISeq} tree.
The additional functions handle subcomponents of the context,
while the handler function \texttt{pcpredHandler} splits predicate branches.
\begin{eqnarray*}
  && \ppr{name,seq,types,exprs,preds,laws,conjs,thms}
\\&& \quad {} = BranchMap_{TD}
              (\annote{Law}\lor\annote{Conj})
              ~(LeafMap~(\annote{Name})~PropName~)
              ~res
\\&& res
\\&& \quad {} = TheoryId(name,seq)
\\&& \quad\qquad nl~\ppr{types}~\ppr{exprs}~\ppr{preds}
     ~(\annote{Law}@\ppr{laws})
     ~(\annote{Conj}@\ppr{conjs})
\end{eqnarray*}
We see that \texttt{ISeq} generation here is mixed with post-processing
(the use of \texttt{cBranchMapTD} here).
\begin{code}
proofContextToISeq layout prec pc
  = cBranchMapTD (\x -> or[elem ALaw x,elem AConj x])
                 (cLeafMap (\x -> elem AName x)
                           ( \ (IString x) -> ITok (P_PROPNAME x)))
                 result
  where
   l2a = ltx2asc layout
   result = iConcat
              [ theoryid'
              , typedefs'
              , consts'
              , exprs'
              , preds'
              , obs'
              -- , precs'
              , types'
              -- , alphas'
              , laws'
              , conject'
              -- , theorems'
              ]
   theoryid' = iConcat
                 [ ITok (P_BEGIN "theoryid"), INewLn
                 , ITok (P_THEORY_ID (thryName pc) (thrySeqNo pc))
                 , INewLn, ITok (P_END "theoryid"), INewLn
                 ]
   typedefs' = pcTypesToISeq ("typedefs",P_JDEFS) prec layout (typedefs pc)
   consts' = pcExprToISeq ("consts",P_JDEFS) prec layout (consts pc)
   exprs' = pcExprToISeq ("exprs",P_JDEFS) prec layout (exprs pc)
   preds' = pcPredToISeq prec layout (preds pc)
   obs' = pcTypesToISeq ("obs",P_JHASTYPE) prec layout (tmap thd3 $ obs pc)
   -- precs' = ...
   types' = pcTypesToISeq ("types",P_JHASTYPE) prec layout (types pc)
   -- alphas' = ...
   laws' = IAnnote [ALaw] (pcLawsToISeq prec layout (laws pc))
   conject' = IAnnote [AConj] (pcConjectToISeq prec layout (conjectures pc))
   -- theorems' = ...
\end{code}

Pretty-printing the \texttt{types} component.
\begin{eqnarray*}
  \ppr{n \mapsto T} &=& (\annote{Var} @ n) : \ppr T
\end{eqnarray*}
\begin{code}
pcTypesToISeq (tename,deftok) prec layout types
 = pcComponentToISeq t8 layout tename AVar (ITok deftok) (flattenTrie types)
 where
    l2a = ltx2asc layout
    t8 = (\y x -> toISeq_type (prec,l2a) 1000 x)
\end{code}

Pretty-printing the \texttt{exprs} component.
\begin{eqnarray*}
  \ppr{n \mapsto E} &=& (\annote{EVar} @ n) \defs \ppr E
\end{eqnarray*}
\begin{code}
pcExprToISeq (eename,deftok) prec layout exprs
 = pcComponentToISeq t2 layout eename AEVar (ITok deftok) (flattenTrie exprs)
 where
   l2a = ltx2asc layout
   t2 = (\y x -> toISeq_expr (prec,l2a) 1000 x)
\end{code}

Pretty-printing the \texttt{preds} component.
\begin{eqnarray*}
  \ppr{n \mapsto P} &=& (\annote{PVar} @ n) \defs \ppr P
\end{eqnarray*}
\begin{code}
pcPredToISeq prec layout preds
 = pcComponentToISeq (pcpredHandler prec) layout ("preds")
                     APVar (ITok P_JDEFS) (flattenTrie preds)
\end{code}

Pretty-printing the \texttt{conjectures} component.
\begin{eqnarray*}
  \ppr{n \mapsto C} &=& (\annote{InfRul} @ n) ::  \ppr C
\end{eqnarray*}
\begin{code}
pcConjectToISeq prec layout conjects
 = pcComponentToISeq (pcAssHandler prec) layout ("conjectures")
                     AInfRul (ITok P_JNAMES) (flattenTrie conjects)
\end{code}

Pretty-printing the \texttt{laws} component.
\begin{eqnarray*}
  \ppr{n \mapsto L} &=& (\annote{InfRul} @ n)   ::  \ppr L
\end{eqnarray*}
\begin{code}
pcLawsToISeq prec layout laws
 = pcComponentToISeq (pclawHandler prec) layout ("laws")
                     AInfRul (ITok P_JNAMES) laws
\end{code}

The Law ``Handler''
\begin{code}
pclawHandler prec layout ((pr,_),_,_) = pcpredHandler prec layout pr
\end{code}

The Assertion ``Handler''
\begin{code}
pcAssHandler prec layout (pr,_) = pcpredHandler prec layout pr
\end{code}

The Predicate ``Handler''
\begin{code}
pcpredHandler prec layout pred
 = iConcat (predSplit (initState layout)
                      (unpackAppend (toISeq_pred (prec,l2a) 1000 pred)))
 where l2a = ltx2asc layout
\end{code}

\subsubsection{Complex Component Renderer}

Function \texttt{pcComponentToISeq} creates an \texttt{ISeq} subtree
when the length of the list (\texttt{comp}) from the flattened trie is ${}>0$.
Argument \emph{\texttt{compConvF}} is the conversion function
for the particular proof context component,
while \emph{\texttt{envString}} is the \LaTeX\ environment
in which the output will be wrapped.
Finally, arguments \emph{\texttt{keyAttr}}
and \emph{\texttt{defsToken}}are the name annotation and  the infix token
between the name and associated item.
\begin{eqnarray*}
  && \ppr{\seqof{(n_1,x_1),\ldots,(n_k,x_k)}}_{(\alpha,=_{def})}
\\&& {} = \verb"\begin{...}"
\\&& \qquad nl~def_1~nl~\verb"\\", \ldots, ~nl~\verb"\\"~def_k
\\&& \qquad [nl]~\verb"\end{...}"~nl
\\&& def_i = (\alpha @ n_i) =_{def} \ppr{x_i}
\end{eqnarray*}
\begin{code}
pcComponentToISeq compConvF layout envString keyAttr defsToken comp
 = iConcat potentialOutput
 where
   len = length comp
   potentialOutput = if len > 0
                      then [ IString (envString), INewLn
                           , ITok (P_BEGIN envString), INewLn]
                           ++ content
                           ++ [optNewLine, ITok (P_END envString), INewLn]
                      else []
   content = interspersel [INewLn, IString ("\\\\")] inital
   inital = map (tupleToBranch layout keyAttr defsToken compConvF) comp
   optNewLine = if len == 0 then INil else INewLn
   -- optToken = if len <= 1 then INil else ITok P_SEMICOLON

\end{code}

\texttt{tupleToBranch} transforms a name/item pair
into an \texttt{ISeq} tree
along with the name annotated as indicated
and the specified token inbetween the two items.
\begin{code}
tupleToBranch
  :: LaTeXLayout -> Annote -> ISeq -> (LaTeXLayout -> a -> ISeq)
     -> (String,a) -> ISeq
tupleToBranch layout nattr itoken f (name, item)
  = iConcat [ IAnnote [nattr] (IString name)
            , itoken
            , f (layout{lineLength = (lineLength layout)
                                      - (length name + 4)})
                item
            ]
\end{code}


\subsection{Expression Pretty-Printing}

The function \texttt{toISeq\_expr} pretty prints an expression.
Most patterns return a branch, but a few don't.
Those that don't return a branch, return an annotated branch.
\begin{code}
toISeq_expr :: ([Trie (Int,b)],String -> Maybe String) -> Int -> Expr -> ISeq
\end{code}

\subsubsection{Pretty-printing atomic expressions}
\begin{eqnarray*}
   \ppr c &=& \rndr c
\\ \ppr v &=& \annote{Var} @ v
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (Num a) = iConcat [IString (show a)]
toISeq_expr (prec,l2a) curprec (Var a) = IAnnote [AVar] ( iConcat [IString $ varKey a] )
\end{code}

\subsubsection{Pretty-printing other expressions}

\begin{eqnarray*}
  \ppr{e_1 \cond C e_2}
     &=& \ppr{e_1}~\cond{\ppr C}~\ppr{e_2}
\\ \ppr{C~e_1~\cdots~e_n}
   &=& \rndr{C}~\ppr{e_1}~\cdots~\ppr{e_n}
\\ \ppr{\lambda v @ e}
   &=& \lambda~\ppr{v}~ @ ~\ppr{e}
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (App nm [EPred p1, e1, e2])
 | nm == n_Cond
 = IAnnote [ACond]
      (iConcat [ br_s, (toISeq_expr (prec,l2a) thisprec e1)
               , ITok P_LHD, (toISeq_pred (prec,l2a) thisprec p1)
               , ITok P_RHD, (toISeq_expr (prec,l2a) thisprec e2), br_e ])
 where thisprec     = 8
       (br_s, br_e) = brackets curprec thisprec

toISeq_expr (prec,l2a) curprec (Abs nm _ q [e])
 = iConcat [ (IString nm), toISeq_Qvar q
           , ITok P_AT, (toISeq_expr (prec,l2a) curprec e)]

toISeq_expr _ _ a = IString ("couldn't handle expr:" ++ show a)
\end{code}



\subsubsection{Pretty-printing delimited expressions}
\begin{eqnarray*}
  && \ppr{(x_1,\ldots,x_n)}
     =  (~\ppr{x_1}~,~\ldots~,~\ppr{x_n}~)
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (App nm a)
 | nm == n_tuple
 = iConcat ([ITok P_PAREN_START]++t++[ITok P_PAREN_END])
 where t = intersperse (ITok P_COMMA) (map (toISeq_expr (prec,l2a) curprec) a)

toISeq_expr (prec,l2a) curprec (App nm list)
 | nm == n_set
 = iConcat ([(ITok P_SET_START)]
            ++ (intersperse (ITok P_COMMA) (map (toISeq_expr (prec,l2a) curprec) list))
            ++[(ITok P_SET_END)])

toISeq_expr (prec,l2a) curprec (App nm list)
 | nm == n_seq
 = iConcat ([(ITok P_SEQ_START)]
            ++(intersperse (ITok P_COMMA) (map (toISeq_expr (prec,l2a) curprec) list))
            ++[(ITok P_SEQ_END)])
\end{code}

\subsubsection{Pretty-printing function applications}

For the \texttt{App} expression construction,
we check if it resembles a infix function,
by using the \texttt{laTeXAsciiMapping} table,
otherwise we output it in the form $f (a_1,\ldots,a_n)$.
\begin{eqnarray*}
  \ppr{\oplus(e_1,e_2)}
     &=& \ppr{e_1}~(\annote{Bin} @ \rndr\oplus)~\ppr{e_2}
\\\ppr{f(e_1,\ldots,e_n)}
     &=& (\annote{App} @ \rndr f)~(~\ppr{e_1}~,~\ldots~,~\ppr{e_n}~)
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (App fname [App nm aexprs])
 | nm == n_tuple
 = if length aexprs == 2 && isJust possPrec
    then iConcat ([br_s] ++ infixop ++ [br_e])
    else iConcat ( [ IAnnote [AApp] (IString fname)
                   , ITok P_PAREN_START]
                   ++ prefixop ++ [ITok P_PAREN_END] )
 where
  possPrec = tslookup prec fname
  infixop = intersperse fname' (map (toISeq_expr (prec,l2a) curprec) aexprs)
  prefixop = intersperse (ITok P_COMMA) (map (toISeq_expr (prec,l2a) curprec) aexprs)
  (br_s, br_e) = brackets curprec (fst (fromJust possPrec))
  fname' = if isJust (l2a fname)
           then IAnnote [ABin] ( IString (fromJust (l2a fname)) )
           else IAnnote [ABin] (IString fname)
\end{code}

\begin{eqnarray*}
  && \ppr{f(e)}
     = (\annote{App} @ \rndr f)~(\ppr{e})
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (App fname [expr])
 = IConcat [ IAnnote [AApp] (IString fname)
           , ITok P_PAREN_START
           , (toISeq_expr (prec,l2a) 1000 expr)
           , ITok P_PAREN_END
           ]
-- why AApp annote here, but none above for prefix name on product?
\end{code}

\begin{eqnarray*}
  \ppr{e_1 = e_2}
     &=& \ppr{e_1}~=~\ppr{e_2}
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (App nm [expra, exprb])
 | nm == n_Equal
 = iConcat [ (toISeq_expr (prec,l2a) curprec expra)
           , (ITok P_EQUALS), (toISeq_expr (prec,l2a) curprec exprb) ]


toISeq_expr (prec,l2a) curprec (App nm list)
 = iConcat ([IAnnote [AApp] (IString nm),(ITok P_PAREN_START)]
            ++ (intersperse (ITok P_COMMA) (map (toISeq_expr (prec,l2a) curprec) list))
            ++[(ITok P_PAREN_END)])
\end{code}

\begin{eqnarray*}
  \ppr{e[sub]~}
     &=& (~\ppr{e}~)~\ppr{~[sub]~}
\end{eqnarray*}
\begin{code}
toISeq_expr (prec,l2a) curprec (ESub expr sub)
 = iConcat ([ ITok P_PAREN_START, toISeq_expr (prec,l2a) curprec expr
            , ITok P_PAREN_END, toISeq_esubs (prec,l2a) curprec sub])
\end{code}

\subsection{Expression-Substitution Pretty-Printing}
\begin{eqnarray*}
  \ppr{[e_1,\ldots,e_n/v_1,\ldots,v_n]}
     &=& [~\ppr{e_1},\ldots,\ppr{e_n}
          ~/~
          (\annote{Var} @ \rndr{v_1}),\ldots,(\annote{Var} @ \rndr{v_n})~]
\end{eqnarray*}
\begin{code}
toISeq_esubs (prec,l2a) curprec sub
 = iConcat ([ ITok P_SUB_START] ++ t ++[ITok P_SUB_END ])
 where
  (exprs,qvars) = unwrapQV sub
  explist       = map (toISeq_expr (prec,l2a) curprec) exprs
  qlist         = map (IAnnote [AVar] . IString . varKey) qvars
  explist'      = (intersperse (ITok P_COMMA) explist)
  qlist'        = (intersperse (ITok P_COMMA) qlist)
  t             = explist' ++ [ITok P_SEP_SLASH] ++ qlist'
\end{code}





\subsection{Predicate Pretty-Printing}


Functions to generate \texttt{ISeq} trees for predicates.
All of these generate unannotated branches. These aren't
annotated as '\texttt{APred}' as that is for higher level code to use.
\begin{code}
toISeq_pred :: ([Trie (Int,b)],String -> Maybe String) -> Int -> Pred -> ISeq
\end{code}

\subsubsection{Pretty-printing ``Atomic'' Predicates}
\begin{eqnarray*}
   \ppr c &=& \rndr c
\\ \ppr P &=& \annote{PVar} @ P
\\ \ppr{\texttt{PExpr}~e} &=& \ppr e
\\ \ppr{e : T} &=& \ppr e ~:~ \ppr T
\end{eqnarray*}
\begin{code}
toISeq_pred (prec,l2a) curprec (TRUE) = iConcat [ITok P_TRUE]

toISeq_pred (prec,l2a) curprec (FALSE) = iConcat [ITok P_FALSE]

toISeq_pred (prec,l2a) curprec (PVar root)
 = iConcat [IAnnote [APVar] (IString $ show root)]

toISeq_pred (prec,l2a) curprec (PExpr e)
  = iConcat [toISeq_expr (prec,l2a) curprec e]

toISeq_pred (prec,l2a) curprec (TypeOf e t)
 = iConcat [ toISeq_expr (prec,l2a) curprec e
           , ITok P_HASTYPE, toISeq_type (prec,l2a) curprec t ]
           -- * ^ THIS MAY NEED TO BE FIXED *
\end{code}

\subsubsection{Pretty-printing Composite Predicates}

\begin{eqnarray*}
   \ppr{\lnot P} &=& \lnot \ppr P
\\ \ppr{P_1 \oplus \cdots \oplus P_n}
   &=& \ppr{P_1}~\rndr\oplus~\cdots~\rndr\oplus~\ppr{P_n}
\end{eqnarray*}
\begin{code}
toISeq_pred (prec,l2a) curprec (PApp nm [p])
 | nm == n_Not
 = iConcat [(ITok P_NOT),(toISeq_pred (prec,l2a) 0 p)] -- force bracketing

toISeq_pred (prec,l2a) curprec (PApp nm plist)
  | nm == n_And
  = iConcat ([br_s] ++ (intersperse (ITok P_AND)
                                    (map (toISeq_pred (prec,l2a) thisprec) plist))
                    ++ [br_e] )
  where (br_s, br_e) = brackets curprec thisprec
        thisprec     = 10

toISeq_pred (prec,l2a) curprec (PApp nm plist)
 | nm == n_Or
 = iConcat ([br_s] ++ (intersperse (ITok P_OR)
                      (map (toISeq_pred (prec,l2a) thisprec) plist))
                   ++ [br_e] )
 where (br_s, br_e) = brackets curprec thisprec
       thisprec     = 11

toISeq_pred (prec,l2a) curprec (PApp nm [pred1, pred2])
 | nm == n_NDC
 = iConcat [ br_s, p_toISeq_pred pred1
           , ITok P_NDC, p_toISeq_pred pred2, br_e ]
 where (br_s, br_e)  = brackets curprec thisprec
       p_toISeq_pred = toISeq_pred (prec,l2a) thisprec
       thisprec      = 11 -- * THIS NEEDS TO BE FIXED *

toISeq_pred (prec,l2a) curprec (PApp nm [pred1, pred2])
 | nm == n_Imp
 = iConcat [ br_s, p_toISeq_pred pred1
           , ITok P_IMPLIES, p_toISeq_pred pred2, br_e ]
 where (br_s, br_e)  = brackets curprec thisprec
       p_toISeq_pred = toISeq_pred (prec,l2a) thisprec
       thisprec      = 12 -- * THIS NEEDS TO BE FIXED *

toISeq_pred (prec,l2a) curprec (PApp nm [pred1, pred2])
 | nm == n_RfdBy
 = iConcat [ br_s, p_toISeq_pred pred1
           , ITok P_RFDBY, p_toISeq_pred pred2, br_e ]
 where (br_s, br_e)  = brackets curprec thisprec
       p_toISeq_pred = toISeq_pred (prec,l2a) thisprec
       thisprec      = 12 -- * THIS NEEDS TO BE FIXED *

toISeq_pred (prec,l2a) curprec (PApp nm [pred1, pred2])
 | nm == n_Eqv
 = iConcat [ br_s, ptoISeq_expr pred1
           , ITok P_EQUIV, ptoISeq_expr pred2, br_e ]
 where (br_s, br_e) = brackets curprec thisprec
       ptoISeq_expr = toISeq_pred (prec,l2a) thisprec
       thisprec     = 13 -- * THIS MAY NEED TO BE FIXED *
\end{code}

\begin{eqnarray*}
   \ppr{P_1 \cond C P_2}
   &=& \annote{Cond} @ \ppr{P_1}~\cond{\ppr C}~\ppr{P_2}
\end{eqnarray*}
\begin{code}
toISeq_pred (prec,l2a) curprec (PApp nm [pred1, pred2, pred3])
 | nm == n_If
 = IAnnote [ACond]
             (iConcat [ br_s, ptoISeq_expr pred2
                      , ITok P_LHD, ptoISeq_expr pred1, ITok P_RHD
                      , ptoISeq_expr pred3, br_e ])
 where (br_s, br_e) = brackets curprec thisprec
       ptoISeq_expr = toISeq_pred (prec,l2a) thisprec
       thisprec = 14 -- * THIS MAY NEED TO BE FIXED *
\end{code}

Now, UTP-specific composites.
\begin{eqnarray*}
   \ppr{P[sub]~}
   &=& (~\ppr{P}~)~\ppr{~[sub]~}
\end{eqnarray*}
\begin{code}
toISeq_pred (prec,l2a) curprec (Sub pred sub)
 = iConcat ([ iConcat first
            , IAnnote [ASubs] (toISeq_esubs (prec,l2a) curprec sub ) ])
 where
  first = [ ITok P_PAREN_START
          , toISeq_pred (prec,l2a) curprec pred, ITok P_PAREN_END]
\end{code}

The \texttt{Lext} cases output tokens
in place of certain strings that represent known common operators.
\begin{eqnarray*}
   \ppr{P \oplus Q} &=& \ppr P~(\annote{Bin}@\rndr\oplus)~\ppr Q
\\ \ppr{v \hookleftarrow e} &=& \ppr v~(\annote{AVE}@\rndr\hookleftarrow)~\ppr e
\\ \ppr{e \diamond P} &=& \ppr e~(\annote{AEP}@\rndr\diamond)~\ppr P
\\ \ppr{P \boxplus_e Q} &=& \ppr P~(\annote{A3}@\rndr{\boxplus_{\ppr e}})~\ppr Q
\end{eqnarray*}
\begin{code}
toISeq_pred (prec,l2a) curprec (Lang opname p les ss)
 = iConcat ( [br_s,IString "Lang-NYI-",token,br_e] )
 where (br_s, br_e) = brackets curprec 16
       token = case opname of -- SHOULD LOOKUP A TABLE !!!
        "|~|" -> (ITok P_INT_CHOICE)
        "[]"  -> (ITok P_EXT_CHOICE)
        "&"   -> (ITok P_GUARD)
        a     -> IString a
\end{code}

\subsubsection{Pretty-printing Quantified Predicates}

\begin{eqnarray*}
   \ppr{\quant v @ P}
   &=&
   \quant~\ppr v~@~\ppr P
\end{eqnarray*}
\begin{code}
toISeq_pred (prec,l2a) curprec (PAbs nm _ qvars [pr])
 | nm == n_Forall
 = iConcat [ br_s, ITok P_FORALL, toISeq_Qvar qvars
           , ITok P_AT, toISeq_pred (prec,l2a) thisprec pr
           , br_e ]
 where (br_s, br_e) = brackets curprec thisprec
       thisprec = 17 -- * THIS MAY NEED TO BE FIXED *

toISeq_pred (prec,l2a) curprec (PAbs nm _ qvars [pr])
 | nm == n_Exists
 = iConcat [ br_s, ITok P_EXISTS, toISeq_Qvar qvars
           , ITok P_AT, toISeq_pred (prec,l2a) thisprec pr
           , br_e ]
 where (br_s, br_e) = brackets curprec thisprec
       thisprec = 16 -- * THIS MAY NEED TO BE FIXED *

toISeq_pred (prec,l2a) curprec (PAbs nm _ qvars [pr])
 | nm == n_Exists1
 = iConcat [ br_s, ITok P_EXISTS1, toISeq_Qvar qvars
           , ITok P_AT, toISeq_pred (prec,l2a) thisprec pr
           , br_e ]
 where (br_s, br_e) = brackets curprec thisprec
       thisprec = 15 -- * THIS MAY NEED TO BE FIXED *

toISeq_pred (prec,l2a) curprec (PAbs nm  _ [] [pred])
 | nm == n_Univ
 = iConcat [ ITok P_UNIV_START
           , toISeq_pred (prec,l2a) curprec pred
           , ITok P_UNIV_END ]
\end{code}


\subsection{Type Pretty-Printing}

Function patterns to output type expressions.
All returned branches are annotated as \texttt{ATyp}.
\begin{eqnarray*}
  \ppr{T} &=& \annote{Typ} @ \rndr T
\end{eqnarray*}
\begin{code}
toISeq_type :: ([Trie (Int,a)],String -> Maybe String) -> Int -> Type -> ISeq

toISeq_type (prec,l2a) curprec (B)
 = IAnnote [ATyp] (iConcat [ITok P_BOOL])

toISeq_type (prec,l2a) curprec (Z)
 = IAnnote [ATyp] (iConcat [ITok P_INTEGER])

toISeq_type (prec,l2a) curprec (TApp n typelist)
 | n==n_Tprod
   = IAnnote [ATyp]
       (iConcat ( [ITok P_PAREN_START]
                  ++ (intersperse (ITok P_CROSS) (map toISeq typelist))
                  ++ [ITok P_PAREN_END] ))
   where toISeq = toISeq_type (prec,l2a) curprec

toISeq_type (prec,l2a) curprec (Tfun t1 t2)
 = IAnnote [ATyp] (iConcat [toISeq t1, ITok P_FUN, toISeq t2])
 where toISeq = toISeq_type (prec,l2a) curprec

toISeq_type (prec,l2a) curprec (Tfree name typelist)
 = IAnnote [ATyp]
     (iConcat ( [ IAnnote [TypeVar] (ITok (P_TFREENAME name))
                , ITok P_HOLDS]
                ++ concat (map f typelist) ))
 where
   toISeq = toISeq_type (prec,l2a) curprec
   f(tag,[])    = [IString tag]
   f(tag,types) = [IString tag, ITok P_LDATA]
                  ++ (map toISeq types) ++ [ITok P_RDATA]

toISeq_type (prec,l2a) curprec (Tvar a)
 = IAnnote [ATyp]
     (iConcat [IAnnote [AVar, TypeVar] (ITok (P_TVARNAME a))])

toISeq_type (prec,l2a) curprec (Tenv)
 = IAnnote [ATyp] (iConcat [ITok P_TENV])

toISeq_type (prec,l2a) curprec (Tarb)
  = IAnnote [ATyp] (iConcat [ITok P_TARB])

toISeq_type (prec,l2a) curprec (Terror a _)
  = IAnnote [ATyp] (iConcat [IString a])

-- toISeq_type _ _ a = IString ("couldn't handle" ++ show a)
\end{code}

\subsection{QVars Pretty-Printing}

Function pattern to write out \texttt{QVars}.
Currently we are required to create tokens for the variables
to ensure that they are distinguishable.
We also need a separator for the \texttt{Qqpair}
as otherwise we wouldn't be able
to distinguish between that or a list,
or the second variable may interfere with the parsing of predicates/expressions
where the \texttt{Qvar} is used%
\footnote{
  The whole issue of parsing and inferring variable usage needs to be addressed.
  Should we use naming conventions? Or other context information?
  Explicit tagging should be avoided, but maybe allowed for users to
  do special things were inference fails to pick something up
  (Andrew Butterfield, Dec. 2008).
}%
.
\begin{eqnarray*}
   \ppr v &=& \annote{Var} @ v
\\ \ppr{v_1,\ldots,v_n}
   &=& (\annote{Var} @ v_1)~,~\ldots~,~(\annote{Var} @ v_n)
\\ \ppr q &=& \annote{QVar} @ q
\\ \ppr{qs} &=& \annote{QVar} @ qs
\\ \ppr{(q_1,q_2)} &=& (~\ppr{q_1}~,~\ppr{q_2}~)
\end{eqnarray*}
\begin{code}
toISeq_var :: Variable -> ISeq
toISeq_var x = toISeq_varlist AVar [x]

toISeq_vars :: [Variable] -> ISeq
toISeq_vars xs = toISeq_varlist AVar xs

toISeq_Qvar :: QVars -> ISeq
toISeq_Qvar ( xs) = toISeq_varlist AVar xs

toISeq_varlist anote xs
 = iConcat (intersperse (ITok P_COMMA)
       (map (IAnnote [anote] . IString . varKey) xs))
\end{code}

\subsection{Pretty-Printing Utilities}

Factored out bracket function that handles the bracketing logic.
\begin{code}
brackets :: Int -> Int -> (ISeq, ISeq)
brackets curLevelPrec thisLevelPrec
 | curLevelPrec <= thisLevelPrec = (ITok P_PAREN_START, ITok P_PAREN_END)
 | otherwise                     = (INil, INil)

iConcat :: [ISeq] -> ISeq
iConcat [] = INil
iConcat [iseq] = iseq
iConcat list = IConcat list
-- why have this function at all ?
-- it could map [] to INil
-- it could map [x] to x, but it seems some processing expects lists
\end{code}





\subsection{Utilities}


\texttt{removeFirstPNewLine} strips the first \texttt{PNewline}
from a \texttt{ISeq} at the highest level
if it is the first item in the list of leaves.
\begin{code}
removeFirstPNewLine (IAnnote alist iseq)
  = IAnnote alist (removeFirstPNewLine iseq)

removeFirstPNewLine (IConcat sl)
 = if head sl == IPNewLn
    then (IConcat (drop 1 sl))
    else (IConcat sl)

removeFirstPNewLine iseq = iseq
\end{code}

\texttt{interspersel} is a variant of Prelude's intersperse,
where instead of taking a single item and interspersing
it in a list,
we take a list and intersperse it in another list.

\begin{code}
interspersel :: [a] -> [a] -> [a]
interspersel []    b      =  b
interspersel _     []     =  []
interspersel ilist (b:bs)
  = if null bs then [b] else [b]++ilist++(interspersel ilist bs)
\end{code}


\newpage
\subsection{Displaying \texttt{ISeq} trees}

The \texttt{iDisplay} function transforms an \texttt{ISeq} tree
by pre-order traversal into a string.
It ignores any annotations, assuming those to have been dealt with
by previous pre-processing steps.
\begin{code}
iDisplay :: ISeq -> String
iDisplay (INil)   = ""
iDisplay (INewLn)   = "\n"
iDisplay (IPNewLn)    = "\n\\\\&& "
iDisplay (Indent i)   = (dupquad i)++" "
iDisplay (IConcat list) = concat (map iDisplay list)
iDisplay (ITok a)   = tokenToString a --    ++ " "
iDisplay (IString a)    = a ++ " "
iDisplay (IAnnote a iseq) = iDisplay iseq
iDisplay (INum a)   = show a --  ++ " "
-- iDisplay (IInfRule a)    = a ++ "!"
\end{code}

Produces an \texttt{Int}'s worth of \LaTeX\ mathmode indentations.
\begin{code}
dupquad :: Int -> String
dupquad num
  = concat ( ["\\qquad" | x <- [1..(num `div` 2)]]
             ++ ["\\quad" | x <- [1..(num `mod` 2)]])
\end{code}

\subsubsection{ITok translations for \LaTeX}

\textbf{Should use tables from \texttt{LaTeXSetup}}
\begin{code}
tokenToString :: LaTeXToken -> String
tokenToString (P_COMMA) = ","
tokenToString (P_PAREN_START) = "("
tokenToString (P_PAREN_END) = ")"
tokenToString (P_TRUE)  = "True"
tokenToString (P_FALSE) = "False"
tokenToString (P_SET_START) = "\\{"
tokenToString (P_SET_END) = "\\}"
tokenToString (P_MAPSTO_START)  = "\\{"
tokenToString (P_MAPSTO_END)  = "\\}"
tokenToString (P_SEQ_START) = "\\langle "
tokenToString (P_SEQ_END) = "\\rangle "
tokenToString (P_LHD)   = "\\lhd "
tokenToString (P_RHD)   = "\\rhd "
tokenToString (P_DEFD)    = "\\Defd "

tokenToString (P_EQUIV) = "\\equiv "
tokenToString (P_IMPLIES) = "\\implies "
tokenToString (P_RFDBY) = "\\refinedby "
tokenToString (P_LAMBDA)  = "\\lambda "
tokenToString (P_AT)    = "@"
tokenToString (P_POINT)   = "."
tokenToString (P_LDATA)   = "\\ldata"
tokenToString (P_RDATA)   = "\\rdata"
tokenToString (P_IF)    = "\\IF "
tokenToString (P_THEN)  = "\\THEN "
tokenToString (P_ELSE)  = "\\ELSE "
tokenToString (P_NOT)   = "\\lnot "
tokenToString (P_EQUALS)  = "="
tokenToString (P_MAP)   = "\\ffun "
tokenToString (P_MAPSTO)   = "\\mapsto "
tokenToString (P_AND)   = "\\land "
tokenToString (P_OR)    = "\\lor "
tokenToString (P_NDC)   = "\\intchoice "
tokenToString (P_SEQCOMP) = "\\seqcomp "
tokenToString (P_EXT_CHOICE)  = "\\extchoice "
tokenToString (P_INT_CHOICE)  = "\\intchoice "
tokenToString (P_SET)   = "\\power "
tokenToString (P_GUARD) = "\\amp "
tokenToString (P_CROSS) = "\\cross "
tokenToString (P_FUN)   = "\\fun "
tokenToString (P_PFUN)  = "\\pfun "
tokenToString (P_FORALL)  = "\\forall "
tokenToString (P_EXISTS)  = "\\exists "
tokenToString (P_EXISTS1) = "\\exists_1 "
tokenToString (P_HOLDS) = "::="
tokenToString (P_HASTYPE) = ":"
tokenToString (P_JHASTYPE)  = "& : &"
tokenToString (P_QVARSEP) = "\\qvarsep "
tokenToString (P_BOOL)  = "\\bool "
tokenToString (P_INTEGER) = "\\num "
tokenToString (P_SEQ)   = "\\seq "
tokenToString (P_SEQP)  = "\\seq_1 "
tokenToString (P_TARB)  = "\\arb "
tokenToString (P_TENV)  = "\\Env "
tokenToString (P_JDEFS) = "& \\defs &"
tokenToString (P_SEMICOLON) = ";"
tokenToString (P_UNIV_START)  = "["
tokenToString (P_UNIV_END)  = "]"
tokenToString (P_SEP_PIPE)  = "|"
tokenToString (P_SUB_START) = "["
tokenToString (P_SUB_END) = "]"
tokenToString (P_SEP_SLASH) = "/"
tokenToString (P_REDUCE)  = "Reduce to True."
tokenToString (P_LHS2RHS) = "Transform left-hand side into right-hand."
tokenToString (P_RHS2LHS) = "Transform right-hand side into left hand."
tokenToString (P_REDUCE_2)  = "Reduce both sides to the same."
tokenToString (P_LAWRED)  = "Reduce Law to Goal : "
tokenToString (P_ASSUME)  = "Assume antecedents, "
tokenToString (P_PR_IMP)  = "\\IMP"
tokenToString (P_PR_EQV)  = "\\EQV"
tokenToString (P_PR_PMI)  = "\\PMI"
tokenToString (P_MATHMODE)  = "$$"
tokenToString (P_ST_PRED) = "&&"
tokenToString (P_SST_PRED)  = "\\\\&&"
tokenToString (P_QED)   = "\\qed "
tokenToString (P_PAPP)  = "\\papp "
tokenToString (P_OBS)   = "\\obs "

tokenToString (P_MACRO m) = '\\':m
tokenToString (P_QVAR x)    = "\\qvar{" ++ x ++ "}"
tokenToString (P_QQVAR x)   = "\\qqvar{" ++ x ++ "}"
tokenToString (P_QQVARLIST x)   = "\\qqvarlist{" ++ x ++ "}"
tokenToString (P_PROOFNAME name)  = "\\ProofName{" ++ name ++ "}"
tokenToString (P_EVARNAME name) = "\\evarname{" ++ name ++ "}"
tokenToString (P_END name)    = "\\end{" ++ name ++ "}"
tokenToString (P_BEGIN name)    = "\\begin{" ++ name ++ "}"
tokenToString (P_THEORY_ID name num)
  =  "\\theoryNameVersion{" ++ name ++ "}{" ++ show num ++ "}"
tokenToString (P_JNAMES)    = "& \\names &"
tokenToString (P_PROPNAME x)    = "\\propname{" ++ x ++ "}"
tokenToString (P_ELAMBDA)   = "\\elambda "
tokenToString (P_PLAMBDA)   = "\\plambda "
tokenToString (P_TVARNAME x)    = x -- no more \tvarname
tokenToString (P_TFREENAME x)   = "\\tfreename{"++x++"}"
-- tokenToString a = show a
\end{code}



\subsection{Currently Unused Stuff}

\texttt{stripDup} removes duplicates from a list.
\begin{code}
stripDup :: (Eq a) => [a] -> [a]
stripDup list   = foldl (\ x y -> if elem y x then x else x++[y]) [] list
\end{code}

Debug function that (badly) prints out an ISeq tree complete with Annotations.
\begin{code}
fprint :: Int -> ISeq -> String
fprint i (IAnnote list iseq)    = show list ++ "::" ++ fprint i iseq
fprint i (IConcat list)     = "\n" ++ (replicate i '\t') ++ "[" ++ (concat (intersperse "," (map (fprint (i+1)) list)))++ "]"
fprint i iseq         = show iseq
\end{code}

\texttt{operatorlist}  is a list of operator tokens,
is currently unused, and possibly incomplete.
\begin{code}
operatorlist  = [ITok P_EQUIV, ITok P_IMPLIES, ITok P_LAMBDA, ITok P_AT, ITok P_IF,
    ITok P_THEN, ITok P_ELSE, ITok P_NOT, ITok P_EQUALS, ITok P_MAPSTO,
    ITok P_AND, ITok P_OR, ITok P_SEQCOMP, ITok P_EXT_CHOICE, ITok P_INT_CHOICE,
    ITok P_SET, ITok P_GUARD, ITok P_CROSS, ITok P_FUN, ITok P_FORALL,
    ITok P_EXISTS, ITok P_EXISTS1, ITok P_HOLDS, ITok P_HASTYPE]
\end{code}

Function \texttt{sublist} returns True iff every element of the first list can be
found in the second list%
\footnote{It depends on both lists being sorted}%
.
\begin{code}
sublist :: (Eq a) => [a] -> [a] -> Bool
sublist small big = small == (take (length small) big)
\end{code}


\subsubsection{\texttt{ISeq} transform: merge annotations}


\texttt{mergeAnnotations} merges a group of a nested Annotations into a single annotation.
Currently not used,
written for the maintainer's sake, and those wishing to extend.
\begin{code}
mergeAnnotations :: ISeq -> ISeq

mergeAnnotations (IAnnote alist1 (IAnnote alist2 iseq))
 = mergeAnnotations (IAnnote alist' iseq)
 where
  alist' = sort (alist1 ++ [ x | x <- alist2, not (elem x alist1)])

mergeAnnotations (IAnnote alist (IConcat list))
 = (IAnnote alist (IConcat ( map mergeAnnotations list)))

mergeAnnotations (IConcat list)
 = (IConcat (map mergeAnnotations list))

mergeAnnotations (IAnnote alist iseq) = (IAnnote alist iseq)

mergeAnnotations a = a
\end{code}

\subsubsection{\texttt{ISeq} transform: conditional map (bottom-up)}

\texttt{cBranchMapBU}  is almost identical to \texttt{cBranchMapTD},
except the order of transformations is reversed.
The transformation at a branch is applied
after the transformation of the sub branches.

This variation of the above is supplied for the sake of completeness.
I feel that for most transformations the end result won't differ,
 depending on the function used.
If there is a difference,
the supplied transformation could (or should) be broken into
smaller transforms.
Note that currently we test first,
then recurse down the tree, then apply the transformation to the list.
\begin{code}
cBranchMapBU :: ([Annote] -> Bool) -> (ISeq -> ISeq) -> ISeq -> ISeq

cBranchMapBU p f (IConcat sl) = IConcat (map (cBranchMapBU p f) sl)

cBranchMapBU p f (IAnnote alist (IConcat sl))
 = if p alist
    then f (IAnnote alist (IConcat (map (cBranchMapBU p f) sl)))
    else  IAnnote alist (IConcat (map (cBranchMapBU p f) sl))

cBranchMapBU p f a = a
\end{code}
