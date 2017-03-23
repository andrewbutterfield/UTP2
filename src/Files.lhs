\section{File Handling}

\begin{code}
module Files where
import Data.List
import System.IO
import System.Directory
import System.FilePath
import Utilities
import Tables
\end{code}

\subsection{Naming Conventions}

\subsubsection{\UTP2-specific files}

Whilst users can save and restore to files they name themselves,
we reserve one file name root for default startup/shutdown storing of persistent data,
as well as one for the shortcut key help file

\begin{code}
acalai = "_ACALAI"                  -- in English: "acolyte".

type FileExtension = String
type FileDescription = String
type FilePattern = String
type FileTypeSpecifier = (FileDescription,[FilePattern])
\end{code}

\subsubsection{\Saoithin\ Filestate}

We now track various file/directory related information. A directory containing
all the files relevant to a given use of \Saoithin\ is called a ``filespace'',
which has a user-supplied name, and records the path to that directory.

\begin{code}
type FileSpace = ( String      -- filespace name
                 , FilePath )  -- path to filespace
\end{code}
We then define the file extensions used:
\subsubsection{general file types}

\begin{code}
txt      = ".txt"
tex      = ".tex"
anyExt   = ".*"
anyName  = '*'

txtFiles = ("ASCII Text",[anyName:txt])
texFiles = ("LaTeX Source",[anyName:tex])
anyFiles = ("Any file type",[anyName:anyExt])
\end{code}


\subsubsection{\Saoithin-specific file types}

\begin{tabular}{|l|l|c|}
  \hline
  Entity & Extension & (literal translation) \\
  \hline
  Predicate & \texttt{.DEARBHU} & (assertion) \\
  Conjecture & \texttt{.BUILLE} & (guess) \\
  Proof & \texttt{.CRUTHU} & (proof) \\
  Theorems & \texttt{.TEOIRIME} & (theorems) \\
  Laws & \texttt{.DLITHE} & (laws) \\
  Proof Context & \texttt{.TEORIC} & (theory) \\
  Startup Script &\texttt{.CREAT} & (framework) \\
  Configuration & \texttt{.CUMRAIOCHT} & (set-up) \\
  Help & \texttt{.CABHRACH}  & (help) \\
  Style & \texttt{.STILE}  & (style) \\
  \hline
\end{tabular}

\begin{code}
dearbhu    = ".dearbhu"
buille     = ".buille"
cruthu     = ".cruthu"
teoirime   = ".teoirime"
dlithe     = ".dlithe"
teoric     = ".teoric"
creat      = ".creat"
cumraiocht = ".cumraiocht"
cabhrach   = ".cabhrach"
stile      = ".stile"
utp        = ".utp"
uttxt      = ".uttxt"

predFiles    = (" Predicate Files",[anyName:dearbhu])
conjFiles    = (" Conjecture Files",[anyName:buille])
proofFiles   = (" Proof Files",[anyName:cruthu])
theoremFiles = (" Theorem Files",[anyName:teoirime])
lawFiles     = (" Law Files",[anyName:dlithe])
contextFiles = (" Context/Theory Files",[anyName:teoric])
theoryFiles  = (" Theory Files",[anyName:teoric,anyName:utp,anyName:uttxt])
startFiles   = (" Startup Files",[anyName:creat])
bundleTxtThryFiles
 = (" Text/Theory Bundle Files",[anyName:uttxt,anyName:teoric])

langFiles    = (" Language Files",[anyName:anyExt])
precFiles    = (" Precedence Files",[anyName:anyExt])
typeFiles    = (" Type Files",[anyName:anyExt])
exprFiles    = (" Expression Files",[anyName:anyExt])
\end{code}
It can be useful to check filenames for type:
\begin{code}
hasExt ext fname = ext `isSuffixOf` fname

isDearbhu    = hasExt dearbhu
isBuille     = hasExt buille
isCruthu     = hasExt cruthu
isTeoirime   = hasExt teoirime
isDlithe     = hasExt dlithe
isTeoric     = hasExt teoric
isCreat      = hasExt creat
isCumraiocht = hasExt cumraiocht
isCabhrach   = hasExt cabhrach
isStile      = hasExt stile
isUtp        = hasExt utp
isUttxt      = hasExt uttxt
\end{code}

\subsection{Filename Cleaning}

We also generate filenames from user-supplied
theory and proof names, and these need to be cleaned
to replace certain characters by alphanumeric equivalents.
We also ensure that any hyphens or dots at the end are
replaced.
\begin{code}
fileNameClean :: String -> String
fileNameClean name = fnFixEnds $ trie_repl fnCleanTrie $ name

fnFixEnds fname = fe $ reverse $ fe $ reverse $ fname
 where
   fe [] = []
   fe nm@(c:rest)
    | c `elem` "-."  =  '_':rest
    | otherwise      =  nm
\end{code}
There is quite a range of characters that should not be
used for maximum portability across Windows/Unix/Mac
\begin{verbatim}
"$&'*/:<>?@\`|~
\end{verbatim}
We also want to cater for combinations that might
occur frequently in ASCII-style conjecture names:
\begin{verbatim}
== => ~ /\ \/ |~| |=
\end{verbatim}
\begin{code}
fnCleanTrie
 = lbuild
    [ "\""  ---> "DQ"
    , "$"   ---> "DLR"
    , "&"   ---> "AMP"
    , "'"   ---> "SQ"
    , "*"   ---> "AST"
    , "/"   ---> "FSL"
    , ":"   ---> "CLN"
    , "<"   ---> "LE"
    , ">"   ---> "GE"
    , "?"   ---> "QM"
    , "@"   ---> "AT"
    , "\\"  ---> "BSL"
    , "`"   ---> "BQ"
    , "|"   ---> "BAR"
    , "="   ---> "EQ"
    , "=="  ---> "EQV"
    , "=>"  ---> "IMP"
    , "~"   ---> "NOT"
    , "/\\" ---> "AND"
    , "\\/" ---> "OR"
    , "|~|" ---> "NDC"
    , "|="  ---> "RFD"
    ]
\end{code}


\subsection{Pathname Handling}

Stripping out directory names was%
\footnote{until we discovered that the notion of ``current
directory'' was nebulous, at best}
a good idea.
Stripping extensions can be good too
\begin{code}
stripDir name = reverse (fst (break isPathSeparator (reverse name)))

stripExt name
 = reverse $ ttail $ dropWhile (/='.') $ reverse name 
\end{code}

