\section{Archiving}

\begin{code}

module Archive where
import Tables
import Datatypes
import Types
import Focus
import Heuristics
import Builtin
import Manipulation
import Proof
import Files
import ImportExport

import Data.List
import System.IO
import System.FilePath
import Control.Exception

\end{code}

\subsection{The General Idea}

This module supports the archival and retrieval of proof-related objects,
with a particular emphasis on \texttt{ProofContext}s.

An archival object has a name, sequence number and state:
\begin{eqnarray*}
   ArchObj_T &\defs& Name \times \nat \times T
\end{eqnarray*}
We recognise 3 levels of modification
(ordered from \emph{Transient} upto \emph{Upgrade}):
\begin{description}
  \item[Transient] not worth saving
  \item[Log] worth saving, but no version change
  \item[Upgrade] need to be saved, and the version number increased
\end{description}

\subsubsection{Escalating Modification Levels}

\begin{code}

raiseTheoryMod thry mod
 | modified thry < mod  =  thry{modified=mod}
 |otherwise             =  thry

\end{code}



\subsubsection{A semi-Formal Model}


A live object is an archival object with an extra modified flag.
\begin{eqnarray*}
   LiveObj_T &\defs& ArchObj_T \times {Transient,Log,Upgrade}
\end{eqnarray*}
An initial or root version of a live object has sequence number zero,
and is unmodifed:
\begin{eqnarray*}
   newLiveObj &:& Name \times T \fun LiveObj_T
\\ newLiveObj(N,\Sigma_0) &\defs& ((N,0,\Sigma_0),Transient)
\end{eqnarray*}
An import operation turns a just-inputted archival object
into an unmodified live object:
\begin{eqnarray*}
   import_T &:& ArchObj_T \fun LiveObj_T
\\ import_T (A) &\defs& (A,Transient)
\end{eqnarray*}
An export operation increments the sequence number if the object has been
marked as requiring an upgrade
\begin{eqnarray*}
   export_T &:& LiveObj_T \fun ArchObj_T
\\ export_T((N,i,\Sigma),Upgrade) &\defs& (N,i+1,\Sigma)
\\ export_T(A,\_) &\defs& A
\end{eqnarray*}
We define four classes of modify operation:
\begin{description}
  \item[Transient] the operation modifies transient state components
   for which saving is not an issue:
   \begin{eqnarray*}
      transientOp_T &:& (T \fun T) \fun LiveObj_T  \fun LiveObj_T
   \\ transientOp_T(f)((N,i,\Sigma),m) &\defs& ((N,i,f~\Sigma),m)
   \end{eqnarray*}
  \item[Permanent:Log] permanent state changes result, requiring saving
   \begin{eqnarray*}
      logOp_T &:& (T \fun T) \fun LiveObj_T  \fun LiveObj_T
   \\ logOp_T(f)((N,i,\Sigma),m) &\defs& ((N,i,f~\Sigma),max(m,Log))
   \end{eqnarray*}
  \item[Permanent:Upgrade] permanent state changes result, requiring a version update:
   \begin{eqnarray*}
      permOp_T &:& (T \fun T) \fun LiveObj_T  \fun LiveObj_T
   \\ permOp_T(f)((N,i,\Sigma),m) &\defs& ((N,i,f~\Sigma),Upgrade)
   \end{eqnarray*}
  \item[Dirty] the state change is incompatible with previous versions,
  so a new identity is required:
   \begin{eqnarray*}
      dirtyOp_T &:& (T \fun T)\times(Name \fun Name) \fun LiveObj_T  \fun LiveObj_T
   \\ \pre{dirtyOp}_T(f,r)((N,\_,\Sigma),m) &\defs& N \neq r~N
   \\ dirtyOp_T(f,r)((N,\_,\Sigma),m) &\defs& ((r~N,0,f~\Sigma),Transient)
   \end{eqnarray*}
   Such an object is deemed new and hence unmodified.
\end{description}
Given an archive of $n$ versions of a structure,
there will be $n+1$ files present, all but one labelled
with both name and number.
The remaining file is labelled with name only,
and matches the latest numbered version:
\begin{eqnarray*}
   fileNames &:& Name \times \power \nat \fun \power FName
\\ fileName (N,\setof{1,\ldots,k}) &\defs& \setof{N\$1,\ldots,N\$k,N}
\\ contents(N) &=& contents(N\$k)
\end{eqnarray*}


\subsection{Archiving Theories}

\begin{code}
archiveTheory cwd thry
 = do let thry' = case modified thry of
                 Upgrade  ->  thry{thrySeqNo = (thrySeqNo thry)+1, modified=Transient}
                 Log      ->  thry{modified=Transient}
                 _        ->  thry
      let dump = dumpPX thry'
      let pcname = thryName thry'
      let pcfname = cwd ++ [pathSeparator] ++ pcname ++ teoric
      putStrLn ("archive pcfname = "++pcfname)
      writeFile pcfname dump
      return thry'
\end{code}

\subsection{Archiving Proofs}
\begin{code}
archiveProof cwd prf
 = do let spcs = takeWhile isSPC (context prf)
      let prftxt =  dumpPLT (prf,spcs)
      let prfName = mkPfn (pname prf) (thname prf)
      writeFile (cwd ++[pathSeparator] ++prfName++cruthu) prftxt

mkProofFileName thnm pfnm
 = fileNameClean thnm ++ pfnSep:fileNameClean pfnm
\end{code}


\subsection{Strict File Reading}

Having problems with lazy readFile%
\footnote{in GHCi 6.4, at least}%
,
we craft our own:
\begin{code}

sReadFile fn
  = bracket (openFile fn ReadMode) hClose readContents
  where readContents fh = do { s <- hGetContents fh; return $! s }

\end{code}
Thanks to Matthew Brecknell \cite{MB:afccar:07}.
