\section{\UTP2\ Synchronisation}

\begin{code}
module WxSynchro where
import Tables
import Precedences
import Datatypes
import DataText
import Manipulation
import Proof
import Theories
import Synchronise
import Utilities
import Files
import ImportExport
import Archive
import DocTextParser
import DSL

import System.IO
import Graphics.UI.WX

import Text.ParserCombinators.Parsec.Expr

import Data.List
import Data.Maybe
import Data.Char

import WxTypes
import WxState
import WxStyle
\end{code}


The top level function pulls out the theory/proof state,
applies a pair of synchronisation functions,
and then replaces the original with the updated state.
We also supply a descriptive string argument to inform the user
about what has happened.
\begin{code}
workSpaceSync syncfs descr work
 = do ss <- varGet work
      let ws = workspace ss
      let (thrys',prfs') = syncApply syncfs (theories ws, currProofs ws)
      let ws' = ws{ theories = thrys', currProofs = prfs' }
      let ss' = workspaceSetf (const ws') ss
      varSet work ss'
      sts <- getSts work
      alert sts ("Workspace synchronised using : "++descr)
\end{code}

Synchronisation is a three-phase process:
\begin{enumerate}
  \item
    Synchronise the theory graph,
    with each theory updated by changes to itself and theories
    below it.
    We do this by synchronising each theory against
    the stack of its descendants.
  \item
    Update the proofs context component to refer to
    the revised theory graph, and revise the special proof theories
  \item
    Synchronise each proof against its own (now revised) context stack.
\end{enumerate}
\begin{code}
syncApply :: (SyncFun Theory, SyncFun Proof)
              -> (TheorySpace, Trie Proofspace)
              -> (TheorySpace, Trie Proofspace)
syncApply (thsynchf, pfsynchf) (thrys, pspaces)
 = let thg = theoryGraph thrys
       thg' = syncTheoryGraph thsynchf thg
       pspaces' = tmap (syncProofspaceStack thsynchf thg') pspaces
       pspaces'' = tmap (syncProof pfsynchf) pspaces'
   in ( TheorySpace
          thg'    -- modified stack
          True    -- mark stack as modified (obviously)!
      , pspaces''
      )
\end{code}

Synchronising a proof stack means copying the revised
theories from the main-stack,
and then updating the special theories accordingly
\begin{code}
syncProofspaceStack :: SyncFun Theory -> TheoryGraph
                  -> Proofspace -> Proofspace
syncProofspaceStack thsyncf thg pspace
 = let prf = currProof pspace
       prf' = syncProofStack thsyncf thg prf
   in  pspace{ currProof=prf', matches=[] }
\end{code}

Synchronising a proof simply means apply the proof-synch function
to each proof, and discarding all matches:
\begin{code}
syncProof :: SyncFun Proof  -> Proofspace -> Proofspace
syncProof pfsyncf pspace
 = let proof = currProof pspace
       proof' = pfsyncf (context proof) proof
   in  pspace{ currProof=proof', matches=[] }
\end{code}
