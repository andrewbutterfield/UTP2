\section{\UTP2\ Test Mainline}

\begin{code}
module UTP2Test where
import Utilities
import Tables
import Datatypes
import DataText
-- import Types
import MatchTypes
-- import Invariants
import Matching
-- import FreeBound
-- import Focus
-- import Heuristics
-- import Builtin
-- import Substitution
import Laws
-- import Normalise
-- import Proof
-- import ProofReplay
-- import Theories
-- import RootTheory
-- import Synchronise
-- import Files
-- import ImportExport
-- import Archive
import DocTextParser
-- import LaTeXSetup
-- import LaTeXPretty

-- import DSL
-- import Logic
-- import GSLogic
-- import GS3001
-- import UTP
-- import R
-- import RAlg

import TestFramework
import AdHocTests
import RepositorySupport
import TestRepository
\end{code}

\subsection{Mainline}

The main program simply lists the available tests:
\begin{code}
main = tests
m = main
\end{code}


\subsection{old test framework}

\begin{code}
tests = disptests tPMDescr
go = tstmtch

disptests godescr
 = sequence_ $ map putStrLn $ (hdr:list)
 where
   hdr = "\nTop-Level Tests\n"
   nl = "\n"
   list = [ scanDescr
          , stdThDescr
          , pctxtDescr
          , cscanDescr
          , tcDescr
          , cfyDescr
          , asnTPDescr
          , prTPDescr
          , eTPDescr
          , tTPDescr
          , tSCDescr
          , nl
          , seqCompDescr
          , assignDescr
          , assignXDescr
          , simAsgnDescr
          , nl
          , rprTADescr
          , rprTPDescr
          , rprTEDescr
          , rprTTDescr
          , rprSCDescr
          , nl
          , mctxtsDescr
          , dollar3Descr
          , nl
          , tPMDescr
          , tPMDescr
          , tCDMDescr
          , rprFTDescr
          , rprIFTDescr
          , tstPSubDescr
          , predOVsDescr
          , tFDescr
          , nl
          , "go === "++godescr
          , "tstrepo :: Trie TDescr"
          , "lstrepo :: String"
          , "tstlog :: String -> TLog -- from tstrepo"
          , "displog :: String -> IO () -- from tstrepo"
          , "shlog :: ((TLog,TLog),TLog) -> IO ()"
          , "replay :: String -> IO () -- runtest 'live'"
          , "rerun :: String -> TLog  -- replay, returning log"
          , "clrun :: String -> IO ()  -- replay, with clean log display"
          , "cleanit :: String -> () -- tstlog, then cleanlog"
          , "benchmark :: [(String,TLog)] -- run tests (for definitive version)"
          , "cleanbm :: [(a,TLog)] -> IO () -- clean display of benchmark output"
          , "regression :: [(TLog,TLog)] -- divergences"
          , "regressed :: [String]"
          , "shReplay :: TestReplay -> IO ()"
          , "scrutinise :: String -> IO () -- rerun, but ask user to assess each sub-test"
          , "failingtests :: [String]"
          , "seefails :: String -> IO () -- show any FAILs in named test"
          , "failures :: IO () -- display all test steps marked as FAIL"
          ]
\end{code}
