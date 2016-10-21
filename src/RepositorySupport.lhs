\section{Test Repository Support}

\begin{code}
module RepositorySupport where
import Utilities
import Tables
import TestFramework
import TestRepository
\end{code}
\begin{code}
tstlog :: String -> TLog
tstlog nm
 = tlog
 where (Just tlog) = fmap tLog $ tlookup tstrepo nm

displog :: String -> IO ()
displog nm = putStrLn $ displayTLog $ tstlog nm

runtest :: String -> TestReplay
runtest = runRepoTest tstrepo

rerun :: String -> TLog
rerun = snd . runtest

clrun :: String -> IO ()
clrun = cleanlog . rerun

replay :: String -> IO ()
replay = shlog . runtest

lstrepo :: IO ()
lstrepo = putStr $ listRepo tstrepo

regression :: [(String, (TLog, TLog))]
regression = regressRepo tstrepo

regressed :: [String]
regressed = map fst regression

cleanit :: String -> IO ()
cleanit = cleanlog . tstlog

benchmark :: [(String,TLog)]
benchmark = benchMarkRepo tstrepo

cleanbm :: [(a,TLog)] -> IO ()
cleanbm = sequence_ . map (cleanlog . snd)

scrutinise :: String -> IO ()
scrutinise = scrutiniseRepo tstrepo


reportFail :: Trie TDescr -> IO ()
reportFail = reportFailingEntries 0 . mapsnd tLog . flattenTrie

reportFailingEntries nf []
	| nf == 0  =  putStrLn "No failures :-)"
	| otherwise  =  return ()
reportFailingEntries nf ((nm,tlog):rest)
 = do nf' <- rep 0 nm tlog
      reportFailingEntries (nf+nf') rest
		where
   rep nf nm []  = return nf
   rep nf nm [_] = return nf
   rep nf nm ((TLogGet _ inp):(TLogPut _ out (FAIL reason)):rest)
     = do putStrLn ("\n'" ++ nm ++ "' with " ++ inp ++ " FAILs ("++reason++") giving:\n"++out)
          rep (nf+1) nm rest
   rep nf nm (_:_:rest) = rep nf nm rest

failures  = reportFail tstrepo

seefails nm
 = do putStrLn("Test: "++nm)
      case tlookup tstrepo nm of
        Nothing -> putStrLn " - not found !"
        Just tdescr -> reportFailingEntries 0 [(nm,tLog tdescr)]

failingtests = map fst $ filter hasFail $ flattenTrie tstrepo

hasFail (_,tdescr) = any isFail $ tLog tdescr

isFail (TLogPut _ _ (FAIL _))  =  True
isFail _                       =  False
\end{code}
These tests are usually cut-n-paste from terminal windows,
where \texttt{cleanit}/\texttt{cleanlog} have been used.
\begin{code}
tstrepo :: Trie TDescr
tstrepo
  =  case lubuild tstlist of
       Left err   -> error "lubuild tstlist failed"
       Right trie -> trie

tstlist =
 [ -- Combinatorial Logic Patterns
   matchAandB
   -- Quantifier Patterns
 , matchAllXP
 , matchAllXsP
 , matchAllXXsP
 , matchAllXsYsP
 , matchAnyOaP
 , matchAnyOmP
 , matchAnySxP
 , matchAnySvP
 , matchAnySvsP
 -- List-Variable Equality Patterns
 , matchEqSS
 , matchEqSx
 , matchEqSv
 , matchEqXsO
 , matchEqXsEs
 , matchEqSVs
 , matchEqSUsVs
 , matchEqXSUs
 , matchEqUsSX
 ]
\end{code}

