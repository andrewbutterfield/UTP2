\section{\UTP2\ Ad-Hoc Tests}

\begin{code}
module AdHocTests where
import Tables
import Datatypes
import DataText
import Types
import MatchTypes
import Matching
import Instantiate
import FreeBound
import Focus
import Heuristics
import Builtin
import Substitution
import Laws
import Normalise
import Proof
import ProofReplay
import Theories
import RootTheory
import Synchronise
import Utilities
import Files
import ImportExport
import Archive
import DocTextParser
import LaTeXSetup
import LaTeXPretty

import GSLogic
import UTP

import TestFramework
\end{code}

\subsection{Testing Contexts}

\subsubsection{Theory Context}

\begin{code}
stdThDescr = "stdTheories :: [Theory]\n_ROOT :: Theory"
stdTheories
 = [ xyzDesignTheory
   , theoryLists
   , theorySets
   , theoryArithmetic
   , theoryEquality
   , gsNonPropTheory
   , gsPropTheory
   , rootTheory
   ]

_ROOT = rootTheory
\end{code}

\subsubsection{Matching Contexts}

\begin{code}
mctxtsDescr = "testMCtxts :: [MatchContext]"
testMCtxts = mkMatchContexts stdTheories
testMCtxt = head testMCtxts
\end{code}

\subsubsection{Parsing Context}

\begin{code}
pctxtDescr = "testPCtxt :: ParseContext"
testPCtxt
 = buildParseContext docNameToks docSymToks stdTheories
\end{code}

\subsubsection{Definition Contexts}

\begin{code}
seqCompDef  = "(P ; Q)       ==  (exists O_m @ P[O_m//O'] /\\ Q[O_m//O])"
assignDef   = "(v := e)      ==  (ok => ok' /\\ v' = e /\\ S'\\v = S\\v)"
assignXDef  = "(x := e)      ==  (ok => ok' /\\ x' = e /\\ S'\\v = S\\v)"
simAsgnDef  = "(v$ ::= e$)   ==  (ok => ok' /\\ v$' = e$ /\\ S'\\v$ = S\\v$)"

seqCompDescr  = "seqCompDef  : " ++  seqCompDef
assignDescr   = "assignDef   : " ++  assignDef
assignXDescr  = "assignXDef  : " ++  assignXDef
simAsgnDescr  = "simAsgnDef  : " ++  simAsgnDef
\end{code}


\subsection{Parsing Tests}

\subsubsection{Token Scanning}

\begin{code}
scanDescr = "testScan :: [Char] -> IO () -- [Token]"
testScan = listPut 0 . scanner ">"
\end{code}


\begin{code}
cscanDescr = "testCScan :: String -> IO () -- [Token]"
testCScan :: String -> IO () -- [Token]
testCScan src
 = let
     pctxt = buildParseContext docNameToks docSymToks stdTheories
     toks = scanner ">" src
   in listPut 2 $ contextScan pctxt toks
\end{code}

\begin{code}
tcDescr = "testTC :: String -> Tok"
testTC src
 | null toks  =  TEOF
 | otherwise  =  snd $ tokClassify ">" (nameMap pctxt) (symMap pctxt) $ head toks
 where
   toks = contextScan pctxt (scanner ">" src)
   pctxt = buildParseContext docNameToks docSymToks stdTheories
\end{code}

\begin{code}
cfyDescr = "testCfy :: String -> IO () -- [Token]"
testCfy src
 = let
     pctxt = buildParseContext docNameToks docSymToks stdTheories
     toks = scanner ">" src
     toks' = contextScan pctxt toks
   in listPut 2 $ contextClassify pctxt ">" toks'
\end{code}

\subsubsection{Parsing Tests}

\begin{code}
asnTPDescr = "testATP :: String -> Assertion"
testATP src
 = case asnTextParser stdTheories ">" src of
    Left msg   ->  (Perror msg, SCtrue)
    Right asn  ->  asn
rprTADescr = "repATP :: IO () -- repeatedly prompt and testATP"
repATP = repparse "Assertion" testATP (Just prcATP)
          -- (Nothing :: Maybe (Assertion->Assertion))
prcATP  = debugAshow
\end{code}

\begin{code}
prTPDescr = "testPTP :: String -> Pred"
testPTP src
 = case predTextParser stdTheories ">" src of
    Left msg  ->  Perror msg
    Right pr  ->  pr
rprTPDescr = "repPTP :: IO () -- repeatedly prompt and testPTP"
repPTP = repparse "Pred" testPTP (Just prcPTP)
          -- (Nothing :: Maybe (Pred->Pred))
prcPTP = debugPshow
\end{code}

\begin{code}
eTPDescr = "testETP :: String -> Expr"
testETP src
 = case exprTextParser stdTheories ">" src of
    Left msg  ->  Eerror msg
    Right e   ->  e
rprTEDescr = "repETP :: IO ()  -- repeatedly prompt and testETP"
repETP = repparse "Expr" testETP (Just prcETP)
prcETP = show . itype (envAllTypes stdTheories)
\end{code}

\begin{code}
-- typeTextParser
tTPDescr = "testTTP :: String -> Type"
testTTP src
 = case typeTextParser stdTheories ">" src of
    Left msg  ->  Terror msg Tarb
    Right t   ->  t
rprTTDescr = "repTTP :: IO ()  -- repeatedly prompt and testTTP"
repTTP = repparse "Type" testTTP (Nothing :: Maybe (Type -> String))
\end{code}

\begin{code}
-- sidecondTextParser
tSCDescr = "testSCP :: String -> SideCond"
testSCP src
 = case sidecondTextParser ">" src of
    Left msg  ->  SCtrue
    Right sc   ->  sc
rprSCDescr = "repSCP :: IO ()  -- repeatedly prompt and testSCP"
repSCP = repparse "Side-Cond" testSCP (Nothing :: Maybe (SideCond -> String))
\end{code}

\subsection{Matching Tests}


\subsubsection{Predicate Matching}


Code to test matching against a given pattern predicate,
where we first match it against itself.
\begin{code}
tPMDescr = "tstmtch :: IO TLog -- get pattern, match self, then repeatedly prompt and match"
tstmtch :: IO TLog
tstmtch = logInterTest tstMtch

tstMtch :: LoggedTest tst => tst TLog
tstMtch
 = setupRepeatTest
     sprompt   -- String
     sparse    -- (String -> (Bool,(Pred, TypeTables)))
     scompute  -- ((Pred, TypeTables) -> (Bool,Bool,Maybe Binding))
     sdescr    -- String
     sdisplay  -- (((Pred, TypeTables),(Bool,Bool,Maybe Binding)) -> String)
     prompt    -- (Pred, TypeTables) -> String
     parse     -- (String -> (Bool,Either String t))
     compute   -- ((Pred, TypeTables)->(Pred, TypeTables)->Maybe Binding)
     descr     -- String
     display   -- ( ( (Pred, TypeTables), (Pred, TypeTables), Maybe Binding )
               --   -> String)
 where

   known = unwords $ concat $ map (concat . map trieDom . knownObs) testMCtxts
   sprompt = "\n\n======================\nObsVar{"
              ++known++"}, Pattern Predicate : "

   sparse ptxt
    = case predTextParser stdTheories ">" ptxt of
       Left _  ->  (False,undefined)
       Right ppr
        -> case typeCheckPred testMCtxt ppr of
            Left _  ->  (False, undefined)
            Right tres -> (True,tres)

   topMC = head testMCtxts
   scompute (ppr, ptts)
     = ( predQVarInv topMC ppr     -- ignored for now
       , predESubstInv topMC ppr
       , lawMatch [] (predFVSet testMCtxt ppr) ptts
                 testMCtxt SCtrue ppr (ppr,SCtrue) ptts )

   sdescr  = ""

   sdisplay ((ppr, ptts),(qinv,esinv,mBinds))
    = unlines' $ outcomeDisp ppr ptts ppr ptts mBinds
   outcomeDisp ppr _ tpr _ Nothing
     = [ ( "\nPATTERN : "++show ppr)
       , (   "TEST    : "++show tpr)
       ,     "        NO MATCH"
       ]
   outcomeDisp ppr ptts tpr ttts (Just bnds)
    = showMatchR ppr ptts tpr ttts bnds

   prompt (ppr, ptts)
     = "\n\n----------------------\nObsVar{"
       ++ known
       ++ "}, Pattern: "++show ppr++", Test: "

   parse = parseNonNull parse'
   parse' ptxt
    = case predTextParser stdTheories ">" ptxt of
       Left msg  ->  Left msg
       Right ppr
        -> case typeCheckPred testMCtxt ppr of
            Left msg  ->  Left msg
            Right tres -> Right tres

   compute (ppr, ptts) (tpr, ttts)
    = lawMatch [] (predFVSet testMCtxt tpr) ttts
                 testMCtxt SCtrue tpr (ppr,SCtrue) ptts

   descr = ""

   display ((ppr, ptts), (tpr, ttts), mBinds)
     = unlines' $ outcomeDisp ppr ptts tpr ttts mBinds
\end{code}


Supporting material for \texttt{tstmtch}:
\begin{code}
showMatchR ppr ptts tpr ttts bnds
 = [ ("\nPATTERN : "++show ppr)
   , (  "TEST    : "++show tpr)
   ]
   ++ showBinding bnds
   ++
   [ "REBUILD  : "++show (instantiatePred testMCtxt bnds ppr) ]

showQVarToDo (pvs,tvs)
 = (mkSepList ',' $ map showVar pvs)
   ++ " <~< "
   ++ (mkSepList ',' $ map showVar tvs)

showSubToDo (psub,tsub,_)
 = (mkSepList ';' $ map showSub psub)
   ++ " |~> "
   ++ (mkSepList ';' $ map showSub tsub)

showSub (v,e)  = show e ++ "/" ++ showVar v
\end{code}


\begin{code}
predOVsDescr = "predOVs :: String -> [String]"
predOVs src
 = case predTextParser stdTheories ">" src of
    Left msg  ->  [msg]
    Right pr  ->  map varKey $ predFreeVars testMCtxt pr
\end{code}

\subsubsection{Clean Deferred Matches}

\begin{code}
tCDMDescr = "tstcdm :: IO TLog -- get vebind, QVarsToDo and then clean"
tstcdm :: IO TLog
tstcdm = logInterTest tstCDM

tstCDM :: LoggedTest tst => tst TLog
tstCDM = return []
\end{code}


\subsubsection{Assertion/Law Matching}

\begin{code}
tLMDescr = "testLmtch :: IO () -- get assertion, and law and match"
testLmtch
 = do let known = unwords $ concat $ map (concat . map trieDom . knownObs) testMCtxts
      putStr "Known Observables : "
      putStrLn known
      putStr "Enter Assertion : "
      ptxt <- getLine
      case asnTextParser stdTheories ">" ptxt of
       Left msg   ->  putStrLn msg
       Right asn@(tpr,tsc)
        -> case typeCheckPred testMCtxt tpr of
            Left msg -> putStrLn ("Ill-typed Assertion:\n"++msg)
            Right (tpr',ttts) -> doTestLMatch ttts tpr' tsc

doTestLMatch ttts tpr tsc
 = do putStr "Enter law name :- "
      lwname <- getLine
      case aslookup (map laws stdTheories) lwname of
        Nothing  ->  putStrLn ("Can't find law '"++lwname++"'")
        Just lw@((lpr,lsc),lprov,_)
         -> do putStrLn ("Found law '"++lwname++"'")
               putStrLn ("Law Predicate : "++show lpr)
               putStrLn ("Law Side-Cond : "++show lsc)
               case typeCheckPred testMCtxt lpr of
                 Left msg -> putStrLn ("Law Predicate Type Error:\n"++msg)
                 Right (lpr', ltts)
                  -> do putStrLn "Matching...\n"
                        fullLawMatch ttts tpr tsc ((lpr',lsc),lprov,ltts)

fullLawMatch ttts tpr tsc lw
 = case subLawMatch [] (predFVSet testMCtxt tpr) ttts
                    testMCtxt tsc (setPFocus tpr) lw
   of
     [] -> putStrLn "\n\tNO MATCHES\n"
     mtchs  ->  showMatches 1 tpr mtchs

showMatches _ _ [] = return ()
showMatches i tpr (mtch:rest)
   =  do putStrLn $
               unlines' ([ "\n----------------------\nMATCH NO:"++show i
                         ++ ", Test Pred = " ++ show tpr
                         ]
                         ++ showMatch mtch
                         ++ ["======================\n"])
         showMatches (i+1) tpr rest

showMatch (mtype,prov,bnds,sc,rprs)
 = [ "MType = "++show mtype ]
   ++ showBinding bnds
   ++
   [ "Side-Condition = "++show sc
   , "Replacement Predicates:"
   ]
   ++map show rprs
\end{code}

\subsection{Type Handling}


\begin{code}
rprFTDescr = "repFXT :: IO () -- repeatedly prompt and fixType"
repFXT = repparse "Pred" testPTP (Just prcFXT)
          -- (Nothing :: Maybe (Pred->Pred))
prcFXT pr
 = "fixType :- " ++ show ftpr
   ++ "\n:\n"
   ++ debugPshow ftpr
   ++ show tts
 where (ftpr,tts) = fixType stdTheories pr
\end{code}

\begin{code}
rprIFTDescr = "repIFT :: IO () -- repeatedly prompt and infer types"
repIFT = repparse "Pred" testPTP (Just $ prcIFT $ map types stdTheories)
          -- (Nothing :: Maybe (Pred->Pred))
prcIFT typs pr
 = "inferPredType:\n" ++ show tbinds
 where tbinds = inferPredType typs pr
\end{code}

\subsection{Substitution Handling}

\begin{code}
tstPSubDescr = "tstPSub :: IO () -- get pred-substn, and apply."
tstPSub = repparse "Pred with Substn" testPTP (Just prcSUB)

prcSUB (Sub pr subs)
 = "predOSub :- " ++ show pr'
   ++ "\n"++show chgd++"\n"
   ++ debugPshow pr'
 where
   (pr',chgd) = predOSub testMCtxt SCtrue subs pr
prcSUB (Obs (Esub e subs))
 = "exprOSub :- " ++ show pr'
   ++ "\n"++show chgd++"\n"
   ++ debugPshow pr'
 where
   (e',chgd) = exprOSub testMCtxt SCtrue subs e
   pr' = Obs e'
prcSUB pr
 = "No substitution."
   ++ "\n:"
   ++ debugPshow pr
\end{code}


\subsection{Focus Handling}

\begin{code}
tFDescr = "testFocus :: IO () -- get predicate, set focus, then repeatedly get moves"
testFocus
 = do putStr "Enter Predicate : "
      ptxt <- getLine
      case predTextParser stdTheories ">" ptxt of
       Left msg   ->  putStrLn msg
       Right ppr  ->  do putStrLn ( "pred QVar invariant : "
                                    ++ show (predQVarInv (head testMCtxts) ppr)
                                   )
                         putStrLn ( "pred ESubst invariant : "
                                    ++ show (predESubstInv (head testMCtxts) ppr)
                                   )
                         showFocii $ setPFocus ppr

showFocii fpr
 = do putStrLn "Current Focus:\n"
      putStrLn $ showPFocus fpr
      putStr "\n\nFocus, u - up, 1,2,3,... down, q - quit > "
      txt <- getLine
      case txt of
        "q"  ->  return ()
        "u"  ->  showFocii $ upPFocus fpr
        "1"  ->  showFocii $ downPFocus 1 fpr
        "2"  ->  showFocii $ downPFocus 2 fpr
        "3"  ->  showFocii $ downPFocus 3 fpr
        _    ->  showFocii fpr
\end{code}

\subsection{Generic Testing}

\begin{code}
dollar3Descr
 = "$$$ :: (Pred -> a) -> String -> a -- f $$$ str  parses str as Pred and applies f"
pfun $$$ src
 = case predTextParser stdTheories ">" src of
    Left msg  ->  error msg
    Right pr  ->  pfun pr
\end{code}
