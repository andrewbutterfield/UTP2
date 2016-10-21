\section{\UTP2\ Test Framework}

\begin{code}
module TestFramework where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)
import Control.Monad.State
import Data.Char

import Utilities
import Tables
\end{code}


\subsection{Logging Test Monad}

We want a way to specify tests that can be interactive,
but also be run in batch mode, and which can be logged,
in a fashion that support their replaying.
An interactive test is in effect an interleaving of \texttt{putStr} and \texttt{getLine}.
The batch equivalent would be a corresponding interleaving of \texttt{putLog}
and \texttt{head inputLines}. If all tests were logged, then the \texttt{putStr} would also
invoke \texttt{putLog}, and \texttt{getLine} would accumulate the event list of \texttt{inputLines}.
We also note we do not want to log everything in an interactive test (e.g. prompts),
but just the key inputs and results. A key assumption in all of this is that
the inputs and test results are all \texttt{String}s, and that all tests have an identifying
name.
We envisage three key actions, and one pure computation,
where \texttt{tst} is a suitable monad:
\begin{itemize}
  \item \texttt{getTestInput :: String -> (String -> a) -> tst a}
   \\ Action \texttt{getTestInput prompt parse}
      issues a prompt if \texttt{tst} includes \texttt{IO},
      obtains a \texttt{String} denoting the test value of type \texttt{a},
      logs it, \texttt{parse}s it,
      and returns it.
  \item \texttt{funUnderTest :: a -> b}
    \\ A pure test function that does some form of computation.
    These are part of the test specification, but are not themselves logged.
  \item \texttt{putTestResult :: String -> (b -> String) -> b -> tst b}
    \\ Action \texttt{putTestResult descr showResult result}
      prints out \texttt{descr} if \texttt{tst} includes \texttt{IO},
      applies \texttt{showResult} to \texttt{result}, logging the outcome,
      displaying it if we have \texttt{IO},
      and then returns \texttt{result}.
  \item \texttt{assessOutcome :: tst ()} obtains an assessment
      which is placed in the most recent result log.
\end{itemize}
The \texttt{tst} monad has to have state, to record the log,
and will also need to be capable of incorporating IO for interactive tests.

We shall define a log entry as identifying the action involved
(including prompt and descr strings) and recording the relevant string information:
\begin{code}
data PutStatus = Unk | FAIL String | OK deriving (Eq, Read)

instance Show PutStatus where
  show Unk            =  "Unk"
  show (FAIL reason)  =  "(FAIL "++show reason++")"
  show OK             =  "OK"

data TLogEntry
 = TLogGet String    -- prompt
           String    -- test input
 | TLogPut String    -- descr
           String    -- test outcome
           PutStatus -- is outcome correct? if not, why not?
 deriving (Eq,Show,Read)

displayTLogEntry (TLogGet prmpt inp) = prmpt ++ inp
displayTLogEntry (TLogPut dscr rslt stts) = dscr ++ rslt ++ '\n':show stts

type TLog = [TLogEntry]
displayTLog = unlines . map displayTLogEntry
\end{code}

We now define a \texttt{LoggedTest} monad class:
\begin{code}
class Monad tst => LoggedTest tst where
  getTestInput  :: String -> (String -> a) -> tst a
  putTestResult :: String -> (b -> String) -> b -> tst b
  assessOutcome :: tst ()
  getTestLog    :: tst TLog
\end{code}

We will also want to format a \texttt{TLog} with sensible linebreaks,
but still keeping it as valid Haskell:
\begin{code}
formatTLog :: Int -> TLog -> String
formatTLog i [] = ilog i ++ "[]"
formatTLog i (lentry:lentries)
 = unlines ((format '[' lentry : map (format ',') lentries)++[ind ++ "]"])
 where
   ind = ilog i
   format c (TLogGet p v)
    =  ind ++ c : " TLogGet " ++ show p ++ ' ' : show v
   format c (TLogPut p v s)
    =  ind ++ c : " TLogPut " ++ show p ++ ' ' : show v
       ++ "\n  " ++ ind ++ show s

ilog 0 = ""
ilog n = ' ':ilog (n-1)
\end{code}

Sometimes we want to clean out the prompt and descr parts in a log:
\begin{code}
cleanTLogEntry :: TLogEntry -> TLogEntry
cleanTLogEntry (TLogGet _ value)  = (TLogGet "" value)
cleanTLogEntry (TLogPut _ result sts) = (TLogPut "" result sts)
\end{code}

An interactive command that cleans and formats a log:
\begin{code}
cleanlog :: TLog -> IO ()
cleanlog = putStrLn . formatTLog 1 . map cleanTLogEntry
\end{code}


\newpage
\subsubsection{Batch Testing}

The state for batch testing needs to include the input as well as the log:
\begin{code}
type TInput = [String]
type BTState = (TInput,TLog)
data BatchTest a = BT { outBT :: (BTState  -> (BTState,a)) }

instance Functor BatchTest where  fmap = liftM

instance Applicative BatchTest where
  pure  = return
  (<*>) = ap

instance Monad BatchTest where
  return x = BT (\bts -> (bts,x))
  bt >>= f = BT (\bts -> let (bts',x') = (outBT bt) bts in (outBT (f x')) bts')
\end{code}

Now, the \texttt{LoggedTest} instance:
\begin{code}
instance LoggedTest BatchTest where

  getTestInput prompt parse
   = do (inp:rest) <- getBTInput
        setBTInput rest
        extBTLog $ TLogGet prompt inp
        return $ parse inp

  putTestResult descr showResult result
   = do let presult = showResult result
        extBTLog $ TLogPut descr presult Unk
        return result

  assessOutcome = return ()

  getTestLog = BT (\bts -> (bts,snd bts))

getBTInput :: BatchTest TInput
getBTInput = BT (\bts -> (bts,fst bts))

setBTInput :: TInput -> BatchTest ()
setBTInput inp = BT (\(_,log) -> ((inp,log),()))

extBTLog :: TLogEntry -> BatchTest ()
extBTLog recd = BT (\(inp,log) -> ((inp,log++[recd]),()))

runBatchTest :: BatchTest a -> TInput -> (BTState, a)
runBatchTest bt inp = outBT bt $ (inp,[])
\end{code}

\newpage

We now write batchmode code to run a test against a log,
that should have been the result of a previous run with that test.
The resulting new test log will also be compared with the one given as
argument, and any difference suffixes reported:
\begin{code}
rerunTest :: BatchTest TLog         -- test
          -> TLog                   -- oldlog
          -> TLog                   -- newlog
rerunTest test oldlog  =  snd $ runBatchTest test $ getLogInputs oldlog

getLogInputs :: TLog -> [String]
getLogInputs []                      =  []
getLogInputs (TLogGet _ val : rest)  =  val : getLogInputs rest
getLogInputs (_:rest)                =  getLogInputs rest
\end{code}

We can check for when test logs diverge:
\begin{code}
divergencesWith :: (a -> a -> Bool) ->  [a] -> [a] -> ([a],[a])
divergencesWith _  [] ys = ([],ys)
divergencesWith _  xs [] = (xs,[])
divergencesWith eq xs@(x:xs') ys@(y:ys')
 | x `eq` y   =  divergencesWith eq xs' ys'
 | otherwise  =  (xs,ys)

isDivergent ([],[]) = False
isDivergent _       = True
\end{code}

We wish to ignore prompt and descr strings in logs
and correctness markings,
when checking test reruns against original logs:
\begin{code}
sameTLog :: TLogEntry -> TLogEntry -> Bool
sameTLog (TLogGet _ sval1)   (TLogGet _ sval2)    =  sval1 == sval2
sameTLog (TLogPut _ sres1 _) (TLogPut _ sres2 _)  =  sres1 == sres2
sameTLog _                   _                    =  False

logDivergences = divergencesWith sameTLog
\end{code}

\newpage
\subsubsection{Interactive Testing}

We shall use the \texttt{StateT} transformer here:
\begin{code}
type InterTest = StateT TLog IO

instance LoggedTest InterTest where

  getTestInput prompt parse
   = do liftIO $ putStr prompt
        inp <- liftIO getLine
        modify (++[TLogGet prompt inp])
        return $ parse inp

  putTestResult descr showResult result
   = do let presult = showResult  result
        liftIO $ putStrLn (descr++presult)
        modify (++[TLogPut descr presult Unk])
        return result

  assessOutcome
   = askUserForOutcome mark
   where
     mark sts
      = do tlog <- get
           put $ setmark sts tlog

  getTestLog = get

runInterTest :: InterTest a -> IO (a, TLog)
runInterTest intt = runStateT intt []

logInterTest :: InterTest a -> IO TLog
logInterTest = fmap snd . runInterTest
\end{code}

We have general code to get a user outcome:
\begin{code}
setmark :: PutStatus -> TLog -> TLog
setmark sts [TLogPut d r _] = [TLogPut d r sts]
setmark sts (l:ls) = l:setmark sts ls
setmark sts [] = []

askUserForOutcome :: (MonadIO tst, Functor tst)
                  => (PutStatus -> tst a)
                  -> tst a
askUserForOutcome mark
 = do liftIO $ putStr  "\nExpected Outcome?  (y/n reason) : "
      inp <- fmap trim $ liftIO getLine
      case inp of
        ""  ->  mark Unk
        (r:rest)
          -> case toLower r of
              'y' -> mark OK
              'n' -> mark $ FAIL $ trim rest
              _   -> mark Unk
\end{code}

\newpage
\subsubsection{Assessment Testing}

Here we want a hybrid of \texttt{BatchTest} and \texttt{InterTest}
that gets its inputs and outcomes from a pre-existing log,
but allows the user to assess each outcome, with the log being
updated accordingly.

Another version might run current code to get the outcome.

\begin{code}
type AssessTest = StateT (TInput,TLog) IO

instance LoggedTest AssessTest where

  getTestInput prompt parse
   = do ((inp:rest),tlog) <- get
        put (rest, tlog++[TLogGet prompt inp])
        return $ parse inp

  putTestResult descr showResult result
   = do let presult = showResult  result
        liftIO $ putStrLn (descr++presult)
        (inps,tlog) <- get
        put (inps, tlog++[TLogPut descr presult Unk])
        return result

  assessOutcome
   = askUserForOutcome mark
   where
     mark sts
      = do (inps, tlog) <- get
           put (inps, setmark sts tlog)

  getTestLog = fmap snd get

runAssessTest :: AssessTest a -> TInput -> IO (a, TLog)
runAssessTest asst inps
 = do (a, (_,tlog)) <- runStateT asst (inps,[])
      return (a,tlog)

logAssessTest :: AssessTest a -> TInput -> IO TLog
logAssessTest asst inps = fmap snd $ runAssessTest asst inps

rerunAssessment :: AssessTest a -> TLog -> IO TLog
rerunAssessment test oldlog = logAssessTest test $ getLogInputs oldlog
\end{code}


\newpage
\subsection{Testing HOFs}

\subsubsection{Simple (single) Test}

\begin{code}
simpleTest :: LoggedTest tst
           => String                      -- prompt
           -> (String -> Either String a) -- parse
           -> (a -> b)                    -- compute
           -> String                      -- descr
           -> (b -> String)               -- display
           -> tst TLog
simpleTest prompt parse compute descr display
 = do einp <- getTestInput prompt parse
      case einp of
        Left msg
         ->  do putTestResult descr id msg
                return ()
        Right inp
         -> do let result = compute inp
               putTestResult descr display result
               assessOutcome
               return ()
      getTestLog
\end{code}

\subsubsection{Repeat (single) Test}
\begin{code}
repeatTest :: LoggedTest tst
           => String
           -> (String -> (Bool,Either String a))
           -> (a -> b) -> String
           -> (b -> String)
           -> tst TLog
repeatTest prompt parse compute descr display
 = do (cont,einp) <- getTestInput prompt parse
      if cont
       then do case einp of
                 Left msg
                  -> do putTestResult descr id msg
                        assessOutcome
                 Right inp
                  -> do let result = compute inp
                        putTestResult descr display result
                        assessOutcome
               repeatTest prompt parse compute descr display
       else getTestLog

-- useful parser modifier for use with repeatTest
parseNonNull :: (String -> t) -> String -> (Bool,t)
parseNonNull parse "" = (False,undefined)
parseNonNull parse cs = (True, parse cs)

-- useful modified read for use with repeatTest
readNonNull :: Read t => String -> (Bool,t)
readNonNull = parseNonNull read
\end{code}

\newpage
\subsubsection{Setup and Repeat}
\begin{code}
setupRepeatTest
 :: LoggedTest tst
 => String                -- sprompt
 -> (String -> (Bool,b))  -- sparse
 -> (b -> br)             -- scompute
 -> String                -- sdescr
 -> ((b,br) -> String)    -- sdisplay
 -> (b -> String)                       -- prompt
 -> (String -> (Bool,Either String t))  -- parse
 -> (b -> t -> tr)        -- compute
 -> String                -- descr
 -> ((b,t,tr) -> String)        -- display
 -> tst TLog
setupRepeatTest sprompt sparse scompute sdescr sdisplay
                prompt  parse  compute  descr  display
 = do (ok,sinp) <- getTestInput sprompt sparse
      if ok
       then do let sresult = scompute sinp
               putTestResult sdescr sdisplay (sinp,sresult)
               assessOutcome
               repTest sinp prompt parse compute descr display
               getTestLog
       else do putTestResult "Setup input failed" id ""
               getTestLog
 where
   repTest base prompt parse compute descr display
     = do (cont,einp) <- getTestInput (prompt base) parse
          if cont
           then
             case einp of
               Left msg
                -> do putTestResult descr id msg
                      assessOutcome
                      repTest base prompt parse compute descr display
               Right inp
                -> do let result = compute base inp
                      putTestResult descr display (base,inp,result)
                      assessOutcome
                      repTest base prompt parse compute descr display
           else return ()
\end{code}

\newpage
\subsection{Test Repository}

A test repository is a lookup table associating a test name
with a description, the test code, and a test log.
The test code itself returns a log.

\subsubsection{Test Repo Types}
\begin{code}
data TDescr = TDescr { tDescr :: String
                     , tCode :: LoggedTest tst => tst TLog
                     , tLog :: TLog }

instance Show TDescr where
  show td = unlines $ ("Test -- " ++tDescr td)
                      : "Inputs:" : getLogInputs (tLog td)

type TestRepo = Trie TDescr
\end{code}

\subsubsection{Test Repo Display}

We want to list a test repository, with just the description
showing:
\begin{code}
listRepo = unlines . trieShowWith tList
 where
   tList tdescr = tDescr tdescr ++ showfail 0 (tLog tdescr)
   showfail n [] = if n==0 then "" else "  (FAIL "++show n++")"
   showfail n (TLogPut _ _ (FAIL _):rest) = showfail (n+1) rest
   showfail n (_:rest) = showfail n rest
\end{code}

\subsubsection{Running Repo Tests}

Normal usage is to run a named test in batch mode
comparing its log with the original one, determining any divergences,
and returning the new log plus divergences
\begin{code}
type TestReplay = ( ( TLog     -- point where old log diverges
                    , TLog  )  -- point where new log diverges
                  , TLog )     -- new test log

shReplay :: TestReplay -> IO ()
shReplay (([],[]),_) = putStrLn "Test OK, No regression."
shReplay ((old,new),_)
 = do putStrLn "Regression Test failed !"
      showDiv "Old" old
      showDiv "New" new
 where
   showDiv title div
    = do putStrLn (title++" Test divergent point is:")
         case div of
           []  ->  putStrLn "No log entry occurs"
           (log:_)  -> putStrLn $ displayTLogEntry log
\end{code}

Normal usage is to run a named test in batch mode
\begin{code}
runRepoTest :: TestRepo -> String -> TestReplay
runRepoTest repo name
 = case tlookup repo name of
     Nothing  ->  ((noTest,[]),noTest)
     Just td  ->  runTest td
 where
   noTest = [TLogPut name " Not found in test repository" Unk]

runTest :: TDescr -> TestReplay
runTest td
 = let
     newlog = rerunTest (tCode td) oldlog
     newlog' = matchAssessment oldlog newlog
   in  (logDivergences oldlog newlog', newlog')
 where
   oldlog = tLog td

matchAssessment [] [] = []
matchAssessment (TLogPut _ _ oldstatus:oldrest)
                (TLogPut newp newr _:newrest)
 = TLogPut newp newr oldstatus : matchAssessment oldrest newrest
matchAssessment (_:oldrest) (new:newrest)
                                        = new : matchAssessment oldrest newrest

shlog = putStr . displayTLog . snd
\end{code}

We can also run all tests, and return a report on divergences:
\begin{code}
runRepo :: TestRepo -> [(String,TestReplay)]
runRepo
 = map run . flattenTrie
 where run (nm,td) = (nm,runTest $ dbgsh tDescr "" $ td)

benchMarkRepo :: TestRepo -> [(String,TLog)]
benchMarkRepo = mapsnd snd . runRepo

regressRepo :: TestRepo -> [(String,(TLog,TLog))]
regressRepo  = dbgsh (\xs -> show (length xs)) "\nNo. of Divs = "
                  . filter (isDivergent . snd) . mapsnd fst . runRepo
\end{code}

We want to run a test interactively,
step-by-step,
and ask the user to assess each outcome,
and finally output a clean log with those assessments included.
\begin{code}
scrutiniseRepo :: TestRepo -> String -> IO ()
scrutiniseRepo repo nm = assessRepo repo nm >>= cleanlog

assessRepo :: TestRepo -> String -> IO TLog
assessRepo repo nm
 = case tlookup repo nm of
     Nothing -> do putStrLn ("No test '"++nm++"' in repository")
                   return []
     Just testDescr
      -> do putStrLn ("\nAssessing test "++tDescr testDescr++"\n")
            rerunAssessment (tCode testDescr) (tLog testDescr)
\end{code}

\newpage
\subsection{Misc Test Support}

Various odds-and-sods live here

\subsubsection{A TestFramework Test}

We shall define a simple ``test'', incrementing an integer twice,
and showing how to call them to see the outcome and the final log.
\begin{code}
intIncrTest :: LoggedTest tst => tst TLog
intIncrTest
  = do int <- getTestInput "Enter an integer : " read
       let int' = int+1
       putTestResult "Increment = " show int'
       let int'' = int'+1
       putTestResult "Increment (again) = " show int''
       getTestLog

batchIIT = putStrLn $ displayTLog $ snd $ runBatchTest intIncrTest ["42"]
interIIT = fmap snd $ runInterTest intIncrTest
\end{code}

\subsubsection{\texttt{repparse} re-imagined}

\begin{code}
repparse  :: Show t
          => String               -- prompt
          -> (String -> t)        -- parse
          -> Maybe (t -> String)  -- mprocess
          -> IO ()
repparse prompt parse mprocess
 = fmap (const ()) $ runInterTest $ rep mprocess
 where
   rep Nothing
     = repeatTest
         ("\n==========================\nEnter "++prompt++" (RETURN to quit) >")
         (parseNonNull (Right . parse))
         id
         ""
         show


   rep (Just process)
     = repeatTest
         ("\n==========================\nEnter "++prompt++" (RETURN to quit) >")
         (parseNonNull (Right . parse))
         id
         "processing ..."
         process
\end{code}
