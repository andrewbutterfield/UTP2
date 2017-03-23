\section{\UTP2\ File Handling}

\begin{code}
{-# LANGUAGE CPP #-}

module WxFiles where

import           Compatibility  (utp2try)
import           GIFiles (Args(..))
import qualified GIFiles as GI

import Utilities
import Tables
import Proof
import Theories
import RootTheory
import ImportExport
import Archive
import Files

import System.IO
import Graphics.UI.WX

import WxTypes
import WxState
import WxProof

import Data.Char
import Data.List
import System.Directory
import System.FilePath
import System.IO.Error
import System.FilePath
\end{code}

We handle tracking files for the program here.


\subsection{\UTP2\ Executable Name}

\begin{code}
saoithinExeName = "UTP2"
\end{code}


\subsection{System Directories}

\begin{code}
systemFilePaths :: IO (String,FileState)
systemFilePaths
 = do user <- getUsername
      appuser <- dirget (getAppUserDataDirectory saoithinExeName) "App User Data" ""
      return (user,emptyFS{appUserDir=appuser})

dirget get descr def
 = do attempt <- utp2try $ get
      case attempt of
       Left ioerror -> do putStrLn ( "cannot get "
                                    ++ descr ++" Directory : "
                                    ++ show ioerror )
                          return def
       Right thing  -> return thing

getUsername -- :: IO String
 = do attempt <- utp2try $ getHomeDirectory
      case attempt of
       Left ioerror -> do putStrLn ("cannot get username: "++show ioerror)
                          return "_anonymous_"
       Right uhome  -> return (extractUsername "" (reverse uhome))

extractUsername uname "" = uname
extractUsername uname (c:cs)
 | c == '\\'  =  uname
 | c == '/'   =  uname
 | otherwise  =  extractUsername (c:uname) cs
\end{code}

\subsection{Startup File Handling}

The expected state of affairs during a normal run
of \UTP2\ is that the user application data directory
contains a configuration file, currently just listing
the current working directory.
The working directory contains the theory framework and
current proof files,
as well as all the current theories
and related material.

Of course, the first time the program is run after installation,
none of this will exist, so the user will then be walked through
setting these directories up. The motivation behind this scheme
is to avoid having complicated os-specific setup instructions or
the need to generate binary installers.

At startup, we follow a number of steps
to establish the relevant system/user directories
and configuration files to be used:
\begin{enumerate}
  \item
    First we access application user data
    directory in order to get set-up information:
  \item
    Access framework data in current directory:
  \item
    Load up initial program state from current directory.
\end{enumerate}
The state of affairs, in particular any failures,
are communicated to the user, along with any
related initialisation actions.
\begin{code}

-- |This datatype contains all of the necessary Wx specific functions which the
-- GUI-independent code, in GIFiles.hs requires.
args w fstate = Args {
    aW                   = w
  , aState               = fstate
  , aAppUserDir          = appUserDir
  , aCurrentFileSpace    = snd . currentFileSpace
  , aDisplayError        = errorDialog w
  , aOnAppUserDirError   = \state -> return state { appUserDir = "" }
  , aFSDirOpenDialog     = dirOpenDialog w True "Select Working FileSpace" ""
  , aFSNameDialog        = fsNameDialog
  , aNewFS               = newFS
  , aReadFSPFileNewState = readFSPFileNewState
  , aWriteFSPFileFSPs    = \state -> (currentFileSpace state):(previousFileSpaces state)
  }
  where readFSPFileNewState state fsps = state {
            currentFileSpace   = head fsps
          , previousFileSpaces = tail fsps
          }


-- |Wx specific implementations of GUI independent counterparts.
startupFileHandling w fstate =
  aState <$> GI.startupFileHandling_GI (args w fstate)
userCreateFS w fstate =
  aState <$> GI.userCreateFS_GI (args w fstate)
writeFSPFile path w fstate =
  GI.writeFSPFile_GI path (args w fstate)
\end{code}

\begin{code}

fsNameDialog w
 = do rawname <- textDialog w "FileSpace Name" "Name (no semicolons)" ""
      return (filter (/= GI.namePathSep) rawname)
\end{code}

\end{enumerate}

\begin{code}
explainError (Right _) = return ()
explainError (Left ioerror) = toConsole ("Ioerror - "++show ioerror)
\end{code}





\subsection{Theory File Handling}

\begin{code}
saveTheories work
 = do saveTheories' work
      top <- getTop work
      repaint top

saveTheories' work
 = do (rdag,trie) <- getThgrf work
      let nmdThrys = flattenTrie trie
      cwd <- getCWD work
      nmdThrys' <- mapM (saveModTheory cwd) nmdThrys
      setThgrf (rdag, lbuild nmdThrys') work

saveModTheory cwd nth@(nm,th)
  = if modified th == Transient
     then return nth
     else do toConsole ("saving theory '"++thryName th++"'")
             th' <- archiveTheory cwd th
             return (nm,th')
\end{code}

\subsection{Startup}

Startup files come in two formats,
identified by an optional keyword on the first line.

The legacy format (v0.92 and earlier),
starts with an optional \texttt{STACK} keyword,
then a list of \texttt{Theory} names, one per line, topmost first.
This is followed by a line consisting of a single period,
and then followed by a list of Theory$\_$Conjecture name
pairs, one per line. e.g.
\begin{verbatim}
STACK
Top
AlmostTop
...
AlmostBottom
Bottom
.
AlmostBottom_Hypothesis1
AlmostBottom_Hyp2
Bottom_Conj1
Top_Conj1
\end{verbatim}

The new version (v0.93 and later)
supports the graph format,
and is flagged by starting keyword \texttt{RDAG}.
The key difference is that the first section lists graph dependencies
as a sequences of lines each consisting of a list of one or more
theory names.
Each line is interpreted as saying that the first name
depends on all those following it.
These lines are listed from the bottom of the graph up,
and any line with only one theory name is interpreted
as citing the root as the sole dependent.
The theory/conjecture list then follows a single period line.
In the event of no graph, the single period is still mandatory.
\begin{verbatim}
RDAG
Thry_A
Thry_B Thry_A
Thry_C Thry_A
Thry_D Thry_B Thry_C
.
AlmostBottom_Hypothesis1
AlmostBottom_Hyp2
Bottom_Conj1
Top_Conj1
\end{verbatim}

\begin{code}
startupFileName = acalai++creat

startupStack = "STACK"
startupRDAG = "RDAG"
startupProofSep = "."

type TheoryRDAGSpec = [(String, [String])]

genStartupText rdag pids
 = unlines ( startupRDAG:rdaglines ++ startupProofSep:pids )
 where
   thrynames = filter isSTDName $ reverse $ map fst $ rdToList rdag
   rdaglines = map mkline $ filter nonRoot $ rdToList rdag
   nonRoot (nm,_) = nm /= rootName
   mkline (nnm, ndeps)
    = nnm ++ (concat $ map (' ':) $ filter (/=rootName) ndeps)

-- look for optional STACK at start of file
parseStartupText :: String -> (TheoryRDAGSpec, [String])
parseStartupText txt
 | null lns                  =  ([], [])
 | head lns == startupRDAG   =  parseGraph $ brkss (tail lns)
 | head lns == startupStack  =  linearGraph $ brkss (tail lns)
 | otherwise                 =  linearGraph $ brkss lns
 where
   lns = map trim (lines txt)
   brkss = setsnd ttail . break (==startupProofSep)

linearGraph (thlines, prooflines)
 = (linlistToRDAG thlines, prooflines)
 where
   linlistToRDAG [] = []
   linlistToRDAG [th] = [(th,[])]
   linlistToRDAG (topth:rest@(nxtth:_))
    = (topth,[nxtth]):(linlistToRDAG rest)

parseGraph (rdaglines, prooflines)
 = (map parseRDAGLine rdaglines, prooflines)

parseRDAGLine :: String -> (String,[String])
parseRDAGLine ln
  = (top, split $ skipSp rest)
  where
    (top, rest) = break isSpace ln
    skipSp = snd . span isSpace
    split "" = []
    split rest
     = nxt : (split $ skipSp rst)
     where (nxt, rst) = break isSpace rest
\end{code}

\subsubsection{Loading initial program state}

Load up initial program state.
We load contexts, checking them carefully for consistency%
\footnote{
Haskell experts beware: We use the \texttt{Either} type constructor to propagate errors,
but given we are left-handed, the \texttt{Left} variant is the error-free one!
}%
:
\begin{code}
loadStartupScript cwd user work
 = do let abspath = cwd ++ [pathSeparator] ++ startupFileName
      attempt <- utp2try $ readFile abspath      -- $
      case attempt of
        Left ioerror  ->  reportNoStartupScript cwd work
        Right txt
          -> do let (rdagspec,pnames) = parseStartupText txt
                toConsole ("loading theories: "++show rdagspec)
                loadNamedTheories cwd rdagspec work
                toConsole ("theories done, now proofs : "++show pnames)
                loadNamedProofs cwd pnames work
                toConsole "proofs done."


reportNoStartupScript cwd work
 = do top <- getTop work
      warningDialog top "No Startup Script" (unlines msgs)
 where
   msgs = [ "File '"++startupFileName++"' not found"
          , "at "++cwd
          , "Starting with root workspace only"
          ]
\end{code}

Loading named theories:
\begin{code}
loadNamedTheories cwd rdagspec work
 = do thrygrf <- loadNamedTheories' (rdROOT rootName)
                                    (lbuild [(rootName,rootTheory)])
                                    rdagspec
      thgrfSetf (const thrygrf) work
 where

  loadNamedTheories' rdag  trie [] = return (rdag,trie)

  loadNamedTheories' rdag  trie ((thnm,deps):rest)
   | thnm `elem` theoriesSoFar  =  loadThFail (mulLoad thnm)
   | not $ null unknown         =  loadThFail $ missing thnm unknown
   | otherwise
     = do result <- loadNmdTheory cwd thnm
          case result of
           Right msg  ->  loadThFail msg

           Left thry
            -> let trie' = tupdate thnm thry trie
               in updateRDAG thry trie'

     where

       theoriesSoFar = trieDom trie
       unknown = deps \\ theoriesSoFar

       mulLoad thnm = "Cannot load '"++thnm++" more than once"
       missing thnm deps = (thnm++" deps:"++show deps++" are missing")
       loadThFail msg
        = do top <- getTop work
             warningDialog top "Bad Theory" msg
             return (rdag,trie)

       updateRDAG thry trie
        = do let res = rdUpdate thnm deps rdag
             case res of
               Left msg  ->  loadThFail $ show msg
               Right rdag'
                -> do let penv = hardGraphToStack thnm (rdag',trie)
                      let mctxt = mkMatchContext (thry:penv)
                      let thry' = fixupTheory mctxt thry
                      let trie' = tupdate thnm thry' trie
                      loadNamedTheories' rdag' trie' rest

-- end loadNamedTheories s

reportTheoryLoadFailure cwd thnm msg thnms work
 = do top <- getTop work
      warningDialog top "Bad Theory" (unlines msgs)
 where
   msgs = [ "Theory File '"++thnm++"' failed to load"
          , "Reason Given:"
          , "  "++msg
          ] ++ missing thnms
   missing [] = []
   missing nms = "The following theories were therefore not loaded"
                 :(map ("  "++) nms)

returnStack stk msgs = (stk,(concat(intersperse "|" msgs)))
rr s m = return (returnStack s m)

loadNmdTheory :: FilePath -> String -> IO (Either Theory String)
loadNmdTheory cwd "" = return (Right "no theory name given")
loadNmdTheory cwd name@(c:name')
 | c == '_'  =  do result <- loadCtxtFile cwd name'
                   return (usePCdefault name' result)
 | otherwise  =  loadCtxtFile cwd name

usePCdefault :: String -> Either Theory String -> Either Theory String
usePCdefault name (Right _) = Left (nmdNullPrfCtxt name)
usePCdefault _    pcs       = pcs

loadCtxtFile :: FilePath -> String -> IO (Either Theory String)
loadCtxtFile cwd name
 = do let abspath = cwd ++ [pathSeparator] ++ name ++ teoric
      attempt <- utp2try $ readFile abspath
      toConsole ("attempted read of "++abspath)
      case attempt of
        Left ioerror  ->  return (Right (fmsg "not found"))
        Right txt
          -> do let (rep,pc) = loadPX $! txt
                case rep of
                  ImportOK         ->  return (Left pc)
                  (ImportFail msg) ->  return (Right (fmsg ("import failed: "++msg)))
 where
   fmsg txt = "'"++name++"' "++txt
\end{code}
Loading named proofs:
\begin{code}
loadNamedProofs cwd [] work = return ()
loadNamedProofs cwd (pnm:pnms) work
 = do result <- loadNmdProof cwd pnm
      case result of
         Right msg
          -> reportProofLoadFailure cwd pnm msg work
         Left (prf,spcths)
          -> do prf' <- rebuildProofContext prf spcths work
                let pid = proofId prf
                pspace' <- makeProofSpace prf' pid work
                proofSpaceUpdate pspace' pid work
      loadNamedProofs cwd pnms work

loadNmdProof cwd pnm
 = do let abspath = cwd ++ [pathSeparator] ++ pnm ++ cruthu
      attempt <- utp2try $ readFile abspath
      toConsole ("tried reading "++abspath)
      case attempt of
        Left ioerror  ->  return (Right (fmsg "not found"))
        Right txt
          -> do let (rep,result) = loadPLT $! txt
                case rep of
                  ImportOK         ->  return (Left result)
                  (ImportFail msg) ->  return (Right (fmsg ("import failed: "++msg)))
 where
   fmsg txt = "'"++pnm++"' "++txt

reportProofLoadFailure cwd pnm msg work
 = do top <- getTop work
      warningDialog top "Bad Proof" (unlines msgs)
 where
   msgs = [ "Proof File '"++pnm++"' failed to load"
          , "Reason Given:"
          , "  "++msg
          ]
\end{code}
\subsubsection{Saving Program State}
\begin{code}
saveStartupScript work
 = do -- toConsole "saving startup script"
      ss <- varGet work
      let ws = workspace ss
      let (thrygraph,thrys) = theoryGraph $ theories ws
      let prfns = map (proofFn . currProof) $ trieRng $ currProofs $ ws
      let script = genStartupText thrygraph prfns
      let cwd = snd (currFS ss)
      let abspath = cwd ++ [pathSeparator] ++ startupFileName
      writeFile abspath script
      setStkMod work False
      top <- getTop work
      repaint top
\end{code}



\subsection{Change Working Directory}

\begin{code}

changeWorking w work
 = do fstate <- getFileState work
      let (_,cwd) = currentFileSpace fstate
      mcwd' <- dirOpenDialog w True "Select Working FileSpace" cwd
      case mcwd' of
        Nothing   ->  return ()
        Just cwd'
         -> do name' <- fsNameDialog w
               if null name'
                then return ()
                else setWorking w name' cwd' work

setWorking w name cwd work
 = do archiveProgState work
      saveStartupScript work

      fstate <- getFileState work
      let fstate' = newFS fstate (name,cwd)
      let cfgpath = appUserDir fstate
                             ++ [pathSeparator]
                             ++ acalai ++ cumraiocht
      writeFSPFile cfgpath w fstate'
      setFileState work fstate'

      uname <- getUser work
      varSetf ((workspaceSetf . const . rootWS) uname) work
      loadStartupScript cwd uname work

      sts <- getSts work
      note sts ("Filespace '"++name++"' loaded")

revertWorking w work
 = do fstate <- getFileState work
      let prevfs = previousFileSpaces fstate
      revertMenu <- buildRevertMenu w work prevfs
      menuPopup revertMenu (pt 10 10) w


buildRevertMenu w work prevfs
 = do rMenu <- menuPane [text:="Previous Filespaces"]
      addRevertSubItems w work rMenu prevfs
      return rMenu

addRevertSubItems w work rMenu [] = return ()
addRevertSubItems w work rMenu ((name,cwd):rest)
 = do sub <- menuItem rMenu
              [ text := name
              , on command := setWorking w name cwd work ]
      addRevertSubItems w work rMenu rest
\end{code}





\subsubsection{Shutdown}

We export any modified contexts, and the current proofs:
\begin{code}
archiveProgState work
  = do saveTheories' work
       prfs <- fmap (map currProof . trieRng) (getCurrprfs work)
       cwd <- getCWD work
       mapM (archiveProof cwd) prfs
\end{code}




%\subsection{User Identification (deprecated)}
%
%We want to be able to identify the program's user,
%via the underlying operating system.
%\begin{code}
%systemLookupUser :: IO String
% = do attempt <- utp2try $ getHomeDirectory       -- $
%      case attempt of
%       Left ioerror
%        -> do putStrLn ("cannot get home directory : "++show ioerror)
%              return "_unknown_"
%       Right uhome
%        -> return (extractUsername "" (reverse uhome))
%\end{code}
