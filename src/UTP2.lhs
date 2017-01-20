\section{\UTP2\ Mainline}

\begin{code}
----------------------- UTP2 Coding Standard Width ------------------------->|
{-# LANGUAGE CPP #-}
module Main where
import Tables
import Datatypes
import DataText
import Types
import MatchTypes
import Invariants
import Matching
import FreeBound
import Focus
import Heuristics
import Builtin
import Substitution
import Laws
import Normalise
import Proof
import Program
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

import DSL
import Logic
import GSLogic
import GS3001
import UTP
import R
import RAlg

import About

import System.IO
import Graphics.UI.WX
import Graphics.UI.WXCore

import Data.Char
import Data.List
import Control.Monad
import Data.Maybe(fromJust)

-- import UTP2Test
-- import Test.QuickCheck hiding (ok)

import WxTypes
import WxState
import WxFiles
import WxStyle
import WxRender
import WxProof
import WxTheory
import WxSynchro
import WxProg

import Debug.Trace
import System.Info
import System.FilePath
import Data.Version
import Data.Time

-- IMPORTANT: INCOMPATIBLE LIBRARY CHANGES
#if __GLASGOW_HASKELL__ < 700
import Data.HashTable        -- needed with 6.10
#else
import Data.Hashable as H    -- needed with 7.x
hashString = H.hash          -- for 7.x
#endif
\end{code}

\subsection{Main Program}

Here we give the program mainline along with the ``top-window'' GUI.

\begin{code}
initWidth, initHeight :: Int
initWidth = 500
initHeight = 150
initLayout = space initWidth initHeight

main = start utp2_gui_run

m = main --- much easier in GHCi !
\end{code}

\newpage
\subsection{Mainline GUI}

\begin{code}
utp2_gui_run
 = do (uname,fstate) <- systemFilePaths
      f <- frame  [text := (fullname++" - "++uname)]
      initfs <- startupFileHandling f fstate
      toConsole uname
      toConsole (show initfs)
      let cwd = snd $ currentFileSpace $ initfs
      p <- panel f []
      top <- scrolledWindow p []

      let welcome = "Welcome, "++uname++", to "++fullname
      toConsole welcome
      status <- statusField [text:=welcome]

      topdd <- varCreate nullDD
      ds <- loadStyleFile (appUserDir initfs)
      toConsole "style file loaded"

      let initGUI = GUIState top status topdd tnil tnil 0 f ds

      work <- varCreate ( WxState
                            (rootWS uname)
                            defaultLD
                            initGUI
                            initfs
                            False
                        )

      putStrLn "preparing to load startup script"
      loadStartupScript cwd uname work
      putStrLn "startup script loaded (if any)"

      bcolour <- getBgColour work

      set top [ virtualSize := sz 1000 2000
              , scrollRate := sz 10 10
              , size := sz 400 500
              , on paint := paintTop work
              , on doubleClick := handleTopClick work hDoubleClk
              , on clickRight := handleTopClick work hRightClk
              , bgcolor := bcolour
              ]

      newF <- getFrame work  -- outer frame
      set newF [bgcolor := bcolour]

      fileMenu <- menuPane [text:="&File"]
      buildFileMenu fileMenu f work

      -- optMenu <- menuPane [text:="&Options"]
      -- buildOptionMenu optMenu f work

      helpMenu <- menuHelp []
      about <- menuAbout helpMenu [help:=("About "++progname)]

      --buildMenu <- mkBuildMenu work

      --maintMenu <- mkMaintMenu work

      --appMenu <- mkAppMenu top f work

      set f [  statusBar := [status]
             , layout := container p
                         $ margin 10
                         $ boxed "Theories"
                         $ fill (widget top)     -- $
             , outerSize := sz 500 700
             , menuBar := [fileMenu,helpMenu] -- ,appMenu,buildMenu,maintMenu]
             , on (menu about) := infoDialog f "About.." aboutText
             , bgcolor := bcolour
             ]

\end{code}

\newpage
\subsection{Rendering the Top Window}

In the top window we display
details of the current workspace,
a global view of the
theories loaded and the proofs currently active in the system.
\begin{code}
paintTop work dc viewArea
 = do ss <- varGet work

      -- Style stuff
      tStyle <- getTextStyle work
      vtStyle <- getVtStyle work
      vStyle <- getVertStyle work
      let currFont = case tStyle of
                          Nothing -> fontDefault
                          (Just style) -> textFont style -- current text font
      let currCol  = case tStyle of
                          Nothing -> defaultColour
                          (Just style) -> textCol style  -- current text colour
      let fontItalStyle -- TextStyle with italic font
            = TextStyle currFont{_fontShape = ShapeItalic} currCol

      -- Workspace display
      let currfs = currFS ss
      let wsTxt = "Workspace '"++fst currfs++"' @ "++snd currfs
      let wDisp = justDraw (DDrawText Nothing wsTxt)


      -- Theory Display
      let thgrf = theorygraph ss
      let stkmod = thrysmodified ss
      let topOrigin = (10,10)
      let fsname = fst (currFS ss)

      let boxer dd = dispBox Nothing (dispSpace 5 5 5 5 dd noClkHandlers)
                             noClkHandlers

      let gTtl = justDraw (DDrawText (Just fontItalStyle)
                                     (smod stkmod ("Global Theories")))
      let thTbl = boxer $ theoryGraphDD currFont currCol thgrf

      -- Active Proof Display
      let pTtl = justDraw (DDrawText (Just fontItalStyle) "Active Proofs")
      let pspaces = trieFlatten "" $ currproofs $ ss
      let prfDS = map showPrf pspaces
      let pTbl =  boxer $ justDraw $
                       ddrawVTable vtStyle 1 DrawUniform DrawTight True prfDS

      let spacer = dispSpacer 10 10

      -- putting it all together
      let ddspec
            = justDraw $ DDrawVert vStyle DrawLeft
                       [ wDisp
                       , spacer
                       , gTtl, thTbl
                       , spacer
                       , pTtl, pTbl
                       ] 0
      let tidv = topdd ss
      varSet tidv (DisplayData topOrigin ddspec)
      paintDisplayData tidv dc viewArea
      overlayDisplayData tidv (theoryGraphOverlay thgrf) dc viewArea

      -- toConsole "paintTop: paintSpec done"
 where
   thryinfo currFont currCol thry
    = ( [ justDraw (DDrawText (Just (TextStyle modfont currCol)) (pcqname thry))
        , justDraw (DDrawText (Just (TextStyle currFont{_fontSize = currSize - 2} currCol))
                                    (concat (intersperse "," (syntaxDeps thry))))
        , justDraw (DDrawText (Just (TextStyle currFont{_fontSize = currSize - 2} currCol))
                                    (concat (intersperse "," (proofDeps thry))))
        ]
      , topTheoryClick thry
      )
    where modfont = case modified thry of
                      Transient  ->  currFont
                      Log        ->  currFont{_fontWeight=WeightBold}
                      Upgrade    ->  currFont{_fontWeight=WeightBold,_fontUnderline=True}
          currSize = _fontSize currFont   -- size of current font
   smod False ttl = ttl
   smod True  ttl = ttl ++ " (modified)"
   hdr font col = ( map (hdrstr font col)
                         [ "Theory", "Syntax Deps.", "Proof Deps."]
                  , noClkHandlers )
   hdrstr font col str = justDraw $   -- $
                           DDrawText (Just (TextStyle font{_fontFamily = FontSwiss} col))
                                     str
   showPrf (pname,pspace) = ( [ justDraw (DDrawText Nothing pname) ]
                            , (topProofClick pspace) )
\end{code}

\newpage
\subsection{Top Window Event Handlers}

\begin{code}
handleTopClick work ksel pnt
 = do -- putStr ("Handling top ")
      -- showClkSelector work ksel
      -- putStrLn (" @ "++show pnt)
      topddv <- getTopDD work
      topdd <- varGet topddv
      let hndlrs = pointDDLookup ksel topdd pnt
      case hndlrs of
       []     ->  noTheoryManipulationMenu pnt work
       (h:_)  ->  h pnt work

topTheoryClick thry
 = ClkHandlers Nothing
               (Just viewThisTheory)
               (Just manipulateThisTheory)
 where
  viewThisTheory pnt = viewTheory thry
  manipulateThisTheory = theoryManipulationMenu thry

topProofClick pspace
 = ClkHandlers Nothing
               (Just viewThisProof)
               Nothing
 where
   viewThisProof pnt work = repaintProofGUI pspace
\end{code}


\subsubsection{Top-Theory Right-Click}

When no theory has been selected:
\begin{code}
noTheoryManipulationMenu pnt work
 = do tmMenu <- menuPane [text:=("Top Window")]
      addCREATEItem  work tmMenu
      addSAVEALLItem work tmMenu
      top <- getTop work
      menuPopup tmMenu pnt top
      repaint top
\end{code}

When a theory has been selected:
\begin{code}
theoryManipulationMenu thry pnt work
 = do tmMenu <- menuPane [text:=("Theory '"++thryName thry++"'")]
      -- first, items if a theory was selected
      addSAVEItem   work thry tmMenu
      addEXPORTItem work thry tmMenu
      addLINKItem  work thry pnt tmMenu
      addDROPItem   work thry tmMenu
      addPROGItem   work thry tmMenu
      -- then, general manipulations
      addCREATEItem  work tmMenu
      addSAVEALLItem work tmMenu
      top <- getTop work
      menuPopup tmMenu pnt top
      repaint top
\end{code}

\newpage
Saving a modified theory
\begin{code}
addSAVEItem work thry tmMenu
 = do svitem <- menuItem tmMenu [text:=svtxt thry]
      set svitem [on command := saveUpdTheory thry work]
      thitem <-  menuItem tmMenu [text:=thtxt thry]
      set thitem [on command := saveTheoremSummary thry work]
 where
  svtxt thry = "Save " ++ thryName thry ++ " (" ++ show (modified thry) ++ ")"
  thtxt thry = "Theorem Summary for " ++ thryName thry

saveUpdTheory thry work
 = do (_,cwd) <- getCurrFS work
      thry' <- archiveTheory cwd thry
      namedTheorySet thry' work

saveTheoremSummary thry work
 = do (_,cwd) <- getCurrFS work
      let fname = cwd ++ [pathSeparator] ++ "Summary-"++thryName thry++".txt"
      let summary = theoremsSummary thry
      let hash = hashString summary
      utct <- getCurrentTime
      tz <- getTimeZone utct
      let loctime = utcToLocalTime tz utct
      let trailer = show loctime ++ "\n[" ++ show hash ++ "]"
      writeFile fname (summary++"\n\n"++trailer)
\end{code}

Exporting a theory
\begin{code}
addEXPORTItem work thry tmMenu
 = do mitem <- menuItem tmMenu [text:=ltxt thry]
      set mitem [on command := exportLaTeXTheory thry work]
      mitem <- menuItem tmMenu [text:=ttxt thry]
      set mitem [on command := exportTexTTheory thry work]
      mitem <- menuItem tmMenu [text:=btxt thry]
      set mitem [on command := exportTheoryBundle thry work]
 where
  ltxt thry = "Export LaTeX (" ++ utp ++ ")"
  ttxt thry = "Export Text (" ++ uttxt ++ ")"
  btxt thry = "Export Bundle (" ++ uttxt ++ "," ++ teoric ++ ")"

exportLaTeXTheory thry work
 = do ss <- varGet work
      let name = thryName thry
      let thstk = hardGraphToStack name $ theorygraph ss
      let prec = map precs thstk
      let llayout = latexlayout ss
      let txt = pprint_proofcontext prec llayout thry
      (_,cwd) <- getCurrFS work
      let fname = cwd ++ [pathSeparator]
                  ++ name++"-"++show (thrySeqNo thry)++utp
      writeFile fname txt
      note (topstatus ss) ("Theory '"++name++"' exported to "++fname)
\end{code}

\newpage
When exporting theories as text, or bundled,
we always increment the sequence number,
as we have no guarantee that the file won't be modified
before it is next read in.
\begin{code}
exportTexTTheory thry work
 = do let name = thryName thry
      let thry' = thry{thrySeqNo = thrySeqNo thry + 1}
      thg <- getThgrf work
      let thstk = hardGraphToStack name thg
      let txt = theory2txt thstk thry'
      cwd <- getCWD work
      let fname = cwd ++ [pathSeparator]
                  ++ name++"-"++show (thrySeqNo thry')++uttxt
      writeFile fname txt
      sts <- getSts work
      note sts ("Theory '"++name++"' exported to "++fname)

exportTheoryBundle thry work
 = do let name = thryName thry
      let thry' = thry{thrySeqNo = thrySeqNo thry + 1}
      (_,cwd) <- getCurrFS work
      let froot = cwd ++ [pathSeparator] ++ name++"-"++show (thrySeqNo thry')
      thg <- getThgrf work
      let thstk = hardGraphToStack name thg
      writeFile (froot++uttxt) (theory2txt thstk thry')
      writeFile (froot++teoric) (dumpPX thry')
      sts <- getSts work
      note sts ("Theory '"++name++"' exported to bundle "++froot)
\end{code}

\newpage
Linking theories:
\begin{code}
addLINKItem work thry pnt tmMenu
 = do mitem <- menuItem tmMenu [text:=dtxt thry]
      set mitem [on command := linkTheoryMenu thry pnt work]
 where
  dtxt thry = "Link this Theory to others"

linkTheoryMenu thry pnt work
 = do let thnm = thryName thry
      (rdag,trie) <- getThgrf work
      let nonRels = rdNonRelatives thnm rdag
      toConsole (thnm++" not related to "++show nonRels)
      linkMenu rdag trie thnm nonRels pnt work

linkMenu rdag trie thnm nonRels pnt work
 = do linkMenu <- menuPane [text:=("Link '"++thnm++"' ...")]
      addLinkItems linkMenu nonRels
      top <- getTop work
      menuPopup linkMenu pnt top
      repaint top
 where
   addLinkItems _ [] = return ()
   addLinkItems linkMenu (nr:rest)
    = do addLinkItem linkMenu ("... above '"++nr++"'") thnm nr
         addLinkItem linkMenu ("... below '"++nr++"'") nr thnm
         addLinkItems linkMenu rest
   addLinkItem linkMenu txt from to
    = do lnkitm <- menuItem linkMenu [text:=txt]
         set lnkitm [on command := linkTheory from to work]

linkTheory from to work
 = do (rdag,trie) <- getThgrf work
      let res = rdUpdate from [to] rdag
      case res of
        Right rdag'
         -> do thgrfSetf (const (rdag',trie)) work
               top <- getTop work
               repaint top
        Left err
         -> do sts <- getSts work
               alert sts ("Cannot link: "++show err)
\end{code}

\newpage
Dropping a theory can only be done if no hard links to it exist.
For now we limit it to top theories only.
\begin{code}
addDROPItem work thry tmMenu
 = do mitem <- menuItem tmMenu [text:=dtxt thry]
      set mitem [on command := dropTheory thry work]
 where
  dtxt thry = "Drop Theory"

dropTheory thry work
 = do let thnm = thryName thry
      (rdag,trie) <- getThgrf work
      sts <- getSts work
      case rdag of
        DTop tops
          -> if thnm `elem` map rdName tops
              then do topf <- getTop work
                      go <- confirmDialog topf
                              "Drop Theory"
                              ("Do you really want to drop theory '"
                               ++ thnm ++ "'"
                              )
                              False
                      if go
                       then setThgrf (rdRemoveTop thnm rdag, trie) work
                       else return ()
              else
                alert sts ("Theory '"++thnm++"' not top, cannot be removed")
        _ -> scream work "Theory Graph not a DTop !!!!"
\end{code}

Creating a new theory
\begin{code}
addCREATEItem  work tmMenu
 = do mitem <- menuItem tmMenu [text:="Create New Theory"]
      set mitem [on command := createTheory work]
\end{code}

Saving all modified theories.
\begin{code}
addSAVEALLItem work tmMenu
 = do mitem <- menuItem tmMenu [text:="Save all modified theories"]
      set mitem [on command := saveTheories work]
\end{code}

\newpage
\subsubsection{The File Menu}

The file menu provides commands to
\begin{itemize}
  \item Load a theory
  \item Save all modified theories
  \item Save theory stack specification as a startup-file
  \item Quit the program (saving state appropriately).
\end{itemize}
\begin{code}
buildFileMenu fileMenu f work
 = do

      newThry <- menuItem fileMenu
                           [ text:="New &Theory\tCtrl+N"
                           , help:="create a new theory"]
      set newThry [on command := createTheory work]

      loadThry <- menuItem fileMenu
                           [ text:="Load &Theory\tCtrl+T"
                           , help:=("load a theory"++thryfileext)]
      set loadThry [on command := loadTheory work]

      saveThrys <- menuItem fileMenu
                            [ text:="Save Theories"
                            , help:="Save any modified theories"]
      set saveThrys [on command := saveTheories work]

      saveStrtUp <- menuItem fileMenu
                             [ text:="Save Stack Details"
                             , help:="Save startup stack configuration"]
      set saveStrtUp [on command := saveStartupScript work]

      saveStyles <- menuItem fileMenu
                             [ text:="Save Appearance"
                             , help:="Save appearance configuration"]
      set saveStyles [on command := saveStyleState work]

      loadPrf <- menuItem fileMenu
                           [ text:="Load Proof"
                           , help:=("load a proof"++prffileext)]
      set loadPrf [on command := importProof work]

      chgWD <- menuItem fileMenu
                           [ text:="Change Working Filespace"
                           ]
      set chgWD [on command := changeWorking f work]

      prevWD <- menuItem fileMenu
                           [ text:="Previous Filespaces..."
                           ]
      set prevWD [on command := revertWorking f work]

      quit <- menuQuit fileMenu [help:="Quit"]
      set quit [on command := closeDown f work]

 where
  thryfileext = "("++teoric++","++utp++")"
  prffileext = "("++cruthu++")"
\end{code}

\newpage
Creating a theory
\begin{code}
createTheory work
 = do topf <- getTop work
      fpar <- get topf frameParent
      newthname <- textDialog fpar "Name" "Create Theory" ""
      if null newthname
       then return ()
       else
        do (rdag,trie) <- getThgrf work
           sts <- getSts work
           case tlookup trie newthname of
            Just _
             -> alert sts ("createTheory '"++newthname++"' already exists")
            Nothing
             -> do let thry = nmdNullPrfCtxt newthname
                   let trie' = tupdate newthname thry trie
                   let rdagres = rdAdd newthname rdag
                   case rdagres of
                    Left err
                     -> alert sts ("Couldn't create theory: "++show err)
                    Right rdag'
                     -> do setThgrf (rdag',trie') work
                           setStkMod work True
                           repaint topf
                           alert sts ("Theory '"++newthname++"' Created.")
\end{code}

Loading a theory requires selecting a theory file or a \LaTeX\ file containing a theory (\texttt{.utp} extension). It is
then loaded, its \texttt{proofDeps} are checked,
and then it is installed at a location compatible with those \texttt{proofDeps} that
is closest to the current main stack top.
\begin{code}
loadTheory work
 = do ss <- varGet work
      let sts = topstatus ss
      let (_,cwd) = currFS ss
      resp <- fileOpenDialog (guitop ss)
               True True "Select Theory"
               [theoryFiles,anyFiles] cwd ""
      case resp of
        Nothing  ->  alert sts "Theory load : no file selected"
        (Just name)
          -> switch name
               [ isTeoric ---> loadTeoric sts work
               , isUttxt  ---> loadUTText sts work
               ] (notTheoryFName sts)

notTheoryFName sts name
 = alert sts ("'"++name++"' is not a theory filename, nothing loaded")
\end{code}


Loading a theory file.
\begin{code}
loadTeoric sts work name
 = do txt <- readFile name
      toConsole "loadTeoric: got txt"
      let (rep,thry) = loadPX txt
      toConsole "loadTeoric: done loadPX"
      case rep of
       (ImportFail msg)  ->  alert sts ("load theory failed : "++msg)
       _  ->  addTheory work thry
\end{code}

\newpage
Loading a unifying-theory plain-text file.
\begin{code}
loadUTText sts work name
 = do txt <- readFile name
      thg <- getThgrf work
      let mstk = graphAsStack thg
-- let result = buildDocParser mstk (stripDir name) txt
      let result = theoryTextParser mstk (stripDir name) txt
      case result of
       (Left msg)    ->  do toConsole ("uttxt fail\n"++msg)
                            alert sts ("Bad uttxt : "++msg)
       (Right thry)  ->  addTheory work thry{modified=Log}
\end{code}


Adding a theory to graph:
\begin{code}
addTheory work thry
 = do let thnm = thryName thry
      (rdag,trie) <- getThgrf work
      sts <- getSts work
      case rdAdd thnm rdag of
       Left err
        -> alert sts ("Cannot add theory: "++show err)
       Right rdag'
        -> do let penv = hardGraphToStack thnm (rdag',trie)
              let mctxt = mkMatchContext (thry:penv)
              let thry' = fixupTheory mctxt thry
              let trie' = tupdate thnm thry' trie
              setThgrf (rdag',trie') work
              setStkMod work True
              top <- getTop work
              repaint top
\end{code}




\subsection{Closing Down}

\begin{code}

closeDown f work
 = do varSetf (shuttingdownSetf (const True)) work
      changedStyles <- getStyleStatus work
      top <- getTop work
      if (changedStyles == True)
        then do yes <- confirmDialog top "Confirm"
                            "The appearance has been changed. Do you wish to save it?" True
                if yes then saveStyleState work else return ()
        else do return ()
      archiveProgState work
      saveStartupScript work
      openf <- getThryFrames work
      toConsole ("closing theories : "++(concat(intersperse "," (trieDom openf))))
      mapM (close . twFrame) (trieRng openf)
      prffs <- getPrfFrms work
      -- toConsole ("closing proof frame ... ")
      mapM windowDestroy prffs
      -- toConsole "closing top frame ..."
      close f
      toConsole "... closed !!! "

\end{code}

\newpage
\subsection{Maintenance/Developement-related stuff}

\subsubsection{``Touching'' a Theory}

Marking a theory as having had a \texttt{Log} or \texttt{Upgrade} change.
\begin{code}
addTOUCHItem work thry tmMenu
 = do  let name = thryName thry
       litm <- menuItem tmMenu [text:="Touch "++name++" as LOG"]
       set litm [on command := touchTheory Log thry work]
       uitm <- menuItem tmMenu [text:="Touch "++name++" as UPGRADE"]
       set uitm [on command := touchTheory Upgrade thry work]

touchTheory mod thry work
 = do let thry' = thry{modified=mod}
      namedTheorySet thry' work
\end{code}

\newpage
\subsubsection{The Build Menu}

\begin{code}
mkBuildMenu work
 = do genPCMenu <- menuPane [text:="&Build"]

      genAllThry <- menuItem genPCMenu [text:="All", help:="generate all default theories"]
      set genAllThry [ on command
                       :=
                       genProofCtxts
                         [ rootTheory
                         , logicLawsTheory
                         , logicProofContext
                         , gsPropTheory
                         , gsNonPropTheory
                         , gsLogicProofContext
                         , gsLogicAllProofContext
                         , theoryEquality
                         , theoryArithmetic
                         , theorySets
                         , theoryLists
                         , theory3BA31Lists
                         , utpProofContext
                         , rAlgAxProofContext
                         , rAlgCjProofContext
                         , rProofContext
                         ] work
                     ]

      genRoot <- menuItem genPCMenu [text:=rootName, help:="generate default root theory"]
      set genRoot [on command := genProofCtxt rootTheory work]

      genLogic <- menuItem genPCMenu [text:="LogicLaws", help:="generate default Logic law conjectures"]
      set genLogic [on command := genProofCtxt logicLawsTheory work]

      genLogic <- menuItem genPCMenu [text:="Logic", help:="generate Morgan&Sanders axioms"]
      set genLogic [on command := genProofCtxt logicProofContext work]

      genPropLogic <- menuItem genPCMenu [text:="PropLogic", help:="generate default PropLogic theory"]
      set genPropLogic [on command := genProofCtxt gsPropTheory work]

      genNonPropLogic <- menuItem genPCMenu [text:="NonPropLogic", help:="generate default NonPropLogic theory"]
      set genNonPropLogic [on command := genProofCtxt gsNonPropTheory work]

      genGSLogic <- menuItem genPCMenu [text:="GSLogic", help:="generate default GSLogic theory"]
      set genGSLogic [on command := genProofCtxt gsLogicProofContext work]

      genGSLogic <- menuItem genPCMenu [text:="GSLogicAll", help:="generate full GSLogic theory"]
      set genGSLogic [on command := genProofCtxt gsLogicAllProofContext work]

      genGS3001 <- menuItem genPCMenu [text:="GS3001", help:="generate default GS3001 theory"]
      set genGS3001 [on command := genProofCtxt gs3001ProofContext work]

      genEquality <- menuItem genPCMenu [text:="Equality", help:="generate default Equality theory"]
      set genEquality [on command := genProofCtxt theoryEquality work]

      genArithmetic <- menuItem genPCMenu [text:="Arithmetic", help:="generate default Arithmetic theory"]
      set genArithmetic [on command := genProofCtxt theoryArithmetic work]

      genSets <- menuItem genPCMenu [text:="Sets", help:="generate default Sets theory"]
      set genSets [on command := genProofCtxt theorySets work]

      genLists <- menuItem genPCMenu [text:="Lists", help:="generate default Lists theory"]
      set genLists [on command := genProofCtxt theoryLists work]

      genLists <- menuItem genPCMenu [text:="3BA31Lists", help:="generate default 3BA31Lists theory"]
      set genLists [on command := genProofCtxt theory3BA31Lists work]

      genUTP <- menuItem genPCMenu [text:="UTP", help:="generate default UTP theory"]
      set genUTP [on command := genProofCtxt utpProofContext work]

      genRAA <- menuItem genPCMenu [text:="RAlgAxioms", help:="generate default Reactive-Algebra axioms"]
      set genRAA [on command := genProofCtxt rAlgAxProofContext work]

      genRAC <- menuItem genPCMenu [text:="RAlgConjs", help:="generate default Reactive-Algebra conjectures"]
      set genRAC [on command := genProofCtxt rAlgCjProofContext work]

      genR <- menuItem genPCMenu [text:="R", help:="generate default Reactive theory"]
      set genR [on command := genProofCtxt rProofContext work]

      genXYZ <- menuItem genPCMenu [text:="X", help:="generate default XYZDesign theory"]
      set genXYZ [on command := genProofCtxt xyzDesignTheory work]

      return genPCMenu
\end{code}

\newpage
\subsubsection{The Maintenance Menu}

\begin{code}
mkMaintMenu work
 = do maintMenu <- menuPane [text:="&Maintenance"]

      syncMenu <- menuPane [text:="&Synchronise"]

      itmGen <- menuSub maintMenu syncMenu
                  [ text:="Theory Synchronisers"
                  , help:="Propagate Theory changes globally"]

      buildSyncMenu work syncMenu availableSynchronisers

      vwFonts <- menuItem maintMenu [ text:="View Fonts"]
      set vwFonts [on command := viewFonts work]

      txtTestT <- menuItem maintMenu [ text := "Test Text Parser (&Type)\tCtrl-Y"]
      set txtTestT [on command := textTest work "Type" typeTextParser debugTshow]

      txtTestE <- menuItem maintMenu [ text := "Test Text Parser (&Expr)\tCtrl-X"]
      set txtTestE [on command := textTest work "Expression" exprTextParser debugEshow]

      txtTestP <- menuItem maintMenu [ text := "Test Text Parser (&Pred)\tCtrl-P"]
      set txtTestP [on command := textTest work "Predicate" predTextParser debugPshow]

      dialogTst <- menuItem maintMenu [ text := "&Dialog Test\tCtrl-D"]
      set dialogTst [on command := dialogTest work]

      glblMap <- menuItem maintMenu [ text := "Global Map (DANGER)"
                                    , help := "applies a transform to *everything*"]
      set glblMap [on command := globalMap work]

      return maintMenu
\end{code}


Building the synchronisation menu:
\begin{code}
buildSyncMenu work menu [] = return ()
buildSyncMenu work menu ((nm,descr,thsyncf,pfsyncf):rest)
 = do mitem <- menuItem menu [ text:=nm, help:=descr ]
      let syncfs = (thsyncf,pfsyncf)
      let fulldescr = nm ++ " - "++descr
      set mitem [on command := workSpaceSync syncfs fulldescr work]
      buildSyncMenu work menu rest
\end{code}

\newpage
Text tests
\begin{code}
textTest work what parser dbgshow
 = do topf <- getTop work
      topf' <- get topf frameParent
      txt <- textDialog topf' what ("Enter "++what) ""
      thg <- getThgrf work
      let mstk = graphAsStack thg
      let result = parser mstk "<user>" txt
      case result of
       Left msg
        ->  errorDialog topf' "parse Failed" (txt++"\n\n"++msg)
       Right thing
        ->  do let thingtext = show thing
               let ttresult = parser mstk "<show>" thingtext
               let ttsummary
                    = case ttresult of
                       Left msg' -> msg'
                       Right thing' -> dbgshow thing'
               infoDialog topf' "Parse OK"
                ( txt
                  ++"\n\n"++dbgshow thing
                  ++"\n\n"++show thing
                  ++"\n\nre-Parsing:\n"++ttsummary
                )
\end{code}

Dialog tests
\begin{code}
dialogTest work
 = do topf <- getTop work
      topf' <- get topf frameParent
      txt <- textDialog topf' "caption" "prompt" "default"
      d  <- dialog topf' [text := "Confirm"]
      ok  <- button d [text := (txt ++ " - OK?")]
      set d [layout := widget ok]
      let f stop
             = do set ok [on command := stop (Just txt)]
      mres <- showModal d f
      case mres of
        Nothing -> return ()
        (Just x) -> infoDialog topf' "dialogTest" x

\end{code}

\newpage
\subsubsection{The Appearance Menu}

\begin{code}
mkAppMenu top f work
 = do appMenu <- menuPane [text:="Appearance"]

      tablePenMenu <- menuPane [text:= "Table Border Width"]

      tableStyleMenu <- menuPane [text := "Table Border Style"]

      itmGen <- menuSub appMenu tablePenMenu
                  [ text:="Table Border Width"
                  , help:="Change the width of the table borders"]

      itmGen2 <- menuSub appMenu tableStyleMenu
                  [ text:="Table Border Style"
                  , help:="Change the pen style of the table borders"]

      penWidth1 <- menuItem tablePenMenu [text:="1"]
      set penWidth1 [ on command := changePenWidth 1 work]

      penWidth2 <- menuItem tablePenMenu [text:="2"]
      set penWidth2 [ on command := changePenWidth 2 work]

      penWidth3 <- menuItem tablePenMenu [text:="3"]
      set penWidth3 [ on command := changePenWidth 3 work]

      penStyle1 <- menuItem tableStyleMenu [text:="----"]
      set penStyle1 [ on command := changeTableStyle 1 work]

      penStyle2 <- menuItem tableStyleMenu [text:="_ _ _"]
      set penStyle2 [ on command := changeTableStyle 2 work]

      penStyle3 <- menuItem tableStyleMenu [text:="- . -"]
      set penStyle3 [ on command := changeTableStyle 3 work]

      penStyle4 <- menuItem tableStyleMenu [text:="____"]
      set penStyle4 [ on command := changeTableStyle 4 work]

      fontMenu <- menuItem appMenu [text:= "Font"]
      set fontMenu [on command := changeFont fontMenu work]

      textColourMenu <- menuItem appMenu [text:= "Text Colour"]
      set textColourMenu [on command := changeTextCol textColourMenu work]

      tableColMenu <- menuItem appMenu [text:= "Table colour"]
      set tableColMenu [on command := changeTCol tableColMenu work]

      bgColourMenu <- menuItem appMenu [text:= "Background Colour"]
      set bgColourMenu [on command := changeBgColour bgColourMenu work]

      toggleWinSplititm <- menuItem appMenu
                           [ text:="Toggle split in Proof windows"
                           , help:="proof windows should be divided (Horizontal/Vertical)"]
      set toggleWinSplititm [on command := toggleSplit work]

      resetMenu <- menuItem appMenu [text:= "Reset"]
      set resetMenu [on command := resetStyles work]

      return appMenu
\end{code}

\newpage
\subsection{Theory Graph Display}

\begin{code}
showTheoryGraph work
 = do f <- frame [text:="Theory Graph Display"]
      p <- panel f []
      sw <- scrolledWindow p []
      set sw [ virtualSize := sz 1000 2000
             , scrollRate := sz 10 10
             , size := sz 500 500
             , on paint := paintTheoryGraph work
             ]
      set f [ layout := container p
                        $ margin 10
                        $ boxed "Theories"
                        $ fill (widget sw)
            , outerSize := sz 600 600
            , visible := True
            ]
\end{code}

Painting the window
\begin{code}
paintTheoryGraph work dc viewArea
 = do thgrf <- getThgrf work
      tStyle <- getTextStyle work
      let currFont = case tStyle of
                          Nothing -> fontDefault
                          (Just style) -> textFont style -- current text font
      let currCol  = case tStyle of
                          Nothing -> defaultColour
                          (Just style) -> textCol style  -- current text colour
      let thgDD = theoryGraphDD currFont currCol thgrf
      dispvar <- varCreate $ DisplayData (20,20) thgDD
      preOverlayDisplayData dispvar
                            (theoryGraphOverlay thgrf)
                            dc viewArea
\end{code}

Specifying the graph drawing.
First some spacing constants:
\begin{code}
thryTextSpacer,thryBoxSpacerX,thryBoxSpacerY,rowSepY :: Int
thryTextSpacer = 4 -- should all live in style data somewhere !!
thryBoxSpacerX = 10
thryBoxSpacerY = 10
rowSepY = 2 * thryBoxSpacerY
\end{code}

\newpage
Then the rendering code:
\begin{code}
theoryGraphDD :: FontStyle -> Color -> TheoryGraph -> DisplayDescr
theoryGraphDD  currFont currCol (rdag,trie)
 = let
    layers = rdStratify rdag
    thboxes = map (intersperse spacebox . map (thryDDs trie)) layers
    levels = map thLevels thboxes
    splevels = intersperse spacebox levels
   in justDraw $ DDrawVert Nothing DrawCentre splevels 0
 where

   thryDDs trie thnm
     = DD thDS (0,0) nullDDBB clkh
     where
       thry = ttlookup unknownPrfCtxt trie thnm
       modfont
        = case modified thry of
           Transient  ->  currFont
           Log        ->  currFont{_fontWeight=WeightBold}
           Upgrade  ->  currFont{_fontWeight=WeightBold,_fontUnderline=True}
       thDS = DDrawBox Nothing
                $ justDraw
                $ DDrawSpace thryTextSpacer thryTextSpacer thryTextSpacer thryTextSpacer
                $ justDraw
                $ DDrawText (Just $ TextStyle modfont currCol)
                $ fullThryName thry
       clkh = topTheoryClick thry

   spacebox = justDraw
              $ DDrawSpace thryBoxSpacerX thryBoxSpacerX thryBoxSpacerY thryBoxSpacerY
              $ displayNothing

   thLevels dds = justDraw
                  $ DDrawHoriz Nothing DrawCentre dds 0
\end{code}

\newpage
We overlay links connecting nodes to immediate
descendants (towards the root):
\begin{code}
theoryGraphOverlay (rdag,trie) ddata dc viewarea
 = case ds of

    DDrawVert _ _ (_:_:_:dd4:_) _  ->  drill $ ddds dd4
    _ -> drawText dc "PANIC - WHERE IS GRAPH?" (Point orgx orgy) []

 where

   (orgx,orgy) = dorigin ddata
   (DD ds og (mbbx,mbby) clkh) = ddescr ddata

   drill (DDrawBox _ ddbox) = drill2 $ ddds ddbox
   drill _ = drawText dc "PANIC.1 - WHERE IS GRAPH?" (Point orgx orgy) []
   drill2 (DDrawSpace _ _ _ _ ddbox)
    = drawoverlay $ abstractDS $ ddds ddbox
   drill2 _ = drawText dc "PANIC.2 - WHERE IS GRAPH?" (Point orgx orgy) []

   drawoverlay (DDrawVert _ _ dds _) = linkRows dds
   drawoverlay _ = putStrLn "drawoverlay: not DDrawVert"

   linkRows [] = return ()
   linkRows (DD row1 _ mbb _:rest)
    = do linkRow mbb row1 rest
         linkRows rest

   linkRow mbb (DDrawHoriz _ _ dds1 _) [] = return ()
   linkRow mbb ds1@(DDrawHoriz _ _ dds1 _)
               (DD (DDrawHoriz _ _ dds2 _) _ _ _:rest)
    = do linkRow' mbb dds2 dds1
         linkRow mbb ds1 rest
   linkRow _ _ _ = putStrLn "linkRow: not DDrawHoriz"

   linkRow' mbbr dds2 [] = return ()
   linkRow' mbbr dds2 ((DD (DDrawText _ nm) orig mbb _):rest)
    = do let rnm = thryNameRoot nm
         let ancs = rdDesc rnm rdag
         link rnm orig mbb ancs dds2
         linkRow' mbbr dds2 rest
   linkRow' _ _ _ = putStrLn "linkRow': not DDrawText"

   link :: String -> (Int,Int) -> (Int,Int) -> [String] -> [DisplayDescr] -> IO ()
   link pname (px,py) (pw,ph) ancs [] = return ()
   link pname po@(px,py) pm@(pw,ph) ancs
        ((DD (DDrawText _ nm) (cx,cy) (cw,ch) _):rest)
    | chname `elem` ancs
      = do drawLink hard px py pw ph cx cy cw ch dc
           link pname po pm ancs rest
    | otherwise = link pname po pm ancs rest
    where
      chname = thryNameRoot nm
      hard = chname `elem` pdeps
      pdeps = case tlookup trie pname of
        Nothing -> []
        (Just thry) -> syntaxDeps thry ++ proofDeps thry
   link _ _ _ _ _ = putStrLn "link: not DDrawText"
\end{code}

\newpage
Drawing a link (need nice picture here)
\begin{code}
drawLink :: Bool -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
         -> DC () -> IO ()
drawLink hard px py pw ph cx cy cw ch dc
 | k == 0
     =  do line dc (Point itx ity) (Point ibx iby) pstyle
           circle dc (Point ibx iby) 3 pstyle
 | otherwise
     = do sequence_ $ map (drawl pstyle) ptsegs
          drawc pstyle (last ptsegs)
 where
  px', py', pw', ph', cx', cy', cw', ch' :: Double
  px' = fromIntegral px
  py' = fromIntegral py
  pw' = fromIntegral pw
  ph' = fromIntegral ph
  cx' = fromIntegral cx
  cy' = fromIntegral cy
  cw' = fromIntegral cw
  ch' = fromIntegral ch
  tx  =  px' + pw'/2.0
  ty  =  py'+ph'
  bx  =  cx' + cw'/2.0
  by  =  cy'
  (itx,ity) = (round tx, round ty)
  (ibx,iby) = (round bx, round by)
  pstyle = if hard then [penWidth:=2] else []
  rsep = fromIntegral rowSepY
  k ::Int
  k = round ( ((by - ty) - rsep) / (ph' + rsep) )
  genSegYs ty s h i
    = (strt,strt+s+slip)
    where strt = ty+(i*(s+h))
          slip = fromIntegral boxOuterSpace
  ysegs = map (genSegYs ty rsep ph' . fromIntegral) [0..k]
  minv = (bx-tx) / (by-ty)
  genx y = ( tx + ((y-ty) * minv), y )
  ptsegs = map (map2 genx) ysegs
  drawl pstyle ((x1,y1),(x2,y2))
   = line dc (Point (round x1) (round y1))
             (Point (round x2) (round y2))
             pstyle
  drawc pstyle ((x1,y1),(x2,y2))
   = circle dc (Point (round x2) (round y2) ) 3 pstyle
\end{code}

\newpage
\subsection{Global Mapping}

This feature is used for once-off transformations
of all datatypes, and shoud be considered \emph{very dangerous}.
Most of the time it should be a simple dummy that
says nothing will happen,
but when ``live'' it will state what is about to happen
and will then ask for confirmation before proceeding.
\begin{code}
globalMap work
 = do topf <- getTop work
      topf' <- get topf frameParent
      warningDialog topf' "Global Map (Maintenance Only)"
        "Currently Disabled\nWhen live, details will appear here"
      -- performGlobalMap (pmap, emap) work
      --  where pmap = ... ; emap = ...
\end{code}
