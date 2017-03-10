\section{\UTP2\ Proof Operations}

Managing proof in the GUI.
\begin{code}
module WxProof where
import Tables
import Datatypes
import DataText
import Types
import MatchTypes
import Matching
import FreeBound
import Focus
import Heuristics
import Builtin
import Substitution
import Laws
import Manipulation
import Normalise
import Proof
import Theories
import Utilities
import Files
import ImportExport
import Archive
import DocTextParser
import LaTeXPretty
import DSL
import UTP
import R
import RAlg

import System.IO
import Graphics.UI.WX
import Graphics.UI.WXCore

import Data.Char
import Data.List
import Data.Maybe
import Control.Monad
import System.FilePath

import WxTypes
import WxState
import WxStyle
import WxRender
import Debug.Trace
\end{code}


\subsection{Proof GUI Top Level}

The main Proof Window.
\begin{code}
createProofWindow pid work
 = do let ftxt = "Proof of '"++pid++"'"
      let stxt = ftxt ++ " started."
      tStyle <- getTextStyle work
      let tCol  = case tStyle of
                       Nothing -> defaultColour
                       Just st -> textCol st
      let tFont = case tStyle of
                       Nothing -> fontDefault
                       Just st -> textFont st
      bcol <- getBgColour work
      f <- frame [text:=ftxt, bgcolor := bcol]
      sts <- statusField [text:=stxt]
      p <- panel f []
      h <- splitterWindow p []

      mp <- panel h []
      mw <- scrolledWindow mp []
      set mw [ on paint := paintMatches pid work
             , virtualSize := sz 2000 5000
             , scrollRate := sz 10 10
             , on doubleClick := findAndApplyLaw pid work
             , bgcolor := bcol
             , textColor := tCol
             , font := tFont
             ]

      gp <- panel h []
      gw <- scrolledWindow gp []
      set gw [ on paint := paintProof pid tFont tCol work
             , virtualSize := sz 2000 5000
             , scrollRate := sz 10 10
             , on clickRight := popupFilteredLawMatches' anyM pid work
             , bgcolor := bcol
             , textColor := tCol
             , font := tFont
             ]
      set gw (shortcutKeys pid work)

      prfMenu <- mkProofSetupMenu pid work
      prfVMenu <- mkProofViewMenu pid work
      prfOMenu <- mkProofOptionMenu pid work
      prfHMenu <- mkHeuristicsMenu pid work
      hlpMenu <- mkProofHelpMenu pid work

      splitVorH <- getSplit work
      let split = if splitVorH then vsplit else hsplit

      set f [ menuBar :=[prfMenu,prfVMenu,prfOMenu,prfHMenu,hlpMenu]
            , statusBar := [sts]
            , closeable := True
            , on closing := abandonProof pid work
            -- may need to invoke windowDestroy
            , layout
              :=
              container p $ margin 10 $ fill $
                  split h 5 150
                    (container mp (minsize (sz 100 100) (boxed "Matches" $ fill $ widget mw)))
                    (container gp $ boxed "Goal and Proof" $ fill $ widget gw)
            , outerSize := sz 1000 700
            , visible := True
            , bgcolor := bcol
            , textColor := tCol
            , font := tFont
            ]

      goaldd <- varCreate nullDD
      mtchdd <- varCreate nullDD

      --Add check here to change these True values to values that can change

      let pgui = ProofGUI f sts gw mw goaldd mtchdd
                          True True False
                          (head availableMatchFilters)
                          (head availableRankHeuristics)
                          (head availableMatchPostProcess)
                          succinct

      return pgui

-- end createProofWindow
\end{code}

\newpage
\subsubsection{Proof Setup Menu}

Proof setup: choosing strategy, etc.
\begin{code}
mkProofSetupMenu pid work
 = do proofSetupMenu <- menuPane [ text:="&Setup" ]

      assumeMenu <- menuPane [ text:="&Assume" ]

      -- Assume sub-menu
      itmAssume <- menuSub proofSetupMenu assumeMenu
                             [ text:="Assume", help:="Assume antecedent" ]

-- current Play setup needs revising - Play should be invoked
--  from Theory, either on a conjecture, or a user-entered project

--    * - starting done from a theory, not a proof
--       itmPlay <- menuItem proofSetupMenu
--                       [ text:="&Play\tCtrl+P"
--                       , help:="Play with a predicate (LHS->RHS)" ]
--       set itmPlay [on command := predPlay pid work]

      itmReduce <- menuItem proofSetupMenu
                        [ text:="&Deduce\tCtrl+D"
                        , help:="Reduce all" ]
      set itmReduce [on command := setProofStrategy pid SSRed work]

      itmLhs2Rhs <- menuItem proofSetupMenu
                        [ text:="&L2R\tCtrl+L"
                        , help:="Reduce LHS to RHS " ]
      set itmLhs2Rhs [on command := setProofStrategy pid SSL2R work]

      itmRhs2Lhs <- menuItem proofSetupMenu
                        [ text:="&R2L\tCtrl+R"
                        , help:="Reduce RHS to LHS " ]
      set itmRhs2Lhs [on command := setProofStrategy pid SSR2L work]

      itmRedBoth <- menuItem proofSetupMenu
                        [ text:="Red. &Both\tCtrl+B"
                        , help:="Reduce Both Sides " ]
      set itmRedBoth [on command := setProofStrategy pid SSRB work]

      itmLawReduce <- menuItem proofSetupMenu
                          [ text:="La&W Reduce\tCtrl+W"
                          , help:="Reduce Law to Goal " ]
      set itmLawReduce [on command := setProofStrategy pid SSLwR work]

      itmInduction <- menuItem proofSetupMenu
                          [ text:="&Induction\tCtrl+I"
                          , help:="Reduce Induction Law to Goal " ]
      set itmInduction [on command := setProofStrategy pid SSInd work]

      itmAReduce <- menuItem assumeMenu
                        [ text:=" then Red", help:="Assume, then Reduce" ]
      set itmAReduce [on command := setProofStrategy pid (SSAss SSRed) work]

      itmAL2R <- menuItem assumeMenu
                     [ text:="then L2R", help:="Assume, then L-to-R"]
      set itmAL2R [on command := setProofStrategy pid (SSAss SSL2R) work]

      itmAR2L <- menuItem assumeMenu
                     [ text:="then R2L", help:="Assume, then R-to-L" ]
      set itmAR2L [on command := setProofStrategy pid (SSAss SSR2L) work]

      itmARB <- menuItem assumeMenu
                    [ text:="then Both", help:="Assume, then red. both" ]
      set itmARB [on command := setProofStrategy pid (SSAss SSRB) work]

      itmALR <- menuItem assumeMenu
                    [ text:="then Law-Reduce"
                    , help:="Assume, then red. law to goal" ]
      set itmALR [on command := setProofStrategy pid (SSAss SSLwR) work]

      itmAInd <- menuItem assumeMenu
                     [ text:="then induction"
                     , help:="Assume, then induction" ]
      set itmAInd [on command := setProofStrategy pid (SSAss SSInd) work]

      itmSynch <- menuItem proofSetupMenu
                        [ text:="Synch Theories"
                        , help:="synchronise local theory copies with global stack" ]
      set itmSynch [on command := synchProof pid work]

      itmEndPlay <- menuItem proofSetupMenu
                        [ text:="Premature End"
                        , help:="turn current proof state into a theorem" ]
      set itmEndPlay [on command := premEnd pid work]

      itmSavPrf <- menuItem proofSetupMenu
                       [ text:="&Save Proof\tCtrl+S", help:="Save Proof" ]
      set itmSavPrf [on command := exportProof pid work]

      itmXPrf <- menuItem proofSetupMenu
                     [ text:="&Abandon Proof\tCtrl+A"
                     , help:="Abandon Proof" ]
      set itmXPrf [on command := abandonProof pid work]

      return proofSetupMenu
\end{code}


\newpage
\subsubsection{Heuristics Menu}

User-controllable heuristics.
\begin{code}
mkHeuristicsMenu pid work
 = do hMenu <- menuPane [ text:="&Heuristics" ]

      fMenu <- menuPane [ text:="(pre-)Filters" ]
      rMenu <- menuPane [ text:="ranking Heuristics" ]
      pMenu <- menuPane [ text:="(post-)Processing" ]

      fSub <- menuSub hMenu fMenu [ text:="(pre-)Filters" ]
      rSub <- menuSub hMenu rMenu [ text:="ranking Heuristics" ]
      pSub <- menuSub hMenu pMenu [ text:="(post-)Processing" ]

      addhs fMenu setMF availableMatchFilters
      addhs rMenu setRH availableRankHeuristics
      addhs pMenu setMPP availableMatchPostProcess

      return hMenu

 where
  addhs hMenu _ [] = return hMenu
  addhs hMenu setH (hdescr:rest)
   = do addh setH hdescr hMenu
        addhs hMenu setH rest

  addh setH hdescr@(name,h,txt) hMenu
    = do itmH <- menuItem hMenu [text:=name, help:=txt]
         set itmH [on command := setH hdescr pid work]

  setMF hdescr pid work
   = proofDo pid work sMF (nSP "setMF")
   where
    sMF _ pid pspace work
     = do let pspace'
               = (proofGUISetf $ currMFSetf $ const hdescr) pspace
          proofSpaceUpdate pspace' pid work
          repaintProofGUI pspace'

  setRH hdescr pid work
   = proofDo pid work sRH (nSP "setRH")
   where
    sRH _ pid pspace work
     = do let pspace'
               = (proofGUISetf $ currRHSetf $ const hdescr) pspace
          proofSpaceUpdate pspace' pid work
          repaintProofGUI pspace'

  setMPP hdescr pid work
   = proofDo pid work sMPP (nSP "setMPP")
   where
    sMPP _ pid pspace work
     = do let pspace'
               = (proofGUISetf $ currMPPSetf $ const hdescr) pspace
          proofSpaceUpdate pspace' pid work
          repaintProofGUI pspace'
\end{code}

\newpage

\subsubsection{Option Menu}

Proof options: mainly what to do once proof is complete.
\begin{code}
mkProofOptionMenu pid work
 = do proofOptionMenu <- menuPane [text:="&Options"]

      toggleASTitm <- menuItem proofOptionMenu
                           [ text:="toggle Auto-Save"
                           , help:="toggle automatic save of completed theorem"]
      set toggleASTitm [on command := toggleAST pid work]

      toggleAPTitm <- menuItem proofOptionMenu
                           [ text:="toggle Auto-Promote"
                           , help:="toggle automatic promotion of theorem to laws"]
      set toggleAPTitm [on command := toggleAPT pid work]

      toggleAMitm <- menuItem proofOptionMenu
                           [ text:="toggle Auto-Match"
                           , help:="show/stop matching all the time"]
      set toggleAMitm [on command := toggleAM pid work]

      return proofOptionMenu

toggleAPT pid work
 = do ap <- getAPT pid work
      sts <- getSts work
      case ap of
        Nothing -> alert sts ("ERROR: Proof not found")
        (Just ap')
          -> do setAPT work pid (not ap')
                alert sts ("Auto-promotion of Theorems is now "++if ap' then "OFF" else "ON")

toggleAST pid work
 = do sts <- getSts work
      ast <- getAST pid work
      case ast of
        Nothing -> alert sts ("ERROR: Proof not found")
        (Just ast')
          -> do setAST work pid (not ast')
                alert sts ("Auto-save of Theorems is now "++if ast' then "OFF" else "ON")

toggleAM pid work
 = do am <- getAM pid work
      sts <- getSts work
      case am of
        Nothing -> alert sts ("ERROR: Proof not found")
        (Just am')
          -> do setAM work pid (not am')
                alert sts ("Auto-matching for Theorems is now "++if am' then "OFF" else "ON")
\end{code}

\newpage

\subsubsection{View Menu}

\begin{code}
mkProofViewMenu pid work
 = do proofViewMenu <- menuPane [text:="&View"]


      -- Verbosity Presets sub-menu
      verbMenu <- menuPane [text:="&Verbosity"]
      itmVerb <- menuSub proofViewMenu verbMenu
                  [ text:="Verbosity Presets"
                  , help:="Verbosity preset levels"]

      -- Verbosity Toggles sub-menu
      vTogMenu <- menuPane [text:="&Toggles"]
      itmVTog <- menuSub proofViewMenu vTogMenu
                  [ text:="Verbosity Toggles"
                  , help:="toggles individual verbosity settings"]

        -- Verbosity Presets

      mkTogVerbosity pid verbMenu work
        (setFocusOnly (const False)) "focus in context"

      mkTogVerbosity pid verbMenu work
        (setFocusOnly (const True)) "focus only"

      mkSetVerbosity pid verbMenu work
        relonly "Rel-only" "only show proof relation (inline)"

      mkSetVerbosity pid verbMenu work
        terse "Terse" "show proof relation and law name (own line)"

      mkSetVerbosity pid verbMenu work
        succinct "Succinct" "Terse plus location, match-type (own line)"

      mkSetVerbosity pid verbMenu work
        expansive "Expansive" "Succinct plus bindings (own line)"

      mkSetVerbosity pid verbMenu work
        showall "Show All" "Expansive plus theory name/number (own line)"

        -- Verbosity Toggles

      mkTogVerbosity pid vTogMenu work
        (setFocusOnly not) "focus"

      mkTogVerbosity pid vTogMenu work
        (setThryName not) "theory name"

      mkTogVerbosity pid vTogMenu work
        (setThryNum not) "theory number"

      mkTogVerbosity pid vTogMenu work
        (setLawName not) "law name"

      mkTogVerbosity pid vTogMenu work
        (setMatchType not) "match type"

      mkTogVerbosity pid vTogMenu work
        (setProvShort not) "prov.(short)"

      mkTogVerbosity pid vTogMenu work
        (setProvFull not) "provenance (full)"

      mkTogVerbosity pid vTogMenu work
        (setLocation not) "focus location"

      mkTogVerbosity pid vTogMenu work
        (setPBinds not) "pred. bindings"

      mkTogVerbosity pid vTogMenu work
        (setEBinds not) "expr. bindings"

      mkTogVerbosity pid vTogMenu work
        (setQBinds not) "quant.-var. bindings"

      -- view by template
      tmplViewItm <- menuItem proofViewMenu
                     [ text:="Law Template View"
                     , help:="Window to find laws matching simple templates" ]
      set tmplViewItm [on command := proofTemplateView pid work]

      toggleWinSplit <- menuItem proofViewMenu
                           [ text:="change view Horizontal/Vertical"
                           , help:="toggle how the windows should be divided"]
      set toggleWinSplit [on command := toggleSplit work]

      return proofViewMenu

toggleSplit work
  = do sts <- getSts work
       note sts ("Proof windows will be split the other way when you open one next")
       splitB <- getSplit work
       setSplitf (not splitB) work

\end{code}
Setting a specified verbosity value:
\begin{code}
mkSetVerbosity pid menu work vb txt hlp
 = do itm <- menuItem menu [ text:=txt , help:=hlp ]
      set itm [on command := setVerbosityLevel pid vb work]

setVerbosityLevel pid nvb work
 = proofDo pid work sVL (nSP "setVerbosityLevel")
 where
  sVL _ pid pspace work
   = do setVb work pid nvb
        repaintProofGUI pspace
\end{code}
Toggling a specified verbosity component:
\begin{code}
mkTogVerbosity pid menu work f txt
 = do itm <- menuItem menu [ text:=txt, help := ("Toggle display of "++txt) ]
      set itm [ on command := toggleVerbosity f pid work]

toggleVerbosity f pid work
 = proofDo pid work tV (nSP "toggleVerbosity")
 where
  tV _ pid pspace work
   = do setfVb work pid f
        repaintProofGUI pspace
\end{code}

\subsubsection{Proof Help Menu}

\begin{code}

mkProofHelpMenu pid work
 = do helpMenu <- menuPane [text:="&Help"]

      itmSCHelp <- menuItem helpMenu
                       [ text:="&Shortcut Keys", help:="Display Shortcut Keys"]
      set itmSCHelp [on command := showKeyShortcuts work]

      itmWhyNot <- menuItem helpMenu
                       [ text:="&Why Not\tCtrl+W"
                       , help:="Diagnostics: Why is the proof Not complete?"]
      set itmWhyNot [on command := diagnoseProof pid work]

      return helpMenu

showKeyShortcuts work
 = do f <- frame [text:="Proof Key Shortcuts"]
      p <- panel f []
      sw <- scrolledWindow p []
      set sw [ on paint := paintMenu work
             , virtualSize := sz 1000 2000
             , scrollRate := sz 10 10
             , size := sz 800 500
             , on click := showCurrentHelp work f
             ]
      set f [ layout
              := container p $ margin 5 $ fill $ widget sw
            ]

\end{code}



\subsubsection{Proof Key Shortcuts}

\begin{code}
shortcutKeys pid work
          =  [ on anyKey := handleKeys pid work]

handleKeys pid work k
  = case k of
      KeyLeft       -> focusLeft pid work
      KeyRight      -> focusRight pid work
      KeyUp         -> focusUp pid work
      KeyDown       -> focusDown 1 pid work
      (KeyChar '1') -> focusDown 1 pid work
      (KeyChar '2') -> focusDown 2 pid work
      (KeyChar '3') -> focusDown 3 pid work
      (KeyChar '4') -> focusDown 4 pid work
      (KeyChar '5') -> focusDown 5 pid work
      (KeyChar '6') -> focusDown 6 pid work
      (KeyChar '7') -> focusDown 7 pid work
      (KeyChar '8') -> focusDown 8 pid work
      (KeyChar '9') -> focusDown 9 pid work
      KeyEscape     -> focusReset pid work
      _             -> func pid work
  where
    func = tupleLookup allKeyHelp (head.showKey $ k)

tupleLookup [] _ = \_ _ -> return ()
tupleLookup ((ky,(fn,_)):rest) nm
  | nm == ky   =  fn
  | otherwise  =  tupleLookup rest nm
\end{code}


\begin{code}
paintMenu work dc va
 = do (fSize,fDesc,fLead) <- getFullTextExtent dc "m"
      let (emH,emW) = (sizeH fSize,sizeW fSize)
      let lineHeight = emH + fDesc + fLead
      setSCMenuLnHeight work lineHeight
      menu <- return (map getInfo allKeyHelp)
      paintLines menu dc va
      where getInfo aShortcut = (fst aShortcut)
                                    : (head.lines.snd.snd $ aShortcut)

\end{code}
We need to get the first line of each entry in the shortcuts file as these are the titles of the shortcuts to be
displayed on the menu
\begin{code}

getMenuLines menuLines [] = reverse menuLines
getMenuLines menuLines (keyHelp:restKeyHelp)
 = getMenuLines (line:menuLines) restKeyHelp
    where line = head(lines keyHelp)

\end{code}

\subsubsection{Helptext for Key Shortcuts}


The following function is called when a line on the key shortcuts menu has been clicked by the user and calls functions
to display relevant helptext
\begin{code}

showCurrentHelp work f clickPt
   = do lineNum <- mouseOnWhichLine work clickPt (0::Int) (0::Int)
        appuser <- getAppUser work
        displayKeyHelp f appuser lineNum

\end{code}
Then, a function to determine which line of the menu the user has selected. Note that heightMenuLine is the height of each line in the menu which was calculated in the paintMenu function. The value returned by the function is the position of the element of the list of Key Shortcuts obtained from
the helptext file which corresponds to the line that was clicked on.
\begin{code}

mouseOnWhichLine work clickPt count ycount
 = do heightMenuLine <- getSCMenuLnHeight work
      let y = pointY(clickPt)
      -- toConsole ("clicked y = "++show y)
      if (y > ycount) && (y <= (ycount + heightMenuLine))
        then do return (count-1) -- skip first line in menu as it's blank
        else do mouseOnWhichLine work clickPt (count + 1) (ycount + heightMenuLine)

\end{code}
Now, function displays the relevant helptext for the shortcut key the user has selected in an info dialog box. It will
display nothing if either a blank line or a partitioning line on the menu is found (refer to how file is laid out)
\begin{code}

displayKeyHelp f appuser lineNum
 = do if lineNum < 0
        then return ()
        else if lineNum >= length allKeyHelp
                then return ()
                else do let helpTxt = key:info
                        if (helpTxt /= "------\n\n") && (helpTxt /= "\t\n\n")
                          then do infoDialog f "Help" helpTxt
                                  return ()
                          else return ()
                        where
                          key  = fst $ allKeyHelp !! lineNum
                          info = snd.snd $ allKeyHelp !! lineNum

\end{code}
A table to hold the help menu shortcuts, the key press is on the left and the tuple on the right is two strings (The explaination of what the shortcut does, The function the shortcut calls).
Number Keys(1-9) are used as placeholder symbols for groups of shortcuts.
\begin{code}

allKeyHelp :: AList Char
    (String -> WxStateRef -> IO(), String)
allKeyHelp
    = [ (' ', ((\_ _ -> return ()), hm_arrowPress))
      , ('#', ((\_ _ -> return ()), hm_numberKeys))
      , ('@', (synchProof, hm_SyncProof))
      , ('h', (popupFilteredLawMatches anyM (pt 50 20), hm_popupFilteredLawMatches))
      , ('u', (undoProof, hm_undo))
      , ('0', (toggleVerbosity (setFocusOnly not), hm_focusToggle))
      , ('I', (instantiateLaw, hm_instantiateLaw))
      , ('r', (replPvar, hm_replPvar))
      , ('d', (defnPvar, hm_defnPvar))
      , ('f', (foldPvar, hm_foldPvar))
      , ('a', (redApp, hm_reduceApp))
      , ('s', (doSub, hm_sub))
      , ('S', (doAlphaSub, hm_alphaSub))
      , ('-', (tidyUp Tflt, hm_tidyFlat))
      , ('t', (tidyUp Tsf, hm_tidyFlatSort))
      , ('<', (tidyUp Tsrt, hm_tidySort))
      , ('T', (tidyUp Tall, hm_tidyFlatSortDups))
      , ('!', (tidyUp Trdp, hm_tidySortDups))
      , ('x', (simplifyIt, hm_predSimp))
      , ('e', (propagateEquality, hm_propEqPred))
      , ('i', (indexSplitIt, hm_indexSplit))
      , ('n', (doDNF, hm_toDNF))
      , ('N', (doCNF, hm_toCNF))
      , ('b', (binderSplitIt, hm_binderSplit))
      , ('m', (findMatches, hm_findLaw))
      , ('l', (applyMatches, hm_applyLaw))
      , ('A', (stripForall, hm_stripForall))
      , ('R', (expandPvars, hm_expandPvars))
      , ('M', (matchGivenLaw, hm_matchGivenLaw))
      , ('X', (popupFilteredLawMatches onlyTREqv (pt 50 20), hm_popupTrivialLawMatches))
      , ('D', (assertDefinedness, hm_assertDefinedness))
      , ('w', (witnessIt, hm_witness))
      , ('c', (switchIt, hm_switch))
      , ('p', (writeCurrProof, hm_write))
      , ('?', (testPattern, hm_testPattern))
      , ('g', (grind anyM, hm_grind))
      ]

hm_focusToggle = (
    unlines $ [" (zero) : Toggle Focus Display\n",
    "Toggling on the focus display",
    "reduces the expression on screen to only the focus.",
    "This is purely a visual aid,",
    "aimed to improve the tractability of expressions",
    "which are too large to digest all at once.",
    "Toggling off the focus display (by pressing 0 again)",
    "returns you to the view of the entire expression."])

\end{code}

\subsection{Rendering Proofs}


\subsubsection{Painting Proof State}
\begin{code}
paintProof pid fnt col work dc viewArea
 = proofDo pid work (pP fnt col dc viewArea) (nSP "paintProof")
 where
  pP fnt col dc viewArea _ pid pspace work
   = do let prf = currProof pspace
        let pgui = proofGUI pspace
        let fname = fst3 $ currMF pgui
        let rname = fst3 $ currRH pgui
        let pname = fst3 $ currMPP pgui
        let vb = verbosity pgui
        oldCol <- get dc textColor
        tStyle <- getTextStyle work
        let tCol  = case tStyle of
                         Nothing -> defaultColour
                         Just st -> textCol st
        let tFont = case tStyle of
                         Nothing -> fontDefault
                         Just st -> textFont st
        set dc [textColor := tCol]  -- change to current text colour
        mctxt <- getMCtxt pid work
        paintText tFont (unlines $ proofLines fname rname pname vb prf) dc viewArea
        set dc [textColor := oldCol] -- change back to old text colour

  proofLines fname rname pname vb prf
     = [ "Goal : " ++ show gpr
       , "Side-Condition : " ++ showSide (side prf)
       , "Strategy : " ++ strategyHeader strat
                       ++ " " ++ showState (done prf)
         ++ "  Heuristic : " ++ fname ++ "->" ++ rname ++ "->" ++ pname
       , thrysDisplay (context prf)
       , targetDisplay gpr strat
       , proofDisplay vb strat
       ]
     where
       gpr = goal prf
       strat = plan prf

  showSide SCtrue = "None"
  showSide sc     = show sc

  showState True = "[DONE]"
  showState False = "[incomplete... ]"

-- end paintProof
\end{code}

Painting current theory stack
\begin{code}
thrysDisplay :: TheoryStack -> String
thrysDisplay []
 = "!?! NO CURRENT THEORIES\n"
thrysDisplay thrys
 = "Global Theories : "
   ++ concat(intersperse " | " (map thryName global))
   ++ "\n---------------------------------------------------\n"
   ++ (unlines $ concat (map (tail . theoryAsLines) local))
 where (local,global) = span isSPC thrys
\end{code}

Painting Hypotheses Details
\begin{code}
hyposDisplay :: Verbosity -> [LawTable] -> String
hyposDisplay vb hypos
 = unlines (concat (intersperse [" ---"] (map (map (hypDisplay vb)) hypos)))

hypDisplay :: Verbosity -> (String,Law) -> String
hypDisplay vb (hname,((hpred,hsc),_,_))
 = showLName vb hname ++ " is " ++ show hpred ++ showSC hsc
\end{code}

Painting Target Predicate Details
\begin{code}
targetDisplay :: Pred -> Strategy -> String
targetDisplay gpr strat
 = "TARGET> " ++ show (proofTarget gpr strat)
\end{code}


Painting Proof(-Section) Details
\begin{code}
proofDisplay vb NoStrategy   = ""
proofDisplay vb (Reduce ps)  = psDisplay vb ps
proofDisplay vb (Lhs2Rhs ps) = psDisplay vb ps
proofDisplay vb (Rhs2Lhs ps) = psDisplay vb ps

proofDisplay vb (RedBoth 1 lhs rhs)
   = "\n**Lefthand Side**\n" ++ psDisplay vb lhs
proofDisplay vb (RedBoth 2 lhs rhs)
   = "\n**Righthand Side**\n" ++ psDisplay vb rhs
proofDisplay vb (RedBoth _ lhs rhs)
  = "\n**Lefthand Side**\n" ++ psDisplay vb lhs
    ++ "\n**Righthand Side**\n" ++ psDisplay vb rhs

proofDisplay vb (LawReduce ln sc ps) = psDisplay vb ps

proofDisplay vb (Assume cnsq strategy) = proofDisplay vb strategy

psDisplay vb (fpred,fovs,ttbl,args)
 = (contextDisplay (getPFContext fpred) fovs ttbl fpred++"\n\n"
    ++ showFocussedPredicate vb fpred ++ "\n\n"
    ++ showProofSteps vb args)
\end{code}

The context we display is the context in the Pfocus, plus the free variables, and type information
\begin{code}
contextDisplay (pol,bs,_) fovs ttbl fpred
 =     "Polarity = "++show pol
   ++  " | Binders = "++showBinders bs
   ++  " | Free vars = " ++ show fovs
   ++  " | " ++ showExprType ttbl fpred
   -- ++ "\n" ++ show ttbl


showBinders :: Binders -> String
showBinders [] = "none"
showBinders bs = concat $ intersperse "," $ map varKey bs

showExprType tts fpred
 = case getPFocus fpred of
    Obs e       ->  "EXPR : " ++ show (evalExprType tts tags e)
    Defd e      ->  "EXPR : " ++ show (evalExprType tts tags e)
    TypeOf e _  ->  "EXPR : " ++ show (evalExprType tts tags e)
    _           ->  "PREDICATE"
 where tags = thd3 $ getPFContext fpred
\end{code}

We now show a focussed predicate, according to the verbosity specification.
This is used

\textbf{THIS NEEDS A FOCUS-AWARE SHOW !!!!!!!!!!!!!!!}

THIS NEEDS A FOCUS-AWARE SHOW !!!!!!!!!!!!!!!

\emph{THIS NEEDS A FOCUS-AWARE SHOW !!!!!!!!!!!!!!!}

\begin{code}
showFocussedPredicate vb fpred
 | focusOnly vb   =  showFOPredicate fpred
 | otherwise      =  show $ getPFTop fpred

showFOPredicate (fpr, _, [])  =  show fpr
showFOPredicate (fpr, _, [_])  =  ".. "++show fpr++" .."
showFOPredicate (fpr, _, _)  =  "... "++show fpr++" ..."
\end{code}




\subsubsection{Match Window Rendering}

\begin{code}
paintMatches pid work dc viewArea
 = proofDo pid work (pM dc viewArea) (nSP "paintMatches")
 where
  pM dc viewArea _ pid pspace work
   = do oldCol <- get dc textColor
        oldFont <- get dc font
        tStyle <- getTextStyle work
        let tCol  = case tStyle of
                         Nothing -> defaultColour
                         Just st -> textCol st
        let tFont = case tStyle of
                         Nothing -> fontDefault
                         Just st -> textFont st
        let size = (_fontSize tFont)
        set dc [textColor := tCol]
        set dc [font := tFont{_fontSize = size - 2}]

        let mtchs = matches pspace
        let prf = currProof pspace
        let mctxts = mtchCtxt prf
        let cpred = currProofPred prf
        let ppMatches = map (matchesSummary cpred dc viewArea) (zip (repeat.head $ mctxts) mtchs)
        let mtchsDDs = mkMatchDDs pspace 1 (zip mtchs ppMatches)
        let mtchsDD = DisplayData
                     (10,10)
                     (dispVert Nothing DrawLeft mtchsDDs noClkHandlers)
        ddvar <- varCreate mtchsDD
        setMatchDD work pid ddvar
        paintDisplayData ddvar dc viewArea

        set dc [textColor := oldCol]
        set dc [font := oldFont]

  matchesSummary cpred dc viewArea (mctxt, (match, _))
   = summariseMatch mctxt cpred match
  getmatchName match = (\(_,_,c) -> c).fst $ match

  mkMatchDDs _ _ [] = []
  mkMatchDDs pspace i (mtch:mtchs)
   = mkMatchDD pspace i mtch : mkMatchDDs pspace (i+1) mtchs

  mkMatchDD pspace i (mtch, ppMatch)
   = dispVert Nothing DrawLeft
              (map drawLine [((show i) ++ ": " ++ getmatchName mtch), ppMatch, " "] )
              (matchClkHandler pspace i mtch)

  --drawMatch txt = map drawLine txt

  drawLine str = dispText Nothing str noClkHandlers

  matchClkHandler pspace i mtch
   = ClkHandlers Nothing
                 (Just $ applyMatch pid pspace mtch)  -- $
                 Nothing
-- end paintMatches
\end{code}

The match handler
\begin{code}
applyMatch pid pspace (match,mctxt) _ work
 = do let prf = currProof pspace
      let cpred = currProofPred prf
      let cptxt = "Current Focus: "++show cpred
      let penv = context prf
      mf <- fParent $ matchWindow $ proofGUI pspace
      (ok,fmatch@(r,(m,p,b,_,_),n))
          <-  finaliseMatch cptxt penv mctxt mf match
      if ok
       then
        do let apred = applyLaw mctxt fmatch cpred
           updateProof pid pspace work apred
                    (EQV,getPFocusPath apred,NamedLaw m n p,b)
       else return ()
\end{code}

Double-click handler for match window:
\begin{code}
findAndApplyLaw pid work pnt
 = proofDo pid work (fAAL pnt) (nSP "findAndApplyLaw")
 where
  fAAL pnt _ pid pspace work
   = do let matchVar = matchDD (proofGUI pspace)
        mtchDD <- varGet matchVar
        let hndlrs = pointDDLookup hDoubleClk mtchDD pnt
        if null hndlrs
         then return ()
         else (head hndlrs) pnt work
\end{code}


\newpage
\subsection{Starting a Proof}

A proof is always initiated for a conjecture within some theory,
which, along with those other theories on which it depends,
make up its (proof-local) theory context, represented
as a theory stack.
In addition a ``proof-local'' theory is created on top
of the stack to hold definitions local to the proof,
as required by those commands that fold and unfold local
definitions.
Certain strategies,
namely those involved with assumptions, may also add further
``hypothesis'' theories on top of the stack.
\begin{code}
startProof thname cjname pred sc work
 = do let pid = mkPid cjname thname
      cprfs <- getCurrprfs work
      case tlookup cprfs pid of
        Just _ -> alertExistingProof pid work
        Nothing
         -> do proof' <- buildProof thname cjname pred sc work
               pspace' <- makeProofSpace proof' pid work
               let cprfs' = tupdate pid pspace' cprfs
               setCurrprfs cprfs' work

alertExistingProof pid work
 = do topf <- getTop work
      warningDialog topf "Existing Proof" ("Proof '"++pid++"' already exists")

makeProofSpace proof pid work
 = do pgui' <- createProofWindow pid work
      return $ Proofspace proof [] pgui'
\end{code}

A new proof takes the stack of theories visible,
in the theory-graph,
from the conjectures theory, and pushes a (empty) proof-local theory
on top:

\begin{tikzpicture}[
Theory/.style={
rectangle,
minimum size=6mm,
minimum width=30mm,
very thick,
draw=blue!50!black!50,
top color=white,
bottom color=green!50!black!20,
font=\itshape
}]
\matrix[row sep=2mm, column sep = 10mm]{
  \node [Theory] {a-top-theory};
 & \node [Theory] {another-top} ;
\\
  \node {\vdots};
\\

&& \node [Theory] {proof-local theory} ;
\\
  \node (pt) [Theory, bottom color=red!50!black!20] {conjectures-theory} ;
&& \node (ptcopy) [Theory, bottom color=red!50!black!20] {proof-theory} ;
\\
  \node (ot) {\vdots};
&& \node (otcopy) {\vdots};
\\
  \node (rt) [Theory] {root-theory} ;
&& \node (rtcopy) [Theory] {root-theory} ;
\\
};
\draw [->] (pt) -- (ptcopy) ;
\draw [->] (ot) -- (otcopy) ;
\draw [->] (rt) -- (rtcopy) ;
\end{tikzpicture}
\begin{code}
buildProof :: String -> String -> Pred -> SideCond
           -> WxStateRef -> IO Proof
buildProof thname cjname pred sc work
 = do penv <- extractProofStack thname work
      uid <- getUser work
      return $ makeProof thname cjname pred sc penv uid

extractProofStack :: String -> WxStateRef -> IO TheoryStack
extractProofStack thnm work
 = do thgrf <- getThgrf work
      return $ hardGraphToStack thnm thgrf

extractProofTheory :: String -> WxStateRef -> IO Theory
extractProofTheory thnm work
 = do (_,trie) <- getThgrf work
      case tlookup trie thnm of
        Nothing  ->  return unknownPrfCtxt
        Just thry -> return thry
\end{code}

\subsubsection{Synchronising a Proof}

Sometimes we want to synchronise a proof's local copy of
the theory stack with the global one
--- typically in inductive proofs once the cases have been done.
\begin{code}
synchroniseProof :: Proof -> WxStateRef -> IO Proof
synchroniseProof proof work
 = do mstk <- extractProofStack (thname proof) work
      return $ synchroniseProofContext mstk proof
\end{code}


\subsubsection{Re-starting a Proof}

When a proof is loaded,
we get a list of names of required theories (\texttt{ctxtNames prf}),
plus a list of the special theories associated with the proof
(\texttt{spcths})
which we use to populate the required theory stack (\texttt{context prf}).
\begin{code}
rebuildProofContext prf spcths work
 = do let prfthnm = thname prf
      penv <- extractProofStack prfthnm work
      let thnms = ctxtNames prf
      let penv' = if null thnms
                   then penv
                   else filter ((`elem`prfthnm:thnms).thryName) penv
      let penv'' = spcths++penv'
      let mctxt' = mkMatchContexts penv''
      let prf'' =  prf{ context=penv'', mtchCtxt=mctxt' }
      return $ makeLive prf''
\end{code}

In the event these are missing (i.e. older legacy proofs),
we need to re-construct them.
\begin{code}
fixSpecialTheories penv prf spcs
  = case (plan prf) of
      (Assume _ _)  ->  fixAssumeTheories penv prf spcs
      _             ->  fixProofTheories prf spcs
\end{code}

For a proof not using the assumption strategy we expect a single PLT theory.
However for now we do not delete other non-PLT theories if present.
\begin{code}
fixProofTheories prf spcs
 | any isPLT spcs  =  spcs
 | otherwise       =  spcs ++ [newPLT (pname prf)]
\end{code}

For a proof using the assumption strategy we expect a single HYP theory,
followed by a PLT theory. As above, we do not
delete any theory fragments not matching this.
\begin{code}
fixAssumeTheories penv prf spcs
 = spcs ++ hyp ++ plt
 where
   hyp = if any isHYP spcs then [] else addAssumeHyps penv prf
   plt = if any isPLT spcs then [] else [newPLT (pname prf)]
\end{code}


\subsubsection{Loading and Saving the Current Proof}

The startup proof file is either empty, or contains the current active proof.
\begin{code}
-- proofFileName = acalai++cruthu
\end{code}
\textbf{We need to add some consistency checking. We then need to check this is consistent with the theories already
present, and if not, to attempt a fix-up. We need theory names in proofs and we check the theory is loaded and bring it
to the top. Also this stuff should really be in \texttt{WxTheory} since it does theory-stack manipulations}

Searches the theory stack for all theories mentioned
in the proofs explicit dependency list.
\begin{code}
setProofTheories prf ths
 = (prf',missing thstk)
 where
    thn = thname prf
    thstk = hardGraphToStack thn $ theoryGraph ths
    mctxt = mkMatchContexts thstk
    prf' = checkProof prf{context=thstk, mtchCtxt=mctxt}
    missing thstk = sort (ctxtNames prf) \\ sort (map thryName thstk)
\end{code}

\subsubsection{Premature End}

This allows us to prematurely end a proof,
provided we rename it as we have proved
something different to the initial goal.
For example, in a ``Lhs-to-Rhs'' proof of $P \equiv Q$,
we may have got stuck having reduced $P$ to $P'$,
and rather abandon completely,
we may decide to save this as a proof of $P \equiv P'$,
under a new name, possibly because it is an interesting result in its
own right.
\begin{code}
premEnd pid work
 = proofDo pid work pE (nSP "premEnd")
 where
  pE _ pid pspace work
   = do let prf = currProof pspace
        let penv = context prf
        let (ok,prf') = prematureEnding penv prf
        let pgui = proofGUI pspace
        let sts = proofStatus pgui
        if ok
         then
          do g <- fParent (goalWindow pgui)
             name <- textDialog g "Theorem Name : " "End Proof Now, as New Conj" ""
             if null name
              then alert sts "Side-ending requires a theorem name"
              else do cheer sts ("Side ended as theorem : "++name)
                      setTheorem pspace pid name prf'{pname=name} work
         else alert sts "Side-ending not possible for this proof."
\end{code}

\subsubsection{Starting Proof}

We use top-level menus to request a particular strategy:

\begin{verbatim}
SSRed | SSL2R | SSR2L | SSRB | SSLwR | SSInd | SSAss StratSpec
\end{verbatim}

A key new feature is the ability for a strategy to return
a number of helper conjectures/lemmas to make it easier
for the proof to be discharged. In particular,
applying the induction strategy with induction axiom
$$
  Q_1 \land \ldots \land Q_n \implies \forall x @ P
$$
will result in the appropriately instantiated $Q_i$ being
returned as helper conjectures.
\begin{code}
setProofStrategy pid stspec work
 = proofDo pid work sPS (nSP "setProofStrategy")
 where
  sPS _ pid pspace work
   = do let prf = currProof pspace
        let pgui = proofGUI pspace
        mf <- fParent (goalWindow pgui)
        let sts = proofStatus pgui
        case (plan prf) of
          NoStrategy -> setAndCheckProofStrategy pspace pid stspec prf sts mf work
          _ -> do goahead <- confirmDialog mf
                               "Restart Proof ?"
                               "This will scrap the current proof ! Are you sure?"
                               False
                  if goahead
                   then setAndCheckProofStrategy pspace pid stspec prf sts mf work
                   else return ()
\end{code}

We scrub any special theories off the stack,
and add a new PLT-theory, just as if \texttt{startProof} has been invoked
(in case we are changing the strategy of an existing proof):
\begin{code}
setAndCheckProofStrategy pspace pid stspec prf sts mf work
 = do let gpred = goal prf
      if isSCompatible stspec gpred
       then
         do let penv = newPLT (pname prf): dropWhile isSPC (context prf)
            let mctxts = mtchCtxt prf
            let (pred',tts,_) = setPredTypes (head mctxts) gpred
            (okay,(prf',hyps),helpers)
               <- setUpStrategy sts prf{goal=pred'} tts mf penv mctxts stspec
            if okay
             then
              do let ctxt = hyps++penv
                 let prf'' = prf'{context=ctxt, mtchCtxt=mkMatchContexts ctxt}
                 setAndCheckProofState notMatch pid pspace work (prf'',noMatches)
                 note sts ("Proof Strategy now "++show stspec)
                 repaintProofGUI pspace
                 setupHelperProofs (thname prf'') work helpers
             else
              return ()
       else
         alert sts ("Cannot use "++show stspec++" with "++show gpred)
\end{code}

Building helper conjectures is easy:
\begin{code}
helperConj pnm sc (Imp (And gs) g)
 = mkHelpers 1 gs
 where
   mkHelpers _      [] = []
   mkHelpers i (gi:gs) = (pnm++"."++show i,(gi,sc)) : mkHelpers (i+1) gs

helperConj pnm sc (Imp q g) = [(pnm++".0",(g,sc))]

helperConj pnm sc ilaw = []
\end{code}

Starting them involves establishing conjectures:
\begin{code}
setupHelperProofs thnm work helpers
 = do let helpconjs = lbuild helpers
      conjs <- conjecturesGet thnm work
      let conjs' = helpconjs `tmerge` conjs
      conjecturesSet thnm conjs' work
      startProofs helpers
 where
   startProofs [] = return ()
   startProofs ((pnm,(pr,sc)):helpers)
    = do startProof thnm pnm pr sc work
         startProofs helpers
\end{code}

\newpage
The real work is done by \texttt{setUpStrategy}:
\begin{code}
setUpStrategy
 :: (Textual w)
 => w -> Proof -> TypeTables -> Window a -> [Theory] -> [MatchContext] -> StratSpec
 -> IO (Bool,(Proof,[Theory]),[(String,Assertion)])
\end{code}

Law-Reduce - ask user for law
\begin{code}
-- the lawname in LawReduce must contain theoryname/number
-- information, or Theories.citations will report an unknown theory

setUpStrategy sts prf tts mf penv mctxts SSLwR
 = do lname <- textDialog mf explanation "LawReduce" ""
      case fullLawLookup lname penv mctxts of
        Nothing
          ->  do alert sts ("Cannot LawReduce - no such law :"++lname)
                 return (False,(prf,[]),[])
        (Just (((lpr,lsc),lprov,_),thname,thno,mctxt))
           ->  do let glawtxt = describe lpr
                  (ok,fmatch)
                    <- finaliseMatch glawtxt penv mctxt mf
                        ( 0
                        , ( All, lprov
                          , ( tnil
                            , tnil
                            , tnil
                            )
                          , lsc,[lpr]
                          )
                        , lname)
                  if ok
                   then
                    do let (lfpr',tts') = fixFType
                                     penv
                                     $ setPFocus (matchReplace mctxt fmatch)
                       let lpr' = clearPFocus lfpr'
                       let fullname = qlawprint3 (thname,thno,lname)
                       return ( True
                              ,(setLawReduce (fullname,(lpr',lsc)) tts' prf, [])
                              ,[] )
                   else
                    do alert sts ("aborted by user")
                       return (False,(prf,[]),[])
 where
  goaltxt = show (goal prf)
  explanation
   = unlines [ "Goal:-"
             , goaltxt
             , ""
             , "Enter name of law from which to reduce:"]
  describe lpr
   = unlines [ "Goal:-"
             , goaltxt
             , "Law:-"
             , show lpr
             ]
\end{code}

Induction- ask user for law, check of the right form
\begin{code}
setUpStrategy sts prf tts mf penv mctxts SSInd
 = do lname <- textDialog mf explanation1
               "Induction" "induction-"
      case fullLawLookup lname penv mctxts of
        Nothing    ->  do alert sts ("Induction law not found :"++lname)
                          return (False,(prf,[]),[])
        (Just (((lpr,lsc),lprov,_),thname,thno,mctxt))
           -> setUpInduction penv mctxt thname thno lname lprov lsc lpr
 where

   goalpr = goal prf

   explanation1
    = unlines [ "Goal :- "
              , "  " ++ show goalpr
              , ""
              , "Enter name of induction law:"
              ]
\end{code}

We are only interested in laws of the form: $Q \implies \forall x @ P$
\begin{code}
   setUpInduction theories mctxt thname thno lname lprov lsc
                  ilawpr@(Imp _ (Forall _ (Q [q]) (Pvar (Std r))))
    | isStdV q
     = do (novar,ivar,ilawpr') <- setInductionVar ilawpr q
          if novar
           then do alert sts "no ivar given"
                   return (False,(prf,[]),[])
           else
           do let goal' = forcePredInductionVar ivar goalpr
              (ok,fmatch)
                 <- instantiateInduction theories mctxt r goal' SCtrue ilawpr' lprov lname
              if ok
               then
                do let ilawpr'' = matchReplace nullMatchContext fmatch

                   let (ilawpr''',tts') = fixType penv ilawpr''
                   let fullname = qlawprint3 (thname,thno,lname)
                   let pnm = pname prf
                   return ( True
                          ,(setLawReduce (fullname,(ilawpr''',lsc)) tts' prf, [])
                          , helperConj pnm lsc ilawpr''' )
               else
               do alert sts "aborted by user"
                  return (False,(prf,[]),[])

   setUpInduction _ mctxt thname thno lname _ _ _
     = do alert sts ("Law '"++lname++"' not of induction 'shape'")
          return (False,(prf,[]),[])
\end{code}

We need to instantiate the induction axiom with
the given goal and induction variable,
being careful to avoid name-capture.
\begin{code}
   instantiateInduction theories mctxt p goal isc ilaw lprov lname
    = do let binds = ( lbuild[(p,TO goal)]
                     , tnil
                     , tnil
                     )
         finaliseMatch (explanation2 ilaw)
                       theories mctxt mf
                       (0,(All,lprov,binds,isc,[ilaw]),lname)

   explanation2 ilaw
    = unlines [ "Induction Law :-"
              , "  "++show ilaw
              , "Goal :="
              , "  "++show goalpr
              ]
\end{code}

We want the user to select the induction variable
from among the free variables of the goal:
\begin{code}
   setInductionVar ilaw q
    = do ivstr <- textDialog mf (explanation3 ilaw)
                  "Induction Variable" $ varKey q
         if null ivstr
          then return (True,undefined,undefined)
          else let ivar = preVar ivstr
               in return (False, ivar,replaceQVar q ivar ilaw)

   goalsc = side prf
   goalmctxt = topMtchCtxt prf
   (_,goalfovs,_,_) = setPSFreeVars goalmctxt goalsc (setPFocus goalpr,fvClosed,tts,[])

   explanation3 ilaw
    = explanation2 ilaw
      ++ "\nFree-variables (choose one) : "++show goalfovs
      ++ "\n\n" ++"Enter induction variable name:"
-- setUpStrategy
\end{code}

The rest --- just do it (no helper proofs to appear)
\begin{code}
setUpStrategy sts prf tts _ penv mctxts stspec
 = return (True,setStrategy penv stspec prf tts,[])
\end{code}

\newpage
\subsubsection{Checking a Proof}

We provide a state-update that checks a proof for completion:
\begin{itemize}
  \item
    If the proof is not complete,
    and the gui action wasn't a match, and auto-matching is enabled,
    then we find matches for display.
  \item
    In any case we update the proof details
    and assess its theoremhood
\end{itemize}
\begin{code}
notMatch, wasMatch :: Bool
notMatch = True
wasMatch = False

setAndCheckProofState notm pid pspace work (prf',mtchs')
 = do let prf'' = checkProof prf' -- modifies done flag
      am <- getAMM pid work
      let mtchs'' = if am && notm && not (done prf'')
                     then matchSearch (proofGUI pspace) prf''
                     else mtchs'
      let pspace' = pspace{currProof=prf'', matches=mtchs''}
      currProofspaceSetf pid (const pspace') work
      assessTheorem pspace' prf'' pid work
      -- toConsole "finalising proof 9 setAndCheckProofState"
\end{code}

Holding space for code
\begin{verbatim}
let pgui =  proofGUI pspace
let r = snd3 $ currRH pgui
let ((pr,fovs),tts) = currProofState prf
let mtchs = matchLaws (passAllMatches,r,idLawMatches)
                      tts fovs penv mctxts (side prf) pr
mf <- goalParent pgui
\end{verbatim}


If done, then shout about it, and set it as a theorem.
\begin{code}
assessTheorem pspace prf pid work
 = if (done prf) -- set by checkProof if proof is complete
   then do repaintProofGUI pspace
           let sts = proofStatus $ proofGUI $ pspace
           let proofName = pname prf
           cheer sts ("Conjecture '"++proofName++"' has been proven!")
           setTheorem pspace pid proofName prf work
   else return ()
\end{code}

Put theorem into table, then promote to a law if required
\begin{code}
setTheorem pspace pid name prf work
 = do let thnm = thname prf
      --putStrLn ("@@@@SETTHM.currProofPred:\n"++show (currProofPred prf))
      --putStrLn ("@@@@SETTHM.goal:\n"++show (goal prf))
      mthry <- doTheoryLookup thnm work
      case mthry of
       Nothing -> setTheoremError pid prf work
       Just thry
        -> do let prfs = theorems thry
              let cnjs = conjectures thry
              -- putStrLn ("setTheorem prf = "++show(proofAssert prf))
              let prfs' = prf : thrmv name prfs
              let cnjs' = tblank name cnjs
              let thry1 = thry{ theorems=prfs'
                              , conjectures=cnjs'
                              , modified=Log }
              let pgui = proofGUI pspace
              if autoPromoteThm pgui
                then do let thry2 = autoPromote pgui prf name thry1
                        doTheoryUpdate thnm thry2 work
                        let pf = proofFrame pgui
                        infoDialog pf "Success !"
                            "Proof Complete !\nConjecture now a Theorem"
                        windowDestroy (proofFrame (proofGUI pspace))
                        if autoSaveThm pgui
                          then saveTheory thnm thry2 work
                          else return ()
                        unsetCurrprf work pid
                else return ()
              repaintTheoryTabs thnm work
              topf <- getTop work
              repaint topf
 where
\end{code}

Most importantly, we ensure that a theorem is
tidied up before being turned into a law: remove outermost
universal quantification; and put trivial equivalence sides on the right.
\begin{code}
   autoPromote pgui prf name thry
    | autoPromoteThm pgui  =  thry'
    | otherwise            =  thry
    where
      thry' = thry{laws=(name,law):(laws thry),modified=Upgrade}
      law = ( ( pred2law $ remOuterForall $ goal prf
              , side prf
              )
            , proofProv prf
            , Bnil
            )

   setTheoremError pid prf work
    = do topf <- getTop work
         warningDialog topf
           "Unable to Set Theorem"
            ("Cannot save theorem with Proof Id "++pid)

-- end setTheorem

saveTheory thnm thry work
 = do (_,cwd) <- getCurrFS work
      thry' <- archiveTheory cwd thry
      doTheoryUpdate thnm thry' work
      topf <- getTop work
      repaint topf

repaintNamedTheory thn work
 = do thfs <- getThryFrames work
      case tlookup thfs thn of
        (Just tw)  ->  repaint (twFrame tw)
        Nothing    ->  return ()
\end{code}

\subsection{Proof Steps --- Builtin}

\subsubsection{Changing the current predicate}

This assumes the current proof is left intact
\begin{code}
chgCurrFPred :: String -> WxStateRef -> (FPred -> FPred) -> IO ()
chgCurrFPred pid work f
 = proofDo pid work cCP (nSP "chgCurrFPred")
 where
  cCP _ pid pspace work
   = do let prf = currProof pspace
        let cfpred = currProofPred prf
        let penv = context prf
        let (nfpred,ntts) = fixFType penv (f cfpred)
        let prf' = setProofPred nfpred ntts prf
        setAndCheckProofState notMatch pid pspace work (prf',noMatches)
        repaintProofGUI pspace

chgCurrPred pid work f
 = chgCurrFPred pid work $ globalPFapp f
\end{code}


\subsubsection{Focussing up/down/left/right}
\begin{code}
hm_numberKeys = (
    unlines $ [" : Number Keys : Focus down to nth child\n",
    "Pressing the number n is equivalent to",
    "pressing DOWN key once, then RIGHT n-1 times."])

hm_arrowPress = (
    unlines $ ["Arrow Keys : Move Focus\n",
    "UP- moves the focus up one level,\n",
    "DOWN- moves the focus down one level.",
    "      The leftmost sub-expression comes into focus here.\n",
    "LEFT/RIGHT- navigate between sibling expressions on the same level."])

focusDown n pid work
  = chgCurrFPred pid work $ downPFocus n

focusUp pid work
  = chgCurrFPred pid work upPFocus

focusRight pid work
  = chgCurrFPred pid work rightPFocus

focusLeft pid work
  = do chgCurrFPred pid work leftPFocus

focusReset pid work
  = do chgCurrFPred pid work (setPFocus.clearPFocus)
\end{code}

\subsubsection{Synchronising Proofs}

Re-connect to global proof results.
\begin{code}
hm_SyncProof = (
    unlines $ [" : Synchronise Proof with Theories\n",
    "A proof works on local copies of the current theories,",
    "set up when the proof started. This command simply",
    "re-loads the latest global state of the theories",
    "so that results of other recent proofs can be incorporated.",
    "Useful for lemmas, and induction proofs."])

synchProof pid work
 = proofDo pid work sP (nSP "synchProof")
 where
  sP _ pid pspace work
   = do let prf = currProof pspace
        prf' <- synchroniseProof prf work
        setAndCheckProofState notMatch pid pspace work (prf',noMatches)
        repaintProofGUI pspace
\end{code}


\subsubsection{Replace \texttt{Pvar}}
\begin{code}
hm_replPvar = (
    unlines $ [" : Replace PVar by definition\n",
    "If a PVar (Predicate variable) is in focus and",
    "is defined in a preddef table in a visible theory,",
    "then the PVar is repaced by its definition."])

replPvar pid work
 = proofDo pid work rP (nSP "replPvar")
 where
  rP _ pid pspace work
   = do let prf = currProof pspace
        let cpred = currProofPred prf
        let penv = context prf
        let npred = repFocus penv cpred
        let jstfy = (EQV,getPFocusPath cpred,NameReplace,nullBinds)
        let prf' = addProofStep npred jstfy prf
        setAndCheckProofState notMatch pid pspace work (prf',noMatches)
        repaintProofGUI pspace
\end{code}

\subsubsection{Recursively expand \texttt{Pvar}s}
\begin{code}
hm_expandPvars = (
    unlines $ [" : Replace PVars by definition, recursively\n",
    "Calls upon the 'r' command recursively",
    "until the entire focus is broken down into base variables.\n",
    "Example:\n",
    "Imagine you have in the theory of R",
    "you have two predicates defined on OBS (observation) variables:\n",
    "  GROW = tr <<=- tr'",
    "  P = wait /\\ GROW\n",
    "Now, imagine you are dealing with an expression",
    "(which is not necessarily true!) such as:\n",
    "  P = GROW\n",
    "and you want to work on this by expanding it out into base variables.",
    "You could go to each term, P and GROW, using the 'r' command,",
    "and you would get the following:\n",
    "  wait /\\ GROW = tr <<=- tr'\n",
    "You would then realise that you still had GROW appearing,",
    "which is a non-base variable,",
    "and would further expand the expression to:",
    "  wait /\\ tr <<=- tr' = tr <<=- tr'",
    "Now you would be happy,",
    "having reduced the expression entirely to base variables and operators.",
    "However, you could have done so more quickly,",
    "using the 'R' command",
    "- which would convert ",
    "  P = GROW ",
    "to ",
    "  wait /\\ tr <<=- tr' = tr <<=- tr' ",
    "in one step."])

expandPvars pid work
 = proofDo pid work eP (nSP "expandPvars")
 where
  eP _ pid pspace work
   = do let prf = currProof pspace
        let cpred = currProofPred prf
        let penv = context prf
        let npred = expandFocus (map preds penv) cpred
        let jstfy = (EQV,getPFocusPath cpred,RecExpand,nullBinds)
        let prf' = addProofStep npred jstfy prf
        setAndCheckProofState notMatch pid pspace work (prf',noMatches)
        repaintProofGUI pspace
\end{code}





\subsubsection{Assert Definedness}

Converts an \texttt{Obs e} to  the conjunction of it and \texttt{Defd e}.
\begin{code}
hm_assertDefinedness = (
    unlines $ [" : Assert Definedness\n",
    "***Not too sure about this***"])

assertDefinedness pid work
 = proofDo pid work aD (nSP "assertDefinedness")
 where
  aD _ pid pspace work
   = do let prf = currProof pspace
        let cpred = currProofPred prf
        let npred = assertDefFocus cpred
        let jstfy = (EQV,getPFocusPath cpred,AssertDefined,nullBinds)
        let prf' = addProofStep npred jstfy prf
        setAndCheckProofState notMatch pid pspace work (prf',noMatches)
        repaintProofGUI pspace
\end{code}



\subsubsection{Define \texttt{Pvar}}

Here we define a Pvar as a shorthand for the current focus,
and replace it, allowing a complex sub-expression to be
folded away, for later expansion, should it be necessary.
The variable introduced must not be one already in use.
\begin{code}
hm_defnPvar = (
    unlines $ [" : Define PVar equal to focus\n",
    "This is essentially a fold (collapse) command.",
    "It allows you to reduce large expressions to single variables.",
    "If d is pressed,",
    "the user is prompted to enter a name for the PVar",
    "which is to replace the current focus.",
    "So long as the name is",
    "none of the predefined observation variables or predicates,",
    "it will then replace the focus ",
    "i.e. the focus will be collapsed to a single name.\n",
    "Similar to the \'0\' key, ",
    "this shortcut aids with the manageability of large expressions.",
    "When it is desired to expand the user-defined PVar",
    "back to the original expression,",
    "you focus in on the PVar in question and press the \'f\' key.\n",
    "Example:\n",
    "Let\'s say you have the expression:",
    "a /\\ TRUE == TRUE \\/ a.",
    "Now imagine you focus on the LHS,",
    "a /\\ TRUE,",
    "and subsequently press the \'d\' key.",
    "You will be prompted to type in a name- ",
    "let\'s say you type in \'LHS\'. ",
    "Then the main expression becomes:",
    "LHS = TRUE \\/ a.",
    "You can now work on the RHS of your expression",
    "until it is simplified (to \'a\' in this case)",
    "before expanding out the LHS, from \'LHS\' to",
    "\'a /\\ TRUE\',",
    "using the \'f\' key."])

defnPvar pid work
 = proofDo pid work dP (nSP "defnPvar")
 where
  dP _ pid pspace work
   = do let pgui = proofGUI pspace
        mf <- goalParent pgui
        let sts = proofStatus pgui
        let prf = currProof pspace
        let cfpred = currProofPred prf
        let penv = context prf
        newvar <- obtainDefnName "Define Predicate meta-Variable" mf cfpred
        if null newvar
         then return ()
         else
          case tslookup (envPreds penv) newvar of
           Just _  ->  alert sts ("PVar '"++newvar++"' already in use")
           Nothing
            -> do let pr = getPFocus cfpred
                  let npred = repPFocus (Pvar $ Std newvar) cfpred
                  let jstfy =(EQV,getPFocusPath cfpred,UName newvar,nullBinds)
                  let prf' = addProofStep npred jstfy prf
                  let (thn',penv') = notePLTPred newvar pr penv
                  let prf'' = prf'{context=penv',mtchCtxt=mkMatchContexts penv'}
                  setAndCheckProofState notMatch pid pspace work (prf'',noMatches)
                  repaintProofGUI pspace
                  repaintNamedTheory thn' work
                  note sts ("User-defined predicate name '"++newvar++"' added")

--obtainDefnName pmsg mf (Pfocus _ (Obs _ (Efocus _ _)) _) = return ""
--obtainDefnName pmsg mf (Pfocus _ pr _)
obtainDefnName pmsg mf _
 = fmap trim $ textDialog mf "Pvar Name" pmsg ""      -- $
--obtainDefnName pmsg mf _ = return ""
\end{code}


\subsubsection{Fold \texttt{Pvar}}
\begin{code}
hm_foldPvar = (
    unlines $ [" : Replace focus by defining PVar\n",
    "See \'d\' - this is its inverse."])

foldPvar pid work
 = proofDo pid work fP (nSP "foldPvar")
 where
  fP _ pid pspace work
   = do let pgui = proofGUI pspace
        mf <- goalParent pgui
        let sts = proofStatus pgui
        let prf = currProof pspace
        let cpred = currProofPred prf
        let penv = context prf
        newvar <- obtainDefnName "Select Fold meta-Variable" mf cpred
        if null newvar
         then alert sts "nothing selected"
         else
          do let qprs@(qpc,qseq,qtgt) = qparse newvar
             case qualLookup qprs predsLkp penv of
              Nothing  ->  alert sts ("no predicate with spec = "++show qprs )
              (Just prdef)
                -> foldPredicateVar
                     pspace prf penv cpred newvar prdef qtgt sts pid work

foldPredicateVar pspace prf penv cpred newvar prdef qtgt sts pid work
 = do let pr = getPFocus cpred
      let penv = context prf
      let ptables = envPreds penv
      let prx = expandPred (predTidy True) ptables pr
      let prdx = expandPred (predTidy True) ptables prdef
      if prx == prdx
       then
         do let npred = repPFocus (Pvar $ Std qtgt) cpred
            let jstfy =(EQV,getPFocusPath cpred,NameFold qtgt,nullBinds)
            let prf' = addProofStep npred jstfy prf
            setAndCheckProofState notMatch pid pspace work (prf',noMatches)
            repaintProofGUI pspace
       else alert sts ("Predicate named '"++newvar++"' does not match goal")
\end{code}


\subsubsection{Reduce Application}
\begin{code}
hm_reduceApp = (
    unlines $ [" : Reduce application\n",
    "This command allows you to expand a pre-defined function",
    "to its full body. ",
    "If the function ",
    "  f(x1, x2, ...., xn)",
    "appears in the focus, and this key is pressed, an expression in",
    "  x1...xn",
    "will replace",
    "  \'f(x1, x2, ...., xn)\',",
    "this expression being equal to the definition of the function, with",
    "  x1...xn",
    "replacing the dummy variables in the definition.\n",
    "Example:\n",
    "Say a function f(x, y), taking integer arguments,",
    "is defined somewhere to be: x < y.",
    "Now, say you are dealing with the expression:",
    "f((a + b), c) == f(a, (c - b)).",
    "If you use \'a\' to expand f on both the LHS and the RHS, you will get:",
    "a + b < c == a < c - b,",
    "and you can then go on to prove the theorem."])

redApp pid work
 = proofDo pid work rA (nSP "redApp")
 where
  rA _ pid pspace work
   = do let prf = currProof pspace
        let mctxt = topMtchCtxt prf
        let penv = context prf
        let cpred = currProofPred prf
        let ptables = envPreds penv
        let (rpred,chgd) = redFocus mctxt (side prf) ptables cpred
        case chgd of
          Chgd
           ->  updateProof pid pspace work rpred
                (EQV,getPFocusPath cpred,IApply,nullBinds)
          _  ->  return ()
\end{code}



\subsubsection{Perform Substitution}
\begin{code}
hm_sub = (
    unlines $ [" : Perform Substitution\n",
    "A substitution is of the form",
    "E[y1,..,yn / x1,...,xn],",
    "where E is some expression, and each",
    "xj in x1,...,xn",
    "is a variable which,",
    "if it occurs in E, ",
    "is to be replaced by the corresponding yj in y1,...,yn.",
    "Pressing \'s\' simply carries out the substitution- ",
    "all variables to be replaced in E are replaced.",
    "If E stands for some arbitrary predicate,",
    "then pressing s does nothing.",
    "If E is a composite expression made up of,",
    "say, P and Q composed under some operation *,",
    "then performing the substitution will take you from",
    " P*Q[y1,..,yn / x1,...,xn]",
    "to",
    " P[y1,..,yn / x1,...,xn]*Q[y1,..,yn / x1,...,xn]",
    "i.e. the substitution propagates to sub expressions.",
    "If an expression can be broken into sub-expressions",
    "repeatedly until it is reduced to only base variables,",
    "then the square brackets can be done away with completely",
    "with the \'s\' command. However, once you hit an arbitrary",
    "expression whose contents are hidden due to its generalization,",
    "then you can substitute no further.\n",
    "Examples:\n",
    "The action of pressing the \'s\' key is denoted here by \"--Press \'s\'->\".\n",
    "1. (x < y)[a,b / x,y]",
    "--Press \'s\'->",
    "a < b.\n",
    "2. (x < y)[a + b / x]",
    "--Press \'s\'->",
    "a + b < y\n",
    "3. (P /\\ x < y)[a,b / x,y]",
    "--Press \'s\'->",
    "P[a,b / x,y] /\\ a < b",
    "...Notice here how the sub on P cannot be further simplified",
    "due to the arbitrary nature of P in this last example."])

doSub pid work
 = proofDo pid work dS (nSP "doSub")
 where
  dS _ pid pspace work
   = do let prf = currProof pspace
        let mctxt = topMtchCtxt prf
        let (spred,chgd) = subFocus mctxt (side prf) (currProofPred prf)
        case chgd of
          Chgd
           ->  updateProof pid pspace work spred
                (EQV,getPFocusPath spred,ISubstitute,nullBinds)
          _  ->  return ()
\end{code}

\subsubsection{$\alpha$ Substitution}

\begin{code}
hm_alphaSub = (
    unlines $ [" : Alpha Substitution\n",
    "Alpha-substitution is often used to get around the",
    "restriction associated with replacing free variables.\n",
    "Example:\n",
    "Let\'s say we really want to replace free \"y\" by \"x - 10\" in",
    "the following:\n",
    "  forall x; x >= 3 => y = 0 /\\ exists y; y > 4 /\\ z = 10\n",
    "First, we use alpha-substitution to rename the binding and",
    "bound occurrences of x to something different (a) - {x -> a}:\n",
    "  forall a; a >= 3 => y = 0 /\\ exists y; y > 4 /\\ z = 10\n",
    "Then we do our desired substitution [x - 10/y]:\n",
    "  forall a; a >= 3 => x-10 = 0 /\\ exists y; y > 4 /\\ z = 10])"])

doAlphaSub pid work
 = proofDo pid work dAS (nSP "doAlphaSub")
 where
  dAS _ pid pspace work
   = do g <- goalParent $ proofGUI $ pspace
        subs@(Substn sub) <- getVarSubst g "alpha-Substitution"
        if null sub
         then return ()
         else
          do let prf = currProof pspace
             let mctxt = topMtchCtxt prf
             let spred
                   = alfFocus mctxt (side prf) subs (currProofPred prf)
             updateProof pid pspace work spred
               (EQV,getPFocusPath spred
                ,AlphaSubs (mapSub Var subs),nullBinds)
\end{code}

For alpha substitution we request the details of what changes are to be made:
\begin{code}
getVarSubst mf caption
 = do vspec <- textDialog mf vmsg caption ""
      return (mkVSubs vspec)
 where
   vmsg = "Enter new/old pairs,\n sep. by space"

mkVSubs vspec
 = Substn (zip (map parseVariable qvrs) $ map parseVariable vars)
   -- ISSUE brittle, needs proper error handling
 where
   (vars,qvrs) = unzip (getvv [] "" vspec)
   getvv vvs _ ""  = vvs
   getvv vvs var (c:cs)
     | c == '/'  =  getvqv vvs var "" cs
     | otherwise =  getvv vvs (c:var) cs
   getvqv vvs var qvr "" = (reverse var,reverse qvr):vvs
   getvqv vvs var qvr (c:cs)
     | c == ' '  = gets ((reverse var,reverse qvr):vvs) cs
     | otherwise = getvqv vvs var (c:qvr) cs
   gets vvs "" = vvs
   gets vvs (c:cs)
     | c == ' '  =  gets vvs cs
     | otherwise =  getvv vvs [c] cs
\end{code}

\subsubsection{Handling Simple Built-in Proof Steps}

\begin{code}
simpleBuiltIn name builtin infer pid work
 = proofDo pid work sBI (nSP name)
 where
  sBI _ pid pspace work
   = do let prf = currProof pspace
        let spred = builtin $ currProofPred $ prf
        updateProof pid pspace work spred
          (EQV,getPFocusPath spred,infer,nullBinds)
\end{code}

\subsubsection{Predicate Tidy-Up}
\begin{code}
tidyUp tspec = simpleBuiltIn "tidyUp" (tdyPred tspec) (ITidy tspec)
\end{code}

\subsubsection{Convert Predicate to DNF/CNF}
\begin{code}
doDNF = simpleBuiltIn "doDNF" (normPred dnf) (INorm "DNF")

doCNF = simpleBuiltIn "doCNF" (normPred cnf) (INorm "CNF")
\end{code}


\subsubsection{Predicate Simplify}
\begin{code}
simplifyIt = simpleBuiltIn "simplifyIt" simpPred ISimplify
\end{code}

\subsubsection{Propagate Equality}

Given a predicate of the form:
$$
  \ldots ( e=f \land \ldots \oplus \ldots P(e) \ldots ) \ldots
$$
where $\oplus$ is either $\land$ or $\implies$,
we can replace $e$ by $f$ in $P$.
\begin{code}
propagateEquality = simpleBuiltIn "propagateEq" propEqPred PropagateEq
\end{code}


\subsubsection{Strip leading for-all}

This action exploits the fact that if any of the following (for arbitrary $\vec v$) are a theorem,
$$
 P \qquad \forall \vec v @ P \qquad [P]
$$
then they all are.
In the LawReduce strategy,
it strips leading universal quantifiers,
provided focus is on the whole
current goal.
\begin{code}
stripForall pid work
 = proofDo pid work sFa (nSP "stripForall")
 where
  sFa _ pid pspace work
   = do let prf = currProof pspace
        let sts = proofStatus $ proofGUI $ pspace
        case plan prf of
         (LawReduce _ _ _) -> stripLRGoal pid pspace prf work
         _ -> alert sts "Can only strip forall in LawReduce strategy"

stripLRGoal pid pspace prf work
 = do let spred = stripPred $ currProofPred $ prf
      updateProof pid pspace work spred
        (EQV,getPFocusPath spred,ForallStrip,nullBinds)
\end{code}



\subsubsection{Predicate Binder Split}
\begin{code}
binderSplitIt pid work
 = proofDo pid work bSI (nSP "binderSplitIt")
 where
  bSI _ pid pspace work
   = do let prf = currProof pspace
        let spred = bndrSplitPred $ currProofPred $ prf
        updateProof pid pspace work spred
          (EQV,getPFocusPath spred,BinderSplit,nullBinds)
   where bs = [] -- NEED TO GET FROM FContext !!!
\end{code}


\subsubsection{Predicate Index-Split}
\begin{code}
indexSplitIt pid work
 = proofDo pid work iSI (nSP "indexSplitIt")
 where
  iSI _ pid pspace work
   = do let prf = currProof pspace
        mf <- goalParent $ proofGUI $ pspace
        ixtxt <- textDialog mf "Numbers sepatated by non-digits" "Specify indices" ""
        case txtToIndices ixtxt of
          Nothing  ->  repaintProofGUI pspace
          (Just ixs)
            -> do let spred = iSplitPred ixs $ currProofPred $ prf
                  updateProof pid pspace work spred
                      (EQV,getPFocusPath spred,ISplit ixs,nullBinds)
\end{code}

\newpage

\subsection{Proof Steps --- Matching}

Currently there are four ways in which the user can invoke
matching against laws, all of which take the current focus
as the matching `test' predicate:
\begin{description}
  \item[Right-Click]
     Matches laws, discards trivial equivalence matches,
     and displays the top 20 in a popup menu
  \item[Full Match (`m')]
    Matches laws, ranks them,
    and displays all matches in the Match window.
  \item[Given Match (`M')]
     Gets a law-name from the user and matches that specific law,
     displaying it in the Match window.
  \item[Trivial Matches ('X')]
         Matches Laws, keeps only trivial equivalence matches,
         and displays the top 20 in a popup menu.
\end{description}
We give here a short precise description of the module and key function calls
used to implement the above
---
matching first:

{\small
\begin{tabular}{|l|c|c|c|}
\hline
 Module & `m` & `M` & right-click,`X`
\\\hline
\hline
  & & & \\
  \texttt{WxProof}
    & \texttt{findMatches}
    & \texttt{matchGivenLaw}
    & \texttt{popupFilteredLawMatches}
\\& & &
\\\hline
  & & & \\
  \texttt{Proof}
    & \texttt{matchInProofEnv}
    &
    & \texttt{matchInProofEnv}
  \\ & & &
\\\hline
  & & & \\
  \texttt{Manipulation}
    & \texttt{findLaws}
    &
    & \texttt{findLaws}
\\
    & \texttt{subLawMatch}
    & \texttt{subLawMatch}
    & \texttt{subLawMatch}
  \\& & &
\\\hline
\end{tabular}
}

then applying a selected match:

{\small
\begin{tabular}{|l|c|c|c|}
\hline
 Module & `m` & `M` & right-click,`X`
\\\hline
\hline
  & & & \\
  \texttt{WxProof}
    & \texttt{applyMatches}
    & \texttt{applyMatches}
    & \texttt{doItemApply}
\\
    & \texttt{finaliseMatch}
    & \texttt{finaliseMatch}
    & \texttt{finaliseMatch}
\\
    & \texttt{applyLaw}
    & \texttt{applyLaw}
    & \texttt{applyLaw}
\\& & &
\\\hline
  & & & \\
  \texttt{Manipulation}
    & \texttt{matchReplace}
    & \texttt{matchReplace}
    & \texttt{matchReplace}
  \\& & &
\\\hline
\end{tabular}
}

There is also a fifth action: \textbf{Instantiate Law (`I')}
that selects a law and mimics a match (against true),
and then lets the user instantiate it as they please,
to implement the following deduction:
\begin{eqnarray*}
  && F
\EQV{logic}
\\ && F \land TRUE
\EQV{any instance of any law}
\\ && F \land \mathcal{I}(L)
\end{eqnarray*}

\newpage
\subsubsection{Find Law Matches}
\begin{code}
hm_findLaw = (
    unlines $ [" : Match Against Laws\n",
    "Produces a list of all the laws that match the current goal focus,",
    "including trivial matches.",
    "Used in conjunction with the \'l\' command,",
    "this command can facilitate the replacement",
    "of some expression with an equivalent expression",
    "(according to the laws of the formal system at hand).",
    "Note that this function is only needed",
    "when useful matches are filtered out of the list of matches",
    "obtained by right clicking on an expression."])

findMatches pid work
 = proofDo pid work fM (nSP "findMatches")
 where
  fM _ pid pspace work
   = do let prf = currProof pspace
        let pgui =  proofGUI pspace
        let mtchs = matchSearch pgui prf
        setAndCheckProofState wasMatch pid pspace work ( prf , mtchs )
        repaintProofGUI pspace
        let sts = proofStatus pgui
        note sts (   "Matching in theories: "
                  ++ (show (map thryName $ context prf))
                  ++ " - "
                  ++ matchReport mtchs
                 )

matchSearch pgui prf
 = let r = snd3 $ currRH pgui
       ((pr,fovs),tts) = currProofState prf
   in matchLaws (passAllMatches,r,idLawMatches)
                tts fovs (context prf) (mtchCtxt prf) (side prf) pr

matchLaws (f,r,p) tts fovs penv mctxts sc fpr
 =  matchInProofEnv f r p
                    (getPFContext fpr)
                    fovs tts sc fpr penv mctxts
\end{code}


\subsubsection{Match against given law}
\begin{code}
matchGivenLaw pid work
 = proofDo pid work mL (nSP "matchGivenLaw")
 where
  mL _ pid pspace work
   = do let prf = currProof pspace
        let penv = context prf
        --putStrLn("matchGivenLaws, penv length = "++ show (length penv))
        let mctxts = mtchCtxt prf
        --putStrLn("matchGivenLaws, mctxts length = "++ show (length mctxts))
        --putStrLn ("matchGivenLaw:laws="++show (map (map fst . laws) penv))
        let laws = concat (envLaws penv)
        let pgui = proofGUI pspace
        let sts = proofStatus pgui
        let r = snd3 $ currRH pgui
        mf <- goalParent pgui
        lname <- textDialog mf "Enter Law Name" "Match Law" ""
        case fullLawLookup lname penv mctxts of
          Nothing  ->  do alert sts ("No such law: "++lname)
                          repaintProofGUI pspace
          (Just (law,thnm,thno,mctxt))
            -> do matchLawAgainstGoal r
                        pspace pid prf thnm thno lname law sts mctxt work
                  repaintProofGUI pspace

matchLawAgainstGoal r pspace pid prf thnm thno lname law sts mctxt work
 = do --toConsole ("Matching "++qlawprint3 (thnm,thno,lname))
      let ((fpr,fovs),tts) = currProofState prf
      let fullname = qlawprint3 (thnm,thno,lname)
      let matches = matchSnglLaw r thnm fullname  fovs mctxt law tts (side prf) fpr
      setAndCheckProofState wasMatch pid pspace work (prf,matches)
      note sts ("Matched against law: '"++lname++"' ("++matchReport matches++")")

matchSnglLaw r thnm flname fovs mctxt law tts sc fpr
  = rankMatches passAllMatches r idLawMatches $ [(thnm,mctxt,map nmtag mtchs)]
  where
    tags = thd3 $ getPFContext fpr
    mtchs = subLawMatch tags fovs tts mctxt sc fpr law
    nmtag mtch = (mtch,flname)
\end{code}

Another version tests the pattern matching:
\begin{code}
hm_testPattern = (
    unlines $ [" : Test against Pattern Predicate in named Law (unsound)\n",
    "This command is useful for finding out why",
    "a certain law is not matching your expression.",
    "When you press this key,",
    "you will be prompted for the name of the law",
    "against which you are to test your expression.",
    "If you type the law in correctly,",
    "the command prompt will give a printout of the matching attempts,",
    "which should give you an indication of what\'s wrong.",
    "A lot of the time, you\'ll find that although your expression looks",
    "like it should match a law, ",
    "it doesn\'t due to type discrepancies."])

testPattern pid work
 = proofDo pid work tP (nSP "testPattern")
 where
  tP _ pid pspace work
   = do let prf = currProof pspace
        let ((pr,fovs),tts) = currProofState prf
        let penv = context prf
        let mctxts = mtchCtxt prf
        let laws = concat (envLaws penv)
        let pgui = proofGUI pspace
        let r = snd3 $ currRH pgui
        let sts = proofStatus pgui
        mf <- goalParent pgui
        lname <- textDialog mf "Law Name" "Choose Law" ""
        toConsole ("\n\n=================================================")
        toConsole ("Match focus: "++show (clearPFocus pr))
        toConsole ("against Law '"++lname++"'\n")
        case fullLawLookup lname penv mctxts of
          Nothing  ->  do alert sts ("No such law: "++lname)
                          repaintProofGUI pspace
          (Just (law,thnm,thno,mctxt))
            -> do let fullname
                       = qlawprint3 (thnm,thno,"???-"++lname++"-???")
                  let matches
                        = testSnglPat r thnm fullname fovs mctxt law tts (side prf) pr
                  putStrLn ("Test Match returned "++show (length matches)++" match(es)")
                  setAndCheckProofState wasMatch pid pspace work (prf,matches)
                     -- (map (\ (x,y) -> (x,y,lname)) matches))
                  repaintProofGUI pspace

testSnglPat r thnm flname fovs mctxt law tts sc fpr
  = rankMatches passAllMatches r idLawMatches $ [(thnm,mctxt,map nmtag mtchs)]
  where
    tags = thd3 $ getPFContext fpr
    mtchs = subPatternTest show tags fovs tts mctxt sc fpr law
    nmtag m = (m,flname)
\end{code}

\subsubsection{Instantiate Law}

\begin{code}
hm_instantiateLaw = (
    unlines $ [" : Instantiate Law\n",
    "The focus F is replaced by (F /\\ I) where I is",
    "any law, instantiated by the user."])

instantiateLaw pid work
 = proofDo pid work iL (nSP "instantiateLaw")
 where
  iL _ pid pspace work
   = do let prf = currProof pspace
        let penv = context prf
        let mctxts = mtchCtxt prf
        let laws = concat (envLaws penv)
        let pgui = proofGUI pspace
        let sts = proofStatus pgui
        mf <- goalParent pgui
        lname <- textDialog mf "Enter Law Name" "Instantiate Law" ""
        case fullLawLookup lname penv mctxts of
          Nothing  ->  do alert sts ("No such law: "++lname)
                          repaintProofGUI pspace
          (Just (law,thnm,thno,mctxt))
            -> do instantiateAndConjoinLaw
                        pspace pid prf thnm thno lname law sts mctxt work
                  repaintProofGUI pspace

instantiateAndConjoinLaw pspace pid prf thnm thno lname ((pr,sc),prov,_) sts mctxt work
 | sc /= SCtrue  =  do alert sts "Instantiated Law must be side-condition free"
 | otherwise
    = do let fullname = qlawprint3 (thnm,thno,lname)
         let match = (0,(All,prov,nullBinds,sc,[pr]),fullname)
         let iltxt = "Instantiate Law:-\n"++show pr
         mf <- goalParent $ proofGUI $ pspace
         let penv = context prf
         (ok,fmatch@(r,(m,p,b,_,reps),n))
           <- finaliseMatch iltxt penv mctxt mf match
         if ok
          then do let ilaw = matchReplace mctxt fmatch
                  let cfpred = currProofPred prf
                  let ifpred = conjoinLawInstance ilaw cfpred
                  updateProof pid pspace work ifpred
                     (EQV,getPFocusPath cfpred,InstantLaw n p,b)
          else return ()
\end{code}


\subsubsection{Apply Matched Law}

\begin{code}
applyMatches pid work
 = proofDo pid work aM (nSP "applyMatches")
 where
  aM _ pid pspace work
   = do let prf = currProof pspace
        let penv = context prf
        let mtchs = matches pspace
        mf <- goalParent $ proofGUI $ pspace
        mno <- fmap readNat
                 $ textDialog mf "Match No." "Apply Matching Law" "" -- $
        case getMatch mno mtchs of
          Nothing  -> return ()
          (Just (match,mctxt))
            -> do let cpred = currProofPred prf
                  let cptxt = "Current Focus: "++show (getPFocus cpred)
                  (ok,fmatch@(r,(m,p,b,_,reps),n))
                    <- finaliseMatch cptxt penv mctxt mf match
                  if ok
                   then
                    do let apred = applyLaw mctxt fmatch cpred
                       updateProof pid pspace work apred
                                (EQV,getPFocusPath apred,NamedLaw m n p,b)
                   else return ()

getMatch _ [] = Nothing
getMatch 1 (m:ms) = Just m
getMatch n (m:ms) = getMatch (n-1) ms
\end{code}


\subsubsection{Popup Filtered Law Matches}

Builds a popup menu based on the matching laws,
guided by a match predicate \texttt{mpred}:
\begin{code}
hm_popupFilteredLawMatches = (
    unlines $ [" : Popup Filtered Law Matches\n",
    "Matches focus against laws, filters then, ranks, them, and displays Top 20.",
    "(Also available via right-mouse click in Proof Goal window)"])

hm_popupTrivialLawMatches = (
    unlines $ [" : Match against trivial equivalences\n",
    "Matches that would usually be filtered out are allowed to pass though here.",
    "This is useful if the normal list of matches isn\'t churning up the right ones."])

popupFilteredLawMatches' mpred pid work pt
  = popupFilteredLawMatches mpred pt pid work
popupFilteredLawMatches mpred pt pid work
 = proofDo pid work mAAL (nSP "popupFilteredLawMatches")
 where
   mAAL _ pid pspace work
    = do let prf = currProof pspace
         let penv = context prf
         let mctxts = mtchCtxt prf
         let ((pr,fovs),tts) = currProofState prf
         let pgui = proofGUI pspace
         let f = snd3 $ currMF pgui
         let r = snd3 $ currRH pgui
         let p = snd3 $ currMPP pgui
         let matches
              = filter mpred (matchLaws (f,r,p) tts fovs penv mctxts (side prf) pr)
         g <- goalParent pgui
         mmenu <- buildMatchMenu pid work matches
         menuPopup mmenu pt g

hm_grind = (
    unlines $ [" : Try to solve by educated attempts\n",
    "Given a conjecture, you try to \"grind\" it down as much as possible by using",
    "techniques that work on the broadly expected form for a conjecture"])

grind mpred pid work    --currently just preforms first possible match
 = proofDo pid work mAAL (nSP "grind")
 where
   mAAL _ pid pspace work
    = do let prf = currProof pspace
         let cpred = currProofPred prf
         let penv = context prf
         let mctxts = mtchCtxt prf
         let ((pr,fovs),tts) = currProofState prf
         let pgui = proofGUI pspace
         let f = snd3 $ currMF pgui
         let r = snd3 $ currRH pgui
         let p = snd3 $ currMPP pgui
         let matches
              = filter mpred (matchLaws (f,r,p) tts fovs penv mctxts (side prf) pr)
         if matches /= []
           then do putStrLn (summariseMatch (head mctxts) cpred (fst.head $ matches))
                   doItemApply pid work (head matches) cpred
           else putStrLn "No Matches"

buildMatchMenu pid work [] = menuPane [text:="No Matches"]
buildMatchMenu pid work matches
 = do mmenu <- menuPane [text:="Law Matches"]
      addMenuItem pid work matchMenuSize 1 mmenu matches

matchMenuSize = 20

addMenuItem pid work lmt i mmenu [] = return mmenu
addMenuItem pid work lmt i mmenu (mtch:mtchs)
  | i > lmt  =  return mmenu
  | otherwise  =  do buildMatchItem pid work mtch mmenu
                     addMenuItem pid work lmt (i+1) mmenu mtchs

buildMatchItem pid work (match@(_,_,name),mctxt) mmenu
 = do prf <- proofGet pid work
      let cpred = currProofPred prf
      mitem <- menuItem mmenu
                  [text:=(menuFormat name (summariseMatch mctxt cpred match))]
      set mitem [on command := doItemApply pid work (match,mctxt) cpred]

menuFormat name replacement
 = ljustify 30 name ++ "  ...  " ++ replacement

ljustify 0 str = str
ljustify n (c:cs) = c:(ljustify (n-1) cs)
ljustify n "" = replicate n ' '

summariseMatch mctxt cpred match@(rank,(mtype,prov,binds,sc,preds),name)
 = show (matchReplace mctxt match)
\end{code}

Code that does the work, applying the selected match:
\begin{code}
doItemApply pid work (match,mctxt) cpred
 = proofDo pid work dIA (nSP "doItemApply")
 where
  dIA _ pid pspace work
   = do let prf = currProof $ pspace
        let penv = context prf
        g <- goalParent $ proofGUI $ pspace
        let cptxt = "Current Focus: "++show (getPFocus cpred)
        (ok,fmatch@(r,(mt,p,b,_,_),n))
            <- finaliseMatch cptxt penv mctxt g match
        if ok
         then
          do --let mctxt = topMtchCtxt prf -- currently null !!!!!
             -- let mctxt = mkMatchContexts penv
             let apred = applyLaw mctxt fmatch cpred
             updateProof pid pspace work apred
                         (EQV,getPFocusPath apred,NamedLaw mt n p,b)
         else return ()
\end{code}

Commonly used match predicates:
\begin{code}
anyM, onlyTREqv, noTREqv :: (RankedMatch,MatchContext) -> Bool

anyM _ = True

onlyTREqv ((_,(TREqv,_,_,_,_),_),_) = True
onlyTREqv _                       = False

noTREqv   ((_,(TREqv,_,_,_,_),_),_) = False
noTREqv   _                       = True
\end{code}

\subsubsection{Existential Witness}

This implements the principle that
$$
 (\exists x @ P)
 \equiv
 ((\exists x @ P) \lor P[e/x])
$$
\begin{code}
hm_witness = (
    unlines $ [" : Existential witness\n",
    "Allows you to bring into existence an instance",
    "of some expression that is being quantified",
    "with the existential quantifier. ",
    "The law being applied is:",
    "(Exists xs | P(xs)) == P(xs)[ys / xs] \\/ (Exists xs | P(xs))",
    "You will be prompted to type in the ys in the expression above.\n",
    "Example:\n",
    "Imagine trying to prove:",
    "(Exists x, y, z | x /\\ y /\\ z)",
    "Immediately, you can see that the witness",
    "x, y, z = TRUE, TRUE, TRUE",
    "proves this proposition.",
    "To incorporate this insight into Saoithin and prove the theorem,",
    "you just press \'w\' and when prompted for substitution pairs, write:",
    "[TRUE/x, TRUE/y, TRUE/Z],",
    "In other words, substitute TRUE for every variable. Then you will get:",
    "TRUE /\\ TRUE /\\ TRUE \\/ (Exists x, y, z | x /\\ y /\\ z) =",
    "TRUE \\/ (Exists x, y, z | x /\\ y /\\ z) =",
    "TRUE."])

witnessIt pid work
 = proofDo pid work wtns (nSP "witnessIt")
 where
  wtns _ pid pspace work
   = do let prf = currProof pspace
        let penv = context prf
        mf <- goalParent (proofGUI pspace)
        wsubs@(Substn subs) <- getExprSubst penv mf "Witness Expressions"
        if null subs
         then return ()
         else do let cpred = currProofPred prf
                 let mctxt = topMtchCtxt prf
                 let cpred' = applyWitness mctxt (side prf) wsubs cpred
                 updateProof pid pspace work cpred'
                  (EQV,getPFocusPath cpred,Witness wsubs,nullBinds)
\end{code}

For a witness we need an expression substitution:
\begin{code}
getExprSubst penv mf caption
 = do vspec <- textDialog mf vmsg caption ""
      return (mkESubs penv vspec)
 where
   vmsg = "Enter expression substitution without enclosing braces"

mkESubs penv wspec
 = case result of
    Right (Esub _ sub) ->  sub
    _                  ->  Substn []
 where
   result = exprTextParser penv "<user>" ("0[ "++wspec++ " ]")
\end{code}


\subsubsection{Case/Branch Switch}

We need to be able to switch between branches of a proof:
\begin{code}
switchIt pid work
 = proofDo pid work sw (nSP "switchIt")
 where
   sw _ pid pspace work
    = do let prf = currProof pspace
         let (switched,prf') = caseSwitch prf
         if switched
          then do setAndCheckProofState notMatch pid pspace work (prf',noMatches)
                  repaintProofGUI pspace
          else return ()
\end{code}

\newpage
\subsubsection{Finalising a Match}

At this point a match has been singled out,
in a variety of ways,
by the user.
We now try to complete any missing match bindings by prompting the
user.
Returning an empty value in a dialogue,
or cancelling at any stage
aborts everything, as signalled by the boolean value returned.
Note that here, as we are in the IO monad,
we cannot use the Maybe monad to do failure.
\begin{code}
-- we handle only one replacement predicate at present.
finaliseMatch :: String -> TheoryStack -> MatchContext -> Window w
              -> RankedMatch -> IO (Bool,RankedMatch)

finaliseMatch toptxt theories mctxt mf
              match@( rank
                    , ( mtyp
                      , prov
                      , bnds@( gpbind, vebind, ttbind )
                      , sc
                      , [repl] )
                    , name )

  = do let pVarsInContext = predAllPVars repl
       let oVarsInContext = predAllOVars repl
       let tVarsInContext = zip (predAllTVars repl) (repeat VorT)

       (cont1,bnds1) <- foldM finalisePVars (True, bnds) pVarsInContext
       (cont2,bnds2) <- foldM finaliseOVars (cont1, bnds1) $ dbg "FINMATCH.ovarsInContext=" oVarsInContext
       (cont3,bnds3) <- foldM finaliseTVars (cont2, bnds2) tVarsInContext

       let (cont',bnds') = (cont3,bnds3)
       return ( cont'
              , ( rank
                , ( mtyp
                  , prov
                  , bnds'
                  , sc
                  , [repl] )
                , name ) )
\end{code}
\newpage
\begin{code}
  where
    rdisp = show repl
    user = "<user>"

    finalisePVars :: (Bool,Binding) -> (GenRoot,VContext) -> IO (Bool, Binding)
    finalisePVars
      = finaliseVar mf toptxt
          "Predicates over GenRoot"              -- what
          (map trieKey $ knownPreds mctxt)           -- known
          fst3                                   -- getSBind
          putfst3                                -- putSBind
          rdisp                                  -- rdisp
          genRootString                          -- vshow
          gpProj                                 -- projV
          (predTextParser theories user)         -- parseTO
          (predsTextParser theories user)        -- parseTSO
          (genRootTextParser user)               -- parseVO
          (genRootsTextParser user)              -- parseVSO

    finaliseOVars :: (Bool,Binding) -> (Variable,VContext) -> IO (Bool, Binding)
    finaliseOVars
      = finaliseVar mf toptxt
          "Expressions over Variable"            -- what
          ((map trieKey $ knownObs mctxt)
           ++(map trieKey $ knownExprs mctxt))   -- known
          snd3                                   -- getSBind
          putsnd3                                -- putSBind
          rdisp                                  -- rdisp
          varKey                                 -- vshow
          veProj                                 -- projV
          (exprTextParser theories user)         -- parseTO
          (exprsTextParser theories user)        -- parseTSO
          (varTextParser user)                   -- parseVO
          (varsTextParser user)                  -- parseVSO

    finaliseTVars :: (Bool,Binding) -> (TVar,VContext) -> IO (Bool, Binding)
    finaliseTVars
      = finaliseVar mf toptxt
          "Types over TVar"                      -- what
          []                                     -- known
          thd3                                   -- getSBind
          putthd3                                -- putSBind
          rdisp                                  -- rdisp
          id                                     -- vshow
          ttProj                                 -- projV
          (typeTextParser theories user)         -- parseTO
          (typesTextParser theories user)        -- parseTSO
          (tvarTextParser user)                  -- parseVO
          (tvarsTextParser user)                 -- parseVSO

-- finaliseMatch [repl]

finaliseMatch _ _ _ _ match = return (False,match)
\end{code}
\newpage
Function \texttt{finaliseVar} is the generic action that gets the user to specify
a variable, if needed:
\begin{code}
finaliseVar :: (Eq v, Eq t, Show v, Show t)
            => (Window w)                         -- mf
            -> String                             -- toptxt
            -> String                             -- what
            -> [Trie ()]                          -- known
            -> (Binding -> SBind v t)             -- getSBind
            -> (SBind v t -> Binding -> Binding)  -- putSBind
            -> String                             -- rdisp
            -> (v -> String)                      -- vshow
            -> (t -> Maybe v)                     -- projV
            -> (String -> Either String t)        -- parseTO
            -> (String -> Either String [t])      -- parseTSO
            -> (String -> Either String v)        -- parseVO
            -> (String -> Either String [v])      -- parseVSO
            -> (Bool, Binding)                    -- (cont,bind)
            -> (v,VContext)                       -- (v,vctxt)
            -> IO (Bool, Binding)

finaliseVar _ _ _ _ _ _ _ _ _ _ _ _ _ fb@(False,bind) _ = return fb

finaliseVar mf toptxt what known
            getSBind putSBind rdisp vshow projV parseTO parseTSO parseVO parseVSO
            cb@(cont,bind@(gpbind,vebind,ttbind)) (v,vctxt)
 =
  do
  let sbind = getSBind bind
  let vstr = vshow v
  case tlookup sbind vstr of
   Just _ -> return cb
   Nothing
    ->
    do
    case tslookup known vstr of
     Just _ -> return (cont,putSBind (tupdate vstr (VO v) sbind) bind)
     Nothing
      ->
      do
      (cont',sbind') <- askUserForBinding mf what background
                                          projV parseTO parseTSO parseVO parseVSO
                                          sbind vstr vctxt
      if cont'
       then return (cont',putSBind sbind' bind)
       else return (cont',bind)
 where
   background
    = unlines [ toptxt
              , ""
              , "Replacement: "++rdisp
              , "",
              "Bindings:"
               ++ lshow (  tshow gpbind
                        ++ tshow vebind
                        ++ tshow ttbind )
              , ""
              ]
   tshow :: Show t => Trie t -> [String]
   tshow = map pshow . flattenTrie
   pshow :: Show a => (String,a) -> String
   pshow (nm,thing) = '\n':nm ++ " |-> " ++ show thing
   lshow [] = " none."
   lshow tes = concat tes
\end{code}
\newpage
\begin{code}
askUserForBinding mf what background
                  projV parseTO parseTSO parseVO parseVSO
                  sbind vstr vctxt
 = do txt <- textDialog mf (background ++ instructions) what vstr
      if  (null txt)
       then return(False,sbind)
       else
        case (std,vctxt) of
          (True,VorT)    ->  reqBinding mf parseTO (updateTO projV vstr) sbind txt
          (True,Vonly)   ->  reqBinding mf parseVO (updateVO vstr) sbind txt
          (False,VorT)   ->  reqBinding mf parseTSO (updateTSO projV vstr) sbind $ clean txt
          (False,Vonly)  ->  reqBinding mf parseVSO (updateVSO vstr) sbind $ clean txt

 where
   std = isStdS vstr
   instructions
    = case vctxt of
        Vonly | std  ->  "Enter single variable:"
        Vonly        ->  ("Enter comma-sep variable list"++dotIsEmpty)
        VorT  | std  ->  "Enter single object:"
        VorT         ->  ("Enter comma-sep object list"++dotIsEmpty)
    where
      dotIsEmpty = "\n(Use a dot `.' to indicate an empty list):"
   clean txt = if txt == "." then "" else txt
\end{code}

\begin{code}
reqBinding mf parse update sbind txt
 = case parse txt of
    Left msg  ->  do errorDialog mf ("Invalid entry: "++txt) ("Parse Error\n"++msg)
                     return (False,sbind)
    Right thing
     -> case update thing sbind of
          Just sbind'  -> return (True, sbind')
          Nothing  -> do errorDialog mf ("Clashing entry: "++txt) "Update Error"
                         return (False,sbind)
\end{code}

\newpage
\subsection{General Proof Handling}

The following adds a proof-step:
\begin{code}
updateProof pid pspace work cpred jstfy
 = do let prf = currProof pspace
      let penv = context prf
      let (fpred,_) = fixFType penv cpred
      let prf' = addProofStep fpred jstfy prf
      setAndCheckProofState notMatch pid pspace work (prf',noMatches)
      repaintProofGUI pspace
\end{code}




\subsubsection{Undoing a proof step}
\begin{code}
undoProof pid work
 = proofDo pid work undo (nSP "undoProof")
 where
   undo _ pid pspace work
    = do let prf = currProof pspace
         let penv = context prf
         let (undone,plan') = undoStrategy (plan prf)
         if undone
          then do setAndCheckProofState notMatch pid pspace work (prf{plan=plan'},noMatches)
                  repaintProofGUI pspace
          else return ()
\end{code}

\subsubsection{Repainting Proof GUI}

\begin{code}
repaintProofGUI pspace
 = do let pgui = proofGUI pspace
      let mw = matchWindow pgui
      mwp <- fParent mw
      repaint mwp
      let gw = goalWindow pgui
      gwp <- fParent gw
      repaint gwp
\end{code}

\subsubsection{Repainting Theory Tab Window}

We want to refresh the theory when we are done
\begin{code}
repaintTheoryTabs thname work
 = do thfrms <- getThryFrames work
      case tlookup thfrms thname of
        Nothing -> return ()
        Just tw
         -> repaint (twFrame tw)
\end{code}



\newpage
\subsubsection{Printing Proof State}

Generic output top-level
\begin{code}
outputCurrProof :: (   String
                    -> Proof
                    -> Verbosity
                    -> StatusField
                    -> Window ()
                    -> Var WxState
                    -> IO ()
                   )            --  output
                -> String       --  what
                -> String       --  pid
                -> Var WxState  --  work
                -> IO ()
outputCurrProof output what pid work
 = proofDo pid work lcp (nSP what)
 where
   lcp _ _ pspace work
    = do let pgui = proofGUI pspace
         let sts = proofStatus pgui
         gw <- fParent (proofFrame pgui)
         let prf = currProof pspace
         let vb = verbosity pgui
         output (pname prf) prf vb sts gw work

\end{code}

Output in ASCII:
\begin{code}
writeCurrProof = outputCurrProof outputASCIIProof "writeCurrProof"

outputASCIIProof prfname prf vb sts f work
 = do (_,cwd) <- getCurrFS work
      resp <- fileSaveDialog f
               True True "Write Proof Script (ASCII Text)"
               [txtFiles,anyFiles] cwd $ fileNameClean prfname
      case resp of
        Nothing -> alert sts "no output file selected"
        (Just fname)
          -> do let text = proofStateScript vb prf
                writeFile fname (unlines text)
                note sts ("Proof of '"++prfname++"' written to "++fname)

\end{code}
Output in \LaTeX:
\begin{code}
latexCurrProof = outputCurrProof outputLaTeXProof "latexCurrProof"

outputLaTeXProof pid prf vb sts f work
 = do (_,cwd) <- getCurrFS work
      resp <- fileSaveDialog f
               True True "Write Proof Script (LaTeX)"
               [texFiles,anyFiles] cwd $ fileNameClean pid
      case resp of
        Nothing -> alert sts "no output file selected"
        (Just fname)
          -> do let mstk = context prf
                let prec = map precs mstk
                layout <- getLayout work
                let hyps = map laws (filter isHYP mstk)
                let text = pprint_proof hyps prec layout prf
                writeFile fname text
                note sts ("Proof of '"++pid++"' written to "++fname)
\end{code}

Diagnosis might be required:
\begin{code}

diagnoseProof pid work
 = proofDo pid work dgns (nSP "diagnoseProof")
 where
   dgns _ _ pspace work
    = do let diagnosis = proofDiagnosis (currProof pspace)
         gw <- fParent (proofFrame (proofGUI pspace))
         infoDialog gw "Diagnosis" diagnosis

\end{code}

\subsubsection{Predicate Pretty-Printing}

\begin{code}
latexifyTheory pid work
 = proofDo pid work pp (nSP "latexifyTheory")
 where
   pp pspaces pid pspace work
    = do topf <- getTop work
         sts <- getSts work
         name <- textDialog topf "Theory Pretty Print" "Enter Theory Name" ""
         if null name
          then alert sts "No theory name supplied"
          else
           do let pcr = thlookup name (context (currProof pspace))
              case pcr of
                Nothing    ->  alert sts ("No such theory "++name)
                (Just thry)  ->
                  do prec <- getPrec pid work
                     layout <- getLayout work
                     let pptxt = pprint_proofcontext prec layout thry
                     writeFile (name++".tex") pptxt
                     note sts ("Theory '"++name++"' pretty printed to "++name++".tex")

\end{code}

\LaTeX\ Configuration (t.b.d.).
\begin{code}
latexConfig work
 = do sts <- getSts work
      layout <- getLayout work
      alert sts "LaTeX Config NYI"
\end{code}



\subsubsection{Importing Predicates}

\begin{code}

importPredicate work
 = do topf <- getTop work
      warningDialog topf "DEPRECTAED" "Import Predicate no longer supported."
\end{code}
Not sure of the utility of the latter:
\begin{code}
exportPredicate pid work
 = proofDo pid work expPr (nSP "exportPredicate")
 where

   expPr pspaces pid pspace work
    = do let pgui = proofGUI pspace
         pf <- fParent (proofFrame pgui)
         let sts = proofStatus pgui
         (_,cwd) <- getCurrFS work
         resp <- fileSaveDialog pf
                  True True "Export Predicate"
                  [predFiles,anyFiles] cwd ""
         case resp of
           Nothing  ->  alert sts "Predicate export aborted: no file selected"
           (Just name)-> do prf <- proofGet pid work
                            let cpred = currProofPred prf
                            expPred sts name cpred

   expPred _ name fpr = writeFile name (dumpPred $ clearPFocus fpr)
\end{code}

\subsubsection{Importing/Exporting Proofs}

First versions that work with an already determined filename.
Reading in:
\begin{code}
readProof fname work
 = do txt <- readFile fname
      sts <- getSts work
      let (rep,plt) = loadPLT $! txt                           -- $
      case rep of
        ImportFail msg -> alert sts ("Proof import failed : "++msg)
        ImportOK
          -> do let (prf,spcs) = plt
                let pid = proofId prf
                ths <- getTheories work
                let (prf1,missing) = setProofTheories prf ths
                let penv' = context prf1
                let spcs' = fixSpecialTheories penv' prf1 spcs
                let prf2 = makeLive prf1
                pgui' <- createProofWindow pid work
                let pspace' = Proofspace prf2 noMatches pgui'
                currProofspaceCreate pid pspace' work
                setAndCheckProofState notMatch pid pspace' work (prf2,noMatches)
                report sts fname missing
 where
    gfn proof = (thname proof)++qualSep:(pname proof)
    report sts fname []  = note sts ("Proof imported from "++fname)
    report sts fname missing
      = alert sts ("Proof imported from "
                    ++ fname
                    ++ ", missing theories: "
                    ++ concat(intersperse "," missing))
\end{code}
Writing Out:
\begin{code}
writeProof pspace fname work
 = do let prf = currProof pspace
      let spcs = (takeWhile isSPC) (context prf)
      writeFile fname (dumpPLT (prf,spcs))
      sts <- getSts work
      note sts ("Proof exported to "++fname)
\end{code}
First, versions that engage in a file dialog:
\begin{code}
importProof work
 = do topf <- getTop work
      sts <- getSts work
      (_,cwd) <- getCurrFS work
      resp <- fileOpenDialog topf False True "Import Proof"
                   [proofFiles,anyFiles] cwd ""
      case resp of
        Nothing  ->  alert sts "Proof import aborted: no file selected"
        (Just fname)
          -> readProof fname work
\end{code}
\begin{code}
exportProof pid work
 = proofDo pid work exportPrf (nSP "exportProof")
 where
   exportPrf pspaces pid pspace work
    = do topf <- getTop work
         sts <- getSts work
         (_,cwd) <- getCurrFS work
         resp <- fileSaveDialog topf
                  True True "Export Proof"
                  [proofFiles,anyFiles] cwd ""
         case resp of
           Nothing  ->  alert sts "Proof export aborted: no file selected"
           (Just fname) -> writeProof pspace fname work
\end{code}
Now, versions that work with a standard name,
based on the \texttt{pid}.
\begin{code}
importUserProof pid work
 = proofDo pid work proofAlready proofImport
 where
   proofImport pid = readProof (pid++cruthu)

   proofAlready _ pid _ work
    = proofImportFailed pid "Proof with this ID already live." work


proofImportFailed pid msg work
  = do sts <- getSts work
       alert sts ("User-Proof '"++pid++"' Import Failed: "++msg)
\end{code}
\begin{code}
exportUserProof pid work
 = proofDo pid work exportUP (nSP "exportUserProof")
 where
   exportUP _ pid pspace = writeProof pspace (pid++cruthu)
\end{code}




\subsubsection{Abandoning a Proof}

\begin{code}
abandonProof pid work
 = do quitting <- fmap shuttingdown (varGet work)
      proofDo pid work (abandonPrf quitting) (nSP "abandonProof")
 where

   abandonPrf qttng pspaces pid pspace work
    = do let prff = proofFrame (proofGUI pspace)
         if qttng
          then xxx prff
          else
           do abandon <- confirmDialog prff "Abandon Proof"
                             "Are you sure you want to abandon ?"
                             False
              if abandon
               then xxx prff
               else return ()

   xxx prff
    = do windowDestroy prff
         unsetCurrprf work pid
         top <- getTop work
         repaint top
\end{code}

\newpage
\subsection{Viewing Laws by Structure}

This feature allows the user to type in an expression template
and get back all the laws that match.
If invoked from a theory, it sees all laws in that theory and those
lower than it in the hierarchy
(\texttt{mkMatchContexts}\texttt{.}\texttt{extractProofStack}).
If invoked from a proof it sees everything
the proof sees (\texttt{mtchCtxt}).
It also is intended to ignore side-conditions (how?)
\begin{code}
proofTemplateView pid work
 = proofDo pid work pTV (nSP "proofTemplateView")
 where
   pTV _ pid pspace work = templateViewFromProof (currProof pspace) work

templateViewFromProof :: Proof -> WxStateRef -> IO ()
templateViewFromProof proof work
 = templateLawView (context proof) work

templateViewFromTheory :: Theory -> WxStateRef -> IO ()
templateViewFromTheory theory work
 = do thrystack <- extractProofStack (thryName theory) work
      templateLawView thrystack work
\end{code}

The template based law viewer
is a window whose state tracks the template text
and the list of uncovered laws.
\begin{code}
type LawTemplateState
 = ( String    --  template string
   , String    --  error message
   , [LawTemplateMatch]  --  matched laws
   ) -- for now
\end{code}

The template viewing window itself:
\begin{code}
templateLawView :: [Theory] -> WxStateRef -> IO ()
templateLawView theories work
 = do let ctxthdrs = intercalate " | " (map thryName theories)

      tStyle <- getTextStyle work
      let tCol  = case tStyle of
                       Nothing -> defaultColour
                       Just st -> textCol st
      let tFont = case tStyle of
                       Nothing -> fontDefault
                       Just st -> textFont st
      bCol <- getBgColour work

      f <- frame [ text:="Template View [ "++ctxthdrs++" ]"
                 , bgcolor := bCol
                 , textColor := tCol
                 , font := tFont
                 ]

      txtp <- panel f [layout := vspace 25]
      txtc <- textEntry txtp []

      vp <- panel f []
      vw <- scrolledWindow vp []

      tvState <- varCreate ( ""  --  current template text
                           , ""  --  no errors
                           , []  --  current law-table
                           )

      set txtc [ on escKey := handleTemplateEntry theories tvState vw txtc
               ]

      set vw [ on paint := paintTemplateLaws tvState f vw work
             , on escKey := handleTemplateEntry theories tvState vw txtc
             , virtualSize := sz 1000 3000
             , scrollRate := sz 10 10
             , size := sz 400 700
             , bgcolor := bCol
             , textColor := tCol
             , font := tFont
             ]

      set f [ layout
                 :=
                 column 3
                   [ container txtp $ boxed "Law Template (ESC to submit)" $ hfill $ widget txtc
                   , container vp $ boxed "Matching Laws" $ fill $ widget vw
                   ]
            , outerSize := sz 500 800
            ]
\end{code}

When the enter key is pressed, we parse the line as a predicate,
and if acceptable, we use it to match against laws.
\begin{code}
handleTemplateEntry
  :: [Theory] -> Var LawTemplateState
     -> ScrolledWindow () -> TextCtrl ()
     -> IO ()
handleTemplateEntry theories tvState vw txtc -- key
 = do txt <- get txtc text
      let result = predTextParser theories "<TE>" txt
      case result of
        Left msg
         -> varSet tvState (txt, msg, [])
        Right pr
         -> matchTemplateEntry theories tvState vw txt pr
      repaint vw

matchTemplateEntry theories tvState vw txt pr
 = do let mtchs = templateLawMatchTheories pr theories
      varSet tvState (txt, "", sort mtchs)
\end{code}

Painting is straightforward:
\begin{code}
paintTemplateLaws tvState f vw work dc viewArea
 = do (ttxt,terr,mtchs) <- varGet tvState

      oldCol <- get dc textColor
      oldFont <- get dc font

      tStyle <- getTextStyle work
      let tCol  = case tStyle of
                       Nothing -> defaultColour
                       Just st -> textCol st
      let tFont = case tStyle of
                       Nothing -> fontDefault
                       Just st -> textFont st
      set dc [textColor := tCol]

      drawText dc terr (Point 10 10) []

      set dc [font:=tFont]

      drawMatches 30 mtchs

      set dc [textColor := oldCol]
      set dc [font := oldFont]

 where

   drawMatches _ [] = return ()
   drawMatches y ((mtyp,thn,lnm,ass):ms)
    = do let ln = show mtyp
                  ++ " - " ++ thn
                  ++ " $ " ++ lnm
                  ++ "   ...   " ++ show ass
         drawText dc ln (Point 10 y) []
         drawMatches (y+20) ms
\end{code}
