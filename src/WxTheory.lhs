\section{\UTP2\ Theory Operations}

\begin{code}
module WxTheory where
import Tables
import Precedences
import Datatypes
import DataText
import Types
import MatchTypes
import Laws
import Proof
import ProofReplay
import Theories
import Utilities
import Files
import ImportExport
import Archive
import DocTextParser
import LaTeXSetup
import DSL
-- import Focus

import System.IO
import Graphics.UI.WX
import Graphics.UI.WXCore

import Text.ParserCombinators.Parsec.Expr

import Data.List
import Data.Maybe
import Data.Char

import WxTypes
import WxState
import WxStyle
import WxRenderOld -- await new rendered
import WxProof
\end{code}

\subsection{Theory Table Notebook Tabs}

\subsubsection{Tabbed Theory Display}

We define string labels used to identify
tabbed windows internally, as well as one to indicate the single fixed window:
\begin{code}
type TabLbl = ( String -- short tag to identify tab
              , String -- explanatory label for tab
              )

typedefsLbl    = ("TD", "Type Definitions (TVar -+-> Type)" )
constsLbl      = ("CD", "Constant Definitions (Var -+-> Expr)" )
exprsLbl       = ("ED", "Expression Definitions (eVar -+-> Expr)" )
predsLbl       = ("PD", "Predicate Definitions (pVar -+-> Pred)" )
obsLbl         = ("OB", "Observation Variables (Var -+-> (Kind,Type))" )
langLbl        = ("LG", "Language Specification (Name -+-> LangSpec)" )
precsLbl       = ("OP", "Operator Precedences (Var -+-> Nat x Assoc)" )
typesLbl       = ("VT", "Variable Types (Var -+-> Type)" )
alphasLbl      = ("AL", "Predicate Alphabets (pVar -+-> Alpha)" )
lawsLbl        = ("LW", "Laws (Name -+-> SideCond x Pred)" )
conjecturesLbl = ("CJ", "Conjectures  (Name -+-> SideCond x Pred)" )
theoremsLbl    = ("TM", "Theorems (Name -+-> Proof)" )

allLbl         = ("A",  "Whole Theory (String -+-> whatever)" )

thTabRepaint tw lbl
 = case tlookup (twTabs tw) (fst lbl) of
     Nothing       ->  return ()
     (Just tabsw)  ->  repaint tabsw
\end{code}

\subsubsection{Generic Manipulation}

We first define a record datatype that contains
all the components needed to manipulate a generic entry:
\begin{description}
  \item[Label] A pair of strings used to identify and describe a table.
  \item[What] A string identifying the kind of entry to the user.
  \item[Display] A function to render an entry as a parseable string.
  \item[ShowAll] A function to show all information about an entry,
     with emphasis on what is missing from what appears in a parseable string.
  \item[Lookup] A function to lookup an entry by name in the relevant table.
  \item[Parser] A parser for the entry type.
  \item[Check] Something to check for non-syntactical errors
    in the entry type, often dependent on the theory context.
  \item[Prompt] A prompt to hint the user about what the parser expects.
  \item[FileType] A specification of the kinds of files containing entries.
  \item[New] A function to add a new entry to the relevant table,
   but which might also require supporting entries in other tables.
  \item[Upd] A function to update existing entry in the relevant table,
    also used to add new entries in simple cases.
  \item[Remove] A function to remove an existing entry from the relevant table.
  \item[Label] The label that identifies the notebook tab, for GUI refresh.
  \item[Table] An accessor that returns the \texttt{Trie} table from the theory
  \item[MkMenu] Code to build a table-specific menu
\end{description}
Most of these are pure functions that update relevant components,
once relevant information has been obtained via standard dialogs.
However, the \textbf{New} feature is more complex as some objects we want to
add will involve more than one table (e.g., language constructs).
For cases where addition is simple, then the \textbf{New} component
will just be a wrapper for \textbf{Add} component.
\begin{code}
data EntryActions t
 = EA { tWhat :: String
      , tDisplay :: t -> String
      , tShowAll :: t -> String
      , tLookup :: String -> Theory -> Maybe t
      , tParser :: [Theory] -> String -> String -> Either String t
      , tCheck  :: [Theory] -> t ->  Either String t
      , tPrompt :: String
      , tFileType :: FileTypeSpecifier
      , tNew :: String
                -> TheoryWidgets
                -> WxStateRef
                -> IO ()
      , tUpd :: String -> t -> Theory -> Theory
      , tRemove :: String -> Theory -> Theory
      , tLabel :: TabLbl
      , tTable :: Theory -> Trie t
      , tMkSpecificMenu :: Menu ()
                           -> String
                           -> TheoryWidgets
                           -> WxStateRef
                           -> Maybe (String, t)
                           -> IO ()
      }
\end{code}
For simple cases of adding,
we provide a wrapper.


\subsection{Theory Display Window}

Create a window as a view on a theory.
We support two ways of viewing a theory:
\begin{enumerate}
  \item
     Viewing each of the table components in its own tabbed window
     ---
     suitable for general theories with lots of entries in many tables.
  \item
     Viewing all contents in one window
     ---
     suitable for special (proof-local) theories with a few entries,
     but those likely to be of immediate interest.
\end{enumerate}
\begin{code}
data TheoryView = TabbedView | FlatView deriving (Eq,Show)
\end{code}

We then encapsulate tab definitions:
\begin{code}
tableTab tstype thname ea triesel work pan dblclk rhtclk
 = do c  <- getBgColour work
      tb <- panel pan []
      sw <- scrolledWindow tb []
      set sw [ on paint := paintTheoryTrie tstype thname tlabel triesel tdisplay work
             , on doubleClick := dblclk work
             , on clickRight := rhtclk work
             , virtualSize := sz 2000 5000
             , scrollRate := sz 20 20
             , size := sz 300 250
             , bgcolor := c
             ]
      return (tb,sw)
 where
    tdisplay = tDisplay ea
    tlabel   = tLabel   ea

nullClkHandler _ _    = return ()

tableTabNH tstype thname ea triesel work thp
 = tableTab tstype thname ea triesel work thp nullClkHandler nullClkHandler

tableTabRH tstype thname ea triesel work thp rhtclk
 = tableTab tstype thname ea triesel work thp nullClkHandler rhtclk

asnTableTab thname tlabel listsel work pan dblclk rhtclk
 = do tb <- panel pan []
      sw <- scrolledWindow tb []
      c  <- getBgColour work
      set sw [ on paint := paintTheoryAsns thname tlabel listsel work
             , on doubleClick := dblclk work
             , on clickRight := rhtclk work
             , virtualSize := sz 2000 5000
             , scrollRate := sz 20 20
             , size := sz 300 250
             , bgcolor := c
             ]
      return (tb,sw)

asnTableTabNH thname tlabel listsel work pan
 = asnTableTab thname tlabel listsel work pan nullClkHandler nullClkHandler

lawTableTab thname tlabel listsel work pan dblclk rhtclk
 = do tb <- panel pan []
      sw <- scrolledWindow tb []
      c  <- getBgColour work
      set sw [ on paint := paintTheoryLaws thname tlabel listsel work
             , on doubleClick := dblclk work
             , on clickRight := rhtclk work
             , virtualSize := sz 2000 5000
             , scrollRate := sz 20 20
             , size := sz 300 250
             , bgcolor := c
             ]
      return (tb,sw)
\end{code}

\subsubsection{Flat Theory Display}

Has been done (Karen Forde), and needs to be integrated in.


\subsubsection{Top-Level Theory Display}


Define top-level theory frame, panel and notebook
\begin{code}
viewTheory thry work
 = do c <- getBgColour work
      thf <- frame [ text := thryHdr
                   , closeable:=True
                   ]
      thsts <- statusField [text:=("Looking at "++thryHdr)]
      thp <- panel thf [bgcolor := c]
      thnb <- notebook thp []
\end{code}
Introduce all the tabs
\begin{code}
      (lawsTb,lawsSw) <- lawTableTab thname lawsLbl laws work thnb
                                nullClkHandler (handleLawRhtClick thname)

      (obsTb,obsSw)
        <- tableTabRH TSmulti thname obsActions obs work thnb
                                               (handleObsRhtClick thname)
      (langTb,langSw)
        <- tableTabRH TSmulti thname langActions lang work thnb
                                              (handleLangRhtClick thname)
      (precsTb,precsSw)
        <- tableTabRH TSmulti thname precActions precs work thnb
                                            (handlePrecsRhtClick thname)
      (typedefsTb,typedefsSw)
        <- tableTabRH TSmulti thname typedefActions typedefs work thnb
                                          (handleTypedefsRhtClick thname)
      (constsTb,constsSw)
        <- tableTabRH TSmulti thname constActions consts work thnb
                                            (handleConstsRhtClick thname)
      (exprsTb,exprsSw)
        <- tableTabRH TSmulti thname exprActions exprs work thnb
                                             (handleExprsRhtClick thname)
      (predsTb,predsSw)
        <- tableTabRH TSmulti thname predActions preds work thnb
                                             (handlePredsRhtClick thname)
      (typesTb,typesSw)
        <- tableTabRH TSmulti thname typeActions types work thnb
                                             (handleTypesRhtClick thname)

      (conjecturesTb,conjecturesSw)
        <- asnTableTab thname conjecturesLbl
                       (trieFlatten "" . conjectures) work
                       thnb (handleConjDblClick thname)
                       (handleConjRhtClick thname)

      (theoremsTb,theoremsSw)
        <- asnTableTab thname theoremsLbl
                       (map proofLaw . theorems)
                       work thnb nullClkHandler (handleThmRhtClick thname)
\end{code}

Put them all in the desired order
\begin{code}
      addThryFrame thf thsts
       (lbuild
         [ (fst lawsLbl,lawsSw)
         , (fst obsLbl,obsSw)
         , (fst langLbl,langSw)
         , (fst precsLbl,precsSw)
         , (fst typedefsLbl,typedefsSw)
         , (fst constsLbl,constsSw)
         , (fst exprsLbl,exprsSw)
         , (fst predsLbl,predsSw)
         , (fst typesLbl,typesSw)
         , (fst conjecturesLbl,conjecturesSw)
         , (fst theoremsLbl,theoremsSw)
         ])
\end{code}

Next, set up menus:
\begin{code}
      thryViewMenu <- menuPane [ text:="&View" ]

      itmSearch <- menuItem thryViewMenu
                       [ text:="&Search\tCtrl+S"
                       , help:="Search with Predicate template" ]
      set itmSearch [on command := templateViewFromTheory thry work]
\end{code}

Finally, set up overall layout
\begin{code}

      set thf  [ menuBar :=[thryViewMenu]
               , statusBar := [thsts]
               , layout
                 :=
                 container thp  $ margin 5 $ fill $
                   tabs thnb [ tab "LAWS" $ container lawsTb $ fill (widget lawsSw)
                             , tab "OBS." $ container obsTb $ fill (widget obsSw)
                             , tab "LANGUAGE" $ container langTb $ fill (widget langSw)
                             , tab "PRECEDENCE" $ container precsTb $ fill (widget precsSw)
                             , tab "TYPEdef" $ container typedefsTb $ fill (widget typedefsSw)
                             , tab "CONSTdef" $ container constsTb $ fill (widget constsSw)
                             , tab "EXPRdef" $ container exprsTb $ fill (widget exprsSw)
                             , tab "PREDdef" $ container predsTb $ fill (widget predsSw)
                             , tab "TYPES" $ container typesTb $ fill (widget typesSw)
                             , tab "CONJ." $ container conjecturesTb $ fill (widget conjecturesSw)
                             , tab "THEOREMS" $ container theoremsTb $ fill (widget theoremsSw)
                             ]
               , outerSize := sz 1000 600
               , bgcolor := c
               ]

 where
  thname = thryName thry
  thryHdr = "Theory '"++pcqname thry++"'"
  addThryFrame f s tbs
    = do thfms <- getThryFrames work
         setThryFrames work (tupdate thname tw thfms)
    where tw = TW f s tbs
\end{code}



\subsection{Theory (Tab) Rendering}

Trie-painting styles:
\begin{code}
data TrieStyle = TSinline  -- list on one line, comma separated
               | TSmulti -- list one per line
\end{code}

Painting a Theory Trie.
\begin{code}
paintTheoryTrie :: Show t
                => TrieStyle
                -> String
                -> TabLbl
                -> (Theory -> Trie t)
                -> (t -> String)
                -> Var WxState
                -> DC a
                -> s
                -> IO ()
\end{code}

First, inlining a table (names only, no definitions).
\begin{code}
paintTheoryTrie TSinline thname (ttag,thdr) triesel tdisplay work dc viewArea
 = do lresult <- doTheoryLookup thname work
      tStyle  <- getTextStyle work
      let trie = case lresult of
                   Nothing      ->  tnil
                   (Just thry)  ->  triesel thry
      let trieOrigin = (30,30)
      let inlineSpec = DrawChars tStyle (dtxt thdr trie)
      let inlineID = ImageDescr trieOrigin inlineSpec nullBB
      idvar <- setNamedImage thidname inlineID work
      paintSpec idvar dc viewArea
 where
   dtxt nm trie = nm++" : "++ concat (intersperse "," (trieDom trie))
   thidname = theoryIDName thname ttag
\end{code}

Secondly, one entry per line --- a static table
\begin{code}
paintTheoryTrie TSmulti thname (ttag,thdr) triesel tdisplay work dc viewArea
 = do lresult <- doTheoryLookup thname work
      let trie = case lresult of
                   Nothing      ->  tnil
                   (Just thry)  ->  triesel thry
      paintTheoryAList thname (ttag,thdr) (trieFlatten "" trie) tdisplay work dc viewArea


paintTheoryAList thname (ttag,thdr) list tdisplay work dc viewArea
 = do tStyle <- getTextStyle work
      let lawOrigin = (30,30)
      let tspecs = map (dpair tStyle) list
      let hdr = DrawChars tStyle thdr
      vtStyle <- getVtStyle work
      vStyle <- getVertStyle work
      let vtable = drawVTable vtStyle 2 DrawTight DrawTight True tspecs
      let multiSpec = DrawVert vStyle DrawCentre [hdr, vtable]
      let multiID = ImageDescr lawOrigin multiSpec nullBB
      idvar <- setNamedImage thidname multiID work
      paintSpec idvar dc viewArea

 where
   dpair tStyle (nm,thing) = [DrawChars tStyle nm,DrawChars tStyle (tdisplay thing)]
   thidname = theoryIDName thname ttag
\end{code}

Assertions have side-conditions we want to separate out:
\begin{code}
paintTheoryAsns thname (ttag,thdr) listsel work dc viewArea
 = do lresult <- doTheoryLookup thname work
      vtStyle <- getVtStyle work
      vStyle <- getVertStyle work
      tStyle <- getTextStyle work
      let lawlist = case lresult of
                   Nothing      ->  []
                   (Just thry)  ->  listsel thry
      let lawOrigin = (30,30)
      let lspecs = map (dtriple tStyle) lawlist
      let hdr = DrawChars tStyle thdr
      let vtable = drawVTable vtStyle 3 DrawTight DrawTight True lspecs
      let multiSpec = DrawVert vStyle DrawCentre [hdr,vtable]
      let multiID = ImageDescr lawOrigin multiSpec nullBB
      idvar <- setNamedImage thidname multiID work
      paintSpec idvar dc viewArea
 where
   dtriple tStyle (nm,(pr,sc))
     = [ DrawChars tStyle nm
       , DrawChars tStyle (show sc)
       , DrawChars tStyle (show pr)
       ]
   thidname = theoryIDName thname ttag
\end{code}
Laws have side-conditions and provenance we want to separate out:
\begin{code}

paintTheoryLaws thname (ttag,thdr) listsel work dc viewArea
 = do lresult <- doTheoryLookup thname work
      vtStyle <- getVtStyle work
      vStyle <- getVertStyle work
      tStyle <- getTextStyle work
      let lawlist = case lresult of
                   Nothing      ->  []
                   (Just thry)  ->  listsel thry
      let lawOrigin = (30,30)
      let lspecs = map (dquad tStyle) lawlist
      let hdr = DrawChars tStyle thdr
      let vtable = drawVTable vtStyle 4 DrawTight DrawTight True lspecs
      let multiSpec = DrawVert vStyle DrawCentre [hdr,vtable]
      let multiID = ImageDescr lawOrigin multiSpec nullBB
      idvar <- setNamedImage thidname multiID work
      paintSpec idvar dc viewArea
 where
   dquad tStyle (nm,((pr,sc),prov,ttbl))
     = [ DrawChars tStyle nm
       , DrawChars tStyle (shortProv prov)
       , DrawChars tStyle (show sc)
       , DrawChars tStyle (show pr)
       ]
   thidname = theoryIDName thname ttag
\end{code}

\subsubsection{Theory Names}

We build names from theories and tab labels
\begin{code}

theoryIDName thname ttag = thname ++ "|" ++ ttag

\end{code}

We need to be able to update named image variables
---
we simply look them up, add if missing,
and set the variable appropriately:
\begin{code}
setNamedImage name img work
 = do nimgs <- getNmdImages work
      (idvar,nimgs') <- getNamedImage nimgs name
      setNmdImages work nimgs'
      varSet idvar img
      return idvar

getNamedImage nimages name
 = case tlookup nimages name of
     (Just idvar)  ->  return (idvar,nimages)
     Nothing
       ->  do idvar <- varCreate nullID
              return(idvar,tupdate name idvar nimages)
\end{code}

\subsection{Table Click Selection}

A generic mechanism to identify a table row
given a mouse point,
assuming tables are as rendered for theory tabs.
\begin{code}
getClickedEntry thname label lkp work pnt
 = do ss <- varGet work
      let thidname = theoryIDName thname (fst label)
      let sts = case tlookup (theoryframes ss) thname of
                  Nothing    ->  topstatus ss
                  (Just tw)  ->  twSts tw
      let nimgs = namedimages ss
      case tlookup nimgs thidname of
        Nothing  ->  do scream work
                         ("Whoops ! Named ImageDescr not found : "++thidname)
                        return (sts,Nothing)
        (Just idvar)  ->  findSelectedRow thname idvar pnt sts lkp work

\end{code}

We now have the theory's image descr,
so see if we actually selected anything.
\begin{code}
findSelectedRow thname idvar pnt sts lkp work
 = do thidescr <- varGet idvar
      let thorig = iorigin thidescr
      let thspec = ispec thidescr
      let thbb   = ibb thidescr
      let (mx,my) = (pointX pnt,pointY pnt)
      case pointLookup (mx,my) thspec thbb thorig of
        Nothing    ->  return (sts,Nothing)
        (Just ix)  ->  locateRow thspec ix thname sts lkp work
\end{code}

We have selected something, so now is it a table row ?
We have two possibilities, tables with 2 or 3 columns,
but we should be able to handle most strictly positive values:
\begin{code}
locateRow (DrawVert _ _ (_:(DrawVTable _ k _ _ _ tspecs):_)) (2:n:_)
          thname sts lkp work
 | k > 0      =  lRow' k tspecs n thname sts lkp work
 | otherwise  =  return (sts,Nothing)

locateRow _ _ _ sts _ _ = return (sts,Nothing)
\end{code}

We then need to work out how an index-list
has to be converted to a row-number.
The following (note code !) sketches out the case when k=3:
{\small
\begin{verbatim}
 DrawVert _ [ DrawChars _ thdr           -- ix=[1]
            , drawVTable 3 _ _ _ tspecs  -- ix=(2:3n(+1,+2):_)
                                                            for nth entry
            ]
 We want the index of the first element
 of the selected tuple

 ix!!1         : 1 2 3 4 5 6 7 8 9 10 ...
 row-start ix  : 1 1 1 4 4 4 7 7 7 10 ...
\end{verbatim}
}
\begin{code}
kthindex k n = 1 + k * ((n-1) `div` k)

lRow' k tspecs n thname sts lkp work
 = do let m = kthindex k n
      case (concat tspecs) `tindex` m of
        Nothing -> return (sts,Nothing)
        (Just name) -> do pthing <- lookupThing thname name lkp work
                          case pthing of
                           Nothing       ->  return (sts,Nothing)
                           (Just thing)  ->  return (sts,Just (name,thing))
 where
   tindex [] _ = Nothing
   tindex ((DrawChars _ cs):rest) i
    | i <= 1     =  Just cs
    | otherwise  =  tindex rest (i-1)
   tindex _ _ = Nothing
\end{code}

We need to lookup the conjecture just selected:
\begin{code}
lookupThing thname oname lkp work
 = do lresult <- doTheoryLookup thname work
      case lresult of
        Nothing  ->  return Nothing
        (Just thry)  ->  return (lkp oname thry)
\end{code}

Given a tab, we can now tell if a click selects a table row or not.
The precise response to the click  depends on its type: left, right
or double (left).


\newpage
\subsection{Generic Right-Click Handling}

The actions to be taken can be at the table level
(no row need be selected), or can be entry specific, if a row is selected.
In each case, there are generic actions that apply regardless of the table type,
and type-specific actions that depend on what kind of entry we have:
theorem, type, conjecture, predicate-definition, whatever \ldots.
We can summarise this in tabular form:
\begin{center}
\begin{tabular}{|c|c|c|}
  \hline
  % after \\: \hline or \cline{col1-col2} \cline{col3-col4} ...
    & Generic & Specific \\\hline
  Table-Level & New, Load & e.g. Check proofs \\\hline
  Entry-Level & Delete, Edit, Print & e.g. Prove conjecture \\
  \hline
\end{tabular}
\end{center}
In general any menu we generate in response to a (right-) click
will display more specific entries first, and most general last,
with entry-level actions before table-level ones.


\subsubsection{Parameterised Right-Click Handler}

Given function to build a specific menu,
we do some basic consistency checking,
invoke the specific menu-builder,
add generic menu items
and then produce the pop-up for the user.
\begin{code}
handleTblRhtClick ea thname work pnt
 = do thryfs <- getThryFrames work
      case tlookup thryfs thname of
        Nothing    -> scream work
                            ("handleGenRhtClick with dud thname "++thname)
        (Just tw)  ->  showTblRhtClickMenu ea thname tw work pnt

\end{code}
Building the menu,
first requires us to establish if an entry has been selected,
create an appropriately titled empty menu,
and then to invoke the specific and generic menu builders
on top of it.
\begin{code}
showTblRhtClickMenu ea thname tw work pnt
 = do (sts,pthing) <- getClickedEntry thname lbl lkp work pnt
      menu <- startTblRhtClickMenu what pthing
      mkmenu menu thname tw work pthing
      buildGenEntryRhtClickMenu menu ea thname tw work pthing
      buildGenTblRhtClickMenu menu ea thname tw work
      menuPopup menu pnt (twFrame tw)
      thTabRepaint tw lbl
 where
  what = tWhat ea
  lbl  = tLabel ea
  lkp  = tLookup ea
  mkmenu = tMkSpecificMenu ea
\end{code}
The menu header mentions the entry-name, if one is selected.
\begin{code}
startTblRhtClickMenu what Nothing
                    = menuPane [text:=(what++" Handling")]
startTblRhtClickMenu what (Just (name,_))
                    = menuPane [text:="Handling "++what++" '"++name++"'"]
\end{code}
Adding generic entry-level actions (Edit, Delete, ShowAll)
\begin{code}
buildGenEntryRhtClickMenu menu ea thname tw work Nothing = return ()

buildGenEntryRhtClickMenu menu ea thname tw work (Just (name,thing))
 = do menuLine menu
      edtItm <- menuItem menu [text:="Edit"]
      set edtItm [on command := editEntry ea thname name thing tw work]
      delItm <- menuItem menu [text:="Delete"]
      set delItm [on command := deleteEntry ea thname name tw work]
      shwItm <- menuItem menu [text:="Show All"]
      set shwItm [on command := showAllEntry ea thname name thing tw work]
\end{code}
Adding generic table-level actions (New, Load, InScope)
\begin{code}
buildGenTblRhtClickMenu menu ea thname tw work
 = do menuLine menu
      newItm <- menuItem menu [text:=("New "++what)]
      set newItm [on command := (tNew ea) thname tw work]
      loadItm <- menuItem menu [text:=("Load "++what++" from file")]
      set loadItm [on command := loadEntry ea thname tw work]
      inscopeItm <- menuItem menu [text:="What's in scope?"]
      set inscopeItm [on command := inScope ea thname tw work]
 where
  what = tWhat ea
\end{code}
We also want to have a build-it-all facility for those tables
that only have generic actions.
We simply provide a specific menu builder that does nothing:
\begin{code}
mkNullSpecificMenu menu thname tw work pconj = return ()
\end{code}

\subsubsection{New Entry (Table-level Generic)}

We provide a number of generic ways to describe
a new entry:
\begin{description}
  \item[Simple] This is a simple mechanism that gets a name/value pair
  from the user and then uses the \textbf{Upd} facility, to enter that into
  the appropriate table.
  \item[Custom]
    This mechanism takes dialog code as a parameter,
    which itself returns a whole-theory update,
    which is then applied.
\end{description}

\paragraph{Simple Entry}

\begin{code}
newSimpleEntry ea thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing
        -> scream work ("New "++what++" with dud thname "++thname)
       (Just thry) ->
        do nname <- ttextDialog (twFrame tw) "Name" ("New "++what) ""
           if badEntryName lkp thry nname
            then alert (twSts tw) ("Name '"++nname++"' already in use")
            else
             do txt <- ttextDialog (twFrame tw)
                      prompt (what++" Text")  ""
                depTheories <- getAllThings id thname work
                putStr "depTheories = "
                putStrLn $ show $ map thryName depTheories
                let parser' = parser depTheories
                let parse = parser' ("New:"++what) txt
                case parse of
                 Left msg -> thryErr tw what "Parse failed" msg
                 Right presult
                  -> case chk depTheories presult of
                      Left msg -> thryErr tw what "Check failed" msg
                      Right thing
                       -> do let thry' = upd nname thing thry
                             let thry'' = raiseTheoryMod thry' Upgrade
                             doTheoryUpdate thname thry'' work
                             thTabRepaint tw lbl
                             note (twSts tw)
                              ("New "++what++" '"++nname++"' added")
 where
  what   = tWhat   ea
  lkp    = tLookup ea
  parser = tParser ea
  chk    = tCheck  ea
  prompt = tPrompt ea
  upd    = tUpd    ea
  lbl    = tLabel  ea

thryErr tw what hdg msg = errorDialog (twFrame tw) (what++" "++hdg) msg

badEntryName lkp thry "" = True
badEntryName lkp thry nm
 = case lkp nm thry of
    Nothing   ->  False
    (Just _)  ->  True
\end{code}

\paragraph{Custom Entry}
\begin{code}
newCustomEntry ea dialog thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("New "++what++" with dud thname "++thname)
       (Just thry) ->
        do thry' <- dialog thname thry tw work
           let thry'' = raiseTheoryMod thry' Upgrade
           doTheoryUpdate thname thry'' work
           thTabRepaint tw lbl
           note (twSts tw)
                ("New "++what++" added")
 where
  what = tWhat  ea
  lbl  = tLabel ea
\end{code}

\subsubsection{Load Entry (Table-level Generic)}

\begin{code}
loadEntry ea thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("loadEntry with dud thname "++thname)
       (Just thry) ->
        do nname <- ttextDialog (twFrame tw) "Name" (what++" Name") ""
           if badEntryName lkp thry nname
            then alert (twSts tw) ("Can't use name : '"++nname++"'")
            else
             do (_,cwd) <- getCurrFS work
                mfile <- fileOpenDialog (twFrame tw) True True
                              (what++" Text File")
                              [filetype,txtFiles,anyFiles] cwd ""
                case mfile of
                  Nothing  ->  return ()
                  Just fname
                   -> do txt <- readFile fname
                         depTheories <- getAllThings id thname work
                         let parse = parser depTheories fname txt
                         case parse of
                          Left msg ->  thryErr tw what "Parse failed" msg
                          Right presult
                           -> case chk depTheories presult of
                               Left msg -> thryErr tw what "Check failed" msg
                               Right thing
                                -> do let thry' = upd nname thing thry
                                      let thry'' = raiseTheoryMod thry' Upgrade
                                      doTheoryUpdate thname thry'' work
                                      thTabRepaint tw lbl
                                      note (twSts tw)
                                          ("New "++what++" '"++nname++"' added")
 where
  what     = tWhat ea
  lkp      = tLookup ea
  filetype = tFileType ea
  parser   = tParser ea
  chk      = tCheck ea
  upd      = tUpd ea
  lbl     = tLabel ea
\end{code}


\subsubsection{in-scope (Table-level Generic)}

Sometimes it is useful to see what is in scope in the current  tab,
i.e, in theories `lower down''.
\begin{code}
inScope ea thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("inScope with dud thname "++thname)
       (Just thry) ->
        do thrys <- getAllThings id thname work
           let report = scopeReport table thrys
           infoDialog (twFrame tw)
                      ("What's in scope for "++what)
                      report
 where
  what  = tWhat ea
  table = tTable ea

scopeReport :: Show t => (Theory -> Trie t) -> [Theory] -> String
scopeReport table thrys
 = concat $ intersperse "\n" $ map (thryReport table) thrys

thryReport :: Show t => (Theory -> Trie t) -> Theory -> String
thryReport table thry
 = thryName thry
   ++ "  :  "
   ++ (concat $ intersperse " " $ map (show . fst) $ flattenTrie $ table thry)
\end{code}



\subsubsection{Delete Entry (Entry-level Generic)}

\begin{code}

deleteEntry ea thname name tw work
 = do go_del <- confirmDialog (twFrame tw)
                  ("Delete "++what++" '"++name++"' ! Are you sure ?")
                  "Confirm Delete" False
      if go_del then do_del else return ()
 where
  what = tWhat ea
  remove = tRemove ea
  lbl = tLabel ea
  do_del
   = do lkpres <- doTheoryLookup thname work
        case lkpres of
          Nothing  ->  scream work ("deleteEntry with dud thname "++thname)
          (Just thry) ->
            do let thry' = remove name thry
               let thry'' = raiseTheoryMod thry' Upgrade
               doTheoryUpdate thname thry'' work
               thTabRepaint tw lbl
               note (twSts tw) (what++" '"++name++"' deleted")


\end{code}

\subsubsection{Edit Entry (Entry-level Generic)}

\begin{code}
editEntry ea thname name thing tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("editEntry with dud thname "++thname)
       (Just thry) ->
         do txt <- textDialog (twFrame tw)
                   prompt (what++" Text") (disp thing)
            depTheories <- getAllThings id thname work
            let parser' = parser depTheories
            let parse = parser' ("New:"++what) txt
            case parse of
             Left msg -> thryErr tw what "Parse failed" msg
             Right presult
              -> case chk depTheories presult of
                  Left msg -> thryErr tw what "Check failed" msg
                  Right thing
                   -> do let thry' = upd name thing thry
                         let thry'' = raiseTheoryMod thry' Upgrade
                         doTheoryUpdate thname thry'' work
                         thTabRepaint tw lbl
                         note (twSts tw)
                           (what++" '"++name++"' changed")
 where
  what = tWhat ea
  disp = tDisplay ea
  lkp = tLookup ea
  parser = tParser ea
  chk      = tCheck ea
  prompt = tPrompt ea
  upd = tUpd ea
  lbl = tLabel ea
\end{code}

\subsubsection{ShowAll Entry (Entry-level Generic)}

\begin{code}
showAllEntry ea thname name thing tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("showAllEntry with dud thname "++thname)
       (Just thry) ->
         infoDialog (twFrame tw)
                    ("Show All of "++what++" '"++name++"'")
                    (showall thing)
 where
  what = tWhat ea
  showall = tShowAll ea
\end{code}

\subsubsection{Generic Check}

The generic check always succeeds
\begin{code}
genericCheck _ res = Right res
\end{code}



\newpage
\subsection{Observation  Variables (Right-) Click Handling}
The right-click handler:
\begin{code}
handleObsRhtClick thname work pnt
 = handleTblRhtClick obsActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
obsActions
 = let ea = EA{ tWhat = "Obs. Var."
              , tDisplay = showKindType
              , tShowAll = show
              , tLookup = obsLkp
              , tParser = obsKindTextParser
              , tCheck = genericCheck
              , tPrompt = "type"
              , tFileType = typeFiles
              -- , tNew = newSimpleEntry ea
              , tNew = newCustomEntry ea newObsDialog
              , tUpd = upd_obs
              , tRemove = rem_obs
              , tLabel = obsLbl
              , tTable = obs
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea

newObsDialog thname thry tw work
 = do let twf = twFrame tw
      newobs <- ttextDialog twf "Variable Name" "New Obs-Var" ""
      let newvar@(nr,nd,_) = parseVariable newobs
      if badObsVar newvar || badEntryName obsLkp thry newobs
       then do warningDialog twf "Warning" ("Obs-Var '"++newobs++"' bad or in use")
               return thry
       else
        do typtxt <- ttextDialog
                      twf  "Variable Kind:Model/Script and Type - use 'M type' or 'S type'"
                           "New Obs-Var" ""
           depTheories <- getAllThings id thname work
           let parse = obsKindTextParser depTheories "" typtxt
           case parse of
            Left msg  ->  do warningDialog twf "Warning" ("invalid type: "++msg)
                             return thry
            Right (_,newk,newt) ->
             do let thry' = upd_obs newobs (newvar,newk,newt) thry
                if nd == Post
                 then return thry'
                 else
                  do let newobs' = newobs++"'"
                     dashit <- confirmDialog twf
                                 "Homogenise?"
                                 ("Add Obs-Var "++newobs'++" as well ?")
                                 True
                     if dashit
                      then return $ upd_obs newobs' ((nr,Post,newobs'),newk,newt) $ thry'
                      else return thry'

badObsVar (_,Pre,_)   =  False
badObsVar (_,Post,_)  =  False
badObsVar _           =  True
\end{code}


\newpage
\subsection{Type Definitions (Right-) Click Handling}
The right-click handler:
\begin{code}
handleTypedefsRhtClick thname work pnt
 = handleTblRhtClick typedefActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
typedefActions
 = let ea = EA{ tWhat = "Type Defn."
              , tDisplay = show
              , tShowAll = show
              , tLookup = typedefsLkp
              , tParser = typeTextParser
              , tCheck = genericCheck
              , tPrompt = "type"
              , tFileType = typeFiles
              , tNew = newSimpleEntry ea
              , tUpd = upd_typedefs
              , tRemove = rem_typedefs
              , tLabel = typedefsLbl
              , tTable = typedefs
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}

\newpage
\subsection{Constant Definitions (Right-) Click Handling}
The right-click handler:
\begin{code}
handleConstsRhtClick thname work pnt
 = handleTblRhtClick constActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
constActions
 = let ea = EA{ tWhat = "Constant (Var) Defn."
              , tDisplay = show
              , tShowAll = show
              , tLookup = constsLkp
              , tParser = exprTextParser
              , tCheck = genericCheck
              , tPrompt = "expr"
              , tFileType = exprFiles
              , tNew = newSimpleEntry ea
              , tUpd = upd_consts
              , tRemove = rem_consts
              , tLabel = constsLbl
              , tTable = consts
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}

\newpage
\subsection{Expression Definitions (Right-) Click Handling}
The right-click handler:
\begin{code}
handleExprsRhtClick thname work pnt
 = handleTblRhtClick exprActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
exprActions
 = let ea = EA{ tWhat = "Expression (eVar) Defn."
              , tDisplay = show
              , tShowAll = debugEshow
              , tLookup = exprsLkp
              , tParser = exprTextParser
              , tCheck = genericCheck
              , tPrompt = "expr"
              , tFileType = exprFiles
              , tNew = newSimpleEntry ea
              , tUpd = upd_exprs
              , tRemove = rem_exprs
              , tLabel = exprsLbl
              , tTable = exprs
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}

\newpage
\subsection{Predicate Definitions (Right-) Click Handling}
The right-click handler:
\begin{code}
handlePredsRhtClick thname work pnt
 = handleTblRhtClick predActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
predActions
 = let ea = EA{ tWhat = "Predicate (pVar)  Defn."
              , tDisplay = show
              , tShowAll = debugPshow
              , tLookup = predsLkp
              , tParser = predTextParser
              , tCheck = genericCheck
              , tPrompt = "pred"
              , tFileType = predFiles
              , tNew = newSimpleEntry ea
              , tUpd = upd_preds
              , tRemove = rem_preds
              , tLabel = predsLbl
              , tTable = preds
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}

\newpage
\subsection{Types (Right-) Click Handling}
The right-click handler:
\begin{code}
handleTypesRhtClick thname work pnt
 = handleTblRhtClick typeActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
typeActions
 = let ea = EA{ tWhat = "Type"
              , tDisplay = show
              , tShowAll = debugTshow
              , tLookup = typesLkp
              , tParser = typeTextParser
              , tCheck = genericCheck
              , tPrompt = "type"
              , tFileType = typeFiles
              , tNew = newSimpleEntry ea
              , tUpd = upd_types
              , tRemove = rem_types
              , tLabel = typesLbl
              , tTable = types
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}

\newpage
\subsection{Precedences (Right-) Click Handling}
The right-click handler:
\begin{code}
handlePrecsRhtClick thname work pnt
 = handleTblRhtClick precActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
precActions
 = let ea = EA{ tWhat = "Precedence"
              , tDisplay = precShorthand
              , tShowAll = show
              , tLookup = precsLkp
              , tParser = parsePrecShorthand
              , tCheck = genericCheck
              , tPrompt = "int L|R|N"
              , tFileType = precFiles
              , tNew = newSimpleEntry ea
              , tUpd = upd_precs
              , tRemove = rem_precs
              , tLabel = precsLbl
              , tTable = precs
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}
Printing precedences (shorthand):
\begin{code}
precShorthand (p,assoc) = show p ++ " " ++ assocShortHand assoc
assocShortHand AssocNone = "N"
assocShortHand AssocLeft = "L"
assocShortHand AssocRight = "R"
\end{code}
Parsing precedence shorthand:
\begin{code}
parsePrecShorthand _ _ txt
 | p == 0       =  fail
 | null rest'   =  fail
 | achr == 'N'  =  Right (p,AssocNone)
 | achr == 'L'  =  Right (p,AssocLeft)
 | achr == 'R'  =  Right (p,AssocRight)
 | otherwise    =  fail
 where
   (p,rest) = getnum 0 txt
   rest' = dropWhile isSpace rest
   achr = head rest'
   fail = Left ("invalid precedence shorthand : '"++txt++"'")
   getnum p "" = (p,"")
   getnum p str@(c:cs)
    | isDigit c  =  getnum (10*p+ord c - ord '0') cs
    | otherwise  =  (p,str)
\end{code}


\newpage
\subsection{Language Constructs (Right-) Click Handling}
The right-click handler:
\begin{code}
handleLangRhtClick thname work pnt
 = handleTblRhtClick langActions thname work pnt
\end{code}
We only handle right-clicks at present in this tab.
\paragraph{Specific Handling} None.
\paragraph{Generic Handling}
We define the entry-action details as follows:
\begin{code}
langActions
 = let ea = EA{ tWhat = "Language Spec."
              , tDisplay = show
              , tShowAll = debugLshow
              , tLookup = langLkp
              , tParser = langTextParser
              , tCheck = genericCheck
              , tPrompt = "lang-spec"
              , tFileType = langFiles
              -- , tNew = newSimpleEntry ea
              , tNew = newCustomEntry ea newLangDialog
              , tUpd = upd_lang
              , tRemove = rem_lang
              , tLabel = langLbl
              , tTable = lang
              , tMkSpecificMenu = mkNullSpecificMenu
              }
   in ea
\end{code}

The parser:
\begin{code}
langTextParser _ _ txt = parseLangSpec txt
\end{code}

A dialog to get a complete entry with supporting definitions
(e.g., precedence, definition)
\begin{code}
newLangDialog thname thry tw work
 = do let twf = twFrame tw
      newLName <- ttextDialog twf
                  "Construct Name (no spaces , will be replaced by dash !)" "New Language Construct" ""
      let newLName' = lmreplace dashForSpace newLName
      if badEntryName langLkp thry newLName'
       then do warningDialog twf
                 "Warning" ("Lang-construct '"++newLName'++"' bad or in use")
               return thry
       else
        do spctxt <- textDialog twf
                      "Lang Specifier"  "New Language Construct" ""
           depTheories <- getAllThings id thname work
           let parse = langTextParser depTheories "" spctxt
           case parse of
            Left msg  ->  do warningDialog twf
                               "Warning" ("invalid lang: "++msg)
                             return thry
            Right lspec -> checkAndInstallLang twf newLName' lspec

 where

   checkAndInstallLang twf newLName lspec
    = do okName <- checkAndApproveName twf newLName lspec
         let thry' = upd_lang okName lspec thry
         user <- fmap uname $ varGet work
         let (ldname,ldefn) = genDummyLangDefn user okName lspec
         let thry'' = upd_laws ldname ldefn thry'
         let extra1 = "Law: '"++ldname++"'"
         let (thry''',extra2) = handleBin okName lspec thry''
         infoDialog twf "Extras"
           (unlines [ "Also added to theory `"++thname++"':"
                    , extra1
                    , extra2]
           )
         return thry'''

   checkAndApproveName twf newLName lspec
    | not  $isBinSpec lspec     =  return newLName
    | newLName == approvedName  =  return newLName
    | otherwise
       = do warningDialog twf
              "Warning"
              (unlines [ "Infix name must match infix symbol"
                       , "Name supplied: `"++newLName++"'"
                       , "Approved Name: `"++approvedName++"'"
                       , "Using approved name."
                       ]
              )
            return approvedName
    where
      approvedName = theBinOpName lspec

   handleBin newLName lspec thry
     | isBinSpec lspec
        = (thry',"Prec : '"++newLName++"'")
     | otherwise  =  (thry,"")
     where
       thry' = upd_precs (theBinOpName lspec)
                         (precTightLang,AssocNone)
                         thry

-- end newLangDialog
\end{code}

We implement a key rule for language constructs,
namely that they cannot contain spaces.
We fix such a name by changing them into dashes:
\begin{code}
dashForSpace ' '  =  Just '-'
dashForSpace _    =  Nothing
\end{code}


\newpage
\subsection{Conjecture Click Handling}


\subsubsection{Conjectures Right-Click Handling}

Conjecture right-click handler:
\begin{code}
handleConjRhtClick thname work pnt
 = handleTblRhtClick conjActions thname work pnt
\end{code}

\paragraph{Specific Handling}
On a right-click, if an entry is selected,
we offer the chance to prove or refute it.
We have no table-level specific handling for conjectures at present.
\begin{code}
mkConjSpecificMenu menu thname tw work pconj
 = mkConjEntryMenu menu thname tw work pconj

mkConjEntryMenu  menu thname tw work Nothing = return ()

mkConjEntryMenu  menu thname tw work (Just (cjname,(pred,sc)))
 = do let sts = twSts tw
      prvCjItm <- menuItem menu [text:="Prove"]
      set prvCjItm [on command := startProof thname cjname pred sc  work]
      refCjItm <- menuItem menu [text:="Refute"]
      set refCjItm [on command := startProof thname nmnot npred sc work]
 where
   nmnot = cjname++"-NOT!"
   npred = Not pred
\end{code}

\paragraph{Specific Checking}

For a conjecture, we run well-formedness and type checks:
\begin{code}
conjectureCheck thrys asn@(pred,_)
 | not qvsOk        =  Left "QVar invariant fails!"
 | not subOk        =  Left "ESubst invariant fails!"
 | not $ null msgs  =  Left $ typeErrorDetails pred' msgs tts
 | otherwise        =  Right asn
 where
   mctxt = mkMatchContext thrys
   qvsOk =  predQVarInv mctxt pred
   subOk =  predESubstInv mctxt pred
   (pred',tts,msgs) = setPredTypes mctxt pred
\end{code}


\paragraph{Generic Handling}
We define the conjecture entry-action details as follows:
\begin{code}
conjActions
 = let ea = EA{ tWhat = "Conjecture"
              , tDisplay = showAssertion
              , tShowAll = debugAshow
              , tLookup = conjecturesLkp
              , tParser = asnTextParser
              , tCheck = conjectureCheck
              , tPrompt = "pred [ ,- sidecond;sidecond ]"
              , tFileType = conjFiles
              , tNew = newSimpleEntry ea
              , tUpd = addConjecture
              , tRemove = remConjecture
              , tLabel = conjecturesLbl
              , tTable = conjectures
              , tMkSpecificMenu = mkConjSpecificMenu
              }
   in ea
\end{code}


\subsubsection{Conjecture Entry Identification}

We need to be able to get the clicked entry, if any.
\begin{code}
getClickedConjecture thname work pnt
 = getClickedEntry thname conjecturesLbl conjecturesLkp work pnt
\end{code}

\subsubsection{Conjecture Double-Click Handling}

Handling a double-click on a conjecture
--- set up as a proof, after checking for an existing one.
\begin{code}
handleConjDblClick thname work pnt
 = do (sts,pconj) <- getClickedConjecture thname work pnt
      case pconj of
        Nothing  -> return ()
        (Just (cjname,(pred,sc)))
          ->  startProof thname cjname pred sc work
\end{code}



\subsubsection{Add In Law}

\begin{code}
addInLaw :: String -> Theory -> String -> Pred -> SideCond
         -> (String -> Law -> LawTable -> LawTable)
         -> TheoryWidgets -> WxStateRef -> IO ()
addInLaw thname thry lname pred sc lwmod tw work
 = do thgrf <- getThgrf work
      let penv = hardGraphToStack thname thgrf
      let mctxt = mkMatchContext (thry:penv)
      if not (predQVarInv mctxt pred)
       then errorDialog (twFrame tw)
                        "Ill Formed Law Predicate"
                        ("A quantifier-list in\n\n   "
                          ++show pred
                          ++"\n\nis ill-formed:\nduplicates,overlaps...")
       else
         if not (predESubstInv mctxt pred)
          then errorDialog (twFrame tw)
                        "Ill Formed Law Predicate"
                        ("A substituion in\n\n   "
                          ++show pred
                          ++"\n\nis ill-formed:\nduplicates,overlaps...")
          else
           do let (pred',tts,msgs) = setPredTypes mctxt pred
              if null msgs
               then addInLaw' thname thry lname pred' sc tts lwmod tw work
               else errorDialog (twFrame tw)
                                "Type Error in Law"
                                (typeErrorDetails pred msgs tts)

addInLaw' thname thry lname pred sc tts lwmod tw work
 = do user <- getUser work
      let prov = FromUSER user
      let law' = ((pred,sc),prov,tts)
      let thry' = thry{laws=lwmod lname law' (laws thry)}
      let thry'' = raiseTheoryMod thry' Upgrade
      doTheoryUpdate thname thry'' work
      thTabRepaint tw lawsLbl
      note (twSts tw)
           ("Law '"++lname++"' added/revised")
\end{code}

\subsubsection{New/Load Law}

\begin{code}
newLaw thname work
 = do thryfs <- getThryFrames work
      sts <- getSts work
      case tlookup thryfs thname of
        Nothing    ->  scream work ("newLaw with dud thname "++thname)
        (Just tw)  ->  do newLaw' thname tw work

newLaw' thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("newLaw' with dud thname "++thname)
       (Just thry) ->
        do nname <- ttextDialog (twFrame tw) "Name" "Law Name" ""
           if badLWname thry nname
            then alert (twSts tw) ("Can't use name : '"++nname++"'")
            else
             do lawtxt <- textDialog (twFrame tw)
                            "pred [ ,- sidecond;sidecond ]" "Law Text"  ""
                depTheories <- getAllThings id thname work
                let parser = asnTextParser depTheories
                let parse = parser "New-Law" lawtxt
                case parse of
                 Left msg  ->  alert (twSts tw) ("Predicate Parse failed: "++msg)
                 Right (pred,sc)
                  -> addInLaw thname thry nname pred sc lwadd tw work

badLWname thry "" = True
badLWname thry nm
 = case alookup (laws thry) nm of
    Nothing   ->  False
    (Just _)  ->  True
\end{code}
\begin{code}
readLaw thname work
 = do thryfs <- getThryFrames work
      sts <- getSts work
      case tlookup thryfs thname of
        Nothing    ->  scream work ("loadLaw with dud thname "++thname)
        (Just tw)  ->  do readLaw' thname tw work

readLaw' thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("newLaw' with dud thname "++thname)
       (Just thry) ->
        do nname <- ttextDialog (twFrame tw) "Name" "Law Name" ""
           if badLWname thry nname
            then alert (twSts tw) ("Can't use name : '"++nname++"'")
            else
             do (_,cwd) <- getCurrFS work
                mcjfile <- fileOpenDialog (twFrame tw) True True
                              "Law Text File"
                              [conjFiles,txtFiles,anyFiles] cwd ""
                case mcjfile of
                  Nothing  ->  return ()
                  Just cjfname
                   -> do predtxt <- readFile cjfname
                         depTheories <- getAllThings id thname work
                         let parser = asnTextParser depTheories
                         let parse = parser cjfname predtxt
                         case parse of
                          Left msg    ->  alert (twSts tw) ("Law Parse failed: "++msg)
                          Right (pred,sc)
                           -> addInLaw thname thry nname pred sc lwadd tw work
\end{code}

\subsubsection{Law Edit}

\begin{code}
editLaw thname lname work
 = do thryfs <- getThryFrames work
      sts <- getSts work
      case tlookup thryfs thname of
        Nothing    ->  scream work ("editLaw with dud thname "++thname)
        (Just tw)  ->  do editLaw' thname lname tw work

editLaw' thname lname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("editLaw' with dud thname "++thname)
       (Just thry) ->
         case alookup (laws thry) lname of
           Nothing -> scream work ("editLaw: Can't find law named : '"++lname++"'")
           Just ((pr,sc),_,_)
            ->
             do let oldtxt = show pr ++ " ,- " ++ show sc
                lawtxt <- textDialog (twFrame tw)
                            "pred [ ,- sidecond;sidecond ]" "Law Text"  oldtxt
                depTheories <- getAllThings id thname work
                let parser = asnTextParser depTheories
                let parse = parser "Edit-Law" lawtxt
                case parse of
                 Left msg  ->  alert (twSts tw) ("Predicate Parse failed: "++msg)
                 Right (pred',sc')
                  -> addInLaw thname thry lname pred' sc' lwupdate tw work
\end{code}


\subsubsection{Law Delete}


\textbf{This should really only work for user-specified laws.}

\begin{code}
delLaw thname lname work
 = do thryfs <- getThryFrames work
      sts <- getSts work
      case tlookup thryfs thname of
        Nothing    ->  scream work ("delLaw with dud thname "++thname)
        (Just tw)  ->  do delLaw' thname lname tw work

delLaw' thname lname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("delLaw' with dud thname "++thname)
       (Just thry) ->
        do let twf = twFrame tw
           proceed <- confirmDialog twf "Confirm Delete"
                                    ("Do you really want to delete '"
                                     ++lname++"'")
                                    False
           if proceed
            then
             do let thry' = thry{laws=lwdelete lname (laws thry)}
                let thry'' = raiseTheoryMod thry' Upgrade
                doTheoryUpdate thname thry'' work
                thTabRepaint tw lawsLbl
                alert (twSts tw)
                     ("Law '"++lname++"' deleted")
            else
              return ()
\end{code}

\subsubsection{Law Show}

\begin{code}
showAllLaw thname lname work
 = do thryfs <- getThryFrames work
      sts <- getSts work
      case tlookup thryfs thname of
        Nothing    ->  scream work ("showAllLaw with dud thname "++thname)
        (Just tw)  ->  do showAllLaw' thname lname tw work

showAllLaw' thname lname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("showAllLaw' with dud thname "++thname)
       (Just thry) ->
         case alookup (laws thry) lname of
           Nothing   ->  scream work ("editLaw: Can't find law named : '"++lname++"'")
           Just law  ->  showAllLawDialog (twFrame tw) lname law

showAllLawDialog f lname ((pr,sc),prov,tts)
 = infoDialog f
              ("Show All for Law '"++lname++"'")
              (shAllLaw pr sc prov tts)

shAllLaw pr sc prov tts
 = "PREDICATE(" ++ show prov ++ ")" ++ dbgPshow 3 pr
   ++ "\nSIDE-CONDITION" ++ dbgSCshow 3 sc
   ++ "\nTYPE-TABLES\n" ++ showAllTTS 3 tts
\end{code}

\subsubsection{Load Conjecture}


\begin{code}

-- will go once read is made generic
badCJname thry "" = True
badCJname thry nm
 = case tlookup (conjectures thry) nm of
    Nothing   ->  False
    (Just _)  ->  True


readConj thname work
 = do thryfs <- getThryFrames work
      sts <- getSts work
      case tlookup thryfs thname of
        Nothing    ->  scream work ("readConj with dud thname "++thname)
        (Just tw)  ->  do readConj' thname tw work

readConj' thname tw work
 = do lkpres <- doTheoryLookup thname work
      case lkpres of
       Nothing  ->  scream work ("readConj' with dud thname "++thname)
       (Just thry) ->
        do nname <- ttextDialog (twFrame tw) "Name" "Conjecture Name" ""
           if badCJname thry nname
            then alert (twSts tw) ("Can't use name : '"++nname++"'")
            else
             do (_,cwd) <- getCurrFS work
                mcjfile <- fileOpenDialog (twFrame tw) True True
                              "Conjecture Text File"
                              [conjFiles,txtFiles,anyFiles] cwd ""
                case mcjfile of
                  Nothing  ->  return ()
                  Just cjfname
                   -> do predtxt <- readFile cjfname
                         depTheories <- getAllThings id thname work
                         let parser = asnTextParser depTheories
                         let parse = parser cjfname predtxt
                         case parse of
                          Left msg    ->  alert (twSts tw) ("Conjecture Parse failed: "++msg)
                          Right (pred,sc)
                           ->  do let thry' = addConjecture nname (pred,sc) thry
                                  let thry'' = raiseTheoryMod thry' Log
                                  doTheoryUpdate thname thry'' work
                                  thTabRepaint tw conjecturesLbl
                                  note (twSts tw)
                                       ("New Conjecture '"++nname++"' added")

\end{code}


%\subsubsection{Predicate Building Dialog}
%This version will provide a dialog to allow a conjecture to be ``built''
%in a structured way:
%\begin{code}
%
%buildNewConj thname work
% = do mf <- matchWindowGet work
%      sts <- proofStatusGet work
%      mconj <- predDialog mf
%      case mconj of
%        Nothing       ->  alert sts "no conjecture given"
%        (Just nconj)  ->  alert sts ("Got: ( "++show nconj++" ), but new Conjecture N.Y.f.I.")
%
%\end{code}
%We define a predicate building dialog:
%\begin{code}
%
%predDialog mf
%  = do d <- dialog mf [text := "Build Predicate"]
%       okb  <- button d [text := "Ok"]
%       showModal d (endDialog okb)
%  where
%    endDialog okb stop
%      = set okb [on command := stop (Just nonsense)]
%
%\end{code}


\subsection{Theorems Right-Click Handling}

\begin{code}
getClickedTheorem thname work pnt
 = getClickedEntry thname theoremsLbl theoremsLkp work pnt
\end{code}

On a right-click, we offer the option outputting
a proof to a file, in ASCII or \LaTeX\ formats.
\begin{code}

handleThmRhtClick thname work pnt
 = do thryfs <- getThryFrames work
      case tlookup thryfs thname of
        Nothing    ->  scream work
                            ("handleThmRhtClick with dud thname "++thname)
        (Just tw)  ->  handleThmRhtClick' thname tw work pnt


handleThmRhtClick' thname tw work pnt
 = do (sts,pthm) <- getClickedTheorem thname work pnt
      case pthm of
         Nothing  -> buildThryRhtClickMenu thname tw work pnt
         (Just (prfname,prf))
           -> buildThmRhtClickMenu thname prfname prf tw work pnt
\end{code}

Building the menus
(Note here we pay for having \texttt{Verbosity}
 as a \texttt{proofGUI} specific component,
rather than a global program attribute)
\begin{code}
buildThryRhtClickMenu thname tw work pnt
 = do thryRMenu <- menuPane [text:=thryHdr]

      let f = twFrame tw
      let sts = twSts tw

      prfReplayAll <- menuItem thryRMenu [text:=("Replay all proofs")]
      set prfReplayAll [on command := runProofsReplay thname f work]

      prfCheckAll <- menuItem thryRMenu [text:=("Check all proofs")]
      set prfCheckAll [on command := runTheoremsCheck thname f work]


      menuPopup thryRMenu pnt f
      thTabRepaint tw theoremsLbl
 where
    thryHdr = "Theory \171"++thname++"\187"


buildThmRhtClickMenu thname prfname prf tw work pnt
 = do thmRMenu <- menuPane [text:=thmHdr]

      let f = twFrame tw
      let sts = twSts tw

      prfASCIIitm <- menuItem thmRMenu [text:=("Output to text File")]
      set prfASCIIitm [on command := outputASCIIProof prfname prf succinct sts f work]

      prfLaTeXitm <- menuItem thmRMenu [text:=("Output to LaTeX File")]
      set prfLaTeXitm [on command := outputLaTeXProof prfname prf succinct sts f work]

      prfShowPrfCites <- menuItem thmRMenu [text:=("Show Citations (this proof)")]
      set prfShowPrfCites [on command := showCites thname [prf] work]

      prfSummarise <- menuItem thmRMenu [text:=("Summarise (this proof)")]
      set prfSummarise [on command := summariseProof thname prf sts f work]

      prfReplay <- menuItem thmRMenu [text:=("Replay this proof")]
      set prfReplay [on command := runProofReplay thname prf f work]

      prfRedo <- menuItem thmRMenu [text:=("Redo this proof")]
      set prfRedo [on command :=  redoProofs thname prf work]

      prfUndo <- menuItem thmRMenu [text:=("Undo this proof")]
      set prfUndo [on command := undoTheorem thname prf f work]

      menuPopup thmRMenu pnt f
      thTabRepaint tw theoremsLbl

 where
    thmHdr = "Theorem \171"++prfname++"\187"
             ++ " (by "++(prover prf)
             ++  ",length:"++show (proofLength prf)++")"
\end{code}

Redoing Proofs
\begin{code}
redoProofs thname prf work
 = startProof thname cjname pred sc work
   where
       cjname = pname prf
       pred = goal prf
       sc = side prf
\end{code}

Showing citations
\begin{code}
showCites thname prfs work
 = do f <- frame [text:="Proof Citations"]
      p <- panel f []
      sw <- scrolledWindow p []
      set sw [ on paint := paintCiteLines (head(organiseCites thname prfs))
             , virtualSize := sz 500 800
             , scrollRate := sz 10 10
             , size := sz 300 250
             ]
      set f [ layout
              := container p $ margin 5 $ fill $ widget sw
            ]
\end{code}

Organising (sorting/grouping) citations:
\begin{code}
organiseCites thname prfs = map (groupSortCites.proofCites thname) prfs

groupSortCites = (groupBy groupCitation).(sortBy sortCitation)

sortCitation :: Citation -> Citation -> Ordering
sortCitation ((thynm,_),_) ((thynm', _),_)
    | thynm >= thynm' = LT
    | otherwise = GT

groupCitation :: Citation -> Citation -> Bool
groupCitation ((thynm,thyId),_) ((thynm', thyId'),_)
    | (thynm == thynm')  && (thyId == thyId') = True
    | otherwise = False
\end{code}


Printing citations:
\begin{code}
paintCiteLines citations dc viewArea
 = do (fSize,fDesc,fLead) <- getFullTextExtent dc "m"
      let (emH,emW) = (sizeH fSize,sizeW fSize)
      let baselineskip = emH + fDesc + fLead
      printCitations dc baselineskip baselineskip emW citations

printCitations dc bs v h [] = return ()
printCitations dc bs v h (cite:cites)
 = do  let (thnm,thno) = (fst.head) cite
       drawText dc (thnm ++ thrySepS++show thno) (pt h v) []
       y <- printSecond dc bs (v+20) (h+20) cite
       printCitations dc bs (y+20) h cites

printSecond dc bs v h [] = return (v)
printSecond dc bs v h (c:cs)
 = do let x = snd c
      drawText  dc x (pt h v) []
      printSecond dc bs (v+20) h cs
\end{code}


Summarising a proof:
\begin{code}
summariseProof thname prf sts f work
 = do let fname = pname prf ++ ".txt"
      let hash = hashProof prf
      let summary
           = thname++thrySepS++pname prf
             ++ " | " ++ prover prf ++ " | " ++ hash
             ++ "\n" ++ (show (goal prf)) ++ " ,- " ++ (show (side prf))
      writeFile fname summary
      infoDialog f "Summary" ("Proof '"++pname prf++"' summarised in "++fname)
\end{code}

\newpage
\subsection{Replaying Proofs}

We want to be able to replay proofs,
expecially when theories are under development,
with non-monotonic changes being made,
as well as during the development of this software,
as a form of regression testing.
\begin{code}
runProofReplay :: String -> Proof -> Frame () -> WxStateRef -> IO ()
runProofReplay thname origPrf f work
 = do penv <- extractProofStack thname work
      let (report,repPrf) = calcProofReplay penv thname origPrf
      infoDialog f
         ("Replayed Proof '" ++ thname ++ thrySepS ++ (pname origPrf) ++ "'" )
         (show report)

calcProofReplay penv thname origPrf
 = let cjname = pname origPrf
       pred = goal origPrf
       sc = side origPrf
       repPrf =  makeProof thname cjname pred sc penv "ProofReplay"
   in  replayProof origPrf repPrf
\end{code}

\begin{code}
runProofsReplay :: String -> Frame () -> WxStateRef -> IO ()
runProofsReplay thname f work
 = do proofs <- theoremsGet thname work
      penv <- extractProofStack thname work
      let reps = map (calcProofReplay penv thname) proofs
      let stack = "Stack : "
                    ++ (concat $ intersperse " | " $ map thryName penv)
      let faillist = filter failures $ map fst reps
      infoDialog f
        ("Replayed Proofs in '" ++ thname ++ "'" )
        (unlines $ (stack:) $ (summary faillist:) $ map show faillist)
 where
   failures (RRS cont _) = not cont
   summary [] = "\nALL OK\n"
   summary fs = "\nFAILED: "++show (length fs) ++ "\n"
\end{code}

\subsection{Undoing Theorems}

In the event that a proof replay fails,
we might want to undo a theorem: remove it from theorems and laws,
and reinstate it in conjectures.
We perform an impact analysis (in the current theory only)
an ask if we wish to proceed.
\begin{code}
undoTheorem :: String -> Proof -> Frame () -> WxStateRef -> IO ()
undoTheorem thname prf f work
 = do ok <- confirmDialog f ("Undo Theorem "++prfname)
                            (unlines
                              [ "Impact Analysis isn't implemented yet."
                              , "This might break other theorems !"
                              , "Are you sure you want to do this ?"
                              ] )
                            False
      if ok
       then do thgrfSetf (removeTheorem thname prfname) work
               repaint f
       else return ()
 where prfname = pname prf

removeTheorem :: String -> String -> TheoryGraph -> TheoryGraph
removeTheorem thname pnm tg@(rdag, trie)
 = case tlookup trie thname of
     Nothing    ->  tg
     Just thry  ->  (rdag, tupdate thname (fromThmToConj pnm thry) trie)

fromThmToConj pnm thry
 = case clookup pname id thms pnm of
    Nothing   ->  thry
    Just prf  ->  thry{ theorems = filter (notP pnm) thms
                      , conjectures = tupdate pnm (proofAssertion prf) conjs
                      , modified = Log }
 where
   thms = theorems thry
   conjs = conjectures thry
   notP n prf = n /= pname prf
\end{code}

\subsection{Checking Theorems}

We want to check that a proof as theorem and law are consistent
(same predicate, modulo top-level universal quantifiers).
\begin{code}
runTheoremsCheck :: String -> Frame () -> WxStateRef -> IO ()
runTheoremsCheck thnm f work
 = do thry <- namedTheoryGet thnm work
      let results = theoremCheck thry
      if null results
       then
         infoDialog f hdr "ALL MATCH OK"
       else
         infoDialog f hdr
           $ unlines ([ "MISMATCHES FOUND", "" ] ++ results)
 where hdr = "Checked Proofs in '" ++ thnm ++ "'"
\end{code}



\newpage
\subsection{Law Right-Click Handling}

\begin{code}
handleLawClick thname work pnt
 = do ss <- varGet work
      let thidname = theoryIDName thname (fst lawsLbl)
      let sts = case tlookup (theoryframes ss) thname of
                  Nothing    ->  topstatus ss
                  (Just tw)  ->  twSts tw
      let nimgs = namedimages ss
      case tlookup nimgs thidname of
        Nothing  -> do scream work
                         ("Whoops ! Named ImageDescr not found : "++thidname)
                       return (sts,Nothing)
        (Just idvar)  ->  findSelectedLawRow thname idvar pnt sts work
\end{code}

We now have the theory's image descr,
so see if we actually selected anything.
\begin{code}
findSelectedLawRow thname idvar pnt sts work
 = do thidescr <- varGet idvar
      let thorig = iorigin thidescr
      let thspec = ispec thidescr
      let thbb   = ibb thidescr
      let (mx,my) = (pointX pnt,pointY pnt)
      case pointLookup (mx,my) thspec thbb thorig of
        Nothing    ->  return (sts,Nothing)
        (Just ix)  ->  locateLawRow thspec ix thname sts work
\end{code}

\begin{code}
locateLawRow (DrawVert _ _ (_:(DrawVTable _ nc _ _ _ tspecs):_)) (2:n:_)
                thname sts work
 = do let m = kthindex nc n
      case (concat tspecs) `tindex` m of
        Nothing -> return (sts,Nothing)
        (Just lname) -> do plaw <- lookupLawThing thname lname work
                           case plaw of
                              Nothing     ->  return (sts,Nothing)
                              (Just (thno,law))  ->  return (sts,Just (thno,lname,law))
 where
   tindex [] _ = Nothing
   tindex ((DrawChars _ cs):rest) i
    | i <= 1     =  Just cs
    | otherwise  =  tindex rest (i-1)
   tindex _ _ = Nothing

locateLawRow _ _ _ sts _ = return (sts,Nothing)
\end{code}

We need to lookup the law just selected:
\begin{code}
lookupLawThing thname oname work
 = do lresult <- doTheoryLookup thname work
      case lresult of
        Nothing      ->  return Nothing
        (Just thry)  ->  return (do law <- lwlookup (laws thry) oname
                                    return (thrySeqNo thry,law))
\end{code}

On a right-click,
 we offer the option of matching the law against the
 current proof focus, if present.
\begin{code}
handleLawRhtClick thname work pnt
 = do thryfs <- getThryFrames work
      toConsole ("Got Law Right CLick at "++show(pointX pnt)++","++show(pointY pnt))
      case tlookup thryfs thname of
        Nothing    ->  scream work
                            ("handleLawRhtClick with dud thname "++thname)
        (Just tw)  ->  handleLawRhtClick' thname tw work pnt


handleLawRhtClick' thname tw work pnt
 = do (sts,plaw) <- handleLawClick thname work pnt
      case plaw of
          Nothing  -> buildLawRhtClickMenu thname tw work pnt
          (Just (thno,lawname,law))
            -> buildLawSelRhtClickMenu thname thno lawname law tw work pnt
\end{code}

Building the menu (when no law is selected):
\begin{code}
buildLawRhtClickMenu thname tw work pnt
 = do sts <- getSts work
      lawRMenu <- menuPane [text:=lawHdr]

      newLwItm <- menuItem lawRMenu [text:="New Law"]
      set newLwItm [on command := newLaw thname work]

      readLwItm <- menuItem lawRMenu [text:="Read Law from file"]
      set readLwItm [on command := readLaw thname work]

      let thf = twFrame tw
      menuPopup lawRMenu pnt thf
      thTabRepaint tw lawsLbl

 where
    lawHdr = "Laws for  \171"++thname++"\187"
\end{code}

Building the menu (when a law is selected):
\begin{code}
buildLawSelRhtClickMenu thname thno lname law tw work pnt
 = do sts <- getSts work
      lawRMenu <- menuPane [text:=lawHdr]
      let thf = twFrame tw

      if True -- isUserLaw law
       then
        do newLwItm <- menuItem lawRMenu [text:=("Edit "++lawHdr)]
           set newLwItm [on command := editLaw thname lname work]
       else return ()

      newLwItm <- menuItem lawRMenu [text:=("Delete "++lawHdr)]
      set newLwItm [on command := delLaw thname lname work]

      showLwItm <- menuItem lawRMenu [text:="Show Law Details"]
      set showLwItm [on command := showAllLaw thname lname work]

      newLwItm <- menuItem lawRMenu [text:="New Law"]
      set newLwItm [on command := newLaw thname work]

      readLwItm <- menuItem lawRMenu [text:="Read Law from file"]
      set readLwItm [on command := readLaw thname work]

      menuPopup lawRMenu pnt thf
      thTabRepaint tw lawsLbl

 where
    lawHdr = "Law \171"++thname++thrySepS++lname++"\187"
\end{code}



\subsubsection{Importing/Exporting Proof Contexts}

First, generating built-in contexts (which are never "modified"):
\begin{code}
genProofCtxt pc work
 = do sts <- getSts work
      (_,cwd) <- getCurrFS work
      pc' <- archiveTheory cwd pc
      note sts("Proof-Context '"++cn pc'++"' exported.")
 where cn pc = thryName pc++qualSep:(show (thrySeqNo pc))

genProofCtxts [] work = return ()
genProofCtxts (pc:pcs) work
  = do genProofCtxt pc work
       genProofCtxts pcs work
\end{code}
