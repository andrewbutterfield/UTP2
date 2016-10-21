\section{Program State}

\begin{code}
module WxState where

import Utilities
import Tables
import Datatypes
import Heuristics
import Builtin
import Manipulation
import Proof
import Program
import Theories
import Files
import LaTeXSetup
import RootTheory
import Logic -- to be dumped
import UTP -- to be dumped
import R -- to be dumped
import RAlg -- to be dumped
import WxTypes

import Graphics.UI.WX

import Text.ParserCombinators.Parsec.Expr

import Data.Char
import Data.List
import Data.Maybe
\end{code}

The program state has two main components: workspace,
and GUI widgets.
The workspace has two main components: the theory stacks,
and the current proofs (if any).

Major change: previously the policy
in the program state was to keep the theory/proof workspace
separate from the GUI features.
With the arrival of multiple current proofs this
approach requires keeping two independent lookup structures
synchronised, with a major potential for subtle coding problems.
So, from 0.89 onwards, we are combining proof workspace information
with the relevant GUI data, and plan to link the theory
data in a similar manner.

We also define record update functions
in accordance with \S\ref{Utilities.NRU},p\pageref{Utilities.NRU}.
\begin{verbatim}
FIELDSetf f recd = recd{ FIELD = f $ FIELD recd }
\end{verbatim}

\subsection{Top Level Program State}

\begin{code}
data WxState = WxState { workspace :: Workspace
                                   , lexical :: LexicalData
                                   , guistate  :: GUIState
                                   , filestate :: FileState
                                   , shuttingdown :: Bool
                                   }

type WxStateRef = Var WxState

workspaceSetf f recd = recd{ workspace = f $ workspace recd }
lexicalSetf f recd = recd{ lexical = f $ lexical recd }
guistateSetf f recd = recd{ guistate = f $ guistate recd }
filestateSetf f recd = recd{ filestate = f $ filestate recd }
shuttingdownSetf f recd = recd{ shuttingdown = f $ shuttingdown recd }
\end{code}

\subsection{State-based Event Handlers}

We first introduce the notion of a general GUI handler
as being a function given a \STHN-state variable
that performs a GUI IO action,
while a click handler has an addition argument giving
the point coordinates.
\begin{code}
type GUIHandler = WxStateRef -> IO ()
type ClkHandler = Point -> GUIHandler
\end{code}
In general we may consider single-, double-
and right-clicks so we group together
the possible handlers in a record:
\begin{code}
data ClkHandlers
 = ClkHandlers
    { hSingleClk, hDoubleClk, hRightClk :: Maybe ClkHandler }

hSingleClkSetf f recd = recd{ hSingleClk = f (hSingleClk recd) }
hDoubleClkSetf f recd = recd{ hDoubleClk = f (hDoubleClk recd) }
hRightClkSetf f recd = recd{ hRightClk = f (hRightClk recd) }

instance Show ClkHandlers where
 show clkHndlr
  = "Click-Handlers:"
    ++ details "single" (hSingleClk clkHndlr)
    ++ details "double" (hDoubleClk clkHndlr)
    ++ details "right"  (hRightClk clkHndlr)
    ++ "."
  where
      details _ Nothing = ""
      details what (Just _) = ' ':what

noClkHandlers = ClkHandlers Nothing Nothing Nothing

type ClkSelector = ClkHandlers -> Maybe ClkHandler

zeroPoint = Point 0 0

showClkSelector work ksel
 = showIt zeroPoint work
 where
   (Just showIt) = ksel showOurselves
   showOurselves = ClkHandlers (Just showClk)
                               (Just showDbl)
                               (Just showRght)
   showClk  _ _  =  putStr "left-click"
   showDbl  _ _  =  putStr "double-click"
   showRght _ _  =  putStr "right-click"
\end{code}

\subsection{Event-Handler Datatypes}


We view gui images
as nested boxes containing visible content,
bounding box information and optional mouse click handlers.
\begin{center}
\begin{tikzpicture}
 \draw (1,1) rectangle +(2,1) ;
 \draw (2,1.5) node {visible1} ;
 \draw[gray,very thin] (-0.5,1.5) -- (1,1.5) ;
 \draw[gray,very thin] (-0.5,1) -- (-0.5,2) ;
 \draw (-0.6,1.75) node[anchor=east] {{\small mbb$((2,1))$}} ;
 \draw (-0.6,1.25) node[anchor=east] {{\small \emph{hClkdOn1}}} ;
%
 \draw (1,2.1) rectangle +(2,1) ;
 \draw (2,2.6) node {visible2} ;
 \draw[gray,very thin] (-0.5,2.6) -- (1,2.6) ;
 \draw[gray,very thin] (-0.5,2.1) -- (-0.5,3.1) ;
 \draw (-0.6,2.85) node[anchor=east] {{\small mbb$((2,1))$}} ;
 \draw (-0.6,2.35) node[anchor=east] {{\small no handler}} ;
%
 \draw (1,1) +(-0.1,-0.1) rectangle +(2.1,2.2) ;
 \draw[gray,very thin] (3.1,2.05) -- (4.6,2.05) ;
 \draw[gray,very thin] (4.6,1.55) -- (4.6,2.55) ;
 \draw (4.7,2.3) node[anchor=west] {{\small mbb$((2.2,2.3))$}} ;
 \draw (4.7,1.8) node[anchor=west] {{\small \emph{hTop}}} ;
%
 \draw[red] (1.9,2.2) -- (1.9,2.4) ;
 \draw[red] (1.8,2.3) -- (2.0,2.3) ;
\end{tikzpicture}
\end{center}
A mouse-click is handled by the innermost
handler in place, so in the above example,
a click at the cross-hairs
(\tikz{ \draw[red] (-0.1,0) -- (0.1,0) ;
        \draw[red] (0,-0.1) -- (0,0.1) ;
})
would invoke \emph{hTop}.


We define a Display Descriptor
as a pair of mutually recursive data-types,
where the first wraps the second with MBB and handler data.
The second data-type defines the various ways
to describe atomic and composite boxes,
the latter referring to sub-instances of the first data-type.
\begin{code}
data DisplayDescr
 = DD DisplayStructure  -- display box structure
      (Int,Int)         -- origin
      (Int,Int)         -- minimum bounding box (MBB)
      ClkHandlers       -- click handlersw

ddds :: DisplayDescr -> DisplayStructure
ddds (DD ds _ _ _) = ds

instance Show DisplayDescr where
 show (DD ds (ox,oy) (bx,by) hs)
  = "AT " ++ show ox ++ "," ++show oy
    ++ " MBB " ++ show bx ++ "x" ++show by
    ++ " " ++ show hs ++ show ds
\end{code}
\newpage

A display structure is a recursive nesting of simple drawing elements:
\begin{code}
data DisplayStructure
 =  DDrawNull                                  -- nothing
\end{code}
\begin{tikzpicture}
 \draw [anchor=west] (0,1.2) node{Rendered text/lines: Black} ;
 \draw [anchor=west, red] (0,0.8) node{Minimum Bounding boxes: Red} ;
 \draw [anchor=west, blue] (0,0.4) node{Dimensions: Blue} ;
 \draw [anchor=west, gray, very thin] (0,0) node{Guide-lines: Gray, thin} ;
\end{tikzpicture}

\begin{code}
 |  DDrawText   (Maybe TextStyle) String       -- text
\end{code}
\begin{tikzpicture}
 \draw (0,0.4) [anchor=west] node{\texttt{DDrawText ts text}} ;
 \draw (6.35,0.2) node{text} ;
 \draw [red, thin] (6,0) rectangle +(0.7,0.35) ;
\end{tikzpicture}


\begin{code}
 |  DDrawSpace Int                             -- left space
               Int                             -- right space
               Int                             -- bottom space
               Int                             -- top space
               DisplayDescr
\end{code}
\begin{tikzpicture}
 \draw (0,0.8) [anchor=west] node{\texttt{DDrawSpace ls rs bs ts dd}} ;
 \draw [red, thin] (6,-0.5) rectangle +(2.5,1.35) ;
 \draw (7.25,0.2) node{dd} ;
 \draw [red, thin] (7,0) rectangle +(0.5,0.35) ;
 \draw [gray, very thin]  (6.1,0.1) -- (6.9,0.1) ;
 \draw [blue] (6.3,0.3) node{ls} ;
 \draw [gray, very thin]  (7.7,0.1) -- (8.4,0.1) ;
 \draw [blue] (7.8,0.3) node{rs} ;
 \draw [gray, very thin]  (7.1,-0.1) -- (7.1,-0.4) ;
 \draw [blue] (7.3,-0.2) node{bs} ;
 \draw [gray, very thin]  (7.1,0.45) -- (7.1,0.75) ;
 \draw [blue] (7.3,0.6) node{ts} ;
\end{tikzpicture}

\begin{code}
 |  DDrawBox    (Maybe BoxStyle) DisplayDescr  -- box around item
\end{code}
\begin{tikzpicture}
 \draw (0,0.6) [anchor=west] node{\texttt{DDrawBox bs dd}} ;
 \draw (6.45,0.2) node{dd} ;
 \draw [red, thin] (6.2,0) rectangle +(0.5,0.35) ;
 \draw (6.15,-0.05) rectangle +(0.6,0.45) ;
 \draw [red, thin] (6.1,-0.1) rectangle +(0.7,0.55) ;
\end{tikzpicture}

\begin{code}
 |  DDrawHoriz  (Maybe HorizStyle)             -- horizontal align
               DrawAlign
               [DisplayDescr]                  -- horiz. list
                -- derived:
               Int                             -- heigth
\end{code}
\begin{tikzpicture}
 \draw (0,1) [anchor=west] node{\texttt{DDrawHoriz hs da [dd1,..,ddn] h}} ;

 \draw (1.5,0.2) node{$dd_1$} ;
 \draw [red, thin] (1.2,0) rectangle +(0.6,0.4) ;

 \draw (2.15,0.2) node{$dd_2$} ;
 \draw [red, thin] (1.85,0) rectangle +(0.6,0.5) ;

 \draw (2.75,0.2) node{$\cdots$} ;

 \draw (3.45,0.2) node{$dd_{n-1}$} ;
 \draw [red, thin] (2.95,-0.1) rectangle +(0.95,0.5) ;

 \draw (4.25,0.2) node{$dd_n$} ;
 \draw [red, thin] (3.95,0) rectangle +(0.55,0.4) ;

 \draw [red, thin] (1.15,-0.15) rectangle +(3.4,0.7) ;

 \draw [gray, very thin] (0,-0.15) -- (1.1,-0.15) ;
 \draw [gray, very thin] (0,0.55) -- (1.1,0.55) ;
 \draw [blue] (0.5,0.2) node{h} ;
\end{tikzpicture}

\newpage
\begin{code}
 |  DDrawVert  (Maybe VertStyle)               -- vertical align
               DrawAlign
               [DisplayDescr]                  -- vert. list
                -- derived:
               Int                             -- width
\end{code}
\begin{tikzpicture}
 \draw (0,2.5) [anchor=west] node{\texttt{DDrawVert vs da [dd1,..,ddn] w}} ;

 \draw (6.35,2.2) node{$dd_1$} ;
 \draw [red, thin] (6.05,2.0) rectangle +(0.55,0.4) ;

 \draw (6.4,1.7) node{$dd_2$} ;
 \draw [red, thin] (6.1,1.35) rectangle +(0.55,0.6) ;

 \draw (6.35,1.2) node{$\vdots$} ;

 \draw (6.45,0.65) node{$dd_{n-1}$} ;
 \draw [red, thin] (6.0,0.45) rectangle +(0.95,0.4) ;

 \draw (6.35,0.2) node{$dd_n$} ;
 \draw [red, thin] (6.05,0) rectangle +(0.55,0.4) ;

 \draw [red, thin] (5.95,-0.05) rectangle +(1.05,2.5) ;

 \draw [gray, very thin] (5.95,-0.1) -- (5.95,-0.5) ;
 \draw [gray, very thin] (7,-0.1) -- (7,-0.5) ;
 \draw [blue] (6.5,-0.3) node{w};
\end{tikzpicture}

\begin{code}
 |  DDrawHTable (Maybe HTableStyle)            -- draw horiz. table
               Int                             -- no of rows
               DrawFit                         -- horiz. fit
               DrawFit                         -- vert. fit
               Bool                            -- draw borders
               [([DisplayDescr],ClkHandlers)]  -- columns of rows
                 -- derived:
               [Int] [Int]                     -- col. width, row height
\end{code}
\begin{tikzpicture}
 \draw (0,1) [anchor=west]
  node{\texttt{DDrawHTable hts r hf vf [col1,...,coln] ws hs}} ;
 \draw (0,0.6) [anchor=west]
  node{\texttt{coli = ([dd\_i1,..,dd\_ir],clkh)}} ;
 \draw (0,0.2) [anchor=west]
  node{\texttt{ws = [w1,..,wn]  hs = [h1,...,hr]}} ;

 \draw (2.75,-0.25) node{col1} ;
 \draw [red, thin] (1.5,-1) rectangle +(2.5,0.5) ;
 \draw (2.75,-0.75) node {$d_{11}$} ;
 \draw (5.5,-0.25) node{col2} ;
 \draw [red, thin] (4.0,-1) rectangle +(3,0.5) ;
 \draw (5.5,-0.75) node {$d_{21}$} ;
 \draw [red] (7.75,-0.75) node{$\cdots$} ;
 \draw (9.5,-0.25) node{coln} ;
 \draw [red, thin] (8.5,-1) rectangle +(2,0.5) ;
 \draw (9.5,-0.75) node {$d_{n1}$} ;

 \draw [red, thin] (1.5,-1.4) rectangle +(2.5,0.4) ;
 \draw (2.75,-1.2) node {$d_{12}$} ;
 \draw [red, thin] (4.0,-1.4) rectangle +(3,0.4) ;
 \draw (5.5,-1.2) node {$d_{22}$} ;
 \draw [red] (7.75,-1.15) node{$\cdots$} ;
 \draw [red, thin] (8.5,-1.4) rectangle +(2,0.4) ;
 \draw (9.5,-1.2) node {$d_{n2}$} ;

 \draw [red] (6,-1.55) node{$\vdots$};

 \draw [red, thin] (1.5,-2.5) rectangle +(2.5,0.6) ;
 \draw (2.75,-2.2) node {$d_{1r}$} ;
 \draw [red, thin] (4.0,-2.5) rectangle +(3,0.6) ;
 \draw (5.5,-2.2) node {$d_{2r}$} ;
 \draw [red] (7.75,-2.25) node{$\cdots$} ;
 \draw [red, thin] (8.5,-2.5) rectangle +(2,0.6) ;
 \draw (9.5,-2.2) node {$d_{nr}$} ;

 \draw [gray, very thin] (1.5,-2.55) -- (1.5,-2.95) ;
 \draw [gray, very thin] (4.0,-2.55) -- (4.0,-2.95) ;
 \draw [blue] (2.75,-2.75) node {$w_1$} ;
 \draw [gray, very thin] (7.0,-2.55) -- (7.0,-2.95) ;
 \draw [blue] (5.5,-2.75) node {$w_2$} ;
 \draw [gray, very thin] (8.5,-2.55) -- (8.5,-2.95) ;
 \draw [gray, very thin] (10.5,-2.55) -- (10.5,-2.95) ;
 \draw [blue] (9.5,-2.75) node {$w_n$} ;

 \draw [gray, very thin] (10.55,-0.5) -- (10.95,-0.5) ;
 \draw [gray, very thin] (10.55,-1) -- (10.95,-1) ;
 \draw [blue] (10.75,-0.75) node{$h_1$} ;
 \draw [gray, very thin] (10.55,-1.4) -- (10.95,-1.4) ;
 \draw [blue] (10.75,-1.2) node{$h_2$} ;
 \draw [gray, very thin] (10.55,-1.9) -- (10.95,-1.9) ;
 \draw [gray, very thin] (10.55,-2.5) -- (10.95,-2.5) ;
 \draw [blue] (10.75,-2.2) node{$h_r$} ;

\end{tikzpicture}


\begin{code}
 |  DDrawVTable (Maybe VTableStyle)            -- draw vert. table
               Int                             -- no. of columns
               DrawFit                         -- horiz. fit
               DrawFit                         -- vert. fit
               Bool                            -- draw borders
               [([DisplayDescr],ClkHandlers)]  -- rows of columns
                 -- derived:
               [Int] [Int]                     -- col. width, row height
\end{code}
\newpage
\begin{code}
instance Show DisplayStructure where
 show DDrawNull = " ()"
 show (DDrawText _ str) = " '"++str++"'"
 show (DDrawSpace _ _ _ _ dd) = " SPACE "++show dd
 show (DDrawBox _ dd) = " BOX "++show dd
 show (DDrawHoriz _ _ dds w)
  = " HORIZ w="++show w ++ concat (map (("\n-"++) . show) dds)
 show (DDrawVert _ _ dds h)
  = " VERT h="++show h ++ concat (map (("\n-"++) . show) dds)
 show (DDrawHTable _ nrow _ _ _ ddss ws hs)
  = " HTABLE nrow="++show nrow ++ " ws="++show ws ++ "hs="++show hs
    ++ concat (map ((" ROW:"++) .concat . (map (("\n--"++).show)) . fst ) ddss)
 show (DDrawVTable _ ncol _ _ _ ddss ws hs)
  = " VTABLE ncol="++show ncol ++ " ws="++show ws ++ "hs="++show hs
    ++ concat (map ((" ROW:"++) .concat . (map (("\n--"++).show)) . fst) ddss)

nullDDBB = (0,0)
displayNothing = DD DDrawNull (0,0) nullDDBB noClkHandlers

justDraw ds = DD ds (0,0) nullDDBB noClkHandlers

getddog (DD _ og _ _) = og
getddbb (DD _ _ bb _) = bb
\end{code}
The last two variants above (\texttt{DDrawHTable}, \texttt{DDrawVTable})
have an invariant,
that says that the length of each sub-list in its last component
must equal the value of the first integer component.
We provide two constructors that enforce this,
as well as setting the column/row sizes to be empty.
The enforcement involves chopping lists longer than
the specified length, and padding shorter ones with null objects.
\begin{code}
ddrawHTable style len hf vf brdr []
 = DDrawHTable style len hf vf brdr (map (dlenfix len) [([],noClkHandlers)]) [] []

ddrawHTable style len hf vf brdr dss
 = DDrawHTable style len hf vf brdr (map (dlenfix len) dss) [] []

ddrawVTable style len hf vf brdr []
 = DDrawVTable style len hf vf brdr (map (dlenfix len) [([],noClkHandlers)]) [] []
ddrawVTable style len hf vf brdr dss
 = DDrawVTable style len hf vf brdr (map (dlenfix len) dss) [] []

dlenfix len (ds,h) = (take len (ds ++ ddsnulls),h)

ddsnulls = displayNothing : ddsnulls
\end{code}
Display descriptors collect all the information
needed to render and select from an image,
in one place, including:
\begin{itemize}
  \item the display origin
  \item the display descriptor
\end{itemize}
\begin{code}
data DisplayData
 = DisplayData { dorigin :: (Int,Int)
               , ddescr   :: DisplayDescr
               }

nullDD = DisplayData (0,0) displayNothing
\end{code}

\newpage
\subsubsection{Display Specification API}

The usual way to use \texttt{DisplayStructure}s and \texttt{DisplayDescr}s
is to set up \texttt{DD}s with null origins and mbbs,
with these data being filled in at render time
(as they are device-context specific).
We provide functions that allow these to be specified
without explicitly mentioning render-time dimensioning data:
\begin{code}
ddSpec :: DisplayStructure -> ClkHandlers -> DisplayDescr
ddSpec ds = DD ds (0,0) nullDDBB

dispNull :: DisplayDescr
dispNull = displayNothing

dispText :: (Maybe TextStyle) -> String -> ClkHandlers -> DisplayDescr
dispText ts txt = ddSpec (DDrawText ts txt)

dispSpace :: Int -> Int -> Int -> Int -> DisplayDescr
           -> ClkHandlers -> DisplayDescr
dispSpace ls rs bs ts dd = ddSpec (DDrawSpace ls rs bs ts dd)

dispSpacer :: Int -> Int -> DisplayDescr
dispSpacer x y = dispSpace 0 x 0 y displayNothing noClkHandlers

dispBox :: (Maybe BoxStyle) -> DisplayDescr -> ClkHandlers -> DisplayDescr
dispBox bs dd = ddSpec (DDrawBox bs dd)

dispHoriz :: (Maybe HorizStyle) -> DrawAlign -> [DisplayDescr]
          -> ClkHandlers -> DisplayDescr
dispHoriz hs da dds = ddSpec (DDrawHoriz hs da dds 0)

dispVert :: (Maybe VertStyle) -> DrawAlign -> [DisplayDescr]
         -> ClkHandlers -> DisplayDescr
dispVert vs da dds = ddSpec (DDrawVert vs da dds 0)

dispHTable :: (Maybe HTableStyle) -> Int -> DrawFit -> DrawFit
           -> Bool -> [([DisplayDescr],ClkHandlers)]
           -> ClkHandlers -> DisplayDescr
dispHTable hts len hf vf brdr dds
                            = ddSpec (ddrawHTable hts len hf vf brdr dds)

dispVTable :: (Maybe VTableStyle) -> Int -> DrawFit -> DrawFit
           -> Bool -> [([DisplayDescr],ClkHandlers)]
           -> ClkHandlers -> DisplayDescr
dispVTable vts len hf vf brdr dds
                            = ddSpec (ddrawVTable vts len hf vf brdr dds)
\end{code}



\subsection{Program State Components}

\subsubsection{\Saoithin Top-level Widgets}

For now we have a top-level window and status bar,
as well as a pointer to the drawing and bounding-box specification of
the current top-level window display,
along with a list of open windows.
\begin{code}
data GUIState
 = GUIState { guiTop :: ScrolledWindow ()
            , topStatus :: StatusField
            , topDD :: Var DisplayData
            , theoryFrames :: Trie TheoryWidgets    -- thryName
            , namedImages :: Trie (Var ImageDescr) -- thryName+Lbl
            , shortcutMenuLineHeight :: Int
            , frame1 :: Frame ()
            , drawStyles :: DrawStyles
            }

guiTopSetf f recd = recd{ guiTop = f $ guiTop recd }
topStatusSetf f recd = recd{ topStatus = f $ topStatus recd }
topDDSetf f recd = recd{ topDD = f $ topDD recd }
theoryFramesSetf f recd = recd{ theoryFrames = f $ theoryFrames recd }
namedImagesSetf f recd = recd{ namedImages = f $ namedImages recd }
shortcutMenuLineHeightSetf f recd = recd{ shortcutMenuLineHeight = f $ shortcutMenuLineHeight recd }
frame1Setf f recd = recd{ frame1 = f $ frame1 recd }
drawStylesSetf f recd = recd{ drawStyles = f $ drawStyles recd }
\end{code}


\subsubsection{Proof Widgets}

We have a collection of windows for the proofs.
Unfortunately, we need to keep the match and proofs windows
explicitly here,
as repainting the proof frame does not propagate down to these sub-windows.
Also we have flags that determine if certain actions are taken automatically
once a proof is complete, to whit:
\begin{itemize}
  \item saving the theorem (and theory) --- on by default.
  \item promoting the theorem to a law --- on by default.
\end{itemize}
\begin{code}
data ProofGUI = ProofGUI { proofFrame :: Frame ()
                         , proofStatus :: StatusField
                         , goalWindow :: ScrolledWindow ()
                         , matchWindow :: ScrolledWindow ()
                         , goalDD :: Var DisplayData
                         , matchDD :: Var DisplayData
                         , autoSaveThm :: Bool
                         , autoPromoteThm :: Bool
                         , autoMatch :: Bool
                         , currMF :: MatchFilterDescr
                         , currRH :: RankHeuristicDescr
                         , currMPP :: MatchPostProcessDescr
                         , verbosity :: Verbosity
                         }

proofFrameSetf f recd = recd{ proofFrame = f $ proofFrame recd }
proofStatusSetf f recd = recd{ proofStatus = f $ proofStatus recd }
goalWindowSetf f recd = recd{ goalWindow = f $ goalWindow recd }
matchWindowSetf f recd = recd{ matchWindow = f $ matchWindow recd }
goalDDSetf f recd = recd{ goalDD = f $ goalDD recd }
matchDDSetf f recd = recd{ matchDD = f $ matchDD recd }
autoSaveThmSetf f recd = recd{ autoSaveThm = f $ autoSaveThm recd }
autoPromoteThmSetf f recd = recd{ autoPromoteThm = f $ autoPromoteThm recd }
autoMatchSetf f recd = recd{ autoMatch = f $ autoMatch recd }
currMFSetf f recd = recd{ currMF = f $ currMF recd }
currRHSetf f recd = recd{ currRH = f $ currRH recd }
currMPPSetf f recd = recd{ currMPP = f $ currMPP recd }
verbositySetf f recd = recd{ verbosity = f $ verbosity recd }
\end{code}

Similarly we need to keep all the tabbed scroll-windows in the
theory notebook
explicitly, along with the frame and status bar:
\begin{code}
data TheoryWidgets
 = TW { twFrame :: Frame ()
      , twSts   :: StatusField
      , twTabs  :: Trie (ScrolledWindow ()) -- TabLbls
      }

twFrameSetf f recd = recd{ twFrame = f $ twFrame recd }
twStsSetf f recd = recd{ twSts = f $ twSts recd }
twTabsSetf f recd = recd{ twTabs = f $ twTabs recd }
\end{code}

Now we need to store all the style data associated with
each window
\begin{code}
data DrawStyles = DrawStyles { backgroundCol :: Color
                             , textStyle     :: Maybe TextStyle
                             , boxStyle      :: Maybe BoxStyle
                             , horizStyle    :: Maybe HorizStyle
                             , vertStyle     :: Maybe VertStyle
                             , htStyle       :: Maybe HTableStyle
                             , vtStyle       :: Maybe VTableStyle
                             , stylesChanged :: Bool
                             }

backgroundColSetf f recd = recd{ backgroundCol = f $ backgroundCol recd }
textStyleSetf f recd = recd{ textStyle = f $ textStyle recd }
boxStyleSetf f recd = recd{ boxStyle = f $ boxStyle recd }
horizStyleSetf f recd = recd{ horizStyle = f $ horizStyle recd }
vertStyleSetf f recd = recd{ vertStyle = f $ vertStyle recd }
htStyleSetf f recd = recd{ htStyle = f $ htStyle recd }
vtStyleSetf f recd = recd{ vtStyle = f $ vtStyle recd }
stylesChangedSetf f recd = recd{ stylesChanged = f $ stylesChanged recd }
\end{code}

\newpage
\subsubsection{\Saoithin\ Workspace}

All the theories and proofs live here:
\begin{code}
data Workspace = Workspace { username :: String
                           , theories :: TheorySpace
                           , currProofs :: Trie Proofspace
                           , currProgs :: Trie ProgramSpace
                           , vertWinSplit :: Bool
                           }

usernameSetf f recd = recd{ username = f $ username recd }
theoriesSetf f recd = recd{ theories = f $ theories recd }
currProofsSetf f recd = recd{ currProofs = f $ currProofs recd }
winSplitSetf f recd = recd{ vertWinSplit = f $ vertWinSplit recd }

emptyWS user = Workspace user emptyTS tnil tnil False
rootWS user = Workspace user rootTS tnil tnil False
\end{code}


We want maintain a graph of theories,
and track if any theory has been modified.
\begin{code}
data TheorySpace = TheorySpace { theoryGraph :: TheoryGraph
                               , thrysModified :: Bool
                               }

theoryGraphSetf f recd = recd{ theoryGraph = f $ theoryGraph recd }
thrysModifiedSetf f recd = recd{ thrysModified = f $ thrysModified recd }

emptyTG = (DTop [], tnil)
rootTG = (rdROOT rname, lbuild [(rname,rootTheory)])
 where
   rname = thryName rootTheory

emptyTS = TheorySpace emptyTG False
rootTS  = TheorySpace rootTG False
\end{code}

A proof-space holds the current proof, any matches found
as well as the relevant gui details.
\begin{code}
data Proofspace = Proofspace { currProof :: Proof
                             , matches :: LawMatches
                             , proofGUI :: ProofGUI
                             }

currProofSetf f recd = recd{ currProof = f $ currProof recd }
matchesSetf f recd = recd{ matches = f $ matches recd }
proofGUISetf f recd = recd{ proofGUI = f $ proofGUI recd }
\end{code}
We also need to keep lexical data for parsing and pretty-printing:
\begin{code}
data LexicalData
 = LexicalData { latex :: LaTeXLayout
               }

latexSetf f recd = recd{ latex = f $ latex recd }

defaultLD = LexicalData $
             defaultLaTeXLayout 48    -- lineLength
                                3     -- indentLength
                                False -- wantBindings
\end{code}


\subsubsection{\Saoithin\ Filestate}

We now track various file/directory related information.
A directory containing all the files relevant to a given use
of \Saoithin\ is called a ``filespace'',
which has a user-supplied name, and records the path to that directory.

\begin{code}
type FileSpace = ( String      -- filespace name
                 , FilePath )  -- path to filespace

showFS (nm,path) = nm ++ " -- " ++ path

data FileState
 = FileState
    { appUserDir         :: FilePath       -- application data (the following:)
    , currentFileSpace   :: FileSpace
    , previousFileSpaces :: [ FileSpace ]
    }

appUserDirSetf f recd = recd{ appUserDir = f $ appUserDir recd }
currentFileSpaceSetf f recd = recd{ currentFileSpace = f $ currentFileSpace recd }
previousFileSpacesSetf f recd = recd{ previousFileSpaces = f $ previousFileSpaces recd }

instance Show FileState where
  show fs = unlines ( [ "AppUserData  =  " ++ appUserDir fs
                      , "Current FileSpace =  " ++ showFS (currentFileSpace fs)
                      , "Previous FileSpaces:\n"
                      ] ++ map dispFS (previousFileSpaces fs) )
            where
              dispFS fs = "  "++showFS fs

emptyFS = FileState "" ("<none>","") []
\end{code}



\subsection{Updating Program State}

wxHaskell provides the following variable handlers:
\begin{verbatim}
varCreate :: t -> IO (Var t)
varSet :: Var t -> t -> IO ()
varGet :: Var t -> IO t
\end{verbatim}
We extend this with an variable setter that takes a update function
to fit in with the \texttt{Setf} style for composing record updates.
\begin{code}
varSetf :: (t -> t) -> Var t -> IO ()
varSetf f v
 = do x <- varGet v
      let x' = f x
      varSet v x'
\end{code}



\subsubsection{Program State Access (Simple)}

It is worth having top level get-/set-operations that go deep.

Workspace:
\begin{code}
uname = username . workspace
getUser = fmap uname . varGet

split = vertWinSplit . workspace
getSplit = fmap split . varGet
splitSetf = varSetf . workspaceSetf . winSplitSetf
setSplitf = splitSetf . const

getTheories = fmap (theories . workspace) . varGet
setTheories work thr'
 = varSetf ((workspaceSetf . theoriesSetf . const) thr') work

theorygraph = theoryGraph . theories . workspace
getThgrf = fmap theorygraph . varGet
thgrfSetf = varSetf . workspaceSetf . theoriesSetf . theoryGraphSetf
setThgrf = thgrfSetf . const

thrysmodified = thrysModified . theories . workspace
getStkMod = fmap thrysmodified . varGet
setStkMod work ro'
 = do ss <- varGet work
      let ws = workspace ss
      let thr = theories ws
      let thr' = thr{thrysModified = ro'}
      let ws' = ws{theories=thr'}
      let ss' = ss{workspace=ws'}
      varSet work ss'

getAllThings :: (Theory -> t) -> String -> Var WxState -> IO [t]
getAllThings sel thname work -- get those visible from named theory
 = do (rdag,trie) <- getThgrf work
      let rchblstk = reachableFrom rdag trie thname
      return (map sel rchblstk)
 where
  reachableFrom rdag trie thn
   = catMaybes thrys
   where
     [rdag'] = rdSearch [thn] rdag
     descs = map snd $ rdStack rdag'
     thrys = map (tlookup trie) descs
\end{code}

Lexical
\begin{code}
latexlayout = latex . lexical
getLayout = fmap latexlayout . varGet
\end{code}

GUIState
\begin{code}
guitop = guiTop . guistate
getTop = fmap guitop . varGet

repaintTop work
 = do topw <- getTop work
      topwp <- fParent topw
      repaint topwp



topstatus = topStatus . guistate
getSts = fmap topstatus . varGet

topdd = topDD . guistate
getTopDD = fmap topdd . varGet

theoryframes = theoryFrames . guistate
getThryFrames = fmap theoryframes . varGet
setThryFrames work thfms
 = do ss <- varGet work
      let gui = guistate ss
      let gui' = gui{theoryFrames=thfms}
      let ss' = ss{guistate=gui'}
      varSet work ss'

scmenulineheight =  shortcutMenuLineHeight . guistate
getSCMenuLnHeight = fmap scmenulineheight . varGet
setSCMenuLnHeight work lineHeight
 = do ss <- varGet work
      let gui = guistate ss
      let gui' = gui{shortcutMenuLineHeight=lineHeight}
      let ss' = ss{guistate=gui'}
      varSet work ss'

namedimages = namedImages . guistate
getNmdImages = fmap namedimages . varGet
setNmdImages work nimgs
 = do ss <- varGet work
      let gui = guistate ss
      let gui' = gui{namedImages=nimgs}
      let ss' = ss{guistate=gui'}
      varSet work ss'

\end{code}
Now, getting/setting identified \texttt{Proofspace}s
\begin{code}
currproofs = currProofs . workspace
getCurrprfs = fmap currproofs . varGet
setCurrprfs proofs work
 = varSetf ((workspaceSetf . currProofsSetf . const) proofs) work
\end{code}
Looking up a \texttt{pid} should never fail, but \emph{might}.
So we provide some defensive programming support.
\begin{code}
proofDo pid work jaction naction
 = do pspaces <- fmap (currProofs . workspace) (varGet work)
      case tlookup pspaces pid of
        Nothing      ->  naction pid work
        Just pspace  ->  jaction pspaces pid pspace work

noSuchProof activity def pid work
 = do topf <- getTop work
      warningDialog topf "No such Proof"
        ("Proof '"++pid++"' not found - "++activity)
      return def

nSP activity = noSuchProof activity ()
\end{code}
Now, getting/setting all \texttt{Proofspace}s
\begin{code}
getCurrprf pid work
  = do prfs <- fmap currproofs $ varGet work
       return $ tlookup prfs pid


currProofspaceCreate pid pspace work
 = proofDo pid work already (proofSpaceUpdate pspace)
 where
   already _ pid _ work
     = do sts <- getSts work
          alert sts ("Proof '"++pid++"' already exists")

proofSpaceUpdate pspace pid work
  = do pspaces <- getCurrprfs work
       let pspaces' = tupdate pid pspace pspaces
       setCurrprfs pspaces' work


currProofspaceSetf pid f work
 = proofDo pid work (setf f) (noSuchProof "currProofspaceSetf" ())
 where
   setf f pspaces pid pspace work
    = do let pspaces' = tupdate pid (f pspace) pspaces
         varSetf ((workspaceSetf . currProofsSetf . const) pspaces') work
-- end currProofspaceSetf

proofSet pid prf = currProofspaceSetf pid ((currProofSetf . const) prf)
matchesSet pid mtches = currProofspaceSetf pid ((matchesSetf . const) mtches)

unsetCurrprf work pid
 = do pspaces <- fmap (currProofs . workspace) (varGet work)
      let pspaces' = tblank pid pspaces
      varSetf ((workspaceSetf . currProofsSetf . const) pspaces') work


\end{code}
Now, selecting GUI components from all active proofs
\begin{code}

proofGUIsGet sel
 = fmap (map (sel . proofGUI) . trieRng) . getCurrprfs

getPrfFrms = proofGUIsGet proofFrame
getGWins   = proofGUIsGet goalWindow
getMWins   = proofGUIsGet matchWindow
getAPTs    = proofGUIsGet autoPromoteThm
getASTs    = proofGUIsGet autoSaveThm

\end{code}
Now, singling out proof components from an identified proof
\begin{code}

proofGetpart sel pid work
 = do prf <- getCurrprf pid work
      return $ fmap (sel . currProof ) prf

getMCtxt  = proofGetpart mtchCtxt


\end{code}
Now, singling out match components from an identified proof
\begin{code}

matchesGet pid work
 = do prf <- getCurrprf pid work
      return $ fmap matches prf

\end{code}
Now, singling out GUI components from an identified proof
\begin{code}

proofguiGetpart sel pid work
 = do prf <- getCurrprf pid work
      return $ fmap (sel . proofGUI ) prf

proofStatusGet = proofguiGetpart proofStatus
goalWindowGet = proofguiGetpart goalWindow
matchWindowGet = proofguiGetpart matchWindow
getVb = proofguiGetpart verbosity
getMatchDD = proofguiGetpart matchDD
getPrfFrm = proofguiGetpart proofFrame
getAPT = proofguiGetpart autoPromoteThm
getAST = proofguiGetpart autoSaveThm
getAM = proofguiGetpart autoMatch

getAMM pid work -- returns False if nothing.
 = do amm <- getAM pid work
      case amm of
        Nothing -> return False
        Just am -> return am

fParent fchild = get fchild frameParent

goalParent pgui = fParent (goalWindow pgui)
matchParent pgui = fParent (matchWindow pgui)

goalParentGet pid work
 = do mgw <- goalWindowGet pid work
      case mgw of
       Nothing -> return Nothing
       Just gw -> return $ Just $ fParent gw

matchParentGet pid work
 = do mgw <- matchWindowGet pid work
      case mgw of
       Nothing -> return Nothing
       Just gw -> return $ Just $ fParent gw

proofguiSetpart setf pid work
 = do cprfs <- getCurrprfs work
      case tlookup cprfs pid of
       Nothing  ->  return () -- should really alert user
       Just cprf
        -> do let cprf' = proofGUISetf setf cprf
              let cprfs' = tupdate pid cprf' cprfs
              varSetf ((workspaceSetf . currProofsSetf . const) cprfs') work

setPrfFrm work pid f'
 = proofguiSetpart (proofFrameSetf (const f')) pid work
setPrfSts work pid s'
 = proofguiSetpart (proofStatusSetf (const s')) pid work
setGWin work pid m'
 = proofguiSetpart (goalWindowSetf (const m')) pid work
setMWin work pid m'
 = proofguiSetpart (matchWindowSetf (const m')) pid work
setfVb work pid vf'
 = proofguiSetpart (verbositySetf vf') pid work
setVb work pid v' = setfVb work pid (const v')
setMatchDD work pid m'
 = proofguiSetpart (matchDDSetf (const m')) pid work
setAPT work pid b'
 = proofguiSetpart (autoPromoteThmSetf (const b')) pid work
setAST work pid b'
 = proofguiSetpart (autoSaveThmSetf (const b')) pid work
setAM work pid b'
 = proofguiSetpart (autoMatchSetf (const b')) pid work
\end{code}

FileState:
\begin{code}
getFileState = fmap filestate . varGet
setFileState work fstate'
 = do ss <- varGet work
      let ss' = ss{filestate=fstate'}
      varSet work ss'

appuser = appUserDir . filestate
getAppUser = fmap appuser . varGet

setAppUser work fp'
 = do ss <- varGet work
      let fs = filestate ss
      let fs' = fs{appUserDir=fp'}
      let ss' = ss{filestate=fs'}
      varSet work ss'

currFS = currentFileSpace . filestate
getCurrFS = fmap currFS . varGet
getCWD = fmap snd . getCurrFS

setCurrFS work fsp'
 = do ss <- varGet work
      let fs = filestate ss
      let fs' = fs{currentFileSpace=fsp'}
      let ss' = ss{filestate=fs'}
      varSet work ss'

newFS fstate fsp'
 = let curr = currentFileSpace fstate
       prev = previousFileSpaces fstate
       prev' = nubBy fileSpaceEq (curr:prev)
   in fstate{ currentFileSpace = fsp'
            , previousFileSpaces = prev' }

fileSpaceEq (_,path1) (_,path2) = path1==path2

setNewFS work fsp'
 = do ss <- varGet work
      let fs = filestate ss
      let fs' = newFS fs fsp'
      let ss' = ss{filestate=fs'}
      varSet work ss'

prevFS = previousFileSpaces . filestate
getPrevFS = fmap prevFS . varGet

setPrevFS work fsps'
 = do ss <- varGet work
      let fs = filestate ss
      let fs' = fs{previousFileSpaces=fsps'}
      let ss' = ss{filestate=fs'}
      varSet work ss'


\end{code}

\subsection{Program State Access (Theories \& Proofs}

We have a central global repository of theorems
(currently \texttt{theoryGraph . theories . workspace}).
We provide a means to access and modify theories in
here, identified by theory name.
\begin{code}
namedTheoryGet thnm work
 = do (rdag,trie) <- getThgrf work
      case tlookup trie thnm of
        Nothing -> return nullPrfCtxt
        Just thry -> return thry

conjecturesGet thnm = fmap conjectures . namedTheoryGet thnm
theoremsGet thnm = fmap theorems . namedTheoryGet thnm

namedTheorySetf thnm thryf work
 = do (rdag,trie) <- getThgrf work
      case tlookup trie thnm of
       Nothing -> return ()
       Just thry
        -> do let trie' = tupdate thnm (thryf thry) trie
              setThgrf (rdag,trie') work

namedTheorySet thry' = namedTheorySetf (thryName thry') (const thry')

conjecturesSet thnm conj'
 = namedTheorySetf thnm (conjecturesSetf (const conj'))
theoremsSet thnm thry'
 = namedTheorySetf thnm (theoremsSetf (const thry'))
\end{code}

When a proof is launched it builds a local stack of the relevant theories
and we need to be able to access this via the proof id.
\begin{code}
proofGet pid work
  = do cprf <- getCurrprfs work
       case tlookup cprf pid of
         Nothing     ->  return dummyProof
         (Just pfspace)  ->  return $ currProof pfspace

penvGet pid work
 = do prf <- proofGet pid work
      return $ context prf

theoryPartGet sel pid = fmap (map sel) . penvGet pid

prfTheoremsGet  = theoryPartGet theorems
getPrec = theoryPartGet precs
prfConjecturesGet = theoryPartGet conjectures
\end{code}


\subsection{Program State Access (Complex)}


\subsubsection{Accessing a Theory by name}

\begin{code}
theorylookup nm ss
 = case tlookup trie nm  of
    Nothing  ->  Nothing
    Just th  ->  Just th
 where
   (_,trie) = theorygraph ss

doTheoryLookup nm = fmap (theorylookup nm) . varGet

-- we do not check that theory is pre-existing !!!!!
-- all uses of this function ensure that thname exists !!!!
doTheoryUpdate thname thry' work
 = do (rdag,trie) <- getThgrf work
      let thry'' = markTheoryDeps thry'
      let trie' = tupdate thname thry'' trie
      setThgrf (rdag,trie') work
      top <- getTop work
      repaint top
\end{code}

\subsubsection{Access/Conversion between Theory-Stacks and Graphs}

Given an rDAG, return the corresponding theory-stack:
\begin{code}
thryGraphToStack :: TheoryGraph -> TheoryStack
thryGraphToStack (rdag,trie)
 = let
     thnames = concat $ rdStratify rdag
     thrys = map (tlookup trie) thnames
   in catMaybes thrys
\end{code}

Given a theory-stack, build the corresponding (linear) rDAG:
\begin{code}
thryStackToLinearGraph :: TheoryStack -> TheoryGraph
thryStackToLinearGraph thrys
  = (rdag, lnbuild thryName thrys)
  where (Right rdag) = linRdFromList $ map thryName thrys
\end{code}


Given a theory-stack, build a rDAG that matches the dependencies:
\begin{code}
thryStackToDependGraph :: TheoryStack -> TheoryGraph
thryStackToDependGraph thrys
  = (thryStackToDepRDAG thrys, lnbuild thryName thrys)

thryStackToDepRDAG :: TheoryStack -> RDAG String
thryStackToDepRDAG []      =  DTop []
thryStackToDepRDAG [thry]  =  rdROOT $ thryName thry
thryStackToDepRDAG (thry:thrys)
 = case res of
    Right grf  -> grf
    Left _     -> DTop []
 where
   res = rdUpdate (thryName thry)
                  (pad $ depsOf thry)
                  (thryStackToDepRDAG thrys)
   pad [] = [rootName]
   pad nms = nms
\end{code}


The default one:
\begin{code}
-- thryStackToGraph = thryStackToLinearGraph
thryStackToGraph = thryStackToDependGraph
\end{code}


\begin{code}
dbgstk stk = show $ map thryName stk
dbggrf (g,_) = show g
\end{code}



\subsubsection{Flagging Notifications and Errors}

An audible accompaniment to notices is often useful.
\begin{code}
notify noisefile txtspot string
 = do let beep = sound noisefile
      set txtspot [text:=string]
      playWait beep

scream work s
 = do top <- getTop work
      errorDialog top "Serious Error" s

alert  t s  = notify "Saoithin-alert.wav" t s
cheer  t s  = notify "Saoithin-cheer.wav" t s
note   t s  = notify "Saoithin-note.wav"  t s
quiet  t s  = set t [text:=s]
\end{code}


\subsubsection{Command Line Processing}

\paragraph{Reading Numbers}

Read positive integer, returning zero if not a number
\begin{code}
readNat str
 = rnat 0 str
 where
   rnat acc "" = acc
   rnat acc (c:cs)
    | isDigit c  =  rnat (10*acc+(ord c - ord '0')) cs
    | otherwise  =  acc
\end{code}


\subsection{General User Interface Utilities}

\subsubsection{Trimming Text Dialog}

It is important to trim leading and trailing space
from names entered in dialog boxes:
\begin{code}
ttextDialog window message caption defaultText
 = do txt <- textDialog window message caption defaultText
      return $ trim txt
\end{code}


Program state access for background colour and drawing styles
\begin{code}

drawstyles = drawStyles . guistate

backgroundcolour =  backgroundCol . drawstyles
getBgColour = fmap backgroundcolour . varGet
setBgColour work colour
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{backgroundCol=colour}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'


f =  frame1 . guistate
getFrame = fmap f . varGet

textS =  textStyle . drawstyles
getTextStyle = fmap textS . varGet
setTextStyle work style
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{textStyle=style}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

boxS =  boxStyle . drawstyles
getBoxStyle = fmap boxS . varGet
setBoxStyle work style
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{boxStyle=style}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

horizS =  horizStyle . drawstyles
getHorizStyle = fmap horizS . varGet
setHorizStyle work style
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{horizStyle=style}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

vertS =  vertStyle . drawstyles
getVertStyle = fmap vertS . varGet
setVertStyle work style
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{vertStyle=style}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

htS =  htStyle . drawstyles
getHtStyle = fmap htS . varGet
setHtStyle work style
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{htStyle=style}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

vtS =  vtStyle . drawstyles
getVtStyle = fmap vtS . varGet
setVtStyle work style
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{vtStyle=style}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

sS =  stylesChanged . drawstyles
getStyleStatus = fmap sS . varGet
setStyleStatus work bool
 = do ss <- varGet work
      let gui = guistate ss
      let ds  = drawStyles gui
      let ds' = ds{stylesChanged=bool}
      let gui' = gui{drawStyles=ds'}
      let ss' = ss{guistate=gui'}
      varSet work ss'

\end{code}

\newpage
\subsection{Global State Mapping}

A function that applies mapping functions to all predicates
and expressions in the system.
Rarely used, except to prepare for major datastructure changes,
particularly when theories are under development,
and we don't want to completely re-do that work.

\begin{code}
performGlobalMap :: (Pred->Pred,Expr->Expr) -> WxStateRef -> IO ()
performGlobalMap pemap work
 = do ss <- varGet work
      let ss' = globalStateMap pemap ss
      varSet work ss'

globalStateMap :: (Pred->Pred,Expr->Expr) -> WxState -> WxState
globalStateMap pemap ss
 = workspaceSetf (workspaceMap pemap) ss

workspaceMap :: (Pred->Pred,Expr->Expr) -> Workspace -> Workspace
workspaceMap pemap
 = currProofsSetf (tmap (proofspaceMap pemap))
  . theoriesSetf (theoryspaceMap pemap)

proofspaceMap :: (Pred->Pred,Expr->Expr) -> Proofspace -> Proofspace
proofspaceMap pemap
 = matchesSetf (const [])  -- clear all matches
   . currProofSetf (proofMap pemap)

theoryspaceMap :: (Pred->Pred,Expr->Expr) -> TheorySpace -> TheorySpace
theoryspaceMap pemap
 = theoryGraphSetf (theorygraphMap pemap)
\end{code}
