\section{Wx State Types}

\begin{code}
module WxTypes where
import Graphics.UI.WX
\end{code}

\subsection{Structured Drawing Style Types}

Drawing styles specific to each variant of DrawSpec:
\begin{code}
data TextStyle   = TextStyle   { textFont :: FontStyle
                               , textCol  :: Color
                               }
                               deriving (Eq, Show)

data BoxStyle    = BoxStyle    { boxPen :: PenStyle
                               }
                               deriving (Eq, Show)

data HorizStyle  = HorizStyle  { hPen     :: PenStyle
                               }
                               deriving (Eq, Show)

data VertStyle   = VertStyle   { vPen      :: PenStyle
                               }
                               deriving (Eq, Show)

data HTableStyle = HTableStyle { htPen  :: PenStyle
                               }
                               deriving (Eq, Show)

data VTableStyle = VTableStyle { vtPen  :: PenStyle
                               }
                               deriving (Eq, Show)
\end{code}

\subsection{Structured Drawing Types}
We shall define a generic data-structure that simplifies
the layout of complex data, with some simple default behaviours:
\begin{code}
data DrawAlign = DrawLeft | DrawCentre | DrawRight | DrawTop | DrawBottom
                 deriving (Eq,Show)

data DrawFit = DrawTight    -- row/column size fits items in that row/col.
             | DrawUniform  -- uniform row/column size
             deriving (Eq,Show)

-- soon to be deprecated
data DrawSpec = DrawNull -- nothing
                |  DrawChars  (Maybe TextStyle) String    -- plain text, default style
                |  DrawText   (Maybe TextStyle) String     -- decorative text
                |  DrawBox    (Maybe BoxStyle) DrawSpec -- box around item
                |  DrawHoriz  (Maybe HorizStyle)          -- horizontal align
                              DrawAlign
                              [DrawSpec]              -- horiz. list
                |  DrawVert   (Maybe VertStyle)            -- vertical line
                              DrawAlign
                              [DrawSpec]               -- vert. list
                |  DrawHTable (Maybe HTableStyle)        -- draw horiz. table
                              Int                        -- no of rows
                              DrawFit                    -- horiz. fit
                              DrawFit                    -- vert. fit
                              Bool                       -- draw borders
                              [[DrawSpec]]           -- columns of rows
                |  DrawVTable (Maybe VTableStyle)        -- draw vert. table
                              Int                        -- no. of columns
                              DrawFit                    -- horiz. fit
                              DrawFit                    -- vert. fit
                              Bool                       -- draw borders
                              [[DrawSpec]]           -- rows of columns
                deriving (Eq,Show)


defaultColour     = rgb 0 0 0

defaultFrameCol   = 15790320 :: Int -- default window color (Int)

defaultTextStyle  = TextStyle fontDefault defaultColour

defaultBoxStyle   = BoxStyle penDefault   -- penDefault is a default PenStyle in wxHaskell

defaultHorizStyle = HorizStyle penDefault

defaultVertStyle  = VertStyle penDefault

defaultHTStyle    = HTableStyle penDefault

defaultVTStyle    = VTableStyle penDefault
\end{code}

The last two options above have an invariant,
that says that the length of each sub-list in its last component
must equal the value of the first integer component.
We provide two constructors that enforce this:
\begin{code}
drawHTable style len hf vf brdr []
 = DrawHTable style len hf vf brdr (map (lenfix len) [[]])

drawHTable style len hf vf brdr dss
 = DrawHTable style len hf vf brdr (map (lenfix len) dss)

drawVTable style len hf vf brdr []
 = DrawVTable style len hf vf brdr (map (lenfix len) [[]])
drawVTable style len hf vf brdr dss
 = DrawVTable style len hf vf brdr (map (lenfix len) dss)

lenfix len ds = take len (ds ++ dsnulls)

dsnulls = DrawNull : dsnulls
\end{code}

We have a problem --- in order to draw everything in the proper location,
esp. with the tables, we need to traverse the whole data-structure
to locate (top-level) components, then traverse again to draw.
If we don't keep a tree-structured record of the first traversal outcome,
then the draw phase will still need to traverse sub-components.
We can't do this all on the fly because alignment and fit require global
knowledge.
We introduce a bounding box data-structure to shadow that of \texttt{DrawSpec}:
\begin{code}
-- soon to be deprecated
data BB = AtmBB   (Int,Int)          -- atomic: Null, Chars, Text
        | BoxBB   (Int,Int) BB       -- box (surround)
        | ListBB  (Int,Int) [BB]     -- lists
        | TableBB (Int,Int) [Int] [Int] [[BB]] -- tables (row/col dimensions)
        deriving (Eq,Show)

nullBB = AtmBB (0,0)

getbb :: BB -> (Int,Int)
getbb (AtmBB  bb)         =  bb
getbb (BoxBB  bb _)       =  bb
getbb (ListBB bb _)       =  bb
getbb (TableBB bb _ _ _)  =  bb
\end{code}

For the precise semantics of \texttt{DrawSpec} and \texttt{BB} see \texttt{WxRender}
(functions \texttt{drawSpecBB} and \texttt{drawSpec}).

Image descriptors collect all the information
needed to render and select from an image,
in one place, including:
\begin{itemize}
  \item the image origin
  \item the drawing specification
  \item the bounding box tree
\end{itemize}
\begin{code}
data ImageDescr
 = ImageDescr { iorigin :: (Int,Int)
              , ispec   :: DrawSpec
              , ibb     :: BB
              }

nullID = ImageDescr (0,0) DrawNull (AtmBB (0,0))
\end{code}
