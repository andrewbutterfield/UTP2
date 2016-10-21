\section{Wx Styles}
\begin{code}
{-# LANGUAGE CPP #-}
module WxStyle where
import Tables
import Datatypes
import DataText
import Types
import FreeBound
import Focus
import Heuristics
import Builtin
import Manipulation
import Normalise
import Proof
import Theories
import Utilities
import Files
import ImportExport
import Archive
import DocTextParser
import Logic
import UTP
import R
import RAlg

import System.IO
import Graphics.UI.WX
import Graphics.UI.WXCore
--import Graphics.UI.WXCore.Draw

import Data.Char
import Data.List
import Control.Monad

import WxTypes
import WxState

--import Test.QuickCheck hiding (ok, Prop)
import System.FilePath

-- IMPORTANT: INCOMPATIBLE LIBRARY CHANGES
#if __GLASGOW_HASKELL__ < 700
import Control.Parallel.Strategies (rnf)  -- needed with 6.10
import System.IO.Error (try)              -- needed with 6.10
utp2try = try                             -- for 6.10
#else
import Control.DeepSeq (rnf)           -- needed with 7.x
import System.IO.Error (tryIOError)    -- needed with 7.x
utp2try = tryIOError                   -- for 7.x
#endif
\end{code}

\subsection{Text Current Position}

We want to render text so we know where the
next chunk of text should go by returning
where text flow stopped%
\footnote{
It is a bit bizarre that wxWidgets doesn't do this as standard
when drawing text
}%
.
\begin{code}
drawTextCP dc txt (x,y) settings
 = do set dc settings
      drawText dc txt (pt x y) []
      (fSize,_,_) <- getFullTextExtent dc txt
      return (x+sizeW fSize,y)
\end{code}


\subsection{Structured Drawing}

First we define constants for key dimensions:%
\footnote{
These should be gathered in a record that is passed around
to allow customisation
}%
.
\begin{code}
boxOuterSpace = (2::Int)
boxBorder = 1
boxInnerSpace = 2
boxOffset = boxOuterSpace + boxBorder + boxInnerSpace
boxGrow = 2 * boxOffset

tableOuterSpace = (1::Int)
tableBorder = 1
tableInnerSpace = 1
tableOffset = tableOuterSpace + tableBorder + tableInnerSpace
tableGrow = 2 * tableOffset
\end{code}



\subsection{Painting text}

\begin{code}
paintLines text dc viewArea
 = do (fSize,fDesc,fLead) <- getFullTextExtent dc "m"
      let (emH,emW) = (sizeH fSize,sizeW fSize)
      let baselineskip = emH + fDesc + fLead
      drawTextLines dc baselineskip baselineskip emW text

drawTextLines dc bs v h [] = return ()
drawTextLines dc bs v h (ln:lns)
  = do drawText dc ln (pt h v) []
       drawTextLines dc bs (v+bs) h lns


paintText fnt ptext dc viewArea
 = do set dc[font :=fnt]
      -- set dc[fontSize := ifl2009Size]  -- IFL2009
      (fSize,fDesc,fLead) <- getFullTextExtent dc "m"
      let (emH,emW) = (sizeH fSize,sizeW fSize)
      let baselineskip = emH + fDesc + fLead
      drawHiLiteLines dc baselineskip baselineskip emW (lines ptext)

\end{code}
We support highlighting as marked by special characters
(\texttt{eFocusStart},\texttt{eFocusEnd},\texttt{pFocusStart}
 and \texttt{pFocusEnd}).
 The code assumes a sensible use of the above:
\begin{code}

type HiSpec = [Prop (DC ())]
eHilite, pHilite, noHilite :: HiSpec
eHilite  = [fontUnderline := True,  fontWeight := WeightBold  ]
pHilite  = [fontUnderline := True,  fontWeight := WeightNormal]
noHilite = [fontUnderline := False, fontWeight := WeightNormal]

normSplit sces ces [] = reverse ((noHilite,(reverse ces)):sces)
normSplit sces ces (c:cs)
 | c == eFocusStart  =  eHiSplit ((noHilite,(reverse ces)):sces) [] cs
 | c == pFocusStart  =  pHiSplit ((noHilite,(reverse ces)):sces) [] cs
 | otherwise         =  normSplit sces (c:ces) cs

eHiSplit sces ces [] = reverse ((eHilite,(reverse ces)):sces)
eHiSplit sces ces (c:cs)
 | c == eFocusEnd  =  normSplit ((eHilite,(reverse ces)):sces) [] cs
 | otherwise       =  eHiSplit sces (c:ces) cs

pHiSplit sces ces [] = reverse ((pHilite,(reverse ces)):sces)
pHiSplit sces ces (c:cs)
 | c == pFocusEnd  =  normSplit ((pHilite,(reverse ces)):sces) [] cs
 | otherwise       =  pHiSplit sces (c:ces) cs

drawHiLiteLines dc bs v h [] = return ()
drawHiLiteLines dc bs v h (ln:lns)
  = do drawHiLiteText dc (h,v) (normSplit [] [] ln)
       drawHiLiteLines dc bs (v+bs) h lns

drawHiLiteText dc (x,y) [] = return ()
drawHiLiteText dc (x,y) ((hlt,s):rest)
 = do set dc hlt
      drawText dc s (pt x y) []
      (fSize,_,_) <- getFullTextExtent dc s
      drawHiLiteText dc (x+sizeW fSize,y) rest

\end{code}

\subsubsection{Painting Current Predicate}
\begin{code}

paintCPred fnt prVar dc viewArea
 = do pr <- varGet prVar
      paintText fnt ("Current Predicate:\n\n"++show pr) dc viewArea

\end{code}



\subsubsection{Rendering Named Lists}

We render lists of name-thing pairs
as having names and things on separate lines,
with the names emphasised
\begin{code}

nlist_show [] = ""
nlist_show [(n,thing)] = n_show n thing
nlist_show ((n,thing):rest)
 = (n_show n thing) ++ ('\n':nlist_show rest)

n_show n thing
  = "[ "++n++" ]\n"
  ++ show thing

\end{code}


%\subsubsection{Painting Context Types}
%\begin{code}
%
%paintTypes fnt work dc viewArea
% = do pe <- getMstk work
%      let types = envNmdCtxtTypes pe
%      paintText fnt (nlist_show types) dc viewArea
%
%\end{code}
%
%\subsubsection{Painting Context Expressions}
%\begin{code}
%
%paintExprs fnt work dc viewArea
% = do pe <- getMstk  work
%      let exprs = envNmdCtxtExprs pe
%      paintText fnt (nlist_show exprs) dc viewArea
%
%\end{code}
%
%\subsubsection{Painting Context Predicates}
%\begin{code}
%
%paintPreds fnt work dc viewArea
% = do pe <- getMstk work
%      let preds = envNmdCtxtPreds pe
%      paintText fnt (nlist_show preds) dc viewArea
%
%\end{code}
%
%\subsubsection{Painting Context Laws}
%\begin{code}
%
%paintLaws fnt work dc viewArea
% = do pe <- getMstk work
%      let nclaws = envNmdCtxtLaws pe
%      paintText fnt (showLawsByContextAsText nclaws) dc viewArea
%
%\end{code}
%
%\subsubsection{Painting Conjectures}
%\begin{code}
%
%paintConjectures fnt work dc viewArea
% = do pe <- getMstk work
%      let ctables = envNmdCtxtConj pe
%      paintText fnt (nlist_show ctables) dc viewArea
%
%\end{code}
%
%\subsubsection{Painting Theorems}
%\begin{code}
%
%paintTheorems fnt work dc viewArea
% = do pe <- getMstk work
%      let prftables = envNmdCtxtThms pe
%      let thmtables = mapsnd (tmap goal) prftables
%      paintText fnt (nlist_show thmtables) dc viewArea
%   where  mapsnd f = map (\(a,b) -> (a,f b))
%
%\end{code}



\subsubsection{Painting fonts}
\begin{code}

paintFontCodes dc viewArea
 = compFontChars dc [font:=fontDefault]
                    [fontFace := "Symbol"] (10,10) [33..255]

compFontChars dc fd1 fd2 (x,y) [] = return ()
compFontChars dc fd1 fd2 (x,y) (n:ns)
 = do drawText dc (show n++":") (pt x y) [font:=fontSmall]
      drawText dc [chr n]  (pt (x+30) y) fd1
      drawText dc [chr n]  (pt (x+45) y) fd2
      compFontChars dc fd1 fd2 (nx,ny) ns
 where
   (nx,ny) = if x>800 then (10,y+20) else (x+65,y)

\end{code}

\subsubsection{Test Tab Rendering}

\begin{code}
paintTest work dc viewArea
 = do -- text <- testAreaGet work
      paintLines ["paintTest","nyi"] dc viewArea
\end{code}

\subsubsection{Font/Symbol Painting Test}

\begin{code}
viewFonts work
 = do f <- frame [text:="View Fonts"]
      p <- panel f []
      sw <- scrolledWindow p []
      set sw [ on paint := old_paintTest
             , virtualSize := sz 500 800
             , scrollRate := sz 10 10
             , size := sz 500 800
             ]
      set f [ layout
              := container p $ margin 5 $ fill $ widget sw
            ]

old_paintTest :: DC () -> Rect -> IO ()
old_paintTest dc viewArea
  = do dLCP (20,20) "Default" [(font:=fontDefault)::Prop (DC ())]
       dLCP (20,40) "Fixed" [(font:=fontFixed)::Prop (DC ())]
       dLCP (20,60) "Small" [(font:=fontSmall)::Prop (DC ())]
       dLCP (20,80) "Italic" [(font:=fontItalic)::Prop (DC ())]
       dLCP (20,100) "Swiss" [(font:=fontSwiss)::Prop (DC ())]
       dLCP (20,120) "-" [(font:=fontDefault)::Prop (DC ())]
       dSS dc (20,150) False
           ["try some ","text"," based ","highlighting"," for effect"]
       dSym dc (20,200) "Symbol" sym
       dSym dc (20,500) "Default" dfl
  where
   sym = [(fontFace := "Symbol")::Prop (DC ())]
   dfl = [(fontFace := "Default")::Prop (DC ())]
   dL (x,y) name fnt
     = do drawText dc name (pt x y) fnt
          drawText dc [symAll] (pt (x+100) y) sym
          drawText dc "x " (pt (x+110) y) fnt
          drawText dc [symDot] (pt (x+130) y) sym
          drawText dc " P(x) " (pt (x+140) y) fnt
          drawText dc [symImp] (pt (x+200) y) sym
          drawText dc " P(t) " (pt (x+220) y) fnt
          drawText dc [symImp] (pt (x+280) y) sym
          drawText dc [symAny] (pt (x+300) y) sym
          drawText dc "x " (pt (x+310) y) fnt
          drawText dc [symDot] (pt (x+330) y) sym
          drawText dc " P(x) " (pt (x+340) y) fnt
   dLCP (x,y) name fnt
     = do drawText dc name (pt x y) fnt
          (x,y) <- drawTextCP dc [symAll] (x+100,y) sym
          (x,y) <- drawTextCP dc "x " (x,y) fnt
          (x,y) <- drawTextCP dc [symDot] (x,y) sym
          (x,y) <- drawTextCP dc " P(x) " (x,y) fnt
          (x,y) <- drawTextCP dc [symImp] (x,y) sym
          (x,y) <- drawTextCP dc " P(t) " (x,y) fnt
          (x,y) <- drawTextCP dc [symImp] (x,y) sym
          (x,y) <- drawTextCP dc [symAny] (x,y) sym
          (x,y) <- drawTextCP dc "x " (x,y) fnt
          (x,y) <- drawTextCP dc [symDot] (x,y) sym
          drawTextCP dc " P(x) " (x,y) fnt
   dSS dc (x,y) _ [] = return ()
   dSS dc (x,y) highlight (s:ss)
     = if highlight
        then do set dc [fontUnderline := True]
                drawText dc s (pt x y) []
                (fSize,_,_) <- getFullTextExtent dc s
                dSS dc (x+sizeW fSize,y) False ss
        else do set dc [fontUnderline := False]
                drawText dc s (pt x y) []
                (fSize,_,_) <- getFullTextExtent dc s
                dSS dc (x+sizeW fSize,y) True ss
   dSym dc (x,y) fname fnt
    = do drawText dc fname (pt x y) []
         dSymN   0  31  x (y+40) fnt
         dSymN  32  63  x (y+60) fnt
         dSymN  64  95  x (y+80) fnt
         dSymN  96 127 x (y+100) fnt
         dSymN 128 159 x (y+120) fnt
         dSymN 160 191 x (y+140) fnt
         dSymN 192 223 x (y+160) fnt
         dSymN 224 255 x (y+180) fnt
   dSymN lwr upr x y fnt
    = do drawText dc (show lwr++".."++show upr) (pt x y) []
         drawText dc (map chr [lwr..upr]) (pt (x+100) y) fnt

symAll = chr 34
symAny = chr 36
symDot = chr 183
symImp = chr 222

\end{code}

\subsubsection{Rendering style changes from Appearance menu}

When the user selects a menu item the following style
information is changed:
\begin{description}
  \item[Table Border width] change width of table/line pen
  \item[Table Border Style] change table/line pen to solid/dashed
  \item[Font]               change text font
  \item[Text Colour]        change colour of text
  \item[Table Colour]       change pen colour for lines/tables
  \item[Background colour]  change the background colour of each window
  \item[Reset]              revert to default styles
\end{description}

\begin{code}

changePenWidth width work
 = do adjustPenWidth width work
      setStyleStatus work True -- new change made
      repaintFrames work

changeTableStyle dash work
 = do adjustTableStyle dash work
      setStyleStatus work True -- new change made
      repaintFrames work

changeFont fontM work
 = do selectFont work
      setStyleStatus work True -- new change made
      repaintFrames work

changeTextCol tcol work
 = do selectColour work "text"
      setStyleStatus work True -- new change made
      repaintFrames work

changeTCol tableColMenu work
 = do selectColour work "table"
      setStyleStatus work True -- new change made
      repaintFrames work

changeBgColour bgCol work
 = do selectColour work "bg"
      setStyleStatus work True -- new change made
      repaintFrames work

resetStyles work
 = do let frameCol = colorFromInt defaultFrameCol
      setStyleStatus work True -- new change made
      adjustBgColour work frameCol
      setTextStyle work Nothing
      setBoxStyle work Nothing
      setVertStyle work Nothing
      setHorizStyle work Nothing
      setVtStyle work Nothing
      setHtStyle work Nothing
      repaintFrames work

adjustPenWidth width work
 = do vStyle      <- getVertStyle work     -- VertStyle
      hStyle      <- getHorizStyle work    -- HorizStyle
      vtableStyle <- getVtStyle work       -- VTableStyle
      htableStyle <- getHtStyle work       -- HTableStyle
      let newPenDef     =   penDefault{_penWidth = width}  -- default pen with new width
      case vStyle of
           Nothing      ->  setVertStyle  work (Just defaultVertStyle{vPen = newPenDef})
           (Just style) ->  setVertStyle  work (Just style{vPen = (vPen style){_penWidth = width}})
      case hStyle of
           Nothing      ->  setHorizStyle work (Just defaultHorizStyle{hPen = newPenDef})
           (Just style) ->  setHorizStyle work (Just style{hPen = (hPen style){_penWidth = width}})
      case vtableStyle of
           Nothing      ->  setVtStyle    work (Just defaultVTStyle{vtPen = newPenDef})
           (Just style) ->  setVtStyle    work (Just style{vtPen = (vtPen style){_penWidth = width}})
      case htableStyle of
           Nothing      ->  setHtStyle    work (Just defaultHTStyle{htPen = newPenDef})
           (Just style) ->  setHtStyle    work (Just style{htPen = (htPen style){_penWidth = width}})


adjustTableStyle dash work
 = do vStyle      <- getVertStyle work   -- VertStyle
      hStyle      <- getHorizStyle work  -- HorizStyle
      vtableStyle <- getVtStyle work     -- VTableStyle
      htableStyle <- getHtStyle work     -- HTableStyle

      case vStyle of
           Nothing      -> do let newVPen  = createPenDash dash penDefault
                              setVertStyle work (Just defaultVertStyle{vPen = newVPen})
           (Just style) -> do let vpen     = vPen style   -- VertStyle pen
                              let newVPen  = createPenDash dash vpen
                              setVertStyle work (Just style{vPen = newVPen})

      case hStyle of
           Nothing      -> do let newHPen   = createPenDash dash penDefault
                              setHorizStyle work (Just defaultHorizStyle{hPen = newHPen})
           (Just style) -> do let hpen      = hPen style   -- HorizStyle pen
                              let newHPen   = createPenDash dash hpen
                              setHorizStyle work (Just style{hPen = newHPen})

      case vtableStyle of
           Nothing      -> do let newVtPen = createPenDash dash penDefault
                              setVtStyle   work (Just defaultVTStyle{vtPen = newVtPen})
           (Just style) -> do let vtpen    = vtPen style  -- VTableStyle pen
                              let newVtPen = createPenDash dash vtpen
                              setVtStyle   work (Just style{vtPen = newVtPen})

      case htableStyle of
           Nothing      -> do let newHtPen = createPenDash dash penDefault
                              setHtStyle   work (Just defaultHTStyle{htPen = newHtPen})
           (Just style) -> do let htpen    = htPen style  -- HTableStyle pen
                              let newHtPen = createPenDash dash htpen
                              setHtStyle   work (Just style{htPen = newHtPen})

       where createPenDash dash pen
               = case dash of
                 -- Change PenKind of pen based on user option
                      1 -> pen{_penKind = PenDash{_penDash = DashDot}}
                      2 -> pen{_penKind = PenDash{_penDash = DashLong}}
                      3 -> pen{_penKind = PenDash{_penDash = DashDotShort}}
                      4 -> pen{_penKind = PenSolid}

selectFont work
 = do style <- getTextStyle work
      let font = case style of
                      Nothing  -> fontDefault
                      (Just s) -> textFont s
      top <- getTop work
      mbf <- fontDialog top font
      case mbf of
           Just f  -> do -- Now that font changed, create new TextStyle
                         let newNothingStyle = Just defaultTextStyle{textFont = f}
                         case style of
                              Nothing  -> do setTextStyle work newNothingStyle
                              (Just s) -> do setTextStyle work (Just s{textFont = f})
           Nothing -> return ()


selectColour work detail
 = do tStyle <- getTextStyle work
      vtStyle <- getVtStyle work
      bgCol <- getBgColour work
      -- Pick what colour is highlighted when dialog opens
      let c = case detail of
                   "text"  -> case tStyle of
                                   Nothing  -> defaultColour
                                   (Just s) -> textCol s
                   "bg"    -> bgCol
                   "table" -> -- Get pen of VTableStyle
                              case vtStyle of
                                   Nothing  -> _penColor penDefault
                                   (Just s) -> _penColor (vtPen s)
      top <- getTop work
      mbc <- colorDialog top c
      case mbc of
           Just c  -> case detail of
                           "text"  -> adjustTextCol work tStyle c
                           "bg"    -> adjustBgColour work c
                           "table" -> adjustTableColour work c
           Nothing -> return ()


adjustTextCol work style c
 = do case style of
           Nothing  -> do setTextStyle work (Just defaultTextStyle{textCol = c})
           (Just s) -> do setTextStyle work (Just s{textCol = c})


adjustTableColour work colour
 = do vStyle  <- getVertStyle work
      hStyle  <- getHorizStyle work
      vtStyle <- getVtStyle work
      htStyle <- getHtStyle work
      case vStyle of
           Nothing  -> do let vpen = penDefault{_penColor = colour}
                          -- Create new style for Nothing case
                          let newNothingVStyle =
                               Just defaultVertStyle{vPen = vpen}
                          setVertStyle work newNothingVStyle
           (Just s) -> do let pen  = vPen s
                          let vpen = pen{_penColor = colour}
                          setVertStyle work (Just s{vPen = vpen})

      case hStyle of
           Nothing  -> do let hpen = penDefault{_penColor = colour}
                          -- Create new style for Nothing case
                          let newNothingHStyle =
                               Just defaultHorizStyle{hPen = hpen}
                          setHorizStyle work newNothingHStyle
           (Just s) -> do let pen  = hPen s
                          let hpen = pen{_penColor = colour}
                          setHorizStyle work (Just s{hPen = hpen})

      case vtStyle of
           Nothing  -> do let vtpen = penDefault{_penColor = colour}
                          -- Create new style for Nothing case
                          let newNothingVTStyle =
                               Just defaultVTStyle{vtPen = vtpen}
                          setVtStyle work newNothingVTStyle
           (Just s) -> do let pen   = vtPen s
                          let vtpen = pen{_penColor = colour}
                          setVtStyle work (Just s{vtPen = vtpen})

      case htStyle of
           Nothing  -> do let htpen = penDefault{_penColor = colour}
                          -- Create new style for Nothing case
                          let newNothingHTStyle =
                               Just defaultHTStyle{htPen = htpen}
                          setHtStyle work newNothingHTStyle
           (Just s) -> do let pen   = htPen s
                          let htpen = pen{_penColor = colour}
                          setHtStyle work (Just s{htPen = htpen})


adjustBgColour work c
 = do thryFs <- getThryFrames work -- Theory frames
      prfFs  <- getPrfFrms work
      top    <- getTop work
      gws     <- getGWins work
      mws     <- getMWins work
      f      <- getFrame work
      setBgColour work c
      set top  [bgcolor := c]
      set f    [bgcolor := c]
      mapM (\tw -> set (twFrame tw)  [bgcolor := c]) (trieRng thryFs)
      tabsTrie <- mapM (\tw -> return(twTabs tw)) (trieRng thryFs)
      mapM (\tw -> setTabs c tw) (map trieRng tabsTrie)
      mapM (\tw -> set tw  [bgcolor := c]) prfFs
      mapM (\tw -> set tw  [bgcolor := c]) gws
      mapM (\tw -> set tw  [bgcolor := c]) mws
      return ()
      where
        setTabs c [] = return ()
        setTabs c (x:xs) = do set x [bgcolor := c]
                              setTabs c xs


repaintFrames work
 = do f <- getFrame work
      prfFs <- getPrfFrms work
      top <- getTop work
      gws <- getGWins work
      mws <- getMWins work
      thryFs <- getThryFrames work -- Theory frames
      mapM (repaint . twFrame) (trieRng thryFs)
      (repaint f)
      mapM repaint prfFs
      (repaint top)
      mapM repaint gws
      mapM repaint mws
      return ()
\end{code}




\subsubsection{Loading DrawSpec style details from file}

\begin{code}

findTextStyle :: [String] -> Maybe TextStyle
findTextStyle [] = Nothing
findTextStyle (line:rest)
 = if ((words line) !! 0) == "TEXTSTYLE"
   then let font = getFontStyle rest
            colour = getColour rest
        in if font /= Nothing   -- Default TextStyle no longer used,need colour
           then let (Just f)   = font
                    colour = getColour rest

                in case colour of
                        Nothing -> Just (TextStyle f defaultColour)
                        (Just c) -> Just (TextStyle f c)
           else case colour of
                        Nothing -> Just (TextStyle fontDefault defaultColour)
                        (Just c) -> Just (TextStyle fontDefault c)
   else findTextStyle rest

getFontStyle fileLines
 = case ((words(fileLines !! 0)) !! 0) of   -- First word of first line of TextStyle section
        "Nothing"  -> Nothing
        "FontSize" -> let -- Strings from file for FontStyle

                          strFontSize   = getDetail fileLines "FontSize"
                          strFontFamily = getDetail fileLines "FontFamily"
                          strFontShape  = getDetail fileLines "FontShape"
                          strFontWeight = getDetail fileLines "FontWeight"
                          strFontULine  = getDetail fileLines "FontULine"
                          strFontFace   = getFontFace fileLines "FontFace"
                          strFontEncode = getDetail fileLines "FontEncode"
                          -- Convert strings to FontStyle constructors
                          fontSize      = read strFontSize  :: Int
                          fontFamily    = getFontFamily strFontFamily
                          fontShape     = getFontShape  strFontShape
                          fontWeight    = getFontWeight strFontWeight
                          fontULine     = getFontULine  strFontULine
                          fontEncoding  = read strFontEncode :: Int
                      in Just (FontStyle fontSize fontFamily fontShape
                               fontWeight fontULine strFontFace fontEncoding)

getFontFace [] detail = ""
getFontFace (line:rest) detail
 = if (((words line) !! 0) == detail) && (length (words line) /= 1)
   then case (length (words line) == 2) of
             True  -> ((words line) !! 1)
             False -> concatFontFace line ((words line) !! 1) 2
   else getFontFace rest detail

-- We need to concatenate the strings of the FontFace line
-- where the name of the FontFace has multiple words

concatFontFace line acc 0 = acc
concatFontFace line acc count
 = let n = length (words line)
   in if count < n
      then concatFontFace line (acc ++ " " ++ ((words line) !! count)) (count+1)
      else concatFontFace line acc 0

getDetail [] detail = ""
getDetail (line:rest) detail
 = if   ((words line) !! 0) == detail
   then ((words line) !! 1)
   else getDetail rest detail

getFontFamily :: String -> FontFamily
getFontFamily string
 | string == "FontDefault"    = FontDefault
 | string == "FontDecorative" = FontDecorative
 | string == "FontRoman"      = FontRoman
 | string == "FontScript"     = FontScript
 | string == "FontSwiss"      = FontSwiss
 | string == "FontModern"     = FontModern

getFontShape :: String -> FontShape
getFontShape string
 | string == "ShapeNormal"    = ShapeNormal
 | string == "ShapeItalic"    = ShapeItalic
 | string == "ShapeSlant"     = ShapeSlant

getFontWeight :: String -> FontWeight
getFontWeight string
 | string == "WeightNormal"   = WeightNormal
 | string == "WeightBold"     = WeightBold
 | string == "WeightLight"    = WeightLight

getFontULine :: String -> Bool
getFontULine string
 | string == "True"           = True
 | string == "False"          = False

getColour :: [String] -> Maybe Color
getColour [] = Nothing
getColour (line:rest)
 = if ((words line) !! 0) == "TextColour"
   then let colourInt = read ((words line) !! 1) :: Int
        in Just (colorFromInt (colourInt))
   else getColour rest


findBoxStyle :: [String] -> Maybe BoxStyle
findBoxStyle [] = Nothing
findBoxStyle (line:rest)
 = if ((words line) !! 0) == "BOXSTYLE"
   then let pen = getPenStyle rest
        in case pen of
                Nothing -> Nothing
                (Just p) -> Just (BoxStyle p)
   else findBoxStyle rest

findHorizStyle :: [String] -> Maybe HorizStyle
findHorizStyle [] = Nothing
findHorizStyle (line:rest)
 = if ((words line) !! 0) == "HORIZSTYLE"
   then let pen = getPenStyle rest
        in case pen of
                Nothing -> Nothing
                (Just p) -> Just (HorizStyle p)
   else findHorizStyle rest

findVertStyle :: [String] -> Maybe VertStyle
findVertStyle [] = Nothing
findVertStyle (line:rest)
 = if ((words line) !! 0) == "VERTSTYLE"
   then let pen = getPenStyle rest
        in case pen of
                Nothing -> Nothing
                (Just p) -> Just (VertStyle p)
   else findVertStyle rest

findHTableStyle :: [String] -> Maybe HTableStyle
findHTableStyle [] = Nothing
findHTableStyle (line:rest)
 = if ((words line) !! 0) == "HTABLESTYLE"
   then let pen = getPenStyle rest
        in case pen of
                Nothing -> Nothing
                (Just p) -> Just (HTableStyle p)
   else findHTableStyle rest

findVTableStyle :: [String] -> Maybe VTableStyle
findVTableStyle [] = Nothing
findVTableStyle (line:rest)
 = if ((words line) !! 0) == "VTABLESTYLE"
   then let pen = getPenStyle rest
        in case pen of
                Nothing -> Nothing
                (Just p) -> Just (VTableStyle p)
   else findVTableStyle rest

findBackground :: [String] -> Color
findBackground [] = colorFromInt defaultFrameCol
findBackground (l1:l2:rest)
 = if ((words l1) !! 0) == "BACKGROUND"
   then if l2 == "Nothing"
        then colorFromInt defaultFrameCol
        else let col = getDetail (l2:rest) "Colour"
             in colorFromInt $ read col
   else findBackground (l2:rest)



getPenStyle fileLines
 = case ((words(fileLines !! 0)) !! 0) of   -- First word of first line of PenStyle section
        "Nothing"  -> Nothing
        "PenKind"  -> let -- Strings from file for PenStyle

                          strPenKind   = getDetail fileLines "PenKind"
                          strPenColour = getDetail fileLines "PenColor" :: String
                          strPenWidth  = getDetail fileLines "PenWidth"
                          -- Convert strings to PenStyle constructors
                          penKind      = getPenKind strPenKind
                          penColour    = colorFromInt (read strPenColour :: Int) :: Color
                          penWidth     = (read strPenWidth :: Int)
                      in Just (PenStyle penKind penColour penWidth CapRound JoinRound)


getPenKind :: String -> PenKind
getPenKind string
 | string == "PenSolid"  = PenSolid
 | otherwise             = getDash string


getDash :: String -> PenKind
getDash string
 | string == "DashDot"      = PenDash{_penDash = DashDot}
 | string == "DashLong"     = PenDash{_penDash = DashLong}
 | string == "DashDotShort" = PenDash{_penDash = DashDotShort}
 | otherwise                = PenSolid

\end{code}

\subsubsection{Loading Styles from DrawStyles File}

\begin{code}

loadStyleFile appuser
 = do mInh <- utp2try $ openFile sfname ReadMode

      case mInh of
           Left ioerror -> do let ds = setDefaultStyles
                              return ds
           Right inh    -> do contents <- hGetContents inh
                              let styleLines = lines contents
                              let ds = setFileStyles $! styleLines
                              rnf contents `seq` hClose inh
                              return ds
 where
  sfname = appuser ++ [pathSeparator] ++ acalai ++ stile


setDefaultStyles
 = -- Set default styles
   let bcolour       = colorFromInt defaultFrameCol
       textStyle     = Nothing -- Maybe TextStyle
       boxStyle      = Nothing -- Maybe BoxStyle
       horizStyle    = Nothing -- Maybe HorizStyle
       vertStyle     = Nothing -- Maybe VertStyle
       htStyle       = Nothing -- Maybe HTableStyle
       vtStyle       = Nothing -- Maybe VTableStyle
       stylesChanged = False  -- user hasn't clicked "Save Appearance"
   in DrawStyles bcolour textStyle boxStyle horizStyle vertStyle htStyle vtStyle stylesChanged


setFileStyles styleLines
 = -- Find style details for DrawSpec from file
   let bcolour       = findBackground styleLines
       textStyle     = findTextStyle styleLines   -- Maybe TextStyle
       boxStyle      = findBoxStyle styleLines    -- Maybe BoxStyle
       horizStyle    = findHorizStyle styleLines  -- Maybe HorizStyle
       vertStyle     = findVertStyle styleLines   -- Maybe VertStyle
       htStyle       = findHTableStyle styleLines -- Maybe HTableStyle
       vtStyle       = findVTableStyle styleLines -- Maybe VTableStyle
       stylesChanged = False  -- user hasn't clicked "Save Appearance"
    in DrawStyles bcolour textStyle boxStyle horizStyle vertStyle htStyle vtStyle stylesChanged


\end{code}


\subsubsection{Saving Styles to DrawStyles File}

\begin{code}

saveStyleState work
 = do appuser <- getAppUser work
      let sfname = appuser ++ [pathSeparator] ++ acalai ++ stile
      attempt <- utp2try (openFile sfname WriteMode)
      case attempt of
       Left ioerror -> do sts <- getSts work
                          alert sts (unable sfname ioerror)
       Right outh
        -> do setStyleStatus work False -- style saved,no new changes
              saveStyles work outh
              hClose outh
 where
  unable fn io = ("Unable ("++show io++") to save style to "++fn)

-- Saving Draw Styles
saveStyles work outh
 = do tStyle  <- getTextStyle work
      bStyle  <- getBoxStyle work
      hStyle  <- getHorizStyle work
      vStyle  <- getVertStyle work
      htableStyle <- getHtStyle work
      vtableStyle <- getVtStyle work
      bgColour <- getBgColour work
      hPutStrLn outh "TEXTSTYLE"
      printTextStyle tStyle outh
      hPutStrLn outh "BOXSTYLE"
      printPenStyle (getBPen bStyle) outh
      hPutStrLn outh "HORIZSTYLE"
      printPenStyle (getHPen hStyle) outh
      hPutStrLn outh "VERTSTYLE"
      printPenStyle (getVPen vStyle) outh
      hPutStrLn outh "HTABLESTYLE"
      printPenStyle (getHtPen htableStyle) outh
      hPutStrLn outh "VTABLESTYLE"
      printPenStyle (getVtPen vtableStyle) outh
      hPutStrLn outh "BACKGROUND"
      hPutStrLn outh ("Colour " ++ (show $ intFromColor bgColour))

getBPen style
 = case style of
        Nothing -> Nothing
        Just s  -> Just (boxPen s)

getHPen style
 = case style of
        Nothing -> Nothing
        Just s  -> Just (hPen s)

getVPen style
 = case style of
        Nothing -> Nothing
        Just s  -> Just (vPen s)

getHtPen style
 = case style of
        Nothing -> Nothing
        Just s  -> Just (htPen s)

getVtPen style
 = case style of
        Nothing -> Nothing
        Just s  -> Just (vtPen s)

printTextStyle tStyle outh
 = case tStyle of
        Nothing  -> do hPutStrLn outh (show tStyle)
        (Just s) -> do let f = textFont s
                       let c = textCol  s
                       hPutStrLn outh ("FontSize "   ++ (show $ _fontSize      f))
                       hPutStrLn outh ("FontFamily " ++ (show $ _fontFamily    f))
                       hPutStrLn outh ("FontShape "  ++ (show $ _fontShape     f))
                       hPutStrLn outh ("FontWeight " ++ (show $ _fontWeight    f))
                       hPutStrLn outh ("FontULine "  ++ (show $ _fontUnderline f))
                       hPutStrLn outh ("FontFace "   ++ (       _fontFace      f))
                       hPutStrLn outh ("FontEncode " ++ (show $ _fontEncoding  f))
                       hPutStrLn outh ("TextColour " ++ (show $  intFromColor  c))

printPenStyle pen outh
 = case pen of
        Nothing  -> do hPutStrLn outh "Nothing"
        (Just p) -> do let c = _penColor p
                       let pk = case (_penKind p) of
                                     PenSolid  -> show PenSolid
                                     PenDash s -> show (_penDash (_penKind p))
                       hPutStrLn outh ("PenKind "  ++ pk)
                       hPutStrLn outh ("PenColor " ++ (show $  intFromColor c))
                       hPutStrLn outh ("PenWidth " ++ (show $ _penWidth     p))
                       hPutStrLn outh ("PenCap "   ++ (show $ _penCap       p))
                       hPutStrLn outh ("PenJoin "  ++ (show $ _penJoin      p))

\end{code}
