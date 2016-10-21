\section{Rendering}

\begin{code}
module WxRender where
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

import Test.QuickCheck hiding (ok)
import System.FilePath

import WxTypes
import WxState
import WxStyle
\end{code}

\subsection{Dimensioning Display Structures}

Rendering a \texttt{DisplayStructure} is at least a three-pass process,
once a device-context (\texttt{DC}) has been identified:
\begin{enumerate}
  \item Traverse structure to compute bounding boxes
    (works from leaves upwards, sorting out alignments on the way up)
  \item Re-traverse to compute origins (top-down)
  \item Re-traverse to render the image on the device context.
\end{enumerate}
The last two steps used to be one (with no explicit origin
annotation in the \texttt{DisplayDescr}),
but have been split apart,
particularly to facilitate overlay rendering
(extra stuff on top of the rendered \texttt{DisplayStructure}).


\subsubsection{Bounding Box Computation}

First, given a device context,
we want to be able to compute the bounding-box of a \texttt{DrawSpec}:
\begin{code}
dispDescrBB :: DC a -> DisplayDescr -> IO DisplayDescr
\end{code}

The null-spec. takes up no space.
\begin{code}
dispDescrBB  _ (DD DDrawNull og _ hdls)
    = return (DD DDrawNull og nullDDBB hdls)
\end{code}

Text-strings take the space
determined by the wxHaskell call \texttt{getFullTextExtent},
ignoring descending and leading dimensions
(which seem to be internal to the bounding box).
\begin{code}
dispDescrBB dc (DD ds@(DDrawText style cs) og _ hdls)
  = do mbb <- drawCharsMBB style dc cs
       return (DD ds og mbb hdls)
  where
   drawCharsMBB Nothing dc cs
    = do (fSize,_,_) <- getFullTextExtent dc cs
         return (sizeW fSize, sizeH fSize)
   drawCharsMBB (Just st) dc cs
    = do fnt0 <- get dc font
         let f = textFont st
         set dc [font := f]
         (fSize,_,_) <- getFullTextExtent dc cs
         set dc[font :=fnt0]
         return (sizeW fSize, sizeH fSize)
\end{code}

A space-spec. takes the bounding box of its constituents
and enlarges it by its four spacing parameters
\begin{code}
dispDescrBB dc (DD ds@(DDrawSpace ls rs bs ts dd) og _ hdls)
  = do dd' <- dispDescrBB dc dd
       let (dx,dy) = getddbb dd'
       return (DD (DDrawSpace ls rs bs ts dd')
                  og (dx+ls+rs,dy+bs+ts) hdls )
\end{code}

A box-spec. takes the bounding box of its constituents
and enlarges it by the \texttt{boxGrow} factor, both width and height.
\begin{code}
dispDescrBB dc (DD ds@(DDrawBox style dd) og _ hdls)
  = do dd' <- dispDescrBB dc dd
       let (dx,dy) = getddbb dd'
       return (DD (DDrawBox style dd')
                  og (dx+boxGrow,dy+boxGrow) hdls )
\end{code}

The horizontal- and vertical-list specs.
line elements up with no extra space,
so the overall bounding box is the sum and maximum
of the appropriate dimensions.
\begin{code}
dispDescrBB dc (DD (DDrawHoriz style da dds _) og _ hdls)
  = do dds' <- mapM (dispDescrBB dc) dds
       let (dxs,dys) = unzip (map getddbb dds')
       let (width,height) = (sum dxs,pmaxima dys)
       return (DD (DDrawHoriz style da dds' height)
                  og (width,height) hdls)

dispDescrBB dc (DD (DDrawVert style da dds _) og _ hdls)
  = do dds' <- mapM (dispDescrBB dc) dds
       let (dxs,dys) = unzip (map getddbb dds')
       let (width,height) = (pmaxima dxs,sum dys)
       return (DD (DDrawVert style da dds' width)
                  og (width,height) hdls)
\end{code}
The horizontal- and vertical-table specs.
involve padding around elements as well as border lines,
and the need to consider the specified `fit' of elements.
\begin{code}
dispDescrBB dc (DD (DDrawHTable style n hf vf db ddss _ _) og _ hdls)
  = do ddss' <- fstmapM (mapM (dispDescrBB dc)) ddss
       let rss = map (map getddbb . fst) ddss'
       let (xss,yss) = (map (map fst) rss,map (map snd) rss)
       let (ws,ell) = (map pmaxima xss,length xss)
       let hs = map pmaxima (transpose yss)
       let dhs = case hf of DrawTight -> hs
                            DrawUniform -> replicate n (pmaxima hs)
       let dws = case vf of DrawTight -> ws
                            DrawUniform -> replicate ell (pmaxima ws)
       let bbx = sum dws + tableOffset*(ell+1)
       let bby = sum dhs + tableOffset*(n+1)
       return (DD (DDrawHTable style n hf vf db ddss' dws dhs)
                  og (bbx,bby) hdls)

dispDescrBB dc (DD (DDrawVTable style n hf vf db ddss _ _) og _ hdls)
  = do ddss' <- fstmapM (mapM (dispDescrBB dc)) ddss
       let rss = map (map getddbb . fst) ddss'
       let (xss,yss) = (map (map fst) rss,map (map snd) rss)
       let (hs,ell) = (map pmaxima yss,length yss)
       let ws = map pmaxima (transpose xss)
       let dhs = case hf of DrawTight -> hs
                            DrawUniform -> replicate ell (pmaxima hs)
       let dws = case vf of DrawTight ->  ws
                            DrawUniform -> replicate n (pmaxima ws)
       let bbx = sum dws + tableOffset*n+tableOffset
       let bby = sum dhs + tableOffset*ell+tableOffset
       return (DD (DDrawVTable style n hf vf db ddss' dws dhs)
                  og (bbx,bby) hdls)
\end{code}

\newpage
\subsubsection{Origin Computation}

\begin{code}
dispDescrOrig :: DisplayDescr -> (Int,Int) -> DisplayDescr
\end{code}
\begin{code}
dispDescrOrig (DD DDrawNull _ mbb clkh) (x,y)
                                     = DD DDrawNull (x,y) mbb clkh
\end{code}

\begin{code}
dispDescrOrig (DD (DDrawText style cs) _ mbb clkh) (x,y)
 = DD (DDrawText style cs) (x,y) mbb clkh
\end{code}

\begin{code}
dispDescrOrig (DD (DDrawSpace ls rs bs ts dd) _ mbb clkh) (x,y)
 = DD (DDrawSpace ls rs bs ts dd') (x,y) mbb clkh
 where dd' = dispDescrOrig dd (x+ls,y+bs)
\end{code}

\begin{code}
dispDescrOrig xx@(DD (DDrawBox style dd) _ mbb clkh) (x,y)
 = DD (DDrawBox style dd') (x,y) mbb clkh
 where dd' = dispDescrOrig dd (x+boxOffset,y+boxOffset)
\end{code}

\begin{code}
dispDescrOrig (DD (DDrawHoriz style vf dds len) _ mbb clkh) (x,y)
 = DD (DDrawHoriz style vf dds' len) (x,y) mbb clkh
 where
   (lx,ly) = mbb
   (dxs,dys) = unzip (map getddbb dds)
   dyoffsets = map (vAlign vf ly) dys
   dxoffsets = offAcc dxs
   subdds  = zip dds (zip (map (x+) dxoffsets)
                          (map (y+) dyoffsets)
                      )
   dds' = map (uncurry dispDescrOrig) subdds
\end{code}

\begin{code}
dispDescrOrig (DD (DDrawVert style hf dds len) _ mbb clkh) (x,y)
 = DD (DDrawVert style hf dds' len) (x,y) mbb clkh
 where
   (lx,ly) = mbb
   (dxs,dys) = unzip (map getddbb dds)
   dxoffsets = map (hAlign hf lx) dxs
   dyoffsets = offAcc dys
   subdds  = zip dds (zip (map (x+) dxoffsets)
                          (map (y+) dyoffsets)
                     )
   dds' = map (uncurry dispDescrOrig) subdds
\end{code}

\begin{code}
dispDescrOrig
  (DD (DDrawHTable style n hf vf brdr ddss colw rowh) _ mbb clkh)
  (x,y)
 = DD (DDrawHTable style n hf vf brdr ddss' colw rowh)
      (x,y) mbb clkh
 where
   xcoords = map ((x+tableOffset)+)
                 (offAcc (map (+tableOffset) colw))
   ycoords = map ((y+tableOffset)+)
                 (offAcc (map (+tableOffset) rowh))
   ddss' = map (distrY ycoords) $ zip ddss xcoords

   distrY ycoords ((dds,clkh),xcoord)
       = (map (appX xcoord) $ zip dds ycoords, clkh)
   appX xcoord (dd,ycoord) = dispDescrOrig dd (xcoord,ycoord)
\end{code}

\begin{code}
dispDescrOrig
  (DD (DDrawVTable style n hf vf brdr ddss colw rowh) _ mbb clkh)
  (x,y)
 = DD (DDrawVTable style n hf vf brdr ddss' colw rowh)
      (x,y) mbb clkh
 where
   xcoords = map ((x+tableOffset)+)
                 (offAcc (map (+tableOffset) colw))
   ycoords = map ((y+tableOffset)+)
                 (offAcc (map (+tableOffset) rowh))
   ddss' = map (distrX xcoords) $ zip ddss ycoords

   distrX xcoords ((dds,clkh),ycoord)
       = (map (appY ycoord) $ zip dds xcoords, clkh)
   appY ycoord (dd,xcoord) = dispDescrOrig dd (xcoord,ycoord)
\end{code}


\newpage
\subsubsection{Image Rendering}

We can now define the paint routine
that calls the detailed drawing routine:
\begin{code}
paintDisplayData :: Var DisplayData -> DC a -> va -> IO ()
paintDisplayData ddvar dc viewArea
 = do ddata <- varGet ddvar
      dd' <- renderDisplayData ddata dc viewArea
      varSet ddvar ddata{ddescr = dd'}

renderDisplayData :: DisplayData -> DC a -> va -> IO DisplayDescr
renderDisplayData ddata dc viewArea
 = do dd1 <- dispDescrBB dc $ ddescr ddata
      let dd2 = dispDescrOrig dd1 $ dorigin ddata
      drawDDescr dc viewArea dd2
      return dd2
\end{code}

We also have a variant with an extra parameter
that allows further drawing after the DisplayDescr has been rendered,
but which does not update any mbb data
(but well may rely on it !)
\begin{code}
overlayDisplayData
     :: Var DisplayData
     -> (DisplayData -> DC a -> va -> IO ())
     -> DC a -> va -> IO ()
overlayDisplayData ddvar overlay dc viewArea
 = do ddata <- varGet ddvar
      dd' <- renderDisplayData ddata dc viewArea
      let ddata' = ddata{ddescr = dd'}
      overlay ddata' dc viewArea
      varSet ddvar ddata'
\end{code}

Sometimes we want to overlay first.
We can do this by merging \texttt{renderDisplayData}
and \texttt{overlayDisplayData}
as follows:
\begin{code}
preOverlayDisplayData
     :: Var DisplayData
     -> (DisplayData -> DC a -> va -> IO ())
     -> DC a -> va -> IO ()
preOverlayDisplayData ddvar overlay dc viewArea
 = do ddata <- varGet ddvar
      dd1 <- dispDescrBB dc $ ddescr ddata
      let dd2 = dispDescrOrig dd1 $ dorigin ddata
      let ddata' = ddata{ddescr = dd2}
      overlay ddata' dc viewArea
      drawDDescr dc viewArea dd2
      varSet ddvar ddata'
\end{code}


Drawing nothing---nothing to do!
\begin{code}
drawDDescr dc viewArea (DD DDrawNull _ _ _) = return ()
\end{code}

Drawing Text:
\begin{code}
drawDDescr dc viewArea (DD (DDrawText style cs) (x,y) _ _)
  = case style of
     Nothing
      -> do drawText dc cs (pt x y) []
     Just st
      -> do fnt0 <- get dc font
            let f = textFont st
            let c = textCol  st
            set dc [font := f]
            drawText dc cs (pt x y) [textColor := c]
            set dc[font :=fnt0]
\end{code}

Drawing a Spaced Item:
\begin{code}
drawDDescr dc viewArea (DD (DDrawSpace ls _ bs _ dd) _ _ _)
  = drawDDescr dc viewArea dd
\end{code}

Drawing a Boxed Item:
\begin{code}
drawDDescr dc viewArea (DD (DDrawBox style dd) (x,y) (bx,by) _)
  = do let penS = case style of
                   Nothing  ->  penDefault
                   Just st  ->  boxPen st
       drawRect dc (Rect (x+boxOuterSpace) (y+boxOuterSpace)
                         (bx-boxOuterSpace) (by-boxOuterSpace))
                   [pen := penS]
       drawDDescr dc viewArea dd
\end{code}

Drawing a Horizontal List:
\begin{code}
drawDDescr dc viewArea (DD (DDrawHoriz style _ dds _) _ _ _)
  = do oldPen  <- get dc pen
       let penS = case style of
                       Nothing -> penDefault
                       Just st -> hPen st
       set dc [pen := penS]
       mapM_ (drawDDescr dc viewArea) dds
       set dc [pen := oldPen]
\end{code}

Drawing a Vertical List:
\begin{code}
drawDDescr dc viewArea (DD (DDrawVert style _ dds _) _ _ _)
  = do oldPen  <- get dc pen
       let penS = case style of
                       Nothing -> penDefault
                       Just st -> vPen st
       set dc [pen := penS]
       mapM_ (drawDDescr dc viewArea) dds
       set dc [pen := oldPen]
\end{code}

Drawing a Horizontal Table:
\begin{code}
drawDDescr
  dc viewArea
  (DD (DDrawHTable style n hf vf brdr ddss colw rowh) (x,y) (lx,ly) _)
 = do oldPen <- get dc pen
      let penS = case style of
                      Nothing -> do penDefault
                      Just st -> do htPen st
      set dc [pen := penS]
      mapM_ (drawDDescr dc viewArea) $ concat $ map fst ddss
      if brdr
        then do drawBorders (lx,ly) colw rowh (x,y) dc viewArea
                set dc [pen := oldPen]
        else set dc [pen := oldPen]
\end{code}

Drawing a Vertical Table:
\begin{code}
drawDDescr
  dc viewArea
  (DD (DDrawVTable style n hf vf brdr ddss colw rowh) (x,y) (lx,ly) _)
 = do oldPen <- get dc pen
      let penS = case style of
                      Nothing -> penDefault
                      Just st -> vtPen st
      set dc [pen := penS]
      mapM_ (drawDDescr dc viewArea) $ concat $ map fst ddss
      if brdr
        then do drawBorders (lx,ly) colw rowh (x,y) dc viewArea
                set dc [pen := oldPen]
        else set dc [pen := oldPen]
\end{code}

Drawing borders:
\begin{code}
drawBorders (lx,ly) colw rowh (x,y) dc viewArea
 = do let bnds@(top,bottom,left,right)
            = ( y+tableOuterSpace
              , y+ly-tableOuterSpace
              , x+tableOuterSpace
              , x+lx-tableOuterSpace
              )
      --drawRect dc (Rect x y lx ly) [pen:=dotpen]
      let colorig = map ((x+tableOuterSpace)+) (offAcc' (map (+tableOffset) colw))
      let roworig = map ((y+tableOuterSpace)+) (offAcc' (map (+tableOffset) rowh))
      let vlines = map (mkcolborder bnds) colorig
      let hlines = map (mkrowborder bnds) roworig
      mapM_ drawline vlines
      mapM_ drawline hlines
      return ()
 where
   mkcolborder (top,bottom,left,right) colx = [(pt colx top),(pt colx bottom)]
   mkrowborder (top,bottom,left,right) rowy = [(pt left rowy),(pt right rowy)]
   drawline coords = drawLines dc coords
\end{code}

We need some auxiliary functions.
The function call x\texttt{Align align space}d \texttt{obj}d
computes the offset of an object
of size \texttt{obj}d in a space of dimension \texttt{space}d,
as specified by \texttt{align}:
\begin{code}
hAlign   DrawLeft _      _    = 0
hAlign DrawCentre spacew objw = (spacew-objw) `div` 2
hAlign  DrawRight spacew objw = spacew-objw
hAlign          _ _      _    = 0

vAlign    DrawTop _      _    = 0
vAlign DrawCentre spacew objw = (spacew-objw) `div` 2
vAlign DrawBottom spacew objw = spacew-objw
vAlign          _ _      _    = 0
\end{code}

The \texttt{offAcc} function turns a list of sizes into
a list of offsets,
whilst
the \texttt{offAcc'} variant adds in the offset due to the last element:
\begin{eqnarray*}
  \lefteqn{\texttt{offAcc} \seqof{x_1,x_2,\ldots,x_{n-1},x_n}}
\\&=& \seqof{0,x_1,x_1+x_2,\ldots,x_1+x+2+\cdots+x_{n-1}}
\\\lefteqn{\texttt{offAcc'} \seqof{x_1,x_2,\ldots,x_{n-1},x_n}}
\\&=&\seqof{0,x_1,x_1+x_2,\ldots,x_1+x+2+\cdots+x_{n-1},x_1+\cdots+x_n}
\end{eqnarray*}
\begin{code}
offAcc xs = oa [] 0 xs
 where oa cca n [] = reverse cca
       oa cca n (x:xs) = oa (n:cca) (n+x) xs

offAcc' xs = oa [] 0 xs
 where oa cca n [] = reverse (n:cca)
       oa cca n (x:xs) = oa (n:cca) (n+x) xs
\end{code}

Function \texttt{hprod} computes the ``product'' of its two list arguments
as nested lists, with 2nd-list iterating fastest:
\begin{eqnarray*}
  \lefteqn{\texttt{hprod}~\seqof{x_1,\ldots,x_m}~\seqof{y_1,\ldots,y_n}}
\\&=& \seqof{\seqof{(x_1,y_1),\ldots,(x_1,y_n)},\ldots,\seqof{(x_m,y_1),\ldots,(x_m,y_n)}}
\end{eqnarray*}
Function \texttt{vprod} is similar except 1st list iterates quickest.
\begin{code}
hprod [] ys = []
hprod (x:xs) ys = (hprod' x ys):(hprod xs ys)

hprod' _ [] = []
hprod' x (y:ys) = (x,y):(hprod' x ys)

vprod xs [] = []
vprod xs (y:ys) = (vprod' xs y):(vprod xs ys)

vprod' [] _ = []
vprod' (x:xs) y = (x,y):(vprod' xs y)
\end{code}

\subsubsection{Point Lookup}

Given a click handler selector,
\texttt{DisplayData} and a (mouse) \texttt{Point}
we can return a list of the handlers associated
with boxes enclosing that point, ordered with the deepest first.
\begin{code}
pointDDLookup :: ClkSelector -> DisplayData -> Point -> [ClkHandler]

pointDDLookup csel
              (DisplayData (x,y) dd)
              (Point mx my)
 = lookupDD [] x y dd
 where
   lookupDD hlist x y (DD ds og (bx,by) hndls)
    | (mx,my) `inRect` (x,y,bx,by)
         = lookupDS (csel hndls `mcons` hlist) x y ds
    | otherwise  =  hlist

   lookupDS hlist _ _ DDrawNull = hlist

   lookupDS hlist _ _ (DDrawText _ _) = hlist

   lookupDS hlist x y (DDrawSpace ls _ bs _ dd)
    = lookupDD hlist (x+ls) (y+bs) dd

   lookupDS hlist x y (DDrawBox _ dd)
    = lookupDD hlist (x+boxOffset) (y+boxOffset) dd

   lookupDS hlist x y (DDrawHoriz _ vf dds ly)
    = do let (dxs,dys) = unzip (map getddbb dds)
         let  dyoffsets = map (vAlign vf ly) dys
         let  dxoffsets = offAcc dxs
         let subdds = zip dds
                          (zip (map (x+) dxoffsets)
                               (map (y+) dyoffsets))
         llookupDD hlist subdds

   lookupDS hlist x y (DDrawVert _ hf dds lx)
    = do let (dxs,dys) = unzip (map getddbb dds)
         let  dxoffsets = map (hAlign hf lx) dxs
         let  dyoffsets = offAcc dys
         let subdds = zip dds
                          (zip (map (x+) dxoffsets)
                               (map (y+) dyoffsets))
         llookupDD hlist subdds

   lookupDS hlist x y (DDrawHTable _ n hf vf brdr ddss colw rowh)
    = do let xcoords' = map ((x+tableOffset)+)
                           (offAcc' (map (+tableOffset) colw))
         let ycoords' = map ((y+tableOffset)+)
                           (offAcc' (map (+tableOffset) rowh))
         let ybottom = last ycoords'
         llookupDTC hlist ybottom xcoords' (tinit ycoords') ddss

   lookupDS hlist x y (DDrawVTable _ n hf vf brdr ddss colw rowh)
    = do let xcoords' = map ((x+tableOffset)+)
                           (offAcc' (map (+tableOffset) colw))
         let ycoords' = map ((y+tableOffset)+)
                           (offAcc' (map (+tableOffset) rowh))
         let xright = last xcoords'
         llookupDTR hlist xright ycoords' (tinit xcoords') ddss

   llookupDD hlist []                = hlist
   llookupDD hlist ((dd,(x,y)):rest) = llookupDD (lookupDD hlist x y dd) rest

   llookupDTC hlist _  []  _  _  =  hlist
   llookupDTC hlist _ [x]  _  _  =  hlist
   llookupDTC hlist _   _ []  _  =  hlist
   llookupDTC hlist _   _  _ []  =  hlist
   llookupDTC hlist yb (x1:xcoords@(x2:_)) ycoords@(yt:_) ((dds,hndls):ddss)
    | (mx,my) `inRect` (x1,yt,x2,yb)
      = llookupDTC hlist' yb xcoords ycoords ddss
    | otherwise = llookupDTC hlist yb xcoords ycoords ddss
    where
      offsets = head (hprod [x1] ycoords)
      subdds = zip dds offsets
      hlist' = llookupDD (csel hndls `mcons` hlist) subdds

   llookupDTR hlist _  []  _  _  =  hlist
   llookupDTR hlist _ [y]  _  _  =  hlist
   llookupDTR hlist _   _ []  _  =  hlist
   llookupDTR hlist _   _  _ []  =  hlist
   llookupDTR hlist xr (y1:ycoords@(y2:_)) xcoords@(xl:_) ((dds,hndls):ddss)
    | (mx,my) `inRect` (xl,y1,xr,y2)
      = llookupDTR hlist' xr ycoords xcoords ddss
    | otherwise = llookupDTR hlist xr ycoords xcoords ddss
    where
      offsets = head (vprod xcoords [y1])
      subdds = zip dds offsets
      hlist' = llookupDD (csel hndls `mcons` hlist) subdds

-- end pointDDLookup
\end{code}
Is a point within a rectangle?
\begin{code}
(x,y) `inRect` (ox,oy,dx,dy)
 = ox <= x && x < ox+dx
   &&
   oy <= y && y < oy+dy
\end{code}
Consing a maybe onto a list:
\begin{code}
mcons :: Maybe a -> [a] -> [a]
Nothing  `mcons` xs = xs
(Just x) `mcons` xs = x:xs
\end{code}

\subsection{Rendering Utilities}

\subsubsection{Display Abstraction}

Sometimes, once rendering has reached the stage where
all coordinates are known,
it can be handdy to filter out all borders, spacing
and null, leaving only the nesting structure of text
and other ``purposefull'' drawings%
\footnote{Of which text is currently the only one}%
.
\begin{code}
abstractDD :: DisplayDescr -> DisplayDescr
abstractDD (DD ds orig mbb clkh) = DD (abstractDS ds) orig mbb clkh

abstractDS :: DisplayStructure -> DisplayStructure
abstractDS (DDrawSpace ls rs bs ts dd) = abstractDS $ ddds dd
abstractDS (DDrawBox mbs dd) = abstractDS $ ddds dd
abstractDS (DDrawHoriz mhs da dds h)
           = DDrawHoriz mhs da (abstractDDS dds) h
abstractDS (DDrawVert mvs da dds w)
           = DDrawVert mvs da (abstractDDS dds) w
abstractDS (DDrawHTable mhts rows hfit vfit brdr ddhs colw rowh)
           = DDrawHTable mhts rows hfit vfit brdr
                         (abstractDDHS ddhs) colw rowh
abstractDS (DDrawVTable mvts cols hfit vfit brdr ddhs colw rowh)
           = DDrawVTable mvts cols hfit vfit brdr
                         (abstractDDHS ddhs) colw rowh
abstractDS ds = ds

abstractDDS  :: [DisplayDescr] -> [DisplayDescr]
abstractDDS = filter notDDnull . map abstractDD

notDDnull :: DisplayDescr -> Bool
notDDnull (DD DDrawNull _ _ _)  =  False
notDDnull _                     =  True

abstractDDHS  :: [([DisplayDescr],ClkHandlers)]
              -> [([DisplayDescr],ClkHandlers)]
abstractDDHS = map abstractDDSH

abstractDDSH  :: ([DisplayDescr],ClkHandlers)
              -> ([DisplayDescr],ClkHandlers)
abstractDDSH (dds,clkh) = (abstractDDS dds, clkh)
\end{code}

\subsection{Stuff}

\begin{code}
fstmapM f abs
 = do let as = map fst abs
      as' <- mapM f as
      return $ zipWith updfst as' abs   -- $
\end{code}



