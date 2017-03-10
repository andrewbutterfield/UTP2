\section{Rendering (old style)}
The rendering scheme based on \texttt{DrawSpec}  and \texttt{BB} as separate
datatypes, with the \texttt{pointLookup} function returning
a list of nesting indices is a poor design,
to be replaced by one that is better.
\begin{code}
{-# LANGUAGE CPP #-}
module WxRenderOld where
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
-- import Logic
-- import UTP
-- import R
-- import RAlg

import System.IO
import Graphics.UI.WX
import Graphics.UI.WXCore
--import Graphics.UI.WXCore.Draw

import Data.Char
import Data.List
import Control.Monad

import Test.QuickCheck hiding (ok)
import System.FilePath

#if __GLASGOW_HASKELL__ < 700
import Control.Parallel.Strategies (rnf) -- needed with 6.10.4
#else
import Control.DeepSeq (rnf)                -- needed with 7.x
#endif

import WxTypes
import WxState
import WxStyle

\end{code}



\subsubsection{Bounding Box Computation}

First, given a device context,
we want to be able to compute the bounding-box of a \texttt{DrawSpec}:
\begin{code}

drawSpecBB :: DC a -> DrawSpec -> IO BB

\end{code}
The null-spec. takes up no space.
\begin{code}

drawSpecBB  _ DrawNull = return nullBB

\end{code}
Text-string specs. take the space
determined by the wxHaskell call \texttt{getFullTextExtent},
ignoring descending and leading dimensions (which seem
to be internal).
\begin{code}

drawSpecBB dc (DrawChars style cs)
  = do -- toConsole "drawSpecBB DrawChars"
       case style of
            Nothing -> do (fSize,_,_) <- getFullTextExtent dc cs
                          return (AtmBB (sizeW fSize, sizeH fSize))
            Just st -> do fnt0 <- get dc font
                          let f = textFont st
                          set dc [font := f]
                          (fSize,_,_) <- getFullTextExtent dc cs
                          set dc[font :=fnt0]
                          return (AtmBB (sizeW fSize, sizeH fSize))

drawSpecBB dc (DrawText style cs)
  = do -- toConsole ("drawSpecBB DrawText '"++cs++"'")
       case style of
            Nothing   -> do (fSize,_,_) <- getFullTextExtent dc cs    -- NEED TO USE DEFAULT STYLE!
                            return (AtmBB (sizeW fSize, sizeH fSize))
            Just st   -> do fnt0 <- get dc font
                            let f = textFont st
                            set dc [font := f]
                            (fSize,_,_) <- getFullTextExtent dc cs
                            set dc[font :=fnt0]
                            return (AtmBB (sizeW fSize, sizeH fSize))


\end{code}
A box-spec. takes the bounding box of its constituents
and enlarges it by the \texttt{boxGrow} factor, both width and height.
\begin{code}

drawSpecBB dc (DrawBox style dspec)
  = do -- toConsole "drawSpecBB DrawBox"
       bbx <- drawSpecBB dc dspec
       let (dx,dy) = getbb bbx
       return (BoxBB (dx+boxGrow,dy+boxGrow) bbx)

\end{code}
The horizontal- and vertical-list specs.
line elements up with no extra space,
so the overall bounding box is the sum and maximum
of the appropriate dimensions.
\begin{code}

drawSpecBB dc (DrawHoriz style _ dspecs)
  = do -- toConsole "drawSpecBB DrawHoriz"
       bbxs <- mapM (drawSpecBB dc) dspecs
       let (dxs,dys) = unzip (map getbb bbxs)
       return (ListBB (sum dxs,pmaxima dys) bbxs)

drawSpecBB dc (DrawVert style _ dspecs)
  = do -- toConsole "drawSpecBB DrawVert"
       bbxs <- mapM (drawSpecBB dc) dspecs
       let (dxs,dys) = unzip (map getbb bbxs)
       return (ListBB (pmaxima dxs,sum dys) bbxs)

\end{code}
The horizontal- and vertical-table specs.
involve padding around elements as well as border lines,
and the need to consider the specified `fit' of elements.
\begin{code}

drawSpecBB dc (DrawHTable style n hf vf _ dspecss)
  = do -- toConsole "drawSpecBB DrawHTable"
       bbxss <- mapM (mapM (drawSpecBB dc)) dspecss
       let rss = map (map getbb) bbxss
       let (xss,yss) = (map (map fst) rss,map (map snd) rss)
       let (ws,ell) = (map pmaxima xss,length xss)
       let hs = map pmaxima (transpose yss)
       let dhs = case hf of DrawTight -> hs
                            DrawUniform -> replicate n (pmaxima hs)
       let dws = case vf of DrawTight -> ws
                            DrawUniform -> replicate ell (pmaxima ws)
       let bbx = sum dws + tableOffset*(ell+1)
       let bby = sum dhs + tableOffset*(n+1)
       return (TableBB (bbx,bby) dws dhs bbxss)

drawSpecBB dc (DrawVTable style n hf vf _ dspecss)
  = do -- toConsole "drawSpecBB DrawVTable"
       bbxss <- mapM (mapM (drawSpecBB dc)) dspecss
       let rss = map (map getbb) bbxss
       let (xss,yss) = (map (map fst) rss,map (map snd) rss)
       let (hs,ell) = (map pmaxima yss,length yss)
       let ws = map pmaxima (transpose xss)
       let dhs = case hf of DrawTight -> hs
                            DrawUniform -> replicate ell (pmaxima hs)
       let dws = case vf of DrawTight ->  ws
                            DrawUniform -> replicate n (pmaxima ws)
       let bbx = sum dws + tableOffset*n+tableOffset
       let bby = sum dhs + tableOffset*ell+tableOffset
       return (TableBB (bbx,bby) dws dhs bbxss)

-- drawSpecBB dc _ = return nullBB

\end{code}

\subsubsection{Image Rendering}

We can now define the paint routine:
\begin{code}

paintSpec idvar dc viewArea
 = do idscr <- varGet idvar
      let orig@(x,y) = iorigin idscr
      let dspec = ispec idscr
      -- toConsole "paintSpec about to drawSpecBB"
      bbx <- drawSpecBB dc dspec
      -- toConsole "paintSpec drawSpecBB done"
      --let (bx,by) = getbb bbx -- for debugging
      --drawRect dc (Rect x y bx by) [pen := dotpen] -- ditto
      -- toConsole "paintSpec about to drawSpec"
      drawSpec dspec bbx orig dc viewArea
      -- toConsole "paintSpec drawSpec done"
      varSet idvar (ImageDescr orig dspec bbx)
      -- toConsole "paintSpec idvar set"

dotpen = PenStyle (PenDash DashDot) black 1 CapRound JoinRound

\end{code}
that calls the detailed drawing routine,
whose code assumes that \texttt{DrawSpec} and \texttt{BB} match
as per the \texttt{drawSpecBB} function.
\begin{code}

drawSpec DrawNull _ _ dc viewArea = return ()

drawSpec (DrawChars style cs) _ (x,y) dc viewArea
 = case style of
        Nothing   -> do drawText dc cs (pt x y) []
        Just st   -> do fnt0 <- get dc font
                        let f = textFont st
                        let c = textCol  st
                        set dc [font := f]
                        drawText dc cs (pt x y) [textColor := c]
                        set dc[font :=fnt0]

drawSpec (DrawText style cs) _ (x,y) dc viewArea
  = do case style of
            Nothing   -> do drawText dc cs (pt x y) []
            Just st   -> do fnt0 <- get dc font
                            let f = textFont st
                            let c = textCol  st
                            set dc [font := f]
                            drawText dc cs (pt x y) [textColor := c]
                            set dc[font :=fnt0]



drawSpec (DrawBox style ds) (BoxBB (bx,by) bbx) (x,y) dc viewArea
  = do case style of
            Nothing   -> do let penS   = penDefault
                            drawRect dc (Rect (x+boxOuterSpace) (y+boxOuterSpace)
                                        (bx-boxOuterSpace) (by-boxOuterSpace)) [pen := penS]
                            drawSpec ds bbx (x+3,y+3) dc viewArea
            Just st   -> do let penS   = boxPen st
                            drawRect dc (Rect (x+boxOuterSpace) (y+boxOuterSpace)
                                        (bx-boxOuterSpace) (by-boxOuterSpace)) [pen := penS]
                            drawSpec ds bbx (x+3,y+3) dc viewArea



drawSpec (DrawHoriz style vf dspecs) (ListBB (lx,ly) bbxs) (x,y) dc viewArea
  = do oldPen  <- get dc pen
       let penS = case style of
                       Nothing -> penDefault
                       Just st -> hPen st
       set dc [pen := penS]
       let (dxs,dys) = unzip (map getbb bbxs)
       let dyoffsets = map (vAlign vf ly) dys
       let dxoffsets = offAcc dxs
       let subspecs  = zip (zip dspecs bbxs)
                           (zip (map (x+) dxoffsets)
                           (map (y+) dyoffsets))
       mapM (drawSubSpec dc viewArea) subspecs
       set dc [pen := oldPen]

drawSpec (DrawVert style hf dspecs) (ListBB (lx,ly) bbxs) (x,y) dc viewArea
  = do oldPen  <- get dc pen
       let penS = case style of
                       Nothing -> penDefault
                       Just st -> vPen st
       set dc [pen := penS]
       let (dxs,dys) = unzip (map getbb bbxs)
       let dxoffsets = map (hAlign hf lx) dxs
       let dyoffsets = offAcc dys
       let subspecs  = zip (zip dspecs bbxs)
                           (zip (map (x+) dxoffsets)
                           (map (y+) dyoffsets))
       mapM (drawSubSpec dc viewArea) subspecs
       set dc [pen := oldPen]


drawSpec (DrawHTable style n hf vf brdr dspecss)
         (TableBB (lx,ly) colw rowh bbxss) (x,y) dc viewArea
 = do oldPen <- get dc pen
      let penS = case style of
                      Nothing -> do penDefault
                      Just st -> do htPen st
      let xcoords = map ((x+tableOffset)+)
                        (offAcc (map (+tableOffset) colw))
      let ycoords = map ((y+tableOffset)+)
                        (offAcc (map (+tableOffset) rowh))
      let dspecs = concat dspecss
      let bbxs = concat bbxss
      let offsets = concat (hprod xcoords ycoords)
      let subspecs = zip (zip dspecs bbxs) offsets
      set dc [pen := penS]
      mapM (drawSubSpec dc viewArea) subspecs
      if brdr
        then do drawBorders (lx,ly) colw rowh (x,y) dc viewArea
                set dc [pen := oldPen]
        else set dc [pen := oldPen]


drawSpec (DrawVTable style n hf vf brdr dspecss)
         (TableBB (lx,ly) colw rowh bbxss) (x,y) dc viewArea
 = do oldPen <- get dc pen
      let penS = case style of
                      Nothing -> penDefault
                      Just st -> vtPen st
      let xcoords = map ((x+tableOffset)+)
                        (offAcc (map (+tableOffset) colw))
      let ycoords = map ((y+tableOffset)+)
                        (offAcc (map (+tableOffset) rowh))
      let dspecs = concat dspecss
      let bbxs = concat bbxss
      let offsets = concat (vprod xcoords ycoords)
      let subspecs = zip (zip dspecs bbxs) offsets
      set dc [pen := penS]
      mapM (drawSubSpec dc viewArea) subspecs
      if brdr
        then do drawBorders (lx,ly) colw rowh (x,y) dc viewArea
                set dc [pen := oldPen]
        else set dc [pen := oldPen]



drawSubSpec dc viewArea ((ds,bbx),(x,y))
 = drawSpec ds bbx (x,y) dc viewArea


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
      mapM drawline vlines
      mapM drawline hlines
      return ()
 where
   mkcolborder (top,bottom,left,right) colx = [(pt colx top),(pt colx bottom)]
   mkrowborder (top,bottom,left,right) rowy = [(pt left rowy),(pt right rowy)]
   drawline coords = drawLines dc coords

\end{code}
We need some auxiliary functions.
The function call x\texttt{Align align space}d\texttt{obj}d
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

In order to take a (mouse) point and determine
what it indicates, we need to traverse both the \texttt{DrawSpec} and corresponding
(matching!) \texttt{BB} data-structure, much as was done to render them.
We need to supply the position at which the image was rendered as well.
\begin{code}

pointLookup :: (Int,Int) -> DrawSpec -> BB -> (Int,Int) -> Maybe [Int]

pointLookup (mx,my) DrawNull _ _  = fail ""

pointLookup (mx,my) (DrawChars _ cs) (AtmBB (bx,by)) (x,y)
 = if (mx,my) `inRect` (x,y,bx,by)
    then return []
    else fail ""

pointLookup (mx,my) (DrawText _ cs) (AtmBB (bx,by)) (x,y)
 = if (mx,my) `inRect` (x,y,bx,by)
    then return []
    else fail ""

pointLookup (mx,my) (DrawBox _ ds) (BoxBB (bx,by) bbx) (x,y)
   = do ix <- pointLookup (mx,my) ds bbx (x+boxOffset,y+boxOffset)
        return (0:ix)

pointLookup (mx,my) (DrawHoriz _ vf dspecs) (ListBB (lx,ly) bbxs) (x,y)
  = do let (dxs,dys) = unzip (map getbb bbxs)
       let  dyoffsets = map (vAlign vf ly) dys
       let  dxoffsets = offAcc dxs
       let subspecs = zip (zip dspecs bbxs)
                          (zip (map (x+) dxoffsets)
                               (map (y+) dyoffsets))
       pointLLookup (mx,my) 1 subspecs

pointLookup (mx,my) (DrawVert _ hf dspecs) (ListBB (lx,ly) bbxs) (x,y)
  = do let (dxs,dys) = unzip (map getbb bbxs)
       let  dxoffsets = map (hAlign hf lx) dxs
       let  dyoffsets = offAcc dys
       let subspecs = zip (zip dspecs bbxs)
                          (zip (map (x+) dxoffsets)
                               (map (y+) dyoffsets))
       pointLLookup (mx,my) 1 subspecs

pointLookup (mx,my) (DrawHTable _ n hf vf brdr dspecss)
         (TableBB (lx,ly) colw rowh bbxss) (x,y)
  = do let xcoords = map ((x+tableOffset)+)
                         (offAcc (map (+tableOffset) colw))
       let ycoords = map ((y+tableOffset)+)
                         (offAcc (map (+tableOffset) rowh))
       let dspecs = concat dspecss
       let bbxs = concat bbxss
       let offsets = concat (hprod xcoords ycoords)
       let subspecs = zip (zip dspecs bbxs) offsets
       pointLLookup (mx,my) 1 subspecs

pointLookup (mx,my) (DrawVTable _ n hf vf brdr dspecss)
         (TableBB (lx,ly) colw rowh bbxss) (x,y)
  = do let xcoords = map ((x+tableOffset)+) (offAcc (map (+tableOffset) colw))
       let ycoords = map ((y+tableOffset)+) (offAcc (map (+tableOffset) rowh))
       let dspecs = concat dspecss
       let bbxs = concat bbxss
       let offsets = concat (vprod xcoords ycoords)
       let subspecs = zip (zip dspecs bbxs) offsets
       pointLLookup (mx,my) 1 subspecs

pointLookup (mx,my) _ bbx (x,y) = fail "invalid spec/bb combination"

\end{code}
The following looks down a list of DrawSpec/BB pairs
and returns the appropriate index in the event of success:
\begin{code}

pointLLookup (mx,my) i [] = fail ""
pointLLookup (mx,my) i (((ds,bbx),(x,y)):rest)
 = case pointLookup (mx,my) ds bbx (x,y) of
     Just ix ->  Just (i:ix)
     Nothing -> pointLLookup (mx,my) (i+1) rest

\end{code}
Is a point within a rectangle?
\begin{code}

(x,y) `inRect` (ox,oy,dx,dy)
 = ox <= x && x < ox+dx
   &&
   oy <= y && y < oy+dy

\end{code}
