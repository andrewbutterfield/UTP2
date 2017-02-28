module Pretty where
--import Utilities
import Data.List

data E = EK Int | EB String [E] | EP P deriving Show

-- mandatory version of EP
ep :: P -> E
ep (PE e) = e
ep p      = EP p


data P = PK Bool | PB String [P] | PE E deriving Show

-- mandatory version of PE
pe :: E -> P
pe (EP p) = p
pe e      = PE e

data E' 
 = EB' String 
       [E]   -- before, in reverse order
       [E]   -- after
 | EP' P deriving Show

data P' 
 = PB' String 
       [P]   -- before, in reverse order
       [P]   -- after
 | PE' E' deriving Show

type Z = (P, [P'])

zinit :: P -> Z
zinit p = (p, [])

down :: Z -> Z -- visit first descendant
down (PB n (p:ps),      wayup) = ( p,    PB' n [] ps       : wayup)
down (PE (EB n (e:es)), wayup) = ( pe e, PE' (EB' n [] es) : wayup)
down z = z

up :: Z -> Z
up ( p, above:wayup) = ( build above p, wayup)
up z = z

build :: P' -> P -> P
build (PB' n before after) p       = PB n (reverse before++p:after)
build (PE' (EB' n before after)) p = PE $ EB n (reverse before++ep p:after)
build _ p = p

right :: Z -> Z
right ( p,   PB' n before (p':after) : wayup)
   =  ( p', (PB' n (p:before) after) : wayup)
right ( p,      PE'  (EB' n before      (e':after)) : wayup)
   =  ( pe e', (PE' $ EB' n (ep p : before) after)  : wayup)
right z = z

left :: Z -> Z
left ( p,   PB' n (p':before)  after : wayup)
   = ( p', (PB' n before  (p:after)) : wayup)
left ( p,      PE'  (EB' n (e':before)    after) : wayup)
   = ( pe e', (PE' $ EB' n before (ep p :after)) : wayup)
left z = z

zend :: Z -> P
zend ( p, [])  = p
zend z = zend $ up z


{- 
   Compositional Pretty-Printing 

   we want 
     pretty (F(P,Q)) = prettyF (pretty P) (pretty Q)
-}
data PP 
  = Lit String  -- literal string
  | Ind Int PP  -- indentation
  | Vrt [PP]    -- vertical list
  | Eff String PP String  -- effect, using start/stop strings
  deriving Show

vrt :: [PP] -> PP
vrt [pp] = pp 
vrt pps = Vrt pps

render :: PP -> String
render = unlines . render' 0

render' i (Lit s) =  [indent i s]
render' i (Ind i' pp) = render' (i+i') pp
render' i (Vrt pps) = concat $ map (render' i) pps
render' i (Eff s1 pp s2)
  = case render' i pp of
     [ln] -> [s1++ln++s2]
     (ln:lns) -> (s1++ln):tack s2 lns
  where
    tack s2 [ln] = [ln++s2]
    tack s2 (ln:lns) = ln : tack s2 lns

indent i s = replicate i ' ' ++ s

display :: PP -> IO ()
display = putStrLn . render

-- stick string on front of first 'line'
-- and indent subsequent lines by its length
prepend :: String -> PP -> PP
prepend s = prepend' (length s) s

prepend' len s (Lit s') = Lit (s ++ s')
prepend' len s (Ind i pp) = Ind i $ prepend' len s pp
prepend' len s (Vrt []) = Lit s
prepend' len s (Vrt (pp:pps))
 = vrt [ prepend' len s pp
       , Ind len $ vrt pps ]
prepend' len s (Eff s1 pp s2) = Eff s1 (prepend' len s pp) s2


-- stick first string on first line
-- and second string on remaining lines
lprepend s0 sn (Lit s) = Lit (s0++s)
lprepend s0 sn (Ind i pp) = Ind i $ lprepend s0 sn pp 
lprepend s0 sn (Vrt []) = Lit s0
lprepend s0 sn (Vrt (pp:pps))
 = vrt (prepend s0 pp : map (prepend sn) pps)
lprepend s0 sn (Eff s1 pp s2) = Eff s1 (lprepend s0 sn pp) s2

-- stick string on end of last 'line'
append :: String -> PP -> PP
append s (Lit s') = Lit (s' ++ s)
append s (Ind i pp) = Ind i $ append s pp 
append s (Vrt pps) = vrt $ append' s pps

append' s [] = [Lit s]
append' s [pp] = [append s pp]
append' s (pp:pps) = pp : append' s pps

pp1 = Lit "pp1"
pp2 = Ind 4 pp1
pp3 = Ind 2 pp2
pp4 = Vrt [pp1,pp2,pp3]
pp5 = Ind 20 pp4
pp6 = Vrt [pp1,pp5,pp3]
pp7 = Vrt $ map lit "AbCdEf" where lit c = Lit [c]
{- Highlighting -}

hiOn = boldSGR
hiOff = resetSGR

eSGR n = "\ESC["++show n++"m"
resetSGR = eSGR 0
boldSGR  = eSGR 1

bold str = boldSGR ++ str ++ resetSGR

{- Highlighting directly on zipper structure -}

ppp :: P -> PP
ppp (PK b)    = Lit $ show b
ppp (PB n ps) = ppbuild n $ map ppp ps
ppp (PE e)    = epp e

epp :: E -> PP
epp (EK n)    = Lit $ show n
epp (EB n es) = ppbuild n $ map epp es 
epp (EP p)    = ppp p

ppbuild n [] = Lit (n++"()")
ppbuild n [pp] = prepend (n++"(") $ append ")" pp
ppbuild n (pp:pps)
  = lprepend (n++"(") (indent len ",") $ append ")" 
    $ Vrt (pp:pps)
  where len = length n

zpp :: Z -> PP
zpp z = Lit "zpp nyi"

disp = display . ppp

zdisp = display . zpp

ex1 = PB "A1" [ PB "B" [PK True]]
ex2 = PB "A2" [ pe $ EB "b" [ EB "c" [ EK 42 ]] ]
ex3 = pe $ ep $ pe $ ep $ PK False
ex4 = PB "A4" [pe $ EB "b" [ep $ PB "C" [pe $ EB "d" [ep $ PK False]]]]
ex5 = PB "A5" [PK False, PK True, PK False]
ex6 = PB "A6" [PK False,PE $ EK 42,PK True, PE $ EK 99]
ex7 = PB "A7" [ex1,ex2,ex3,ex4,ex5,ex6]
ex8 = PB "A8" [PB "B8" [PB "C8" [PB "D8" [PK True,PB "E8" []]]]]

