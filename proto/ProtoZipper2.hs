module ProtoZipper2 where
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

{- Highlighting by marking focus -}

hi = "__hi__"
hiOn = "<<"
hiOff = ">>"

hilite :: P -> P
hilite p = PB hi [p]

zhilite :: Z -> String
zhilite (p, wayup) = phrender $ zend (hilite p, wayup)

phrender :: P -> String
phrender (PK b) = show b
phrender (PB n [p]) 
  | n == hi  =  hiOn ++ phrender p ++ hiOff
phrender (PB n ps) 
  = n ++ "(" ++ pshrender ps ++ ")"
phrender (PE e) = ehrender e

pshrender [] = ""
pshrender [p] = phrender p
pshrender (p:ps) = phrender p ++ ',':pshrender ps

ehrender :: E -> String
ehrender (EK n) = show n
ehrender (EB n es) = n ++ "(" ++ eshrender es ++ ")"
ehrender (EP p) = phrender p

eshrender [] = ""
eshrender [e] = ehrender e
eshrender (e:es) = ehrender e ++ ',':eshrender es

{- Highlighting directly on zipper structure -}

hrender :: Z -> String
hrender ( p, wayup) = hrender' p $ reverse wayup

hrender' p []  = hiOn ++ phrender p ++ hiOff
hrender' p (top:waydown)
 = let rfocus = hrender' p waydown
   in hrender'' rfocus top

hrender'' rfocus (PB' n before after)
 =  let
      rbefore = map phrender before
      rafter  = map phrender after
    in n ++ "(" ++ commasep (rbefore ++ rfocus:rafter) ++ ")"
hrender'' rfocus (PE' (EB' n before after))
 =  let
      rbefore = map ehrender before
      rafter  = map ehrender after
    in n ++ "(" ++ commasep (rbefore ++ rfocus:rafter) ++ ")"

commasep = concat . intersperse ","

-- we need compositional rendering!
--  render F(P,Q) = renderF (render P) (render Q)

ex1 = PB "A" [ PB "B" [PK True]]
ex2 = PB "A" [ pe $ EB "b" [ EB "c" [ EK 42 ]] ]
ex3 = pe $ ep $ pe $ ep $ PK False
ex4 = PB "A" [pe $ EB "b" [ep $ PB "C" [pe $ EB "d" [ep $ PK False]]]]
ex5 = PB "A" [PK False, PK True, PK False]
ex6 = PB "A" [PK False,PE $ EK 42,PK True, PE $ EK 99]

