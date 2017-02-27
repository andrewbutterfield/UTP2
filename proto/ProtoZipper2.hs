module ProtoZipper2 where
--import Utilities
--import Data.List

data E
  = EK Int | EB String [E] | EP P 
  deriving Show

data E'
  = EB' String [E] [E] | EP' P'
  deriving Show

data P 
  = PK Bool | PB String [P] | PE E
  deriving Show

data P'
  = PB' String [P] [P] | PE' E'
  deriving Show

type Z = (P, [P'])

zinit :: P -> Z
zinit p = (p, [])

down :: Z -> Z -- visit first descendant
down (PB n (p:ps), wayup) 
 = ( p,  PB' n [] ps : wayup)
down z = z

up :: Z -> Z
up ( p, above:wayup) = ( build above p, wayup)
up z = z

build :: P' -> P -> P
build (PB' n before after) p = PB n (before++p:after)
build _ p = p

ex1 = PB "A" [ PB "B" [PK True]]


