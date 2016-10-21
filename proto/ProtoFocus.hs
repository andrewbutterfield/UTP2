module Tfocus where
import Utilities
import List

data Expr = K Int | Plus [Expr] | Focus Expr

instance Show Expr where
  show (K i) = show i
  show (Plus es) = '(' : (concat $ intersperse "+" $ map show es) ++ ")" 
  show (Focus e) = "{"++show e ++ "}"

type FExpr uctxt = [ (Expr, Int, uctxt) ]

-- invariant: 
--   list non empty
--   Top-level Focus can only appear in last entry
--                         precisely when list is a singleton
--   expr in first element in non-singleton list has no Focus
--   for [..(ce,i,_),(pe,...)..],  descend i pe always succeeds

-- PUBLIC API

set :: uctxt -> Expr -> FExpr uctxt
set c0 e = [ ( Focus $ strip e, 0, c0 ) ]

down :: (Expr -> Int -> dctxt) -- context fragment relevant to path
     -> (uctxt -> dctxt -> Expr -> uctxt)  -- build new context
     -> Int -> FExpr uctxt -> FExpr uctxt
down fd fu i fe@[ (Focus te,k,uc) ]
 = case descend fd i te of
    Nothing  ->  fe
    Just (ne, dc)  ->  let (Just te') = irep (Focus ne) i te
                       in [ (ne,i,fu uc dc ne), (te', k, uc) ]
down fd fu i fe@((ce,j,uc):(pe,k,uc'):rest)
 = case descend fd i ce of
    Nothing  ->  fe
    Just (ne, dc)  ->  let
                        Just ce' = irep (Focus ne) i ce
                        Just pe' = irep ce' j pe
                       in (ne,i,fu uc dc ne):(ce',j,uc):(pe',k,uc'):prop pe' k rest 
down _ _ _ fe = fe

up :: FExpr uctxt -> FExpr uctxt
up fe@[_] = fe
up [(ce,j,uc),(te,k,uc')]
 = let Just te' = irep ce j te
   in [(Focus te',k,uc')]
up ((ce,j,uc):(pe,k,uc'):rest)
 = let
     Just pe' = irep ce j pe
   in (pe',k,uc'):prop (Focus pe') k rest

rep :: Expr -> FExpr uctxt -> FExpr uctxt
rep e [(te,k,uc)] = [(Focus e,k,uc)]   
rep e ((ce,i,uc):rest) = (e,i,uc):prop (Focus e) i rest  

showFE fe = show $ fst3 $ last fe

path :: FExpr uctxt -> [Int]
path ctxts = tail $ reverse $ map snd3 ctxts

clear :: FExpr uctxt -> Expr
clear = strip . fst3 . last 
    
-- UNDER THE HOOD

-- this is where the Expr boilerplate lives

strip :: Expr -> Expr
strip (Focus fe) = strip fe
strip (Plus es) = Plus $ map strip es
strip e = e

descend :: (Expr -> Int -> dctxt) ->Int -> Expr -> Maybe (Expr, dctxt)
descend f i e@(Plus es)
  | 1 <= i && i <= length es  =  Just (es!!(i-1), f e i )
descend _ _ _ = Nothing

irep :: Expr -> Int -> Expr -> Maybe Expr  -- boilerplate
irep ne i (Plus es)
  | 1 <= i && i <= length es  =  Just $ Plus (take i' es ++ ne:drop i es)
  where i' = i-1
irep _ _ oe = Nothing

prop e i [] = []
prop e i ((pe,j,uc):rest)
 = let
    Just pe' = irep e i pe
   in (pe',j,uc):prop pe' j rest


-- TESTING

ex1 = Plus [ K 10
           , Plus [ K 20
                  , K 30
                  , Plus [ K 40
                         , Plus [ K 50
                                , K 60
                                , K 70
                                ]
                         ]
                  ]
           , K 80
           ]
  
uc0 :: (Int, Bool)
uc0 = (0,True)
dcf :: Expr -> Int -> Bool         
dcf  e i = even i
ucf :: (Int,Bool) -> Bool -> Expr -> (Int,Bool)
ucf (uci,_) dc e = (uci+1, dc)

