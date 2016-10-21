module Test where
import List

data Expr = K Int | V String | Plus Expr Expr | Times [Expr] | Focus Expr

instance Show Expr where
  show (K i) = show i
  show (V v) = v
  show (Plus e1 e2) = "("++show e1++"+"++show e2++")"
  show (Times es) = concat $ intersperse "*" $ map show es
  show (Focus e) = "{"++show e ++ "}"


stripF :: Expr -> Expr
stripF (Focus fe) = stripF fe
stripF (Plus e1 e2) = Plus (stripF e1) (stripF e2)
stripF (Times es) = Times $ map stripF es
stripF e = e

onFocus :: (Expr -> Expr) -> Expr -> (Bool,Expr)
onFocus f (Focus e) = (True, Focus $ f e)
onFocus _ ee        = (False, ee)

down :: (Expr -> (Bool,Expr)) -> Int -> Expr -> (Bool,Expr)

down f i (Focus e) = down f i e

down f 1 e@(Plus e1 e2)
 | ok         = (ok, Plus e1' e2)
 | otherwise  =  (ok, e)
 where (ok, e1') = f e1
down f 2 e@(Plus e1 e2)
 | ok         = (ok, Plus e1 e2')
 | otherwise  =  (ok, e)
 where (ok, e2') = f e2

down f i e@(Times es)
 | i' < 0          =  (False, e)
 | i' < length es  =  (ok,    Times $ take i' es ++ (e':drop i es))
 | otherwise       =  (ok,    e)
 where
  i' = i-1
  (ok, e') = f (es!!i')

down _ _ e             = (False, e)

get :: Int -> Expr -> (Bool,Expr)

get 1 (Plus e1 e2) = (True, e1)
get 2 (Plus e1 e2) = (True, e2)
get i e@(Times es)
 | i' < 0          =  (False, e)
 | i' < length es  =  (True,  es!!i')
 | otherwise       =  (False, e)
 where i' = i-1


type FP = [Int]


down' :: (Expr -> (Bool, Expr)) -> FP -> Expr -> (Bool,Expr)

down' _ [] e = (False, e)

down' f fp (Focus e) = down' f fp e

down' f [n] e
 | ok         =  (ok, e')
 | otherwise  =  (False, e)
 where (ok,e') = down f n e

down' f (n:ns) e  =  down (down' f ns) n e


get' :: FP -> Expr -> (Bool,Expr)
get' [] e = (True, e)
get' (n:ns) e
 | ok         =  get' ns e'
 | otherwise  =  (ok, e)
 where
   (ok, e') = get n e

type FE = (FP,Expr)

setF :: Expr -> FE
setF e = ([],Focus e)

clrF :: FE -> Expr
clrF (_,fe) = stripF fe

okF :: Expr -> (Bool, Expr)
okF e = (True, Focus e)

downF :: Int -> FE -> FE
downF n fe@([],Focus e)
 | ok         =  ([n],e')
 | otherwise  =  fe
 where (ok,e') = down okF n e
downF n fe@(fp,e)
 | ok         =  (fp++[n],e')
 | otherwise  =  fe
 where
   f (Focus ef) = down okF n ef
   f ee = (False, ee)
   (ok,e') = down' f fp e

okMap :: (Expr -> Expr) -> (Bool,Expr) -> (Bool,Expr)
okMap f (True, e)       =  (True, f e)
okMap _ fe@(False, _)  =  fe

upF :: FE -> FE

upF fe@([],e) = fe

upF fe@([n],e)
 | ok         =  ([],e')
 | otherwise  =  fe
 where
   (ok,e') = okMap Focus $ down f2 n e
   f2 (Focus e)  =  (True, e)
   f2 ee         =  (False, ee)

upF fe@(fp,e)
 | ok         =  (fp',e')
 | otherwise  =  fe
 where
   fp' = init fp
   (ok,e')  =  down' f1 fp' e
   f1  =  okMap Focus . down f2 (last fp)
   f2 (Focus e)  =  (True, e)
   f2 ee         =  (False, ee)

getF :: FE -> Expr
getF (fp,e) = snd $ get' fp e

repFf :: (Expr -> Expr) -> FE -> FE
repFf f fe@(fp,e)
 | ok  =  (fp,e')
 | otherwise  =  fe
 where
   (ok, e')  =  down' (onFocus f) fp e

repF :: Expr -> FE -> FE
repF = repFf . const
