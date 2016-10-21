module TTypes where
import List
import Utilities
import Tables

type TVar = Int

data Type
 = Tarb
 | Tvar TVar
 | B
 | Z
 | Tprod [Type]
 | Tfun Type Type
 | Terr String [Type]
 deriving (Eq,Ord,Show)

data Expr
 = N Int
 | Var String
 | Lam String Expr 
 | App String Expr -- Lams must be in top-level table for now.
 deriving (Eq, Ord, Show)

data Pred
 = TRUE
 | Not Pred
 | And Pred Pred
 | Obs Expr
 deriving (Eq,Ord,Show)

type VT = Trie TVar            --  Var  -+-> TVar
type TT = Btree TVar Type      --  TVar -+-> Type
type TTT = Trie Type           --  Var  -+-> Type
type TVEQV = [ (TVar, Type) ]  --  TVar equivalences

-- type utilities

-- merge types to get most specific (if it exists)
mrgtyp :: Type -> Type -> ( Type, TVEQV)

mrgtyp t Tarb = (t, [])
mrgtyp Tarb t = (t, [])

mrgtyp t1@(Tvar i) t2@(Tvar j)
 | i == j     =  (t1, [])
 | otherwise  =  (t1, [(i,t2)])

mrgtyp t1@(Tvar i) t2  =  (t2, [(i,t2)])
mrgtyp t1 t2@(Tvar j)  =  (t1, [(j,t1)])

mrgtyp (Tprod ts1) (Tprod ts2)
 = (Tprod ts, eqvs)
 where (ts, eqvs) = mrgtyps ts1 ts2


mrgtyp (Tfun td1 tr1) (Tfun td2 tr2)
 = let (td, deqvs) = mrgtyp td1 td2
       (tr, reqvs) = mrgtyp tr1 tr2
   in (Tfun td tr, deqvs++reqvs)

mrgtyp B B = (B, [])
mrgtyp Z Z = (Z, [])

mrgtyp t1 t2 = (Terr "mrgtyp fail" [t1,t2], [])

mrgtyps :: [Type] -> [Type] -> ([Type],TVEQV)
mrgtyps [] [] = ([], [])

mrgtyps (t1:ts1) (t2:ts2)
 = let (t, teqvs) = mrgtyp t1 t2
       (ts, tseqvs) = mrgtyps ts1 ts2
   in (t:ts, teqvs++tseqvs)

mrgtyps _ _ = ([Terr "mrgtyps of unequal lists" []], [])


etype :: TTT -> VT -> TT -> Expr -> Uniq ( TVar  -- tvar for e
                                         , Type  -- type for e
                                         , VT    -- Var -+-> TVar
                                         , TT    --  TVar -+-> Type
                                         , TVEQV 
                                         )
etype _ vt tt (N _)
 = do tv <- newu
      return (tv,Z,vt,btupdate tv Z tt, [])
      
etype ttt vt tt (Var v)
 = case tlookup vt v of
     Nothing  ->  do tv <- newu
                     let ty = case tlookup ttt v of
                                Nothing   ->  Tvar tv
                                Just vty  ->  vty
                     return (tv,ty,tupdate v tv vt, btupdate tv ty tt, [])
     Just tv  ->  let (Just ty) = btlookup tt tv
                  in return (tv,ty,vt,tt,[])
                  
etype ttt vt tt (Lam x e)
 = do let (origx,vtx) = vtHide x vt -- this x is local
      xtv <- newu
      let xty = Tvar xtv
      (etv,ety,evt,ett,eeqv) <- etype ttt (tupdate x xtv vt) (btupdate xtv xty tt) e
      ltv <- newu
      let lty = Tfun xty ety 
      return (ltv,lty,vtRestore x origx evt,btupdate ltv lty ett,eeqv)

etype ttt vt tt (App f a)
 = do (ftv,fty,fvt,ftt,feqv) <- etype ttt vt tt f
      (atv,aty,avt,att,aeqv) <- etype ttt fvt ftt a
      rtv <- newu
      let rty = Tvar rtv
      let fty' = Tfun aty rty
      case mrgtyp fty fty' of
        (Tfun aty' rty', reqv)
           ->  return ( rtv
                      , rty'
                      , avt
                      , btupdate atv aty' $ btupdate rtv rty' att
                      , feqv++aeqv++reqv
                      )
        (errty, eeqv)
           -> return ( rtv
                     , rty
                     , avt
                     , btupdate rtv (Terr "Fun mismatch" [fty,fty']) att
                     , feqv++aeqv++eeqv 
                     )

etypes :: TTT -> VT -> TT -> [Expr] -> Uniq ( [(TVar,Type)] 
                                            , VT    -- Var -+-> TVar
                                            , TT    --  TVar -+-> Type
                                            , TVEQV 
                                            )
etypes ttt vt tt [] = return ( [], vt, tt, [] )
etypes ttt vt tt (e:es)
 = do (etv,ety,evt,ett,eeqv) <- etype ttt vt tt e
      (estvy,esvt,estt,eseqv) <- etypes ttt evt ett es
      return ( (etv,ety):estvy, esvt, estt, eeqv++eseqv )

vtHide x vt
  = case tlookup vt x of
     Nothing  ->  (Nothing, vt)
     jtv      ->  (jtv, tblank x vt)
     
vtRestore x Nothing vt   = tblank x vt
vtRestore x (Just tv) vt = tupdate x tv vt
                  
prop_Restore_o_Hide x vt
  =  vt == vtRestore x old hvt  
  where (old,hvt) = vtHide x vt         

-- part two : unifying VT,TT,TVEQV to find out (most?) general types

-- part three : building TTT from VT,TT,TVEQV

-- part four: using TTT to determine type of an expression
--              (one drawn from the list in part one above).



-- Test Data
ttt1
 = lbuild 
    [ ("+",Tfun Z $ Tfun Z Z)
    , ("i",Tfun Z Z)
    ]


