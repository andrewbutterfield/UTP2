\section{Type Inference and Checking}

\begin{code}
module Types where
import Data.Char
import Data.List
import Data.Maybe
import Control.Monad
import Tables
import Datatypes
import DataText
import DSL
import Utilities
import Focus
import AlphaSubs
import MatchTypes
import Matching
import MatchingType
import FreeBound
\end{code}



\subsection{Type Inference}

We really need a proper type inference system.
\input{doc/Types-Inference}

\subsection{Top-Level Type Inference}

At the top level we always have a predicate, within which expressions are
embedded.
The main idea is that we build a table (\texttt{VarTypes}) that maps
(observation) variables to \texttt{Type}s.
We then deal with nested scopes by using a list of indices (\texttt{TTTag})
giving variable-type tables in order from deepest scope to topmost,
the topmost always having tag 0.
\begin{code}
setFPredTypes :: MatchContext -> FPred -> (FPred, TypeTables, [Message])
setFPredTypes mctxt fpr
 = (globalPFapp (const pr') fpr, ttbl', terrs')
 where (pr', ttbl', terrs') = setPredTypes mctxt $ clearPFocus fpr

setPredTypes :: MatchContext -> Pred -> (Pred, TypeTables, [Message])
setPredTypes mctxt pr
 = let (pr', tts', teqs') = runu 1 $ setpredtypes mctxt $ setTypeTags pr
       (tvt', terrs') = solveTypeEqns teqs'
       tts'' = btmap (tmap (snd . typeVarMap tvt')) tts'
   in (pr', tts'', terrs')
 where
  setpredtypes mctxt pr
   = do (pr',ttalist) <- recBoundTVars mctxt pr
        let ttbls' = bbuild ttalist
        (vt0, ttbls'', teqns) <- harvestTypeEqns mctxt ttbls' pr'
        let ttbls''' = btupdate 0 vt0 ttbls''
        return (pr', ttbls''', teqns)
\end{code}

An string giving error details would be nice:
\begin{code}
typeErrorDetails :: Pred -> [Message] -> TypeTables -> String
typeErrorDetails pred msgs tts
 = ( show pred
   ++ "\n-----"
   ++ concat (map ('\n':) msgs)
   ++ "\n-----"
   ++ showAllTTS 0 tts
   )

showAllTTS i tts
 = render $ mapfst show $ mapsnd (mapsnd show . flattenTrie) $ inorder tts
 where
   render = concat . map render'
   render' (ttag,vtyps) = concat $ map (render'' ttag) vtyps
   render'' ttag (vnm,vtyp) = hdr i ++ ttag++"."++vnm++" : "++vtyp
\end{code}

Typechecker with error reporting:
\begin{code}
typeCheckPred :: MatchContext -> Pred -> Either String (Pred, TypeTables)
typeCheckPred mctxt pred
 | null msgs'  =  Right (pred', tts')
 | otherwise   =  Left $ typeErrorDetails pred' msgs' tts'
 where (pred', tts', msgs') = setPredTypes mctxt pred
\end{code}


A variant that just ignores messages:
\begin{code}
fpredTypeTables :: MatchContext -> FPred -> (FPred, TypeTables)
fpredTypeTables mctxt fpr
 = (globalPFapp (const pr') fpr, ttbl')
 where (pr', ttbl') = predTypeTables mctxt $ clearPFocus fpr

predTypeTables :: MatchContext -> Pred -> (Pred, TypeTables)
predTypeTables mctxt pr = (pr',tts')
 where (pr',tts',_) = setPredTypes mctxt pr
\end{code}



\subsubsection{Assigning Unique Table Tags}

We need a way to annotate all binders with unique type-table tags
\begin{code}
setTypeTags :: Pred -> Pred
setTypeTags pr
 = runu 1 $ pset pr
 where

   pset (Obs e)  =  fmap Obs $ eset e
   pset (Defd e)  =  fmap Defd $ eset e
   pset (TypeOf e typ) = fmap (flip TypeOf typ) $ eset e

   pset (Not pr)  =  fmap Not $ pset pr
   pset (And prs)  =  fmap And $ mapM pset prs
   pset (Or prs)  =  fmap Or $ mapM pset prs
   pset (Imp pr1 pr2)  =  liftM2 Imp (pset pr1) (pset pr2)
   pset (Eqv pr1 pr2)  =  liftM2 Eqv (pset pr1) (pset pr2)
   pset (Forall _ qvs pr) = qset1 Forall qvs pset pr
   pset (Exists _ qvs pr)  =  qset1 Exists qvs pset pr
   pset (Exists1 _ qvs pr)  =  qset1 Exists1 qvs pset pr
   pset (Univ _ pr)
    = do tt <- newu
         pr' <- pset pr
         return $ Univ tt pr'
   pset (Sub pr esub)  =  liftM2 Sub (pset pr) (sset eset esub)
   pset (If prc prt pre)  =  liftM3 If (pset prc) (pset prt) (pset pre)
   pset (NDC pr1 pr2)  =  liftM2 NDC (pset pr1) (pset pr2)
   pset (RfdBy pr1 pr2)  =  liftM2 RfdBy (pset pr1) (pset pr2)
   pset (Lang str i les sss)
    =  do les' <- mapM lset les
          return $ Lang str i les' sss
   pset (Pforall qvs pr)  =  fmap (Pforall qvs) $ pset pr
   pset (Pexists qvs pr)  =  fmap (Pexists qvs) $ pset pr
   pset (Psub pr psub)  =  liftM2 Psub (pset pr) (sset pset psub)
   pset (Psapp pr prset)  =  liftM2 Psapp (pset pr) (psset prset)
   pset (Psin pr prset)  =  liftM2 Psapp (pset pr) (psset prset)
   pset (Peabs qvs pr)  =  fmap (Peabs qvs) $ pset pr
   pset (Ppabs qvs pr)  =  fmap (Ppabs qvs) $ pset pr
   pset (Papp pr1 pr2)  =  liftM2 Papp (pset pr1) (pset pr2)
   pset (Pfocus pr)  =  fmap Pfocus $ pset pr
   pset pr  =  return pr

   lset (LExpr e)  =  fmap LExpr $ eset e
   lset (LPred pr)  =  fmap LPred $ pset pr
   lset (LList les)  =  fmap LList $ mapM lset les
   lset (LCount les)  =  fmap LCount $ mapM lset les
   lset le  =  return le

   psset (PSet prs)  =  fmap PSet $ mapM pset prs
   psset (PSetC qvs pr1 pr2)  =  liftM2 (PSetC qvs) (pset pr1) (pset pr2)
   psset (PSetU prset1 prset2)  =  liftM2 PSetU (psset prset1) (psset prset2)
   psset prset  =  return prset


   eset (Prod es)  =  fmap Prod $ mapM eset es
   eset (App str e)  =  fmap (App str) $ eset e
   eset (Bin str i e1 e2)  =  liftM2 (Bin str i) (eset e1) (eset e2)
   eset (Equal e1 e2)  =  liftM2 Equal (eset e1) (eset e2)
   eset (Set es)  =  fmap Set $ mapM eset es
   eset (Setc _  qvs pr e)  =  qset2 Setc qvs pset pr eset e
   eset (Seq es)  =  fmap Seq $ mapM eset es
   eset (Seqc _ qvs pr e)  =  qset2 Seqc qvs pset pr eset e
   eset (Map drs)
    = do let (des,res) = unzip drs
         des' <- mapM eset des
         res' <- mapM eset res
         return $ Map $ zip des' res'
   eset (Cond pr e1 e2)  =  liftM3 Cond (pset pr) (eset e1) (eset e2)
   eset (Build str es)  =  fmap (Build str) $ mapM eset es
   eset (The _ str pr)  =  qset1 The str pset pr
   eset (Eabs _ qvs e)  =  qset1 Eabs qvs eset e
   eset (Esub e esub)  =  liftM2 Esub (eset e) (sset eset esub)
   eset (Efocus e)  =  fmap Efocus $ eset e
   eset (EPred pr)  =  fmap EPred $ pset pr
   eset e  =  return e

   qset1 quant qvs tset thing
    = do tt <- newu
         thing' <- tset thing
         return $ quant tt qvs thing'

   qset2 quant qvs t1set thing1 t2set thing2
    = do tt <- newu
         thing1' <- t1set thing1
         thing2' <- t2set thing2
         return $ quant tt qvs thing1' thing2'

   sset tset (Substn sub)
    = do let (xs,ts) = unzip sub
         ts' <- mapM tset ts
         return $ Substn (zip xs ts')
\end{code}

\subsubsection{Setting up Type Tables}

Given a tagged predicate,
we want to create the relevant tables,
and populate them with the bound variables mapped to
unique type variables:
\begin{code}
recBoundTVars :: MatchContext -> Pred -> Uniq (Pred, [(TTTag,VarTypes)])
recBoundTVars mctxt pr
 = prec [] pr
 where

   prec tts (Obs e)  =  fmap12 Obs erec tts e
   prec tts (Defd e)  =  fmap12 Defd erec tts e
   prec tts (TypeOf e typ)  =  fmap12 (flip TypeOf typ) erec tts e
   prec tts (Not pr)  =  fmap12 Not prec tts pr
   prec tts (And prs)  =  app12 And $ mapM12 prec tts prs
   prec tts (Or prs)  =  app12 Or $ mapM12 prec tts prs
   prec tts (Imp pr1 pr2)  =  liftM12 Imp tts prec pr1 prec pr2
   prec tts (Eqv pr1 pr2)  =  liftM12 Eqv tts prec pr1 prec pr2
   prec tts (Forall tt qvs pr)  =  qrec tts Forall tt qvs prec pr
   prec tts (Exists tt qvs pr)  =  qrec tts Exists tt qvs prec pr
   prec tts (Exists1 tt qvs pr)  =  qrec tts Exists1 tt qvs prec pr
   prec tts (Univ tt pr)
    = do let vs = predFreeVars mctxt pr
         vtyps <- qvrec tnil vs
         let tts' = (tt,vtyps):tts
         (pr', tts'') <- prec tts' pr
         return (Univ tt pr', tts'')
   prec tts (Sub pr esub)  =  liftM12 Sub tts prec pr (srec erec) esub
   prec tts (If prc prt pre)  =  liftM13 If tts prec prc prec prt prec pre
   prec tts (NDC pr1 pr2)  =  liftM12 NDC tts prec pr1 prec pr2
   prec tts (RfdBy pr1 pr2)  =  liftM12 RfdBy tts prec pr1 prec pr2
   prec tts (Lang str i les sss)
    =  do (les',tts') <- mapM12 lrec tts les
          return (Lang str i les' sss, tts')
   prec tts (Pforall qvs pr)  =  fmap12 (Pforall qvs) prec tts pr
   prec tts (Pexists qvs pr)  =  fmap12 (Pexists qvs) prec tts pr
   prec tts (Psub pr psub)  =  liftM12 Psub tts prec pr (srec prec) psub
   prec tts (Psapp pr prset)  =  liftM12 Psapp tts prec pr psrec prset
   prec tts (Psin pr prset)  =  liftM12 Psin tts prec pr psrec prset
   prec tts (Peabs qvs pr)  =  fmap12 (Peabs qvs) prec tts pr
   prec tts (Ppabs qvs pr)  =  fmap12 (Ppabs qvs) prec tts pr
   prec tts (Papp pr1 pr2)  =  liftM12 Papp tts prec pr1 prec pr2
   prec tts (Pfocus pr)  =  fmap12 Pfocus prec tts pr
   prec tts pr  =  return (pr, tts)

   lrec tts (LExpr e)  =  app12 LExpr $ erec tts e
   lrec tts (LPred pr)  =  app12 LPred $ prec tts pr
   lrec tts (LList les)  =  app12 LList $ mapM12 lrec tts les
   lrec tts (LCount les)  =  app12 LCount $ mapM12 lrec tts les
   lrec tts le  =  return (le, tts)

   psrec tts (PSet prs)  =  app12 PSet $ mapM12 prec tts prs
   psrec tts (PSetC qvs pr1 pr2)  =  liftM12 (PSetC qvs) tts prec pr1 prec pr2
   psrec tts (PSetU prrec1 prrec2)  =  liftM12 PSetU tts psrec prrec1 psrec prrec2
   psrec tts prrec  =  return (prrec, tts)

   erec tts (Prod es)  =  app12 Prod $ mapM12 erec tts es
   erec tts (App str e)  =  fmap12 (App str) erec tts e
   erec tts (Bin str i e1 e2)  =  liftM12 (Bin str i) tts erec e1 erec e2
   erec tts (Equal e1 e2)  =  liftM12 Equal tts erec e1 erec e2
   erec tts (Set es)  =  app12 Set $ mapM12 erec tts es
   erec tts (Setc tt qvs pr e)  =  qrec2 tts Setc tt qvs prec pr erec e
   erec tts (Seq es)  =  app12 Seq $ mapM12 erec tts es
   erec tts (Seqc tt qvs pr e)  =  qrec2 tts Seqc tt qvs prec pr erec e
   erec tts (Map drs)  =  app12 Map $ mrec tts drs
   erec tts (Cond pr e1 e2)  =  liftM13 Cond tts prec pr erec e1 erec e2
   erec tts (Build str es)  =  app12 (Build str) $ mapM12 erec tts es
   erec tts (The tt v pr)
    = do tv <- newu
         let vtyps = tsingle (varKey v) $ tag2tvar tv
         let tts' = (tt,vtyps):tts
         (pr', tts'') <- prec tts' pr
         return (The tt v pr', tts'')
   erec tts (Eabs tt qvs e)  =  qrec tts Eabs tt qvs erec e
   erec tts (Esub e esub)  =  liftM12 Esub tts erec e (srec erec) esub
   erec tts (Efocus e)  =  fmap12 Efocus erec tts e
   erec tts (EPred pr)  =  fmap12 EPred prec tts pr
   erec tts e  =  return (e, tts)

   qrec tts quant tt qvs@(Q vs) trec thng
    = do vtyps <- qvrec tnil vs
         let tts' = (tt,vtyps):tts
         (thng', tts'') <- trec tts' thng
         return (quant tt qvs thng', tts'')

   qvrec vtyps [] = return vtyps
   qvrec vtyps (v:vs)
    = do tv <- newu
         let vtyps' = tvupdate v (tag2tvar tv) vtyps
         qvrec vtyps' vs

   qrec2 tts quant tt qvs@(Q vs) t1rec th1 t2rec th2
    = do vtyps <- qvrec tnil vs
         let tts' = (tt,vtyps):tts
         (th1', tts'') <- t1rec tts' th1
         (th2', tts''') <- t2rec tts' th2
         return (quant tt qvs th1' th2', tts''')

   mrec tts drs
    = do let (des,res) = unzip drs
         (des', tts') <- mapM12 erec tts des
         (res', tts'') <- mapM12 erec tts' res
         return (zip des' res', tts'')

   srec trec tts (Substn sub)
    = do let (xs,ts) = unzip sub
         (ts',tts') <-  mapM12 trec tts ts
         return (Substn (zip xs ts'), tts')

   fmap12 cons trec tts thing
    = do (thing',tts') <- trec tts thing
         return (cons thing', tts')

   mapM12 trec tts [] = return ([], tts)
   mapM12 trec tts (thing:things)
    = do (thing', tts') <- trec tts thing
         (things', tts'') <- mapM12 trec tts' things
         return (thing':things', tts'')

   app12 cons res
    = do (thing, tts) <- res
         return (cons thing, tts)

   liftM12 cons tts t1rec th1 t2rec th2
    = do (th1',tts') <- t1rec tts th1
         (th2',tts'') <- t2rec tts' th2
         return (cons th1' th2', tts'')

   liftM13 cons tts t1rec th1 t2rec th2 t3rec th3
    = do (th1',tts') <- t1rec tts th1
         (th2',tts'') <- t2rec tts' th2
         (th3',tts''') <- t3rec tts'' th3
         return (cons th1' th2' th3', tts''')
\end{code}

Making a type-var from a tag:
\begin{code}
tag2tvar :: Int -> Type
tag2tvar tag = Tvar $ 't':show tag
\end{code}


\subsubsection{Type Tables Management}

When we encounter a variable,
we are in a nested context denoted by a list (deepest first)
of \texttt{TTTag}s.
We search the corresponding tables for the variable.
If present, there is nothing more to do other than note its type.
If absent, then we add it to the top level table, with a new type-variable.
\begin{code}
recVarType :: MatchContext -> VarTypes -> TypeTables -> Variable
           -> [TTTag] -> Uniq (Type,VarTypes)
recVarType mctxt vt0 tts v []
 = case tvlookup vt0 v of
     Just t  ->  return (t, vt0)
     Nothing
      -> case tsvlookup (knownTypes mctxt) v of
           Just t -> do t' <- freshType t
                        return (t' ,tvupdate v t' vt0)
           Nothing
             -> do tv <- newu
                   let t = tag2tvar tv
                   return (t, tvupdate v t vt0)
recVarType mctxt vt0 tts v vts@(tag:tags)
 = case btlookup tts tag of
     Nothing  ->  error ("Types.recVarType - no table with tag "++show tag)
     Just vtyps
       -> case tvlookup vtyps v of
            Just t   ->  return (t, vt0)
            Nothing  ->  recVarType mctxt vt0 tts v tags
\end{code}
The \texttt{error} should never happen.


\subsubsection{Harvesting Type Equations}

We go through the predicate, with tags and bound-variables already set up,
harvesting all variables and noting their types, and type equivalences
as equations
\begin{code}
type TypeEqn = (Type, Type)

harvestTypeEqns :: MatchContext -> TypeTables -> Pred
                 -> Uniq ( VarTypes   -- top-level variable types
                         , TypeTables -- quantifier type tables
                         , [TypeEqn]  -- type equations
                         )
harvestTypeEqns mctxt tts pr
 = phvst tnil tts [] pr
 where

   phvst vt0 tts tags (Obs e)
    = do (te,(vt',tts',teqs)) <- ehvst vt0 tts tags e
         return (vt',tts,(te,B):teqs) -- Obs must be boolean
   phvst vt0 tts tags (Defd e)  =  fmap snd $ ehvst vt0 tts tags e
   phvst vt0 tts tags (TypeOf e typ)  =  fmap snd $ ehvst vt0 tts tags e
   phvst vt0 tts tags (Not pr)  =  phvst vt0 tts tags pr
   phvst vt0 tts tags (And prs)  =  pshvst vt0 tts tags prs
   phvst vt0 tts tags (Or prs)  =  pshvst vt0 tts tags prs
   phvst vt0 tts tags (Imp pr1 pr2)  =  pshvst vt0 tts tags [pr1,pr2]
   phvst vt0 tts tags (Eqv pr1 pr2)  =  pshvst vt0 tts tags [pr1,pr2]
   phvst vt0 tts tags (Forall tt qvs pr)  =  phvst vt0 tts (tt:tags) pr
   phvst vt0 tts tags (Exists tt qvs pr)  =  phvst vt0 tts (tt:tags) pr
   phvst vt0 tts tags (Exists1 tt qvs pr)  =  phvst vt0 tts (tt:tags) pr
   phvst vt0 tts tags (Univ tt pr)  =  phvst vt0 tts (tt:tags) pr
   phvst vt0 tts tags (Sub pr (Substn ssub))
    = do (vt0', tts', teqs') <- phvst vt0 tts tags pr
         (vt0'',tts'',teqs'') <- fmap snd $ eshvst vt0' tts' tags
                                          $ map snd ssub
         return (vt0'', tts'', teqs'++teqs'')
   phvst vt0 tts tags (If prc prt pre)  =  pshvst vt0 tts tags [prc,prt,pre]
   phvst vt0 tts tags (NDC pr1 pr2)  =  pshvst vt0 tts tags [pr1,pr2]
   phvst vt0 tts tags (RfdBy pr1 pr2)  =  pshvst vt0 tts tags [pr1,pr2]
   phvst vt0 tts tags (Lang str i les sss)  =  lshvst vt0 tts tags les
   phvst vt0 tts tags (Pforall qvs pr)  =  phvst vt0 tts tags pr
   phvst vt0 tts tags (Pexists qvs pr)  =  phvst vt0 tts tags pr
   phvst vt0 tts tags (Psub pr (Substn ssub))
    = do (vt0', tts', teqs') <- phvst vt0 tts tags pr
         (vt0'',tts'',teqs'') <- pshvst vt0' tts' tags $ map snd ssub
         return (vt0'', tts'', teqs'++teqs'')
   phvst vt0 tts tags (Psapp pr prset)  =  psethvst vt0 tts tags pr prset
   phvst vt0 tts tags (Psin pr prset)  =  psethvst vt0 tts tags pr prset
   phvst vt0 tts tags (Peabs qvs pr)  =  phvst vt0 tts tags pr
   phvst vt0 tts tags (Ppabs qvs pr)  =  phvst vt0 tts tags pr
   phvst vt0 tts tags (Papp pr1 pr2)  =  pshvst vt0 tts tags [pr1,pr2]
   phvst vt0 tts tags (Pfocus pr)  =  phvst vt0 tts tags pr
   phvst vt0 tts tags _  =  return (vt0, tts, [])

   pshvst vt0 tts tags [] = return (vt0, tts, [])
   pshvst vt0 tts tags (pr:prs)
    = do (vt0', tts', teqs') <- phvst vt0 tts tags pr
         (vt0'', tts'', teqs'') <-  pshvst vt0' tts' tags prs
         return (vt0'', tts'',  teqs'++teqs'')

   lhvst vt0 tts tags (LExpr e)  =  fmap snd $ ehvst vt0 tts tags e
   lhvst vt0 tts tags (LPred pr)  =   phvst vt0 tts tags pr
   lhvst vt0 tts tags (LList les)  =  lshvst vt0 tts tags les
   lhvst vt0 tts tags (LCount les)  =  lshvst vt0 tts tags les
   lhvst vt0 tts tags _  =  return (vt0, tts, [])

   lshvst vt0 tts tags [] = return (vt0, tts, [])
   lshvst vt0 tts tags (le:les)
    = do (vt0', tts', teqs') <- lhvst vt0 tts tags le
         (vt0'', tts'', teqs'') <-  lshvst vt0 tts tags les
         return (vt0'', tts'',  teqs'++teqs'')

   psethvst vt0 tts tags pr prset
    = do (vt0', tts', teqs') <- phvst vt0 tts tags pr
         (vt0'', tts'', teqs'') <- sethvst vt0' tts' tags prset
         return (vt0'', tts'', teqs'++teqs'')

   sethvst vt0 tts tags (PSet prs)  =  pshvst vt0 tts tags prs
   sethvst vt0 tts tags (PSetC qvs pr1 pr2)  =  pshvst vt0 tts tags [pr1,pr2]
   sethvst vt0 tts tags (PSetU prset1 prset2)
    = do (vt0', tts', teqs') <- sethvst vt0 tts tags prset1
         (vt0'', tts'', teqs'') <- sethvst vt0' tts' tags prset2
         return (vt0'', tts'', teqs'++teqs'')
   sethvst vt0 tts tags _  =  return (vt0, tts, [])

   eshvst vt0 tts tags [] = return ([], (vt0, tts, []))
   eshvst vt0 tts tags (e:es)
    = do (t', (vt0', tts', teqs')) <- ehvst vt0 tts tags e
         (ts', (vt0'', tts'', teqs'')) <-  eshvst vt0' tts' tags es
         return (t':ts', (vt0'', tts'',  teqs'++teqs''))
\end{code}

Everything above is largely boilerplate.
Now, with type harvesting at the expression-level,
we get down to business.

Constants are easy---just return their type:
\begin{code}
   ehvst vt0 tts tags T  =  return (B, (vt0, tts, []))
   ehvst vt0 tts tags (F)  =  return (B, (vt0, tts, []))
   ehvst vt0 tts tags (Num i)  =  return (Z, (vt0, tts, []))
\end{code}

For variables, get a type variable setup:
\begin{code}
   ehvst vt0 tts tags (Var v)
    = do (vtyp, vt0') <- recVarType mctxt vt0 tts v tags
         return (vtyp, (vt0', tts, []))
\end{code}

There is no constraint on product types:
\begin{code}
   ehvst vt0 tts tags (Prod es)
     = do (ts', (vt0', tts', teqs')) <- eshvst vt0 tts tags es
          return (mkTprod ts', (vt0', tts', teqs'))
\end{code}

Applications/Conditions introduce equations:
\begin{code}
   ehvst vt0 tts tags (App f e)
    = do (ftyp, vt0') <- recVarType mctxt vt0 tts (preVar f) tags
         (atyp, (vt0'', tts'', teqs'')) <- ehvst vt0' tts tags e
         rtv <- newu
         let rtyp = tag2tvar rtv
         return ( rtyp, (vt0'', tts'', (ftyp,Tfun atyp rtyp):teqs''))

   ehvst vt0 tts tags (Bin op i e1 e2)
    = do (optyp, vt0') <- recVarType mctxt vt0 tts (preVar op) tags
         (t1, (vt0'', tts'', teqs'')) <- ehvst vt0' tts tags e1
         (t2, (vt0''', tts''', teqs''')) <- ehvst vt0'' tts'' tags e2
         rtv <- newu
         let rtyp = tag2tvar rtv
         return ( rtyp, (vt0''', tts'''
                        , (optyp,Tfun (mkTprod [t1,t2]) rtyp):teqs''++teqs''')
                )

   ehvst vt0 tts tags (Equal e1 e2)
    = do (t1, (vt0', tts', teqs'))    <- ehvst vt0 tts tags e1
         (t2, (vt0'', tts'', teqs'')) <- ehvst vt0' tts' tags e2
         return ( B, ( vt0'', tts'', (t1,t2):teqs'++teqs''))

   ehvst vt0 tts tags (Cond pr e1 e2)
    = do (t1, (vt0', tts', teqs')) <- ehvst vt0 tts tags e1
         (t2, (vt0'', tts'', teqs'')) <- ehvst vt0' tts' tags e2
         return ( t1, (vt0'', tts'', (t1,t2):teqs'++teqs''))
\end{code}

Abstraction is the dual of application:
\begin{code}
   ehvst vt0 tts tags (Eabs tt (Q vs) e) -- ignore multis for now
    = do (btyp, (vt0', tts', teqs')) <- ehvst vt0 tts (tt:tags) e
         let tqvs = qvlookup tts tt vs
         return (curriedTfun btyp tqvs, (vt0',tts',teqs'))

   ehvst vt0 tts tags (The tt x pr)
    = do (vt0', tts', teqs') <- phvst vt0 tts (tt:tags) pr
         case qvlookup tts tt [x] of
           [xt] -> return (xt, (vt0', tts', teqs'))
           xts -> return( Terror ("Can't find '"++varKey x++"' in 'The'")
                                 $ mkTprod xts
                        , (vt0', tts', teqs'))
\end{code}

Sets, Sequences and Map enumerations introduce many equations:
\begin{code}
   ehvst vt0 tts tags (Set es)
    = do (ts', (vt0', tts', teqs')) <- eshvst vt0 tts tags es
         case ts' of
           [] -> do stv <- newu
                    let styp = tag2tvar stv
                    return (mkTset styp, (vt0', tts', teqs'))
           (t:ts) -> return (mkTset t, (vt0', tts', tlisteq t ts ++ teqs'))

   ehvst vt0 tts tags (Seq es)
    = do (ts', (vt0', tts', teqs')) <- eshvst vt0 tts tags es
         case ts' of
           [] -> do stv <- newu
                    let styp = tag2tvar stv
                    return (mkTseq styp, (vt0', tts', teqs'))
           (t:ts) -> return (mkTseq t, (vt0', tts', tlisteq t ts ++ teqs'))

   ehvst vt0 tts tags (Map drs)
    = do let (des,res) = unzip drs
         (dts', (vt0', tts', teqs')) <- eshvst vt0 tts tags des
         (rts', (vt0'', tts'', teqs'')) <- eshvst vt0' tts' tags res
         let tqs = teqs'++teqs''
         case (dts',rts') of
           ([],[]) -> do dtv <- newu ; let dtyp = tag2tvar dtv
                         rtv <- newu ; let rtyp = tag2tvar rtv
                         return (Tfun dtyp rtyp, (vt0'', tts'', tqs))
           (dt:dts,rt:rts) -> return (Tfun dt rt,
                                       (vt0'', tts'', tlisteq dt dts
                                                      ++ tlisteq rt rts
                                                      ++ tqs))
\end{code}

Comprehensions have the type of the given expression
\begin{code}
   ehvst vt0 tts tags (Setc tt qvs pr e) = cmphvst vt0 tts (tt:tags) pr e
   ehvst vt0 tts tags (Seqc tt qvs pr e)  =  cmphvst vt0 tts (tt:tags) pr e
\end{code}

Substitution:
\begin{code}
   ehvst vt0 tts tags (Esub e (Substn ssub))
    = do (te', (vt0', tts', teqs')) <- ehvst vt0 tts tags e
         (vt0'',tts'',teqs'') <- fmap snd $ eshvst vt0' tts' tags
                                          $ map snd ssub
         return (te', (vt0'', tts'', teqs'++teqs''))
\end{code}

Odds and ends:
\begin{code}
   ehvst vt0 tts tags (Evar str)  =  return (Tarb, (vt0, tts, []))
   ehvst vt0 tts tags (Eerror s) = return ( Terror ("Eerror "++s) Tarb
                                          , (vt0,tts,[])
                                          )
   ehvst vt0 tts tags (Efocus e)  =  ehvst vt0 tts tags e
   ehvst vt0 tts tags (EPred pr)
    = do ph <- phvst vt0 tts tags pr
         return (Tarb, ph)
\end{code}

Free types are currently poorly supported.
For now we can only guess the top-level type name
\begin{code}
   ehvst vt0 tts tags (Build str es)
    = do (ts', eh) <- eshvst vt0 tts tags es
         return (Tfree "?" [(str,ts')], eh)
\end{code}

Comprehensions:
\begin{code}
   cmphvst vt0 tts tags pr e
    = do (vt0', tts', teqs') <- phvst vt0 tts tags pr
         (te,(vt0'', tts'', teqs'')) <- ehvst vt0' tts' tags e
         return (mkTset te, (vt0'', tts', teqs'++teqs''))
\end{code}
\begin{code}
\end{code}

Type equality-lists boilerlate.
Do we turn \texttt{[t1,t2,t3,t4]}
\\into \texttt{[(t1,t2),(t1,t3),(t1,t4)]}
\\or \texttt{[(t1,t2),(t2,t3),(t3,t4)]} ?
\\Which is better?
\begin{code}
tlisteq t [] = []
tlisteq t (t':ts) = (t,t'):tlisteq t ts
\end{code}

Table lookup boilerplate (very tolerant!)
\begin{code}
qvlookup tts tt vs
 = case btlookup tts tt of
    Nothing  ->  []
    Just vtyps -> catMaybes $ map (tvlookup vtyps) vs
\end{code}

Curried function builder
\begin{code}
curriedTfun btyp [] = btyp
curriedTfun btyp (t:ts) = Tfun t $ curriedTfun btyp ts
\end{code}


\subsubsection{Solving Type Equations}

\begin{code}
solveTypeEqns :: [TypeEqn] -> (TVarTypes,[Message])
solveTypeEqns teqs
 = (tvt',msgs')
 where
   neqns = lnorm $ catMaybes $ map typeEqnNorm teqs
   (tvt,msgs) = mergeTEs tnil [] $ reverse neqns
   (tvt',msgs') = tCloseTVT tvt msgs
\end{code}

We normalise type-pairs using the type ordering:
\begin{code}
typeEqnNorm :: TypeEqn -> Maybe TypeEqn
typeEqnNorm te@(t1,t2)
 = case compare t1 t2 of
     EQ  ->  Nothing       -- discard identity pairs
     GT  ->  Just (t2,t1)  -- least first
     _   ->  Just te
\end{code}

Merging equations:
\begin{code}
mergeTEs :: TVarTypes -> [Message] -> [TypeEqn] -> (TVarTypes,[Message])
mergeTEs tvt errs [] = (tvt, errs)
mergeTEs tvt errs ((t1,t2):teqns)
 = let (tvt',errs') = mergeTE tvt errs t1 t2
   in mergeTEs tvt' errs' teqns
\end{code}

Merging single type-equations into the type-variable table.
It is always the case that \texttt{t1 < t2} here.
\begin{code}
mergeTE :: TVarTypes -> [String] -> Type -> Type -> (TVarTypes,[Message])
mergeTE tvt errs t1 t2
 = case mrgType t1 t2 of
     Left msg  ->  (tvt, msg:errs)
     Right (t',tvtls,tveqls)  -> (updateTVT tvtls tveqls tvt, errs)
\end{code}

Merging types:
\begin{code}
mrgType :: Type -> Type
        -> Either Message
                  ( Type
                  , [(String,Type)]   -- TVar -+-> Type
                  , [(String,String)] -- TVar == TVar
                  )
mrgType Tarb t2 = return (t2,[],[]) -- Tarb is a unit
mrgType t1 Tarb = return (t1,[],[]) -- Tarb is a unit

mrgType t1@(Tvar a) (Tvar b)
 | a < b      =  return (t1,[],[(a,b)])
 | otherwise  =  return (t1,[],[(b,a)])

mrgType (Tvar a) t2 = return (t2,[(a,t2)],[])
mrgType t1 (Tvar b) = return (t1,[(b,t1)],[])

mrgType (TApp tcn1 ts1) (TApp tcn2 ts2)
 = do (ts',bnds',eqvs') <-  mrgTs tcn1 [] [] [] ts1 ts2
      return (TApp tcn1 ts',bnds',eqvs')

mrgType t1@(Tfree n1 fs1) t2@(Tfree n2 fs2)
 | n1 == n2   =  mrgFS n1 [] [] [] fs1 fs2
 | otherwise  =  mrgErr "Tfree" t1 t2

mrgType (Tfun td1 tr1)  (Tfun td2 tr2)  = mrgF Tfun td1 tr1 td2 tr2

mrgType Tenv Tenv  =  return (Tenv,[],[])
mrgType Z Z        =  return (Z,[],[])
mrgType B B        =  return (B,[],[])

mrgType (Terror msg t) _ = fail (msg++" with "++show t)
mrgType _ (Terror msg t) = fail (msg++" with "++show t)

mrgType t1 t2 = mrgErr "<default>" t1 t2

mrgErr what t1 t2 = fail msg
 where msg = show t1 ++ " in "++what++" cannot equal " ++ show t2


mrgBox box t1 t2
 = do (t',bnds',eqvs') <-  mrgType t1 t2
      return (box t',bnds',eqvs')

mrgF fun td1 tr1 td2 tr2
 = do (td,bndd,eqvd) <-  mrgType td1 td2
      (tr,bndr,eqvr) <-  mrgType tr1 tr2
      return (fun td tr,bndd++bndr,eqvd++eqvr)

mrgTs cons st bnds eqvs [] [] = return (reverse st,bnds,eqvs)
mrgTs cons st bnds eqvs (t1:ts1) (t2:ts2)
 = do (t',bnds',eqvs') <- mrgType t1 t2
      mrgTs cons (t':st) (bnds'++bnds) (eqvs'++eqvs) ts1 ts2
mrgTs cons st bnds eqvs [] ts2 = prodErr cons (reverse st) ts2
mrgTs cons st bnds eqvs ts1 [] = prodErr cons (reverse st) ts1

prodErr cons ts trest = fail msg
 where msg = cons++" length mismatch "++show ts++" | "++show trest


mrgFS n fs bnds eqvs [] [] = return (Tfree n (reverse fs),bnds,eqvs)
mrgFS n fs bnds eqvs ((cn1,ts1):fs1) ((cn2,ts2):fs2)
 | cn1 /= cn2  =  freeErr n cn1 cn2
 | otherwise
    = do (ts1,bnds1,eqvs1)
             <-  mrgTs ("Tfree "++n++"."++cn1) [] [] [] ts1 ts1
         let fs' = ((cn1,ts1):fs)
         let bnds' = bnds1 ++ bnds
         let eqvs' = eqvs1 ++ eqvs
         mrgFS n fs' bnds' eqvs' fs1 fs2
mrgFS n fs bnds eqvs ((cn,_):_) [] = freeErr n cn "<none>"
mrgFS n fs bnds eqvs [] ((cn,_):_) = freeErr n cn "<none>"

freeErr n cn1 cn2 = fail msg
 where msg = "Tfree '"++n++"' constructor mismatch: "++cn1++","++cn2
\end{code}

The \texttt{typErrMrg} function merges two types,
creating an error type if an error occurs.
\begin{code}
typeErrMrg :: Type -> Type -> Type
typeErrMrg t1 t2
 = case mrgType t1 t2 of
    Left msg       ->  Terror msg Tarb
    Right (t,_,_)  ->  t
\end{code}

We can build a total typevar table merge using this:
\begin{code}
tvtmerge :: Trie Type -> Trie Type -> Trie Type
tvtmerge tvt1 tvt2
 = fromJust $ tmmerge justTEM tvt1 tvt2
 where
   justTEM :: Type -> Type -> Maybe Type
   justTEM t1 t2 = Just $ typeErrMrg t1 t2
\end{code}

Given new information about type-variables,
merge it into an existing type-variable table:
\begin{code}
updateTVT :: [(TVar,Type)]   -- TVar -+-> Type
          -> [(TVar,TVar)] -- TVar == TVar
          -> TVarTypes         -- Tvar -+-> Type
          -> TVarTypes
updateTVT tvtls tveqls tvt
 = applyTVEqs tveqls (tvt `tvtmerge` lbuild tvtls)
\end{code}

Given known type-variable equalities,
update a typevar table to reflect these:
\begin{code}
applyTVEqs [] tvt = tvt
applyTVEqs ((tv1,tv2):teqs) tvt = applyTVEqs teqs $ applyTVEq tv1 tv2 tvt

applyTVEq :: String -> String -> Trie Type -> Trie Type
applyTVEq tv1 tv2 tvt
 = case tlookup tvt tv1 of
     Nothing
      -> case tlookup tvt tv2 of
          Nothing  --  tv1,tv2 new
           -> let newt = Tvar tv1
              in tvt `tmerge` lbuild [(tv1,newt),(tv2,newt)]
          Just t2  --  tv1 new, tv2 present
           -> tvt `tmerge` tsingle tv1 t2
     Just t1
      -> case tlookup tvt tv2 of
          Nothing  --  tv1 present, tv2 new
           -> tvt `tmerge` tsingle tv2 t1
          Just t2  --  tv1, tv2 present
           -> let newt = typeErrMrg t1 t2
              in tvt `tmerge` lbuild [(tv1,newt),(tv2,newt)]
\end{code}

We construct a transitively-closed typevar table
by repeatedly overwriting its range type entries
using the table itself until either
(i) no further change occurs,
or (ii) we find a typevar mappimg to a type that mentions itself
(occurs check),
in which case we report an infinite type error.
\begin{code}
tCloseTVT :: TVarTypes -> [Message] -> (TVarTypes,[Message])
tCloseTVT tvt msgs
 = let closure = map tvclose $ flattenTrie tvt
       (tvts',msgss') = unzip closure
   in (lbuild tvts', concat $ msgs:msgss')
 where

   tvclose tvtyp@(tv,Tvar tv')
    | tv == tv' = (tvtyp,[])
   tvclose (tv,typ)
    | tv `elem` typeVarsOf typ
       = ((tv,typ),["Typevar loop! "++tv++" = "++show typ])
    | otherwise
       = tvcontinue tv typ

   tvcontinue tv typ
    | chgd  =  tvclose (tv,typ')
    | otherwise  =  ((tv,typ),[])
    where (chgd,typ') = typeVarMap tvt typ

-- end tCloseTVT
\end{code}


\begin{code}
typeVarMap tvt t
 = tvmap t
 where
   tvmap typ@(Tvar tv)
    = case tlookup tvt tv of
        Nothing                      ->  (False, typ)
        Just (Tvar tv') | tv == tv'  ->  (False, typ)
        Just typ'                    ->  (True, typ')
   tvmap (TApp tcn typs) = tvsmap (TApp tcn) typs
   tvmap (Tfree str cases)  =  undefined
   tvmap (Tfun t1 t2) = tvmap2 Tfun t1 t2
   tvmap typ = (False, typ)

   tvmapf tcon t = let (chgd,t') = tvmap t in (chgd,tcon t')

   tvsmap tcon ts
    = let (chgs,ts') = unzip $ map tvmap ts
      in (any id chgs, tcon ts')

   tvmap2 tcon t1 t2
    = let [(ch1,t1'),(ch2,t2')] = map tvmap [t1,t2]
      in (ch1||ch2, tcon t1' t2')
-- end typeVarMap
\end{code}

Extracting all typevars mentioned in a type:
\begin{code}
typeVarsOf :: Type -> [String]
typeVarsOf (Tvar s) = [s]
typeVarsOf (Tfun t1 t2) = concat (map typeVarsOf [t1,t2])
typeVarsOf (Tfree _ css) = concat (map typeVarsOf (concat (map snd css)))
typeVarsOf (TApp _ ts) = concat (map typeVarsOf ts)
typeVarsOf _ = []
\end{code}

\subsection{Constructing Types}





\newpage
\section{OLD TYPE STUFF BELOW --- DEPRECATE?}

First we extract all the top-level expressions,
along with the relevant variable binders.
An expression inside a quantifier has bound variables, so
given a top-level expression inside a quantifier:
$$
 \forall x,y,z @ \ldots e \ldots
$$
its extracted form is viewed as a lambda-expression, for type-checking
purposes:
$$
 \lambda x,y,z @ e.
$$
\begin{code}
topLvlExprs :: MatchContext -> Pred -> [(Binders,Expr)]
topLvlExprs mctxt pr
 = predExprs [] pr
 where

   tlerror what = error ("topLvlExprs undefined for "++what)

   addB (Q xs) bnds = lnorm ( xs ++ bnds )

   addU pr bnds = lnorm ( predFreeVars mctxt pr ++ bnds )

   withB bnds e = (bnds,e)

   predExprs bnds (TRUE)  =  []
   predExprs bnds (FALSE)  =  []
   predExprs bnds (Obs e)  =  [(bnds,e)]
   predExprs bnds (Defd e)  =  [(bnds,e)]
   predExprs bnds (TypeOf e atyp)  =  [(bnds,e)]
   predExprs bnds (Not pr)  =  predExprs bnds pr
   predExprs bnds (And prs)  =  predsExprs bnds prs
   predExprs bnds (Or prs)  =  predsExprs bnds prs
   predExprs bnds (Imp pr1 pr2)  =  predsExprs bnds [pr1,pr2]
   predExprs bnds (Eqv pr1 pr2)  =  predsExprs bnds [pr1,pr2]
   predExprs bnds (Forall tt qvs pr)  =  predExprs (addB qvs bnds) pr
   predExprs bnds (Exists tt qvs pr)  =  predExprs (addB qvs bnds) pr
   predExprs bnds (Exists1 tt qvs pr)  =  predExprs (addB qvs bnds) pr
   predExprs bnds (Univ tt pr)  =  predExprs (addU pr bnds) pr
   predExprs bnds (Sub pr esub)  =  predExprs bnds pr ++ esubExprs bnds esub
   predExprs bnds (Pvar str)  =  []
   predExprs bnds (If pr1 pr2 pr3)  =  predsExprs bnds [pr1,pr2,pr3]
   predExprs bnds (NDC pr1 pr2)  =  predsExprs bnds [pr1,pr2]
   predExprs bnds (RfdBy pr1 pr2)  =  predsExprs bnds [pr1,pr2]
   predExprs bnds (Lang str i les sss)  =  lelemsExprs bnds les
   predExprs bnds (Pforall qvs pr)  =  predExprs bnds pr
   predExprs bnds (Pexists qvs pr)  =  predExprs bnds pr
   predExprs bnds (Psub pr psub)  =  predExprs bnds pr ++ psubExprs bnds psub
   predExprs bnds (Psapp pr prset)  =  tlerror "Psapp"
   predExprs bnds (Psin pr prset)  =  tlerror "Psin"
   predExprs bnds (Peabs qvs pr)  =  predExprs (addB qvs bnds) pr
   predExprs bnds (Ppabs qvs pr)  =  predExprs bnds pr
   predExprs bnds (Papp pr1 pr2)  =  predsExprs bnds [pr1,pr2]
   predExprs bnds (Perror str)  =  []
   predExprs bnds (Pfocus pr)  =  predExprs bnds pr

   predsExprs bnds prs = concat $ map (predExprs bnds) prs

   esubExprs bnds (Substn ssub) = map (withB bnds . snd) ssub

   psubExprs bnds (Substn ssub) = concat $ map (predExprs bnds . snd) ssub

   lelemExprs bnds (LExpr e)  =  [(bnds,e)]
   lelemExprs bnds (LPred pr)  =  predExprs bnds pr
   lelemExprs bnds (LList les)  =  lelemsExprs bnds les
   lelemExprs bnds (LCount les)  =  lelemsExprs bnds les
   lelemExprs _ _  =  []

   lelemsExprs bnds les = concat $ map (lelemExprs bnds) les
\end{code}




\subsubsection{Type Inference Phase I}

\input{doc/Types-Inference-Phase-I}
\begin{code}
type VT = Trie [String]
type TT = Trie [Type]
\end{code}
We let $vt \oplus v \mapsto t$ (resp. $tt \oplus t \mapsto T$) denote the addition
of $t$ (resp. $T$) into the normalised list associated with $v$ (resp. $t$).
\begin{code}
insTentry :: Ord t => String -> t -> Trie [t] -> Trie [t]
insTentry name thing table = tenter mrgTentry name [thing] table
mrgTentry xs [x] = insnorm x xs
insTVentry :: Ord t => Variable -> t -> Trie [t] -> Trie [t]
insTVentry = insTentry . varKey
\end{code}
$\tau \oplus n \mapsto \seqof{t_1,\ldots,t_n}$
\begin{code}
insTeList :: Ord t => String -> [t] -> Trie [t] -> Trie [t]
insTeList name []             table  =  table
insTeList name (thing:things) table  =  insTentry name thing (insTeList name things table)
insTVeList :: Ord t => Variable -> [t] -> Trie [t] -> Trie [t]
insTVeList = insTeList . varKey
\end{code}
$\tau \oplus n_i \mapsto t_i, i \in 1 \ldots n$
\begin{code}
insTEntries :: Ord t => [String] -> [t] -> Trie [t] -> Trie [t]
insTEntries []     _              table  =  table
insTEntries _      []             table  =  table
insTEntries (n:ns) (thing:things) table  =  insTEntries ns things (insTentry n thing table)
insTVEntries :: Ord t => [Variable] -> [t] -> Trie [t] -> Trie [t]
insTVEntries = insTEntries . map varKey
\end{code}

\input{doc/Types-bldTT}


We use a monad (\texttt{Utilities.Uniq})
to hide unique name generation.
\begin{code}
newtvar = fmap mkTvarName (newu)

mkTvarName n = 't':(show n)

newtvars [] = return []
newtvars (_:xs)
 = do t <- newtvar
      ts <- newtvars xs
      return (t:ts)
\end{code}

\textbf{WE WILL NEED THE FRESH STUFF FROM HERE }

We also need a monadic action that takes a type
and replaces all type-vars mentioned with fresh variables
(to enforce the locality of their scope),
and a type lookup (\texttt{flookup})
that does this freshening on the fly.
\begin{code}
type TVarEqvs = Trie TVar

freshType :: Type -> Uniq Type
freshType typ
 = do tmap <- genFreshTypeVars typ tnil
      return (buildFreshType tmap typ)

genFreshTypeVars :: Type -> TVarEqvs -> Uniq (TVarEqvs)

genFreshTypeVars (Tvar v) tmap
 = case tlookup tmap v of
    (Just _)  ->  return tmap
    Nothing   ->  do t <- newtvar
                     return (tupdate v t tmap)

genFreshTypeVars (Tfun td tr) tmap
     = seqgenFreshTypeVars [td,tr] tmap

genFreshTypeVars (TApp _ ts) tmap
     = seqgenFreshTypeVars ts tmap

genFreshTypeVars (Tfree _ fs) tmap
 = seqgenFreshTypeVars (concat (map snd fs)) tmap

genFreshTypeVars _ tmap = return tmap

seqgenFreshTypeVars [] tmap = return tmap
seqgenFreshTypeVars (t:ts) tmap
 = do tmap' <- genFreshTypeVars t tmap
      seqgenFreshTypeVars ts tmap'
\end{code}

Building a fresh type, given a mapping:
\begin{code}
buildFreshType :: Trie TVar -> Type -> Type

buildFreshType tmap (Tvar v) = Tvar t
 where (Just t) = tlookup tmap v

buildFreshType tmap (TApp tcn ts)
  = TApp tcn (map (buildFreshType tmap) ts)

buildFreshType tmap (Tfun td tr)
   = Tfun (buildFreshType tmap td) (buildFreshType tmap tr)

buildFreshType tmap (Tfree name fs)
 = Tfree name (map bfts fs)
 where bfts (cons,ts) = (cons,map (buildFreshType tmap) ts)

buildFreshType tmap t = t

flookup gamma v
 = case tsvlookup gamma v of
     Nothing  ->  return Nothing
     (Just t)  ->  do t' <- freshType t
                      return (Just t')
\end{code}

Now we can define \texttt{bldTT},
augmented to take a list of expressions,
and also, in each case, to return the type-variable list
associated with the immediate children of the top-level
expression, if likely to be underlying types.
\begin{code}
bldTT :: [Trie Type]            -- type environment
      -> [Expr]                 -- expressions to be typed
      -> ( [(String,[String])]  -- (top,children) Tvars
         , Trie [String]        -- Var -+-> [Tvar]
         , Trie [Type] )        -- Tvar -+-> [Type]

bldTT gamma es = runu 0 (bldtts es [] tnil tnil)
 where

  bldtts [] res vt tt = return (reverse res,vt,tt)
  bldtts (e:es) res vt tt
   = do (top,vt',tt',children) <- bldfocus e vt tt
        bldtts es ((top,children):res) vt' tt'
\end{code}

First, we define the top-level expression builder,
that does special \texttt{Efocus} handling
\begin{code}
  bldfocus e vt tt
   = do (top,vt',tt',children,tfocus) <-  bldtop e vt tt
        case tfocus of
          Nothing
            -> return (top,vt',tt',children)
          (Just (ftop,fchildren))
            ->  return (ftop,vt',tt',fchildren)
\end{code}

Next, a top-level handler, that looks
for top-level \texttt{Var}s and \texttt{Evar}s,
which should of course be viewed as being boolean
(but lets not assert that here for now !):
\begin{code}
  bldtop (Var v) vt tt
   = do t <- newtvar
        let vt' = insTVentry v t vt
        res <- flookup gamma v
        case res of
          (Just typ)
            -> do typ' <- freshType typ
                  return (t,vt',insTentry t typ' tt,[],Nothing)
          -- Nothing -> return (t,vt',insTentry t B tt,[],Nothing)
          Nothing -> return (t,vt',tt,[],Nothing)

  bldtop (Evar v) vt tt
   = do t <- newtvar
        let vt' = insTVentry v t vt
        res <- flookup gamma v
        case res of
          (Just typ)
            -> do typ' <- freshType typ
                  return (t,vt',insTentry t typ' tt,[],Nothing)
          -- Nothing -> return (t,vt',insTentry t B tt,[],Nothing)
          Nothing -> return (t,vt',tt,[],Nothing)

  bldtop e vt tt = bld gamma e vt tt
\end{code}

We need to fuse focus type data from two sources,
at least one of which should be \texttt{Nothing}:
\begin{code}
  Nothing `fuse` y = y
  x `fuse` Nothing = x
  (Just a) `fuse` (Just b) = error ("bldTT: two Efocii !!")
\end{code}

Next, we define re-useable builders
\begin{code}
  addTT typ vt tt -- typ should be Tvar-free
   = do t <- newtvar
        let tt' = insTentry t typ tt
        return (t,vt,tt',[],Nothing)

  addDR t tr ta td vt tt ft
   = do let tt' = insTentry t tr (insTentry ta td tt)
        return (t,vt,tt',[ta],ft)

  addBIN t tr t1 ta t2 tb vt tt ft
   = do let tt1 = insTentry t1 ta tt
        let tt2 = insTentry t2 tb tt1
        let tt' = insTentry t tr tt2
        return (t,vt,tt',[t1,t2],ft)
\end{code}
\begin{eqnarray*}
   bldTT_\Gamma (\setof{e1,\ldots,e_n},vt,tt)
   &\defs& (t,vt',tt')
\\ \WHERE && new~t
\\  && new~t_e
\\  && (t_1,vt_1,tt_1) = bldTT_\Gamma(e_1,vt,tt)
\\  && \vdots
\\  && (t_n,vt_n,tt_n) = bldTT_\Gamma(e_n,vt_{n-1},tt_{n-1})
\\ && (vt',tt')
     = (vt_n,
        tt_n \oplus t_e \mapsto \seqof{t_1,\ldots,t_n} \oplus t \mapsto \power t_e)
\end{eqnarray*}
\begin{code}
  addBOX tbox es vt tt
   = do t <- newtvar
        te <- newtvar
        (ts,vtn,ttn,_,ft) <- blds gamma es vt tt
        let tts = insTeList te (map Tvar ts) ttn
        let tt' = insTentry t (tbox (Tvar te)) tts
        return(t,vtn,tt',[],ft)
\end{code}

Now, we handle different expression classes
\begin{eqnarray*}
   bldTT_\Gamma (k,vt,tt)
   &\defs& (t,vt,tt \oplus t \mapsto T), \qquad \Gamma(k)=T
\\ &&      (t,vt,tt), \qquad k \notin \Gamma
\\ \WHERE && new~t
\end{eqnarray*}
\begin{code}
  bld gamma T vt tt = addTT B vt tt
  bld gamma F vt tt = addTT B vt tt
  bld gamma (Num _) vt tt = addTT Z vt tt
\end{code}

Variables
\begin{eqnarray*}
   bldTT_\Gamma (v,vt,tt)
   &\defs&(t,vt \oplus v \mapsto t,tt), \qquad \Gamma(v) \mbox{ is a type-var.}
\\ &&     (t,vt \oplus v \mapsto t,tt \oplus t \mapsto T), \qquad \Gamma(v)=T
\\ &&     (t,vt \oplus v \mapsto t,tt), \qquad v \notin \Gamma
\\ \WHERE && new~t
\end{eqnarray*}
\begin{code}
  bld gamma (Var v) vt tt
   = do t <- newtvar
        let vt' = insTVentry v t vt
        res <- flookup gamma v
        case res of
          Nothing          -> return (t,vt',tt,[],Nothing)
          (Just (Tvar _))  -> return (t,vt',tt,[],Nothing)
          (Just typ)
            -> do typ' <- freshType typ
                  return (t,vt',insTentry t typ' tt,[],Nothing)

  bld gamma (Evar e) vt tt
   = do t <- newtvar
        let vt' = insTVentry e t vt
        res <- flookup gamma e
        case res of
          Nothing          -> return (t,vt',tt,[],Nothing)
          (Just (Tvar _))  -> return (t,vt',tt,[],Nothing)
          (Just typ)
            -> do typ' <- freshType typ
                  return (t,vt',insTentry t typ' tt,[],Nothing)
\end{code}

Abstraction
\begin{eqnarray*}
   bldTT_\Gamma(\lambda x_1,\ldots,x_n @ e)
   &\defs& (t,vt',tt')
\\ \WHERE && new~t; new~t_1; \ldots ; new~t_n
\\ && (t_e,vt_e,tt_e) = bldTT_{(\Gamma\oplus{x_i \mapsto t_i})}(e,vt,tt)
\\ && (vt',tt') = (vt_e,tt_e \oplus t \mapsto t_1 \fun \ldots \fun t_n \fun t_e)
\end{eqnarray*}
\begin{code}
  bld gamma (Eabs _ qs e) vt tt
   = do t <- newtvar
        let evs = outQ qs
        ts <- newtvars evs
        let tvs = map Tvar ts
        let gamma' = (lbuild (zip (map varKey evs) tvs)):gamma
        (te,vte,tte,_,ft) <- bld gamma' e vt tt
        let typ' = mmap tvs (Tvar te)
        let tt' = insTentry t typ' tte
        return (t,vte,tt',[],Nothing)
   where
    mmap [] tr = tr
    mmap (td:tds) tr = Tfun td (mmap tds tr)
\end{code}

Applications
\begin{eqnarray*}
   bldTT_\Gamma (f~a,vt,tt)
   &\defs& (t,vt',tt')
\\ \WHERE && new~t
\\  && (t_a,vt_a,tt_a) = bldTT_\Gamma(a,vt,tt)
\\ && (vt',tt') = (vt_a,tt_a \oplus t_a \mapsto D, t \mapsto R), \qquad \Gamma(f) = D \fun R
\\ && (vt',tt') = (vt_a,tt_a), \qquad f \notin \Gamma
\end{eqnarray*}
\begin{code}
  bld gamma (App f a) vt tt
   = do t <- newtvar
        (ta,vta,tta,_,ft) <- bld gamma a vt tt
        res <- flookup gamma (preVar f)
        case res of
         Nothing  ->  return(t,vta,tta,[ta],ft)
         (Just (Tfun td tr))  -> addDR t tr ta td vta tta ft
         (Just typ) -> do let typ' = terr f typ
                          let tt' = insTentry t typ' tta
                          return (t,vta,tt',[ta],ft)
   where terr f t = Terror ("'Fun' "++f++" has type ") t

  bld gamma (Bin op _ e1 e2) vt tt
   = do t <- newtvar
        (t1,vt1,tt1,_,ft1) <- bld gamma e1 vt tt
        (t2,vt2,tt2,_,ft2) <- bld gamma e2 vt1 tt1
        let ft = ft1 `fuse` ft2
        res <- flookup gamma $ preVar op
        case res of
         Nothing  ->  return(t,vt2,tt2,[t1,t2],ft)
         (Just (Tfun td@(TApp tcn [ta,tb]) tr))
           | tcn==n_Tprod  -> addBIN t tr t1 ta t2 tb vt2 tt2 ft
         (Just typ) -> do let typ' = terr op typ
                          let tt' = insTentry t typ' tt2
                          return (t,vt2,tt',[t1,t2],ft)
   where terr op t = Terror ("'Binop' "++op++" has type ") t

  bld gamma (Equal e1 e2) vt tt
   = do t <- newtvar
        (t1,vt1,tt1,_,ft1) <- bld gamma e1 vt tt
        (t2,vt2,tt2,_,ft2) <- bld gamma e2 vt1 tt1
        let ft = ft1 `fuse` ft2
        ta <- fmap Tvar newtvar
        addBIN t B t1 ta t2 ta vt2 tt2 ft

  bld gamma (Cond _ e1 e2) vt tt
   = do t <- newtvar
        (t1,vt1,tt1,_,ft1) <- bld gamma e1 vt tt
        (t2,vt2,tt2,_,ft2) <- bld gamma e2 vt1 tt1
        let ft = ft1 `fuse` ft2
        tc <- fmap Tvar newtvar
        addBIN t tc t1 tc t2 tc vt2 tt2 ft
\end{code}

Substitution (a fusion of application and abstraction !)
\begin{eqnarray*}
   bldTT_\Gamma (e[e_1,\ldots,e_n/x_1,\ldots,x_n],vt,tt)
   &\defs& (t,vt',tt' \oplus t \mapsto t')
\\ \WHERE && new~t
\\  && (t_1,vt_1,tt_1) = bldTT_\Gamma(e_1,vt,tt)
\\  && \vdots
\\  && (t_n,vt_n,tt_n) = bldTT_\Gamma(e_n,vt_{n-1},tt_{n-1})
\\  && (t',vt',tt') = bldTT_\Gamma(e,vt_n \oplus x_i \mapsto t_i,tt_n)
\end{eqnarray*}
\begin{code}
  bld gamma (Esub e (Substn ssub)) vt tt -- ignore mvars ????
   = do t <- newtvar
        (ts,vtn,ttn,_,ft1) <- blds gamma es vt tt
        (t',vt',tt',tc,ft2) <- bld gamma e (insTVEntries xs ts vtn) ttn
        return (t,vt',insTentry t (Tvar t') tt',tc,ft1 `fuse` ft2)
   where
     (xs,es) = unzip ssub
\end{code}

Product
\begin{eqnarray*}
   bldTT_\Gamma ((e1,\ldots,e_n),vt,tt)
   &\defs& (t,vt',tt')
\\ \WHERE && new~t
\\  && (t_1,vt_1,tt_1) = bldTT_\Gamma(e_1,vt,tt)
\\  && \vdots
\\  && (t_n,vt_n,tt_n) = bldTT_\Gamma(e_n,vt_{n-1},tt_{n-1})
\\ && (vt',tt') = (vt_n,tt_n \oplus t \mapsto t_1 \times \ldots \times t_n)
\end{eqnarray*}
\begin{code}

  bld gamma (Prod es) vt tt
   = do t <- newtvar
        (ts,vtn,ttn,_,ft) <- blds gamma es vt tt
        let typs = map Tvar ts
        return(t,vtn,insTentry t (mkTprod typs) ttn,[],ft)
\end{code}

Sets, Sequences, \ldots (see \texttt{addBOX} defn. above)
\begin{code}
  bld gamma (Set es)     vt tt  =  addBOX mkTset es vt tt
  bld gamma (Seq es)     vt tt  =  addBOX mkTseq es vt tt
  bld gamma (Seqc _ _ _ e) vt tt  =  addBOX mkTseq [e] vt tt
  bld gamma (Setc _ _ pr e) vt tt
   =  do t <- newtvar
         (ts,vtr,ttr,_,fr) <- blds gamma (exprsOf pr) vt tt
         (t',vt',tt',tc,fs) <- bld gamma e vtr ttr
         return (t,vt',insTentry t (mkTset (Tvar t')) tt',tc,fr `fuse` fs)
\end{code}

Maps
\begin{eqnarray*}
   bldTT_\Gamma (\mapof{d_i \mapsto r_i},vt,tt)
   &\defs& (t,vt',tt')
\\ \WHERE && new~t, td, tr
\\  && (t_1,vt_1,tt_1) = bldTT_\Gamma(d_1,vt,tt)
\\  && \vdots
\\  && (t_n,vt_n,tt_n) = bldTT_\Gamma(d_n,vt_{n-1},tt_{n-1})
\\  && (t_{n+1},vt_{n+1},tt_{n+1}) = bldTT_\Gamma(r_1,vt_n,t_n)
\\  && \vdots
\\  && (t_{2n},vt_{2n},tt_{2n}) = bldTT_\Gamma(r_n,vt_{2n-1},tt_{2n-1})
\\ && vt' = vt_{2n} \oplus td \mapsto t_1 \ldots t_n
                     \oplus tr \mapsto t_{n+1} \ldots t_{2n}
\\ && tt' = tt_{2n} \oplus t \mapsto (t_d \pfun t_r)
\end{eqnarray*}
\begin{code}
  bld gamma (Map drs) vt tt
   = do t <- newtvar
        td <- newtvar
        tr <- newtvar
        (tds,vtd,ttd,_,ft1) <- blds gamma (map fst drs) vt tt
        (trs,vtr,ttr,_,ft2) <- blds gamma (map snd drs) vtd ttd
        let ft = ft1 `fuse` ft2
        let vtp = insTeList td tds vtr
        let vt' = insTeList tr trs vtp
        let tt' = insTentry t (Tfun (Tvar td) (Tvar tr)) ttr
        return (t,vt',tt',[],ft)
\end{code}

Definite description:
\begin{eqnarray*}
\\ bldTT_\Gamma(\theta x @ P,vt,tt)
   &\defs& (t,vt,tt \oplus t \mapsto T), \qquad  \Gamma \infer x ::T \mbox{ in } P
\\&&       (t,vt,tt \oplus t \mapsto t'), \qquad \mbox{otherwise}
\\ \WHERE && new~t \quad new~t'
\end{eqnarray*}
\begin{code}
  bld gamma e@(The _ v pr) vt tt
   = do t <- newtvar
        let tbinds = inferPredType gamma pr
        case tvlookup tbinds v of
          Nothing   ->  do typ' <- freshType (Tvar t)
                           return (t,vt,insTentry t typ' tt,[],Nothing)
          Just typ  ->  do typ' <- freshType typ
                           return  (t,vt,insTentry t typ' tt,[],Nothing)
\end{code}


Focus handling:
\begin{code}
  bld gamma (Efocus e) vt tt
   = do (top,vt',tt',children,ft) <- bld gamma e vt tt
        case ft of
          (Just _)  ->  return (error "bldTT: nested Efocii!")
          Nothing
           ->  return (top,vt',tt',children,Just (top,children))
\end{code}

Error handling last case.
\begin{code}
  bld gamma e vt tt = addTT terror vt tt
   where terror = Terror ("bldTT("++debugEshow e++") not handled") Tarb
\end{code}

Doing lists of expressions
\begin{code}
  blds gamma [] vt tt = return ([],vt,tt,[],Nothing)
  blds gamma (e:es) vt tt
   = do (t,vt1,tt1,_,ft1) <- bld gamma e vt tt
        (ts,vt',tt',_,ft2) <- blds gamma es vt1 tt1
        let ft = ft1 `fuse` ft2
        return( t:ts,vt',tt',[],ft)
\end{code}

The top-level expression is associated with \verb'Tvar "0"',
and we solve the system of equations implied by the above
tables to get a (most-general) ground instance for the top-level type.

\subsubsection{Type Inference Phase II}

\input{doc/Types-Inference-Phase-II}

\begin{code}
vt2tlist :: Trie [TVar] -> [[Type]]
vt2tlist = map  (lnorm . map Tvar) . trieRng

tt2tlist :: Trie [Type] -> [[Type]]
tt2tlist = map ttmrg . flattenTrie
           where ttmrg (v,ts) = lnorm (Tvar v:ts)

eqvInduce :: [Type] -> [[Type]]
eqvInduce ts = ts:(eqvInd (dropWhile nonTypeCons ts))
 where

  eqvInd :: [Type] -> [[Type]]
  eqvInd [] = []
  eqvInd [t] = []
  eqvInd (t1:ts@(t2:ts'))
   = eqvInd2 t1 t2 ++ eqvInd ts

  eqvInd2 :: Type -> Type -> [[Type]]
  eqvInd2 t1 t2
   = case tMatch t1 t2 of
      Nothing  ->  []
      Just tbinds  ->  map (lnorm . vvEqv) tbinds

  vvEqv :: (String,Type) -> [Type]
  vvEqv (v,B)           =  [Tvar v,B]
  vvEqv (v,Z)           =  [Tvar v,Z]
  vvEqv (v,Tenv)        =  [Tvar v,Tenv]
  vvEqv (v,t@(Tvar _))  =  [Tvar v,t]
  vvEqv _               =  []

 -- end eqvInduce
\end{code}

All of these are pooled and merged to get a minimal set
of types, all equivalent.
Basically any lists with a non-empty intersection
are merged.
\begin{code}
detEquivLists :: Trie [TVar]  -- Var  -+-> [Tvar]
              -> Trie [Type]    -- Tvar -+-> [Type]
              -> [[Type]]
detEquivLists vt tt
 = let eqlists = vt2tlist vt ++ tt2tlist tt
       indlists = concat $ map eqvInduce $ eqlists
   in sort (fuseEqvLists indlists)

fuseEqvLists :: Ord t => [[t]] -> [[t]]
fuseEqvLists xxs = fel (length xxs) xxs where
 fel len xxs
  | len' == len  =  xxs'
  | otherwise    =  fel len' xxs'
  where xxs' = fuseEqvPass xxs
        len' = length xxs'

fuseEqvPass :: Ord t => [[t]] -> [[t]]
fuseEqvPass [] = []
fuseEqvPass (xs:xxs) = fep [] [] xs xxs where
 -- acc, accumulator for fully fused lists
 -- rss, accumulator lists still to fuse
 -- xs, list currently being fused
 -- yys, lists to be checked
 fep acc [] xs [] = xs:acc
 fep acc [rs] xs [] = rs:xs:acc
 fep acc (rs:rss) xs [] = fep (xs:acc) [] rs rss
 fep acc rss xs (ys:yys)
  | null ys' = fep acc rss xs' yys
  | otherwise  =  fep acc (ys:rss) xs yys
  where (xs',ys') = fuseEqvListPair xs ys

fuseEqvListPair :: Ord t => [t] -> [t] -> ([t],[t])
fuseEqvListPair xs ys = felp xs ys where
 felp [] bs = (xs,ys) -- no common element found
 felp as [] = (xs,ys) -- no common element found
 felp as@(a:ar) bs@(b:br)
  | a < b  =  felp ar bs -- assume lists are ordered
  | a > b  =  felp as br
  | otherwise  =  (xs `mrgnorm` ys,[]) -- assume no duplicates
\end{code}

It is at this stage that we can detect ``type-loops'',
where a type-variable is set equivalent to the application of a type-constructor
to itself.
\begin{code}
findTypeLoops :: [[Type]] -> [(Type,Type)]
findTypeLoops teqvss = concat (map findTypeLoop teqvss)

findTypeLoop :: [Type] -> [(Type,Type)]
findTypeLoop [] = []
findTypeLoop (Tvar tv:typs)
 = concat (map (findTVarLoop tv) typs) ++ findTypeLoop typs
findTypeLoop (_:typs) = findTypeLoop typs

findTVarLoop :: String -> Type -> [(Type,Type)]
findTVarLoop tv typ
 | tv `elem` typeVarsOf typ  =  [(Tvar tv,typ)]
 | otherwise              =  []
\end{code}


\subsubsection{Type Inference Phase III}

\input{doc/Types-Inference-Phase-III}


We have a lookup mechanism that explores both maps,
and totalises lookups:
\begin{code}
vvlookup (vmap,vtyp) a
 = case tlookup vtyp a of
     (Just ta)  ->  ta
     Nothing
      -> case tlookup vmap a of
           Nothing  ->  Tvar a
           (Just b)
            -> case tlookup vtyp b of
                 Nothing    ->  Tvar b
                 (Just tb)  -> tb
\end{code}

We build this map-pair by turning an equivalence-list into two sub-lists,
one capturing \texttt{Tvar} to \texttt{Type} bindings (i.e. $vtyp$),
the other pairing equivalent \texttt{Tvar}s (i.e $vmap$).
We assume that an equivalence list is sorted and always starts with
a \texttt{Tvar}.
\begin{code}
splitDetList :: [(TVar, Type)]
             -> [(TVar,TVar)]
             -> [Type]
             -> ([(TVar,Type)]
                ,[(TVar,TVar)])
splitDetList tbinds veqvs (Tvar a:rest)
 = sdl tbinds veqvs rest
 where
   sdl tbs vqs [] = (tbs,vqs)
   sdl tbs vqs (Tvar b:rest) = sdl tbs ((a,b):vqs) rest
   sdl tbs vqs (t:rest)      = sdl ((a,t):tbs) vqs rest
splitDetList tbinds veqvs _ = (tbinds,veqvs)

splitDetLists :: [[Type]]
              -> ( [(String, Type)]       -- Tvar -+-> Type
                 , [(String, String)] )   -- Tvar -+-> Tvar
splitDetLists dels = sdl [] [] dels where
  sdl tbs vqs [] = (tbs,vqs)
  sdl tbs vqs (del:dels) = sdl tbs' vqs' dels
    where (tbs',vqs') = splitDetList tbs vqs del
\end{code}

We then process these to produce the two maps, doing $vtyp$ updates first.
In the process of updating $vtyp$, we may need to merge two (hopefully consistent)
types, denoted $(T_1 \downarrow T_2)$, which may produce addition equivalence
list material.
This additional material is added back into the lists for immediate processing.
\begin{code}
buildEqvTables :: [(String, Type)]    -- Tvar -+-> Type
               -> [(String, String)]  -- Tvar -+-> Tvar
               -> ( TVarEqvs       -- Tvar -+-> Tvar
                  , Trie Type )       -- Tvar -+-> Type
buildEqvTables tbinds veqvs = bet tnil tnil tbinds veqvs where

 bet vmap vtyp  [] [] = (vmap,vtyp)

 bet vmap vtyp [] (veqv:veqvs)
  = bet vmap' vtyp' tbinds' veqvs'
   where
    (vmap',vtyp',tbinds',veqvs1) = addTVEqv veqv vmap vtyp
    veqvs' = veqvs1 ++ veqvs

 bet vmap vtyp  (tbind:tbinds) veqvs
  = bet vmap' vtyp' tbinds' veqvs'
   where
    (vmap',vtyp',tbinds1,veqvs1) = addTBind tbind vmap vtyp
    veqvs' = veqvs1 ++ veqvs
    tbinds' = tbinds1 ++ tbinds
\end{code}

Adding in a type binding is straightforward:
\begin{code}
addTBind (e,typ) vamp vtyp
 = case tlookup vamp e of

     (Just e0)  ->  let (vtyp',tbinds',veqvs') = vtypUpdate e0 typ vtyp
                    in (vamp,vtyp',tbinds',veqvs')

     Nothing    ->  let (vtyp',tbinds',veqvs') = vtypUpdate e typ vtyp
                    in (vamp,vtyp',tbinds',veqvs')

\end{code}

Updating type bindings is a common task:
\begin{code}
vtypUpdate a typ vtyp
 = case tlookup vtyp a of
     Nothing  ->  (tupdate a typ vtyp,[],[])
     (Just typ0) -> let (typ',tbinds',veqvs') = mergeTypes typ typ0
                    in (tupdate a typ' vtyp,tbinds',veqvs')
\end{code}

The implementation of $T_1 \downarrow T_2$ is boilerplate:
\begin{code}
mergeTypes :: Type -> Type
           -> ( Type
              , [(TVar, Type)]
              , [(TVar, TVar)] )
mergeTypes t1 t2
 = case compare t1 t2 of
    EQ  ->  (t1,[],[])  -- covers B Z Tenv
    LT  ->  mrgT t1 t2
    GT  ->  mrgT t2 t1
 where

  mrgT Tarb t2 = (t2,[],[]) -- Tarb is a unit

  mrgT t1@(Tvar a) (Tvar b) = (t1,[],[(a,b)]) -- we know a < b (above)

  mrgT (Tvar a) t2 = (t2,[(a,t2)],[])

  mrgT (TApp tcn1 ts1) (TApp tcn2 ts2)
   | tcn1==tcn2
   = let (ts',bnds',eqvs') = mrgTs tcn1 [] [] [] ts1 ts2
     in (TApp tcn1 ts',bnds',eqvs')

  mrgT t1@(Tfree n1 fs1) t2@(Tfree n2 fs2)
   | n1 == n2  =  mrgFS n1 [] [] [] fs1 fs2
   | otherwise  =  (mrgErr t1 t2,[],[])

  mrgT (Tfun td1 tr1)  (Tfun td2 tr2)  = mrgF Tfun td1 tr1 td2 tr2

  mrgT t1 t2 = (mrgErr t1 t2,[],[])

  mrgErr t1 t2 = Terror msg Tarb
   where msg = show t1 ++ " cannot equal " ++ show t2


  mrgBox box t1 t2
   = let (t',bnds',eqvs') = mrgT t1 t2
     in (box t',bnds',eqvs')


  mrgF fun td1 tr1 td2 tr2
   = let (td,bndd,eqvd) = mrgT td1 td2 in
     let (tr,bndr,eqvr) = mergeTypes tr1 tr2 in
     (fun td tr,bndd++bndr,eqvd++eqvr)


  mrgTs cons st bnds eqvs [] [] = (reverse st,bnds,eqvs)
  mrgTs cons st bnds eqvs (t1:ts1) (t2:ts2)
   = let (t',bnds',eqvs') = mergeTypes t1 t2 in
     mrgTs cons (t':st) (bnds'++bnds) (eqvs'++eqvs) ts1 ts2
  mrgTs cons st bnds eqvs [] ts2 = ([prodErr cons (reverse st) ts2],[],[])
  mrgTs cons st bnds eqvs ts1 [] = ([prodErr cons (reverse st) ts1],[],[])

  prodErr cons ts trest = Terror msg Tarb
   where msg = cons++" length mismatch "++show ts++" | "++show trest


  mrgFS n fs bnds eqvs [] [] = (Tfree n (reverse fs),bnds,eqvs)
  mrgFS n fs bnds eqvs ((cn1,ts1):fs1) ((cn2,ts2):fs2)
   | cn1 /= cn2  =  (freeErr n cn1 cn2,[],[])
   | otherwise = mrgFS n fs' bnds' eqvs' fs1 fs2
   where
     (ts1,bnds1,eqvs1) = mrgTs ("Tfree "++n++"."++cn1) [] [] [] ts1 ts1
     fs' = ((cn1,ts1):fs)
     bnds' = bnds1 ++ bnds
     eqvs' = eqvs1 ++ eqvs
  mrgFS n fs bnds eqvs ((cn,_):_) [] = (freeErr n cn "<none>",[],[])
  mrgFS n fs bnds eqvs [] ((cn,_):_) = (freeErr n cn "<none>",[],[])

  freeErr n cn1 cn2 = Terror msg Tarb
   where msg = "Tfree '"++n++"' constructor mismatch: "++cn1++","++cn2
\end{code}

Given that \texttt{Tarb} is a unit for \texttt{mergeTypes},
we can define a useful total lookup for \texttt{vtyp} as follows:
\begin{code}
vlkp :: VarTypes -> TVar -> Type
vlkp vtyp a
 = case tlookup vtyp a of
    Nothing   ->  Tarb
    (Just t)  ->  t
\end{code}

Adding in a \texttt{Tvar} equivalence is \emph{not} straightforward.
In fact this is where most of the algorithmic complexity resides.
A key utility function is the following, used when a \texttt{Tvar}
replaces an existing one in $vtyp$, that has to be moved back into
$vmap$, which has to be updated to refer to the new variable:
\begin{eqnarray*}
   n \searrow v \mapsto T_v
   &\defs& ranmap (v \mapsto n) vmap \cup \mapof{ v \mapsto n}
\\ && vtype \dagger \mapof{ n \mapsto T_n \downarrow T_v }\setminus \setof v
\end{eqnarray*}
Here we adopt a notational convention that $T_v$ denotes
the type mapped to by $vtyp$, i.e. $vtyp(v) = T_v$,
while $(x \mapsto y)$ is a function that leaves its argument
unchanged, except if it is $x$, in which case it returns $y$.
It also returns any type bindings or \texttt{Tvar} equivalences that
result from the $T_n \downarrow T_v$ term.
\begin{code}
tvDisplace :: TVar -> TVar
           -> (TVarEqvs, VarTypes)
           -> ( TVarEqvs, VarTypes
              , [(TVar,Type)]
              , [(TVar,TVar)] )
tvDisplace n v (vmap,vtyp)
 | n == v     =  (vmap,vtyp,[],[])
 | otherwise  =  ( vmap', vtyp', tbnds' , veqvs' )
 where

    vmap' =  tupdate v n (tmap (v `becomes` n) vmap)
    (a `becomes` b) v
      | a == v     =  b
      | otherwise  =  v

    vtyp'
      | triv tn tv  =  vtyp1
      | otherwise   =  tupdate n t' vtyp1
    vtyp1 = (tblank v vtyp)
    triv Tarb Tarb = True
    triv (Tvar u) (Tvar v) = v == u
    triv _ _       = False
    tn = vlkp vtyp n
    tv = vlkp vtyp v
    (t',tbnds',veqvs') = mergeTypes tn tv
\end{code}

Adding an equivalence is a large exercise in case-analysis
\begin{code}
addTVEqv :: (TVar, TVar)
         -> TVarEqvs
         -> VarTypes
         -> ( TVarEqvs
            , VarTypes
            , [(TVar,Type)]
            , [(TVar,TVar)] )
addTVEqv (a,b) vmap vtyp
 = case tlookup vmap a of
     Nothing
       -> case tlookup vmap b of
            Nothing   ->  displace a b
            (Just u)  ->  if a < u
                           then displace a u
                           else displace u a
     (Just v)
       -> case tlookup vmap b of
            Nothing   ->  displace v b
            (Just u)  ->  if u < v
                           then displace u v
                           else displace v u
 where displace x y = tvDisplace x y (vmap,vtyp)
\end{code}

We need to be able to ``map'' $vmap$ over the range
of $vtyp$, and to transitively close the latter:
\begin{code}
typeVarEqvMap :: TVarEqvs -> Type -> Type
typeVarEqvMap trie t = tm  t where

  tm tv@(Tvar v)
   = case tlookup trie v of
       Nothing    ->  tv
       (Just v')  ->  Tvar v'
  tm (TApp tcn ts) = TApp tcn (map tm ts)
  tm (Tfun td tr) = Tfun (tm td) (tm tr)
  tm (Tfree tn fs) = Tfree tn (map fm fs)
  tm t = t

  fm (fn,ts) = (fn,map tm ts)


transClose :: Trie Type -> Trie Type
transClose tvmap -- loops forever eating memory if tvmap loops.
 | tvmap == tvmap'  =  tvmap
 | otherwise        = transClose tvmap'
 where
   tvmap' = tmap (typeMap tvmap) tvmap
\end{code}

Also, straightforward type mapping
\begin{code}
typeMap :: Trie Type -> Type -> Type
typeMap trie t = tm  t where

  tm tv@(Tvar v)
   = case tlookup trie v of
       Nothing    ->  tv
       (Just t')  ->  t'
  tm (TApp tcn ts) = TApp tcn (map tm ts)
  tm (Tfun td tr) = Tfun (tm td) (tm tr)
  tm (Tfree tn fs) = Tfree tn (map fm fs)
  tm t = t

  fm (fn,ts) = (fn,map tm ts)
\end{code}

\newpage
Now, we can assemble the final type-inference system.
First a function doing the inference:
\begin{code}
inferTypes :: [Trie Type]
           -> [Expr]
           -> ( Trie Type         -- Var  -+-> Type
              , [(Type,[Type])]   -- [(Tvar,[Tvar])]
              )
inferTypes typs es
 | null (idbg "loops" loops)  =  (vt',    idbg "tpchlds'" tpchlds')
 | otherwise                  =  (loopvt, map loopresult tpchlds  )
 where

  tpchlds :: [(TVar,[TVar])]       --  [(Tvar,[Tvar])]
  vt :: Trie [String]              --  Var  -+-> [Tvar]
  tt :: Trie [Type]                --  Tvar -+-> [Type]
  (tpchlds,vt,tt) = bldTT typs (idbg "es" es)

  teqvs :: [[Type]]
  teqvs = detEquivLists (idbg "vt" vt) (idbg "tt" tt)

  loops = findTypeLoops (idbg "teqvs" teqvs)

  tbinds :: [(String, Type)]   --  Tvar -+-> Type
  veqvs :: [(String,String)]   --  Tvar -+-> Tvar
  vmap :: TVarEqvs          --  Tvar -+-> Tvar
  vtyp, vtyp' :: Trie Type     --  Tvar -+-> Type
  (tbinds,veqvs) = splitDetLists (idbg "teqvs" teqvs)
  (vmap,vtyp) = buildEqvTables (idbg "tbinds" tbinds) (idbg "veqvs" veqvs)
  vtyp' = transClose (tmap (typeVarEqvMap (idbg "vmap" vmap)) (idbg "vtyp" vtyp))

  vvmap  :: String -> Type                         --  Tvar -> Type
  vvmap2 :: (String,[String]) -> (Type,[Type])
  vt'    :: Trie Type                              -- Var -+-> Type
  vvmap = vvlookup (vmap,(idbg "vtyp'" vtyp'))
  vt' = tmap (vvmap . head) vt
  vvmap2 (top,chlds) = (vvmap top,map vvmap chlds)
  tpchlds' = map vvmap2 (idbg "tpchlds" tpchlds)

  loopresult (top,chlds) = (looperr,map (const looperr) chlds)
  looperr = Terror ("Tvar loop for '"++loopvar++"' in ") looptype
  (Tvar loopvar,looptype) = head loops
  loopvt = tmap (Tvar . head) vt

  idbg nm vr = vr -- dbg ("ITYPES."++nm++" =\n") vr
\end{code}

Then some wrapper code to take what we want:
\begin{code}
itype :: [Trie Type] -> Expr -> (Type,[Type])
itype typs e = head (itypes typs [e])

itypes :: [Trie Type] -> [Expr] -> [(Type,[Type])]
itypes typs es = snd $ inferTypes typs es
\end{code}

The above code is very much tailored for the requirements
of type-chekcing to support pattern matching,
and replacement.
The following code is a little more general,
returning type bindings for all the observation
and expression variables present
(under the assumption that they are all distinct):
\begin{code}
inferPredType :: [Trie Type] -> Pred -> Trie Type
inferPredType typs pr = fst $ inferTypes typs $ exprsOf pr
\end{code}



\subsection{Underlying Types}

\input{doc/Types-Underlying}

We tag all observation predicates with their underlying type
to facilitate law matching.
\begin{code}
topType top children
 = case top of
     B  ->  case children of
              []  ->  B
              [tt]  ->  tt
              _     -> mkTprod children
     Tfun B B  ->  Tfun B B
     Tarb      ->  inventType children
     Tvar _    ->  inventType children
     _         ->  Terror topNotBool top

topNotBool = "Top-level not B : "

boolNotRequired terr@(Terror msg typ)
 | msg == topNotBool  =  typ
 | otherwise          =  terr
boolNotRequired typ   =  typ
\end{code}

When the top-level type is arbitrary,
or a type variable,
we invent one for it, rather than recording an error.
\begin{code}
inventType [] = B -- must be boolean !
inventType ts
 = mkTprod (invent 1 [] ts)
 where
  invent n st' [] = reverse st'
  invent n st' (Tarb:ts) = invent (n+1) (Tvar ("a"++show n):st') ts
  invent n st' (t:ts) = invent n (t:st') ts
\end{code}

We do a global analysis of types,
once we have $\alpha$-renamed all bound variables
to be distinct from themselves and any free variables present.
We then add the type annotations back into the original predicate.
\begin{code}
addUType :: [Trie Type] -> FPred -> FPred

addUType typs fpr = globalPFapp (addutype typs) fpr
 where
   addutype typs pr
     = let
        fbpr = freeBoundPartition nullMatchContext pr
        es = exprsOf fbpr
        tpchlds = itypes typs es
        etypes' = map eutype (zip es tpchlds)
       in fst (obsTypeReplace etypes' pr)
\end{code}
If we have a \texttt{Efocus} that is not top-level,
then the underlying type is the type of the focus.
\textbf{Broken - we need to refactor how types are done.}
\begin{code}
-- eutype (e@(Efocus _ (_:_)),(top,_)) = top
eutype (e,(top,children)) = topType top children
\end{code}

\subsection{Type Checking}


Have we got a type-error?
\begin{code}
errsInType :: Type -> [String]

errsInType (Terror s t)  = [s]
errsInType (TApp _ ts)    = concat $ map errsInType ts
errsInType (Tfree _ cs)  = concat $ map errsInType $ concat $ map snd cs
errsInType (Tfun tf ta)  = errsInType tf ++ errsInType ta
errsInType _             = []
\end{code}

\newpage
\subsection{Observation Type-Replacement}

We also provide a predicate expression-type
replacement function (that works at the observation level).
We are simply replacing type annotations
in \texttt{Obs} by new values --- nothing else is changed.
We do need to check in certain contexts for erroneous type errors.

The important point here is that the list of observation types
has the same length as the expression list
obtained from \texttt{exprsOf}.
\begin{code}
obsTypeReplace :: [Type] -> Pred -> (Pred,[Type])

obsTypeReplace (newt:newts') old@(Obs e) = (Obs e,newts')
obsTypeReplace (newt:newts') old@(Defd e) = (Defd e,newts')
obsTypeReplace (newt:newts') old@(TypeOf e t) = (TypeOf e t,newts')

obsTypeReplace newts TRUE = (TRUE,newts)
obsTypeReplace newts FALSE = (FALSE,newts)
obsTypeReplace newts pr@(Pvar _) = (pr,newts)

obsTypeReplace newts (Not pr) = (Not pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Univ _ pr) = (Univ 0 pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Forall _ qs pr) = (Forall 0 qs pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Exists _ qs pr) = (Exists 0 qs pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Exists1 _ qs pr) = (Exists1 0 qs pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Ppabs s pr) = (Ppabs s pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Peabs s pr) = (Peabs s pr',newts')
 where (pr',newts') = obsTypeReplace newts pr

obsTypeReplace newts (NDC pr1 pr2) = (NDC pr1' pr2',newts')
 where ([pr1',pr2'],newts') = obsReplaces newts [pr1,pr2]
obsTypeReplace newts (Imp pr1 pr2) = (Imp pr1' pr2',newts')
 where ([pr1',pr2'],newts') = obsReplaces newts [pr1,pr2]
obsTypeReplace newts (RfdBy pr1 pr2) = (RfdBy pr1' pr2',newts')
 where ([pr1',pr2'],newts') = obsReplaces newts [pr1,pr2]
obsTypeReplace newts (Eqv pr1 pr2) = (Eqv pr1' pr2',newts')
 where ([pr1',pr2'],newts') = obsReplaces newts [pr1,pr2]
obsTypeReplace newts (Papp prf pra) = (Papp prf' pra',newts')
 where ([prf',pra'],newts') = obsReplaces newts [prf,pra]

-- IMPORTANT -- exprsOf only visits 1st element at present
obsTypeReplace newts (Psapp pr spr) = (Psapp pr' spr,newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Psin pr spr) = (Psin pr' spr,newts')
 where (pr',newts') = obsTypeReplace newts pr


obsTypeReplace newts (Pforall pvs pr) = (Pforall pvs pr',newts')
 where (pr',newts') = obsTypeReplace newts pr
obsTypeReplace newts (Pexists pvs pr) = (Pexists pvs pr',newts')
 where (pr',newts') = obsTypeReplace newts pr

obsTypeReplace newts (And prs) = (And prs',newts')
 where (prs',newts') = obsReplaces newts prs
obsTypeReplace newts (Or prs) = (Or prs',newts')
 where (prs',newts') = obsReplaces newts prs

obsTypeReplace newts (If prc prt pre) = (If prc' prt' pre',newts')
 where ([prc',prt',pre'],newts') = obsReplaces newts [prc,prt,pre]

-- need to treat atomic predicate substitution carefully
-- the whole thing is viewed as one expression

obsTypeReplace (newt:newts') (Sub (Obs e) sub)
 = (Sub (Obs e) sub,newts')

obsTypeReplace newts (Sub pr sub@(Substn ssub))
 = (Sub pr' sub,newts'')
 where
   newts' = drop (length ssub) newts
   (pr',newts'') = obsTypeReplace newts' pr

obsTypeReplace newts (Psub pr sub@(Substn ssub))
 = (Psub pr' (Substn ssub'),newts'')
 where
   (pr',newts') = obsTypeReplace newts pr
   (vs,sprs) = unzip ssub
   (sprs',newts'') = obsReplaces newts' sprs
   ssub' = zip vs sprs'

obsTypeReplace newts (Pfocus prf) = (Pfocus prf',newts')
 where (prf',newts') = obsTypeReplace newts prf

obsTypeReplace newts (Lang s p les ss) = (Lang s p les' ss,newts')
 where (les',newts') = obsLListReplace newts les

obsTypeReplace newts pr
 = error $ unlines $ [ "obsTypeReplace NYFI"
                     , "\t pr is "++show pr
                     , "\tobs is "++show newts
                     ]

-- replacing newts in predicate lists

obsReplaces newts [] = ([],newts)
obsReplaces newts (pr:prs) = (pr':prs',newts'')
 where (pr',newts') = obsTypeReplace newts pr
       (prs',newts'') = obsReplaces newts' prs

-- replacing newts in language lists
-- now a simple linear pass..

obsLListReplace newts les
 = obsLLR [] newts les
 where

   obsLLR sel newts [] = (reverse sel,newts)

   obsLLR sel [] les = (reverse sel++les,[])
   obsLLR sel (newt:newts) (le@(LVar _):les)  = obsLLR (le:sel) newts les
   obsLLR sel newts        (le@(LType _):les) = obsLLR (le:sel) newts les
   obsLLR sel (newt:newts) (le@(LExpr _):les) = obsLLR (le:sel) newts les

   obsLLR sel newts      (LPred pr:les)
    = obsLLR (LPred pr':sel) newts' les
    where
       (pr',newts') = obsTypeReplace newts pr

   obsLLR sel newts (LList les':les)
    = obsLLR (LList les'':sel) newts' les
    where
       (les'',newts') = obsLLR [] newts les'

   obsLLR sel newts (LCount les':les)
    = obsLLR (LCount les'':sel) newts' les
    where
       (les'',newts') = obsLLR [] newts les'


-- test for correctness, with etypes set to "arbitrary".

prop_obsTypeReplace_id pr
 = let
     etypes = replicate (length (exprsOf pr)) Tarb
     (pr',_) = obsTypeReplace etypes pr
   in pr' == fst (obsTypeReplace etypes pr')
\end{code}


\subsubsection{Unification}

\input{doc/Types-Unification}
