\section{\UTP2\ Program\ Verification}

\begin{code}
module WxProg where
import Tables
import Debug.Trace

import Datatypes
import DataText
import Types
import MatchTypes
import Matching
import Instantiate
import FreeBound
import Focus
import Heuristics
import Builtin
import Substitution
import Laws
import Manipulation
import Normalise
import Proof
import Program
import Theories
import Utilities
import Files
import ImportExport
import Archive
import DocTextParser

import DSL
import Logic
-- import GSLogic
-- import GS3001
-- import UTP
-- import R
-- import RAlg
-- import LaTeXTest

import System.IO
import Graphics.UI.WX
import Graphics.UI.WXCore

import Data.Char
import Data.List
import Control.Monad

import Test.QuickCheck hiding (ok)

import WxTypes
import WxState
import WxTheory
import WxProof

import Data.Maybe
import Control.Monad

\end{code}
\subsection{Creating a Program}

The handler for the top-level right-click menu

\begin{code}
addPROGItem work thry tmMenu
 = do mitem <- menuItem tmMenu [text:=ptxt thry]
      set mitem [on command := createProg thry work]
 where
  ptxt thry = "Create Program over Theory"

\end{code}
Drawing code for the active program area,
and click handlers for the area.

\begin{code}
showProgspace (prname, progsp) = ( [ DD (DDrawText Nothing (show progsp)) nullDDBB (0,0) ]
                       , (topProgClick progsp)
                       )

topProgClick progspace
 = ClkHandlers Nothing
               (Just viewTheProgram)
               Nothing
   where
     viewTheProgram pnt work = repaintProgGUI progspace

repaintProgGUI progspace
 = do let pg = progFrame $ progGUI progspace
      repaint pg

createProg thry work
 = do topf <- getTop work
      fpar <- get topf frameParent
      ss <- varGet work
      let lprogs = currProgs $ workspace $ ss
      progname <- textDialog fpar "Program Name" ("Create Program over " ++ thryName thry) ""
      if null progname
       then return ()
       else
        do (rdag,trie) <- getThgrf work
           sts <- getSts work
           let cthnm = thryName thry
           let newthname = cthnm ++ "-" ++ progname
           let thnames = concat $ rdStratify rdag
           if newthname `elem` thnames
            then alert sts ("createTheory '"++newthname++"' already exists")
            else
             do let thry = nmdNullPrfCtxt newthname
                let prog = mkProgram newthname progname newthname
                prgspace <- createProgramSpace prog work
                addThry work thry
                linkThry newthname cthnm work
                insertPspace prgspace work
                repaint topf
                alert sts ("Theory '"++newthname++"' Created.")

addThry work thry
 = do let thnm = thryName thry
      (rdag,trie) <- getThgrf work
      let trie' = tupdate thnm thry trie
      sts <- getSts work
      case rdAdd thnm rdag of
       Left err
        -> alert sts ("Cannot add theory: "++show err)
       Right rdag'
        -> do setThgrf (rdag',trie') work
              setStkMod work True
              top <- getTop work
              repaint top

linkThry from to work
 = do (rdag,trie) <- getThgrf work
      let res = rdUpdate from [to] rdag
      case res of
        Right rdag'
         -> do thgrfSetf (const (rdag',trie)) work
               top <- getTop work
               repaint top
        Left err
         -> do sts <- getSts work
               alert sts ("Cannot link: "++show err)


-- update the workspace
currProgsSetf f recd = recd{ currProgs = f $ currProgs recd }

insertPspace pspace work
 = do ss <- varGet work
      let ws = workspace ss
      let ws' = currProgsSetf (tupdate (pid $ prog $ pspace) pspace) ws
      let ss' = ss{workspace=ws'}
      varSet work ss'

\end{code}
\subsection{Program Editor}
Program entry dialog. Possibly move this to WxEdit or similar once it
becomes sufficiently advanced.

\begin{code}
createProgramWindow program work =
  do window <- frame [text := "Program Editor"]
     editor <- textCtrl window [font := fontFixed, text := ptext program]
     focusOn editor

     actions <- menuPane [text := "Actions"]
     menuItem actions [ text := "Load", on command := openProg editor window (pid program) work]
     menuItem actions [ text := "Save", on command := saveProg editor window (pid program) work]
     menuItem actions [ text := "Abandon",
      on command := (\w -> do windowClose w False; return ()) window ]

     debugM <- menuPane [text := "Debug"]
     menuItem debugM [ text := "Sync", on command := syncProg editor (pid program) work]
     menuItem debugM [ text := "Show", on command := progDo (pid program) work showP noP]
     menuItem debugM [ text := "Finalise", on command := finalise editor window program work]

     set window [menuBar := [actions, debugM]]

     set window [ layout := fill $ widget editor
                , clientSize := sz 480 480
                , visible := True
                , closeable := True
                , on closing := abandonProg (pid program) work
                ]

     let pgui = ProgramGUI window True
     return pgui

     where
      showP pspaces pid pspace work
       = do toConsole $ ptext $ prog pspace

      noP pid work
       = do return ()

--remove the program from the active programs (modify the trie)
unsetCurrprg work pid
 = do pspaces <- fmap (currProgs . workspace) (varGet work)
      let pspaces' = tblank pid pspaces
      varSetf ((workspaceSetf . currProgsSetf . const) pspaces') work

progDo pid work jaction naction
 = do pspaces <- fmap (currProgs . workspace) (varGet work)
      case tlookup pspaces pid of
        Nothing      ->  naction pid work
        Just pspace  ->  jaction pspaces pid pspace work

noProg pid work
 = do topf <- getTop work
      warningDialog topf "No such Program" ("Program '"++pid++"' not found")

addPredicate name pred thry
 = thry{preds=tupdate name pred (preds thry)}

remPredicate name thry
 = thry{preds=tblank name (preds thry)}

insertPredicate thryname predname pred work
 = do thry <- doTheoryLookup thryname work
      case thry of
       Nothing    -> return ()
       (Just thr) ->
        do let thr' = addPredicate predname pred thr
           doTheoryUpdate thryname thr' work

finalise editor window program work
 = do parse <- pcondPopup (pid program) editor work
      case parse of
        Left msg -> do warningDialog editor "Parse failed" ("Predicate Parse failed: "++msg)
        Right (postC,sc) -> do fillTheory editor window postC (pid program) work

fillTheory editor window postC progpid work
 = do syncProg editor progpid work
      preds <- instantiatePredList progpid work
      if head (map isNothing preds)
        then
          warningDialog window "Parse Error" "Program failed to parse correctly"
        else
          do let safePred = fromJust.head $ preds
             pspaces <- fmap (currProgs . workspace) (varGet work)
             case tlookup pspaces progpid of
              Nothing      ->  return ()
              Just pspace  ->
               do let name = (const "PP") safePred
                  let thryname = pthname $ prog pspace
                  lawPrefix <- textDialog window "Enter a law prefix" "Law Acquisition"  ""
                  insertPredicate thryname name safePred work
                  insertPredicate thryname "postcondition" postC work
                  conj <- genVCS thryname work postC safePred name
                  case conj of
                   Nothing -> scream work $ "genVCS parse error - failed to construct \""
                                            ++ lawPrefix ++ "\" predicate"
                   Just (aPred,sc) ->
                    do let conjName = prname (prog pspace) ++ "-conj"
                       thry <- doTheoryLookup thryname work
                       tstack <- extractProofStack thryname work
                       let newConjs = progMatching lawPrefix progpid work tstack aPred sc window
                       addConjs 1 (fromJust thry) conjName thryname work newConjs

addConjs i thry cname tname work [] = doTheoryUpdate tname thry $ work
addConjs i thry cname tname work  (conj:conjs)
 = do let thry' = addConjecture (cname ++ ('.':show(i))) conj thry
      let thry'' = raiseTheoryMod thry' Log
      addConjs (i+1) thry'' cname tname work conjs

progMatching lawPrefix pid work tstack pred sc window
  = do let wpLaws = lawCmp lawPrefix (allLaws tstack)
       let safeLaws = map fromJust (filter (\x -> x /= Nothing) (map checkSides wpLaws))
       let lawsAndRHS = zip (map lawAsLHS safeLaws) (map getRHS safeLaws)
       let newStack = replaceLaws tstack safeLaws
       let matchCtxt = mkMatchContext newStack
       zip (sepAtAnd (applyAllMatches ([1..]) pid work sc matchCtxt lawsAndRHS pred)) (repeat sc)
    where
      lawAsLHS (name,(((PApp nm [lhs, _]),sc),prov,tts))
       | nm==n_Eqv  = ((lhs,sc),tts)
      getRHS (_,(((PApp nm [_, rhs]),_),_,_)) | nm==n_Eqv  =  rhs
      allLaws (x:xs) = concatMap laws xs
      replaceLaws (newThry:x:xs) wpLaws = x{laws = wpLaws} : xs

sepAtAnd (pr@(Lang s p les ss),_)
  | lesPreds les /= [] = sepAtAnd (head.lesPreds $ les, False)
  | otherwise = [pr]
sepAtAnd ((PApp nm prs),_) | nm==n_And  =  prs
sepAtAnd (pr,_)                         =  [pr]

lawCmp [] _ = []
lawCmp _ [] = []
lawCmp y ((x,law):xs)
  | match = [(x,law)] ++ lawCmp y xs
  | otherwise = lawCmp y xs
  where match = y == take (length y) x

applyAllMatches count pid work sc mCtxt lawsAndRHS pred
  | change = mapFunc ans
  | otherwise = (performSub mCtxt sc ans, change)
  where
    eNoChg e = (e, False)
    mapFunc = mapPf (applyAllMatches (tail count) pid work sc mCtxt lawsAndRHS, eNoChg)
    matchSimp = progMatcher (head count) mCtxt sc lawsAndRHS
    (newPred, change) = mapFunc (matchSimp pred)
    ans = predFlatten.matchSimp $ newPred

performSub mCtxt sc (Sub pr subs) = fst $ predOSub mCtxt sc subs pr
performSub _ _ pr = pr

progMatcher inum mCtxt sc lawsAndRHS pred
  | matchAndRHS /= Nothing = newPred
  | otherwise = pred
  where
    (pred',tts) = predTypeTables mCtxt pred
    matchAndRHS = findLawMatch (FVSet []) mCtxt tts sc lawsAndRHS pred'
    (binding, rhs) = fromJust matchAndRHS
    newPred = instantiatepred (show inum) mCtxt binding rhs

--Cloned from instantiatePred to assign unique number to generated Invariants
instantiatepred inum mctxt bnds@(gpbnds,vebnds,ttbnds) pat
 = bP pat
 where

   bP (PVar v)
     = case gplookupTO (varGenRoot v) gpbnds of
         Nothing     ->  PVar $ varmap (++inum) v
         (Just pr)  ->  pr

   bP (PExpr (App nm [Var v1, Var v2]))
    | nm == n_Equal = bE2P mkEqual v1 v2
   bP (PExpr e) = PExpr (instantiateExpr mctxt bnds e)

   bP (TypeOf e t) = TypeOf (instantiateExpr mctxt bnds e) (instantiateType mctxt bnds t)
   bP (PApp nm prs) = PApp nm (map bP prs)
   bP (PAbs nm _ qs prs)
     = PAbs nm 0 (instantiateQ mctxt bnds qs) (map bP prs)
   bP (Sub pr sub) = mkSub (bP pr) (instantiateESub mctxt bnds sub)
   bP (Lang nm p [le1,le2] ss) = bL2P nm p ss le1 le2
   bP (Lang nm p les ss) = Lang nm p (bLES les) ss

   bP pat = pat
\end{code}

\newpage
Handling for 2-place atomic predicates with meta-variables.
Note that meta-variable subtractions may have pattern variables
and we should bind these first.
\begin{code}
   bE2P apred v1 v2
    | isStdV v1                 =  std
    | isStdV v2                 =  std
    | notSeq r1                 =  std'
    | notSeq r2                 =  std'
    | length es1 /= length es2  =  std'
    | otherwise = mkAnd (map (b2E apred) (zip es1 es2))
    where

     -- std -------------------------------------------
     e1 = instantiateExpr mctxt bnds (Var v1)
     e2 = instantiateExpr mctxt bnds (Var v2)
     std = PExpr (apred e1 e2)

     -- r1, r2  ---------------------------------------
     v1' = instantiatemv v1
     v2' = instantiatemv v2

     instantiatemv (r@(Gen _),decor,_)
      = mkVar r decor []
     instantiatemv (r@(Rsv _ subs),decor,_)
      = mkVar r decor (map bv subs)

     bv g = case velookupTO (rootAsVar $ Gen g) vebnds of
              Just (Var ((Gen g'),Pre,_))  ->  g'
              _                            ->  g

     r1 = expand v1'
     r2 = expand v2'

     expand mv
      | nonRsvList mv   =  velookupTO mv vebnds
      | null ovars      =  Nothing
      | null leftover   =  Just $ mkSeq $ map Var ovars
      | otherwise       =  Nothing -- ISSUE: should we handle leftovers?
      where
        (ovars,leftover) = lVarDenote mctxt mv

     -- notSeq ----------------------------------------
     notSeq (Just (App nm _)) | nm==n_seq  =  False
     notSeq _                              =  True

     -- std' ------------------------------------------
     e1' = instantiateExpr mctxt bnds (Var v1')
     e2' = instantiateExpr mctxt bnds (Var v2')
     std' = PExpr (apred e1' e2')


     -- es1, es2 --------------------------------------
     (Just (App _ es1)) = r1
     (Just (App _ es2)) = r2

   -- end bE2P

   b2E apred (e1,e2) = PExpr (apred e1 e2)
\end{code}

Doing it all for languages:
\begin{code}
   bL2P nm p ss le1 le2
    | not $ isLELstV le1        =  std
    | not $ isLELstV le2        =  std
    | notSeq r1                 =  std
    | notSeq r2                 =  std
    | length es1 /= length es2  =  std
    | otherwise = mkAnd (map (b2L nm p ss) (zip es1 es2))
    where

     std = Lang nm p (bLES [le1,le2]) ss

     vof (LVar g) = mkGVar Scrpt g
     vof (LExpr (Var v)) = v
     v1 = vof le1
     v2 = vof le2

     r1 = velookupTO v1 vebnds
     r2 = velookupTO v2 vebnds
     notSeq (Just (App nm _)) | nm==n_seq  =  False
     notSeq _                              =  True
     (Just (App _ es1)) = r1  -- should be a n_seq
     (Just (App _ es2)) = r2  -- should be a n_seq

   -- end bL2P

   b2L nm p ss (e1,e2) = Lang nm p [LExpr e1,LExpr e2] ss
\end{code}

Other \texttt{instantiatePred mctxt} auxilliaries:
\begin{code}
   bLES [] = []
   bLES (le:les) = bLE le : bLES les

   bLE (LVar g)     = LVar (case velookupTO (mkGVar Scrpt g) vebnds of
                              Nothing       ->  g
                              Just (Var (Gen g',_,_)) ->  g'
                              Just e        ->  Std ("??Lvar '"++show g++"' to "++show e++"??")
                           )
   bLE (LType t)    = LType (instantiateType mctxt bnds t)
   bLE (LExpr e)    = LExpr (instantiateExpr mctxt bnds e)
   bLE (LPred pr)   = LPred (bP pr)
   bLE (LList les)  = LList (map bLE les)
   bLE (LCount les) = LCount (map bLE les)

   bPV pvs = map (stripPvar . bP . PVar . parseVariable . psName) pvs

   stripPvar (PVar r) = show r
   stripPvar pr       = "?PredSet-Name-expected?"

findLawMatch fv mctxt ptts sc [] pred = Nothing
findLawMatch fv mctxt ptts sc (((lhs,ltts),rhs):xs) pred
  | match == Nothing = findLawMatch fv mctxt ptts sc xs pred
  | otherwise = Just (fromJust match, rhs)
  where match = lawMatch [] fv ltts mctxt sc pred lhs ptts

checkSides law@(_,(((PApp nm [_, _]),_),_,_))
 | nm == n_Eqv = Just law
checkSides _ = Nothing

pcondPopup progpid pwin wk
 = do pspaces <- fmap (currProgs . workspace) (varGet wk)
      case tlookup pspaces progpid of
        Nothing      ->  return $ Left "Dud program name in postcondition insertion"
        Just pspace
          -> do mbThry <- doTheoryLookup (pthname $ prog pspace) wk
                case mbThry of
                  Nothing -> return $ Left $ "Dud theory name in postcondition insertion"++(pthname $ prog pspace)
                  (Just thry)
                    -> do predtxt <- textDialog pwin "Enter a postcondition predicate" "Postcondition Text"  ""
                          let thname = pthname $ prog pspace
                          let nname = (prname $ prog pspace) ++ "-postcondition"
                          depTheories <- getAllThings id thname wk
                          let parser = asnTextParser depTheories
                          return $ parser "New-Predicate" predtxt

doMultiparse thname pwin work predtxts
 = do depTheories <- getAllThings id thname work
      let parser = asnTextParser depTheories
      mapM (xxx parser) predtxts
   where
    xxx parser predtxt
      = do let parse = parser "do-parse" predtxt
           case parse of
             Left msg        -> return Nothing
             Right (pred,sc) -> return $ Just pred
             --does it make sense for lines in a program to have side-conditions?
             --TODO: figure out how to do this without throwing away errors
             -- perhaps return Either Pred Error?

--sometimes we want a result back from the IO action taken
progDoResult pid work jaction naction
 = do pspaces <- fmap (currProgs . workspace) (varGet work)
      case tlookup pspaces pid of
        Nothing      ->  return $ naction pid work
        Just pspace  ->  return $ jaction pspaces pid pspace work

--if there is no such program, we need a 'zero' result
noProgResult result pid work
 = do topf <- getTop work
      warningDialog topf "No such Program" ("Program '"++pid++"' not found")
      return $ result

--instantiate a list containing one predicate for each program statement
instantiatePredList ppid work
 = progDo ppid work getPreds (noProgResult [])
 where
   getPreds pspaces pid pspace work
    = do let ps = ptext $ prog pspace  --lines
         preds <- doMultiparse (pthname $ prog pspace) (progFrame $ progGUI pspace) work [ps]
         return $ preds

{-

Programmatically insert observation variables and their dashed counterparts.
1.  obtain the list of free variables from a predicate
2.  -insert such variables in the theory-

-- Note: we automatically insert a dashed variable if we can
addNewObs thname thry varname vartype
 = do depTheories <- getAllThings id thname work
      let parse = obsKindTextParser depTheories "" vartype
        case parse of
          Left msg  ->  toConsole "Bad obsvar type: "++msg
                        return thry
          Right okind ->
           do let thry' = upd_obs varname okind thry
              if last varname == '\''
               then return thry'
               else
                  do let varname' = varname++"'"
                     return $ upd_obs varname' okind $ thry'
-}

syncProg editor progpid work
 = do progDo progpid work synctext noProg
 where
   synctext pspaces pid pspace work
    = do newtext <- (get editor text)
         let oldtext = ptext $ prog pspace
         if newtext == oldtext
          then toConsole "Sync not needed" >> return ()
          else do
            let oldprog = prog pspace
            let pspaces' = tupdate pid (progSetf (const (oldprog {ptext = newtext})) pspace) pspaces
            varSetf ((workspaceSetf . currProgsSetf . const) pspaces') work

abandonProg progpid work
 = do quitting <- fmap shuttingdown (varGet work)
      progDo progpid work (abandonPrg quitting) noProg
 where
   abandonPrg qttng pspaces pid pspace work
    = do let prg = progFrame (progGUI pspace)
         if qttng
          then xxx prg
          else
           do abandon <- confirmDialog prg "Abandon Program Entry"
                             "Are you sure you want to abandon ?"
                             False
              if abandon
               then xxx prg
               else return ()

   noProg pid work
    = do topf <- getTop work
         warningDialog topf "No such Program" ("Program '"++pid++"' not found")

   xxx prg
    = do windowDestroy prg
         unsetCurrprg work progpid
         top <- getTop work
         repaint top

createProgramSpace program work
 = do pgui <- createProgramWindow program work
      return $ ProgramSpace pgui program

openProg editor win ppid work
 = do (_,cwd) <- getCurrFS work
      maybePath <- fileOpenDialog win True True "Open file..."
                                   [("UTP programs (*.utprog)",["*.utprog"]),
                                    ("Any file (*.*)",["*.*"])]
                                   cwd ""
      case maybePath of
        Nothing   -> return ()
        Just path -> do textCtrlLoadFile editor path
                        set win [text := "Program Editor - " ++ path]

saveProg editor win ppid work
 = do (_,cwd) <- getCurrFS work
      maybePath <- fileSaveDialog win True True "Save file..."
                                  [("UTP programs (*.utprog)",["*.utprog"]),
                                   ("Any file (*.*)",["*.*"])]
                                  cwd ""
      case maybePath of
       Nothing   -> return ()
       Just path -> do textCtrlSaveFile editor path
                       set win [text := "Program Editor - " ++ path]

\end{code}

Functioning verification condition generation stuff (more in verification.lhs)

\begin{code}

mkWp thname work predA predB
 = do depTheories <- getAllThings id thname work    --do I want all theorys or just the ones in wp
      let parser = asnTextParser depTheories
      let txtA = show predA
      let txtB = show predB
      let txtwp = "(" ++ txtA ++ ") wp " ++ txtB
      return $ parser "auto-wp" txtwp

genVC thryname work pred predname postcond
 = do precond <- mkWp thryname work pred postcond
      case precond of
        Left msg      -> return $ Nothing
        Right assertion@(vc,sc) ->
          do let wpredname = "w"++predname
             insertPredicate thryname wpredname vc work
             return $ Just assertion

genVCS tname work pcondP pred predname
 = genVC tname work pred predname pcondP
\end{code}
