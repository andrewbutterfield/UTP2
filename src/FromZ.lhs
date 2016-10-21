\section{Z to \Saoithin\ Translator}

Simon Dardis, Summer 2008.

\begin{code}
module FromZ where
import Datatypes
import Tables
import Precedences
import DataText
import DSL
import LaTeXAST
import LaTeXLexer -- for debug purposes
import LaTeXParse
import Proof
import Theories
import Data.Maybe
import Data.List
import Data.Char
import Laws
import Data.Int
import LaTeXSetup
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
\end{code}

\subsection{Translation Types}

Structure \texttt{Contexttables} stores the
list of predicates, variables, types and precedence,
so we can detect when a variable is actually a predicate.

\begin{code}
data Contexttables
  = Contexttables
     { prectable  :: [Trie (Int,Assoc)] -- prec: builtin operator precedence and associativity table
     , vartable   :: [Trie Type]       -- obs:  theory observation variables (set)
     , typetable  :: [Trie Type]   -- typ: type-table stack
     , predtable  :: [Trie Pred]   -- preds: named predicates stack
     , ltxtable   :: LaTeXLayout  -- all the LaTeX stuff
     }
\end{code}

\newpage
The type \texttt{ProofContextPart}  is used to accumulate the results
of a translated parse as association lists
before turning most of them into  \texttt{Trie}s.
\begin{code}

data ProofContextPart
  = PCP { pcpName :: String
        , pcpSeqNo :: Int
        , pcpTdefs :: [(String,Type)]
        , pcpConsts :: [(String,Expr)]
        , pcpExprs  :: [(String,Expr)]
        , pcpPreds  :: [(String,Pred)]
        , pcpObs    :: [(String,ObsKind)]
        , pcpPrecs  :: [(String,Precs)]
        , pcpTypes  :: [(String,Type)]
        , pcpAlphas :: [(String,Alphabet)]
        , pcpLaws   :: LawTable
        , pcpConjs  :: [(String,Assertion)]
        , pcpThms   :: [(String,Proof)]
        }

nullPCP = PCP "NoName" 0 [] [] [] [] [] [] [] [] [] [] []

addName pcp n = pcp{pcpName = n}
addSeqNo pcp n = pcp{pcpSeqNo = n}
addTdefs pcp as = pcp{pcpTdefs = as:(pcpTdefs pcp)}
addConsts pcp as = pcp{pcpConsts = as:(pcpConsts pcp)}
addExprs pcp as = pcp{pcpExprs = as:(pcpExprs pcp)}
addPreds pcp as = pcp{pcpPreds = as:(pcpPreds pcp)}
addObs pcp as = pcp{pcpObs = as:(pcpObs pcp)}
addPrecs pcp as = pcp{pcpPrecs = as:(pcpPrecs pcp)}
addTypes pcp as = pcp{pcpTypes = as:(pcpTypes pcp)}
addAlphas pcp as = pcp{pcpAlphas = as:(pcpAlphas pcp)}
addLaws pcp as = pcp{pcpLaws = as:(pcpLaws pcp)}
addConjs pcp as = pcp{pcpConjs = as:(pcpConjs pcp)}
addThms pcp as = pcp{pcpThms = as:(pcpThms pcp)}

\end{code}

\subsection{Translation Functions}

Functions to translate Jaza's Z-Expression types into the equivalent Saoithin datatypes.
\begin{code}
fromZVar (zroot,zdecors)
 = mkVar r d []
 where
  r = Gen $ Std zroot
  d = if null zdecors
       then Pre
       else case head zdecors of
         "'"      ->  Post
         ('_':s)  ->  Subscript s
         _        ->  NoDecor

showZvar = varKey . fromZVar

zvar = Var . preVar
\end{code}

Extracting expressions.
\begin{code}
fromZExpr (prec,l2a) (ZInt num) = Num (fromInteger num)
fromZExpr (prec,l2a) (ZSetDisplay set) = Set (map (fromZExpr (prec,l2a)) set)
fromZExpr (prec,l2a) (ZSeqDisplay [(ZCall x y)])
  = Seq (nestedCalls (prec,l2a) (ZCall x y))

fromZExpr (prec,l2a) (ZSeqDisplay seq) = Seq (map (fromZExpr (prec,l2a)) seq)
fromZExpr (prec,l2a) (ZFSet fset) = Set (map (fromZExpr (prec,l2a)) fset)
fromZExpr (prec,l2a) (ZVar varname) = Var (fromZVar varname)
fromZExpr (prec,l2a) (ZIf_Then_Else pred exp1 exp2)
  = Cond (fromZPred (prec,l2a) pred) (fromZExpr (prec,l2a) exp1) (fromZExpr (prec,l2a) exp2)

fromZExpr (prec,l2a) (ZTuple list) = Prod (map (fromZExpr (prec,l2a)) list)
fromZExpr (prec,l2a) (ZGiven givenValue) = zvar (givenValue)
fromZExpr (prec,l2a) (CEVarExpr string zExpr)
  = Build (showZvar string) (map (fromZExpr (prec,l2a)) zExpr)

fromZExpr (prec,l2a) (CEEabs zVars zExpr) = Eabs 0 t (fromZExpr (prec,l2a) zExpr)
 where t = Q (map fromZVar zVars)
fromZExpr (prec,l2a) (CESub e e1 v1)
  = Esub (fromZExpr (prec,l2a) e) (packlistQV (zip exprlist qlist))
  where
    qlist     =  map (fromZVar) v1
    exprlist  =  map (fromZExpr (prec,l2a)) e1

fromZExpr (prec,l2a) (CSetComp qvar pred expr)
  = Setc 0 (fromZQVar qvar) (fromZPred (prec,l2a) pred) (fromZExpr (prec,l2a) expr)

fromZExpr (prec,l2a) (CSeqCompre qvar pred expr)
  = Seqc 0 (fromZQVar qvar) (fromZPred (prec,l2a) pred) (fromZExpr (prec,l2a) expr)

\end{code}
These \texttt{ZCall} constructions can either be infix binary operators, or a function call. A helper function
is called to do the determination and translation.
\begin{code}

fromZExpr (prec,l2a) (ZCall (ZVar a) (ZCall b c))
  = App (showZvar a) (fromZExpr (prec,l2a) (ZCall b c))

fromZExpr (prec,l2a) (ZCall (ZCall var1 (ZVar func)) var2)
  = binOrApp (prec,l2a) func [var1,var2]

fromZExpr (prec,l2a) (ZCall (ZVar func) (ZTuple tuple))
  = binOrApp (prec,l2a) func tuple

fromZExpr (prec,l2a) (ZCall (ZGiven x) y) = binOrApp (prec,l2a) (make_zvar x []) [y]
fromZExpr (prec,l2a) (ZCall (ZVar x) (ZVar y))
  = App (showZvar x) (Var (fromZVar y))

fromZExpr (prec,l2a) a
  = Eerror ("FromZ.fromZExpr : cannot handle ZExpr ( " ++ show a ++ " )")

\end{code}
Nested Calls occur in \texttt{ZSeqDisplay}.

\CHECK{%
  Do we really want to flatten nested calls like this?
  Shouldn't we respect the left-associativity of application?
  Note that it seems only to be used for sequence display!
}
\begin{code}

nestedCalls :: ([Trie (Int,a)],String -> Maybe String) -> ZExpr -> [Expr]
nestedCalls (prec,l2a) (ZCall x y) = nestedCalls (prec,l2a) x ++ nestedCalls (prec,l2a) y
nestedCalls (prec,l2a) a           = [fromZExpr (prec,l2a) a]

\end{code}
Extracting \texttt{QVars} from new (non-Z) types
\begin{code}

fromZQVar (CQVarlist qlist) = Q (map fromZVar qlist)
fromZQVar (CQQVar x)        = Q [preVar x]
fromZQVar (CQQVarlist x)    = Q [preVar x]
fromZQVar (CQQPair x y)     = (fromZQVar x) `qsmrg` (fromZQVar y)
fromZQVar (CQVar x)         = Q [preVar x]

fromZExpr2Q p = toQ . fromZExpr p
 where
   toQ e = Q [eDrop e]
\end{code}
Schema expressions, only names are handled.
(Greek decorations added, Andrew Butterfield, Nov. 2008)
\begin{code}

fromZSexpr (ZSRef b _ _) = fromZSName b
fromZSexpr _             = "Schema Expression not implemented"
fromZSName (ZSPlain s)   = s
fromZSName (ZSDelta s)   = "Delta:"++s
fromZSName (ZSXi s)      = "Xi:"++s

\end{code}

Predicate translations:
We ignore the reason list for true, false.
\begin{code}
fromZPred (prec,l2a) (ZTrue _) = TRUE
fromZPred (prec,l2a) (ZFalse _) = FALSE
fromZPred (prec,l2a) (ZAnd x y)
 = And [ ((fromZPred (prec,l2a)) x), ((fromZPred (prec,l2a)) y) ]

fromZPred (prec,l2a) (ZOr x y)
 = Or [ ((fromZPred (prec,l2a)) x), ((fromZPred (prec,l2a)) y) ]

fromZPred (prec,l2a) (ZImplies x y)
 = Imp ((fromZPred (prec,l2a)) x) ((fromZPred (prec,l2a)) y)

fromZPred (prec,l2a) (ZNot x) = Not ((fromZPred (prec,l2a)) x)
fromZPred (prec,l2a) (ZIff x y) = Eqv ((fromZPred (prec,l2a)) x) ((fromZPred (prec,l2a)) y)

fromZPred (prec,l2a) (ZExists q pred)
  = Exists 0 (fromZExpr2Q (prec,l2a) q) ((fromZPred (prec,l2a)) pred)

fromZPred (prec,l2a) (ZExists_1 q pred)
  = Exists1 0 (fromZExpr2Q (prec,l2a) q) ((fromZPred (prec,l2a)) pred)	
  -- Need to get the proper mapping.

fromZPred (prec,l2a) (ZForall q pred)
  = Forall 0 (fromZExpr2Q (prec,l2a) q) ((fromZPred (prec,l2a)) pred)

fromZPred (prec,l2a) (ZEqual zexpr1 zexpr2)
  = Eqv (Obs ((fromZExpr (prec,l2a)) zexpr1))
        (Obs ((fromZExpr (prec,l2a)) zexpr2))

fromZPred (prec,l2a) (ZPSchema zsexpr)= Pvar $ Std (fromZSexpr zsexpr)
fromZPred (prec,l2a) (ZMember (ZTuple x) (ZVar func))
  = Obs (binOrApp (prec,l2a) func x)

fromZPred (prec,l2a) (ZMember exp1 exp2)
  = Obs (Bin "in" 5 ((fromZExpr (prec,l2a)) exp1) ((fromZExpr (prec,l2a)) exp2))

fromZPred (prec,l2a) (CSeqComp zPred1 zPred2)
  = (fromZPred (prec,l2a) zPred1) >>> (fromZPred (prec,l2a) zPred2)

fromZPred (prec,l2a) (CIntChoice zPred1 zPred2)
  = Lang "|~|" 60
               [ LPred (fromZPred (prec,l2a) zPred1)
               , LPred (fromZPred (prec,l2a) zPred2)
               ]
               [SSNull,SSTok "|~|",SSNull]

fromZPred (prec,l2a) (CExtChoice zPred1 zPred2)
  = Lang "[]" 60
              [ LPred (fromZPred (prec,l2a) zPred1)
              , LPred (fromZPred (prec,l2a) zPred2)
              ]
              [SSNull,SSTok "[]",SSNull]

fromZPred (prec,l2a) (CGuard zPred1 zPred2)
  = Lang "&" 70
             [ LPred (fromZPred (prec,l2a) zPred1)
             , LPred (fromZPred (prec,l2a) zPred2)
             ]
             [SSNull,SSTok "&",SSNull]

fromZPred (prec,l2a) (CHPred pred1 pred2)
  = Papp (fromZPred (prec,l2a) pred1) (fromZPred (prec,l2a) pred2)

fromZPred (prec,l2a) (CPabs zVar zPred) = Ppabs (Q vars) (fromZPred (prec,l2a) zPred)
 where vars = map fromZVar zVar

fromZPred (prec,l2a) (CEabs zVar zPred) = Peabs (Q vars) (fromZPred (prec,l2a) zPred)
 where vars = map fromZVar zVar
fromZPred (prec,l2a) (CIfThenElse pred1 pred2 pred3)
   = If (fromZPred (prec,l2a) pred1) (fromZPred (prec,l2a) pred2) (fromZPred (prec,l2a) pred3)

fromZPred (prec,l2a) (CUniv pred) = Univ 0 (fromZPred (prec,l2a) pred)
fromZPred (prec,l2a) (CSub zPred expl varl)
   = Sub (fromZPred (prec,l2a) zPred) (packlistQV (zip exprlist qlist))
   where qlist = map (fromZVar) varl
         exprlist = map (fromZExpr (prec,l2a)) expl

fromZPred (prec,l2a) (CEqu zpred1 zpred2)
  = Eqv (fromZPred (prec,l2a) zpred1) (fromZPred (prec,l2a) zpred2)

fromZPred (prec,l2a) (CObs e relist)
  = relListHandler (prec,l2a) (fromZExpr (prec,l2a) e) relist
fromZPred (prec,l2a) pred
  = Defd (Eerror ("FromZ.fromZPred - cant translate : ( " ++ show pred ++ " )"))
\end{code}

Function \texttt{relListHandler} turns an expression
and a list of relation/expression pairs into a sort of
linked list using \texttt{Bin}
to hold the operation and the last expression,
or the next expression in the list.
\begin{code}
relListHandler (prec,l2a) e [] = Obs e
relListHandler (prec,l2a) e ((op,next):ax)
  = relListHandler (prec,l2a) (Bin op' 0 e (fromZExpr (prec,l2a) next)) ax
  where
    vn = varKey $ fromZVar op
    op' = if (head vn) == '\\' then drop 1 vn else vn
\end{code}

Function pattern to turn type expressions from Jaza to \Saoithin.
\texttt{CtFreeComp} should only appear, and be
the only type in the list component of a \texttt{CtFree}.
\begin{code}
fromZTExpr (CtBasic (TArb)) = Tarb
fromZTExpr (CtBasic (TEnv)) = Tenv
fromZTExpr (CtBasic (TBool)) = B
fromZTExpr (CtBasic (TInteger)) = Z
fromZTExpr (CtBasic (TVar x)) = Tvar x
fromZTExpr (CtSet zPred) = Tset (fromZTExpr zPred)
fromZTExpr (CtSeq zPred) = Tseq (fromZTExpr zPred)
fromZTExpr (CtProd zTPredList) = Tprod (map fromZTExpr zTPredList)
fromZTExpr (CtFun zPred1 zPred2) = Tfun (fromZTExpr zPred1) (fromZTExpr zPred2)
fromZTExpr (CtMap zPred1 zPred2) = Tmap (fromZTExpr zPred1) (fromZTExpr zPred2)
fromZTExpr (CtFree name blist)	
 = Tfree name (map (\(CtFreeComp zvar lis) -> (showZvar zvar,(map fromZTExpr lis))) blist)
\end{code}

Function pattern to extract names from Jaza's generators and filters.
\begin{code}
getZVarGenFilt (Choose zvar ztexpr) = varKey $ fromZVar zvar
getZVarGenFilt (AltChoose zvar) = varKey $ fromZVar zvar
getZVarGenFilt (Include e) = "GenFlt Include not handled: "++show e
getZVarGenFilt (Check pr) = "GenFlt Check not handled: "++show pr
getZVarGenFilt (Evaluate v e1 e2)
  = "GenFlt Evaluate not Handled: "++show (fromZVar v)
\end{code}

\texttt{ZParas} are the top level constructs returned by the Jaza parser.
This function pattern translates and places the result in a \texttt{ProofContextPart}.
If the argument doesn't have a name, we use the empty
string, and deal with it later.
\begin{code}
fromZPara :: ([Trie (Int,b)],String -> Maybe String)
             -> ProofContextPart -> ZPara -> ProofContextPart

fromZPara (prec,l2a) pcp (ZPredicate p)
 = addPreds pcp ("",fromZPred (prec,l2a) p)

fromZPara (prec,l2a) pcp (CNConst var expr)
  = addConsts pcp (varKey $ fromZVar var, (fromZExpr (prec,l2a) expr))

fromZPara (prec,l2a) pcp (CNExpr var expr)
  = addExprs pcp (varKey $ fromZVar var, (fromZExpr (prec,l2a) expr))

fromZPara (prec,l2a) pcp (ZAbbreviation var expr)
  = addExprs pcp (varKey $ fromZVar var, (fromZExpr (prec,l2a) expr))

fromZPara (prec,l2a) pcp (CNPred var pred)
  = addPreds pcp (varKey $ fromZVar var,fromZPred (prec,l2a) pred)

fromZPara (prec,l2a) pcp (CTypedef name ctype)
  = addTdefs pcp (varKey $ fromZVar name, fromZTExpr ctype)

fromZPara (prec,l2a) pcp (CTypes name ctype)
  = addTypes pcp (varKey $ fromZVar name, fromZTExpr ctype)
\end{code}
The pattern below extracts out the name and number of a \texttt{theoryid}
for a string of the form \verb"{[a-zA-z][a-zA-Z0-9']*}{[0-9]+]}".
\begin{code}
fromZPara (prec,l2a) pcp (CTheory s) = addSeqNo (addName pcp name) num
  where (name',num') = span (\x -> x /= '}') s
        name         = [x | x <- name', x /= '{']
        num''        = [x | x <- num', isDigit x]
        num          = if length num'' > 0 then read num'' else 0

fromZPara (prec,l2a) pcp (CLaw name pred)
  = addLaws pcp (t, ((fromZPred (prec,l2a) pred,SCtrue),FromUSER "@LaTeX",Bnil)) -- FUDGE
  where t = [x | x <- varKey $ fromZVar name, x /= '{', x /='}']

fromZPara (prec,l2a) pcp (CConject name pred)
  = addConjs pcp (varKey $ fromZVar name, (fromZPred (prec,l2a) pred,SCtrue))

fromZPara (prec,l2a) pcp p
  = addPreds pcp ("",(Defd (Eerror ("fromZPara: can't handle (" ++ show p ++ ")"))))
\end{code}

Function \texttt{readZSpec} is the top level function of this module.
It returns either a proof context or a string describing the
error returned from the parser.
\begin{code}
readZSpec params text
  = case (parseZspec ll text) of
      Ok plist                ->  Right (mkctxt plist)
      Fail                    ->  Left "fail"
      Undefined e             ->  Left ("undefined" ++ show e)
      TooBig bigInfo e        ->  Left ("toobig" ++ show bigInfo ++ show e)
      Impossible e            ->  Left ("Impossible" ++ show e)
      IllFormed e             ->  Left ("Illformed" ++ show e)
      SyntaxErrors errorlist  ->  Left (concat (map show errorlist))
  where
    precs = prectable params
    ll = ltxtable params
    l2a = ltx2asc ll
    mkctxt pl = buildPContext
                 (transEP params
                          (foldl (fromZPara (precs, l2a)) nullPCP pl))

readZSpecDebug params text
  = case (parseZspec ll text) of
      Ok plist                ->  Right (map show plist ++ "---":tls)
      Fail                    ->  Left "fail"
      Undefined e             ->  Left ("undefined" ++ show e)
      TooBig bigInfo e        ->  Left ("toobig" ++ show bigInfo ++ show e)
      Impossible e            ->  Left ("Impossible" ++ show e)
      IllFormed e             ->  Left ("Illformed" ++ show e)
      SyntaxErrors errorlist  ->  Left (concat (map show errorlist ++ "---":tls))
  where
    ll = ltxtable params
    toks = zlex (ltx2sym ll) lexstate0 text
    tls = map show toks
\end{code}

Function \texttt{buildPContext}
relies on \texttt{genNames} to turn a \texttt{ProofContextPart}
into a \texttt{Theory}
by building a \texttt{Trie} from lists of name/item pairs.
\begin{code}
buildPContext pcp
 = (buildLangDefinitions . markTheoryDeps)
    (Theory
       (pcpName pcp)
       (pcpSeqNo pcp)
       []
       pTdefs
       pConsts
       pExprs
       pPreds
       pObs
       pPrecs
       tnil
       pTypes
       pLaws
       pConjs
       pThms
       Transient [] tnil)
 where pcp' = genNames pcp

       pTdefs = lbuild $ pcpTdefs pcp'
       pConsts = lbuild $ pcpConsts pcp'
       pExprs = lbuild $ pcpExprs pcp'
       pPreds = lbuild $ pcpPreds pcp'
       pObs = lbuild $ pcpObs pcp'
       pPrecs = lbuild $ pcpPrecs pcp'
       pTypes = lbuild $ pcpTypes pcp'
       pAlphas = lbuild $ pcpAlphas pcp'
       pLaws = pcpLaws pcp'
       pConjs = lbuild $ pcpConjs pcp' -- SIDE-COND fudge (AB, 03/09)
       pThms = map snd $ pcpThms pcp'

       addTrueSC (name,pred) = (name,(pred,SCtrue))  -- SIDE-COND fudge (AB 03/09)

\end{code}
\textbf{The above will all have to be fixed to allows side-conditions be
linked to laws, somehow.}

Functions \texttt{transEP} , \texttt{wrapEx2Pred} and \texttt{obsToPred} pattern match Obs predicates into Papps. This is done
by checking if the variables that exist in structure are the names of predicates that have been parsed or exist in the
proof contexts we were passed.
Function \texttt{transEP} updates the
predicate portion of the \texttt{Contexttable} with the
names of the predicates matched to the trivial predicates
we just parsed.
This is so we can query the table for names.
In this module we're only interested in the names.
\begin{code}

transEP ctable pcp	
  = pcp{pcpPreds = preds'}
  where
   preds = pcpPreds pcp
   preds' = map (\(x,y) -> (x, wrapEx2Pred ctable' y)) preds
   ctable' = ctable{ predtable = ptable}
   ptable = (predtable ctable)
             ++ [ (lbuild (zip (map fst preds) [ TRUE | x <- [1..]])) ]
\end{code}

Function \texttt{wrapEx2Pred} matches the produced predicates that could be the application of one function to another.
\begin{code}
wrapEx2Pred ctable (Obs e ) = obsToPred ctable e
wrapEx2Pred ctable a        = a
\end{code}

Function \texttt{obsToPred} looks up the predicates portion of the \texttt{contexttable}
to determine if the function is a predicate,
and if so then whether the second part is a value or another predicate.
\begin{code}
obsToPred ctable (App func expr)	
 = result
 where
    result = if tslookup (predtable ctable) func == Nothing
              then Obs (App func expr)
              else Papp (Pvar $ Std func) second
    second = case expr of
              T -> TRUE
              F -> FALSE
              Var (_,_,"True") -> TRUE
              Var (_,_,"False") -> FALSE
              Var a -> if tsvlookup (typetable ctable) a /= Nothing
                        then Obs (Var a)
                        else Pvar $ varGenRoot a
              App _ _ -> obsToPred ctable expr
              _ -> Obs expr
obsToPred ctable a = Obs a
\end{code}
%Function \texttt{pcpMerge} turns a list of \texttt{ProofContextPart} in a single one.
%\begin{haskell}
%
%> pcpMerge :: [ProofContextPart] -> ProofContextPart
%> pcpMerge tList
%>   = foldl ( \(a1,a2,a3,a4,a5,a6) (b1,b2,b3,b4,b5,b6)
%>             -> (a1++b1, a2++b2, a3++b3, a4++b4,a5++b5,a6++b6))
%>           ([],[],[],[],[],[]) tList
%
%\end{haskell}

Function \texttt{buildResultString} is a debug function
for producing the text result of a parse.
\begin{code}
buildResultString :: ([Trie (Int,a)],String -> Maybe String) ->  ZSpec ->  String
buildResultString (prec,l2a) plist
 = "buildResultString NYFI"++prnl (pcpPreds pcp)
 where pcp = foldl (fromZPara (prec,l2a)) nullPCP plist
       dis var = (map (toStrLn . show) var)
       prnl var = foldl (++) "" (dis var)

toStrLn = (\x ->  x ++ "\n")
\end{code}

Function \texttt{genNames} numbers all un-named items in the \texttt{Theory}.
\begin{code}
genNames pcp
  = pcp{ pcpTdefs = fixup "_TD" (pcpTdefs pcp)
       , pcpConsts = fixup "_K" (pcpConsts pcp)
       , pcpExprs = fixup "_E" (pcpExprs pcp)
       , pcpPreds = fixup "_P" (pcpPreds pcp)
       , pcpObs = fixup "_O" (pcpObs pcp)
       , pcpPrecs = fixup "_PR" (pcpPrecs pcp)
       , pcpTypes = fixup "_T" (pcpTypes pcp)
       , pcpAlphas = fixup "_A" (pcpAlphas pcp)
       , pcpConjs = fixup "_CJ" (pcpConjs pcp)
       , pcpThms = fixup "_TH" (pcpThms pcp)
       , pcpLaws = fixup "_L" (pcpLaws pcp)
       }
\end{code}

Function \texttt{fixup} names all un-named items
to names of the form ``p$n$'', where $n$ ranges from
1 upwards, and ``p'' is a supplied prefix
\begin{code}

fixup pfx t = tran' ++ canonical
  where (tran, canonical) = partition ((=="").fst) t
        reduced = map snd tran
        tran' = zip (map pshow [1..]) reduced	
        pshow n = pfx ++ reverse (show n)		

\end{code}
Function \texttt{binOrApp} is a function
that determines if a symbol is an operator by using the precedence tables.
\begin{code}

binOrApp :: ([Trie (Int,a)],String -> Maybe String) -> ZVar -> [ZExpr] -> Expr
binOrApp (prec,l2a) operator applist	
  = result
  where
   operator' = fromZVar operator
   symbol = varKey operator'
   -- symbol = if (take 1 operator') == "\\" then (drop 1 operator')
   --                                        else operator'
   transymbol = l2a symbol
   symbol' = case transymbol of
               Nothing       ->  symbol
               (Just trsym)  ->  trsym
   isOperator = isJust (tslookup prec symbol')
   preclevel = fst (fromJust (tslookup prec symbol'))
   tlen = length applist
   result = case ((tlen == 2) && isOperator) of
     True -> Bin symbol' preclevel
                 (fromZExpr (prec,l2a) (head (applist)))
                 (fromZExpr (prec,l2a) (head (tail applist)))
     False -> App symbol' (Prod (map (fromZExpr (prec,l2a)) applist))

-------------------------------------------------------------------------
\end{code}
