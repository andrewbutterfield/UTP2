\section{Import/Export}

\begin{code}
module ImportExport where
import Utilities
import Tables
import Datatypes
import DataText
import Precedences
import Focus
import DSL
import MatchTypes
import FreeBound
import Heuristics
import Manipulation
import Laws
import Proof
import Theories
import Data.Char
import Data.List
import Test.QuickCheck
import Text.ParserCombinators.Parsec.Expr
\end{code}

\subsection{Version Control}

Current Version (changes as \texttt{ImportExport} is revised):
\begin{code}
versionArg = "3.7"
\end{code}
Historical Versions (once defined, these should never change)
\begin{code}
versionProv = "2.3"
\end{code}
0.1, 0.2 --- early versions\\
0.3 --- adding in alpha-substitution\\
0.4 --- adding in ProofContexts\\
0.5 --- adding in Alphabets\\
0.6 --- Proof has undergone several changes (stacks, etc.)
      most notably with the addition of username hashing.
      Also, negative numbers are now handled properly.\\
0.7 --- proofs now saved with contents of special theories.
      Proof loading views these theories as optional
      - prevents this change being a major revision.\\
0.8 --- now load/save 3 or 4-tuple match bindings\\
1.0 --- incompatible changes to Expr and Theory\\
2.0 --- incompatible change to Pred (Lang)\\
2.1 --- added Pset support.\\
2.2 --- side-condition revisions\\
2.3 --- provenance handling \\
3.0 --- proofs that list their context theories \\
3.3 --- various changes, including \texttt{ObsKind} introduction\\
3.4 --- new inference component (InstantLaw)\\
3.5 --- introduction of \texttt{TTag}\\
3.6 --- \texttt{Binding} revision (now 9 \texttt{Trie}s)\\
3.7 --- \texttt{LVar} revision, from Var to GenRoot\\
The version command occurs only at the very start of a file.
Conventionally
the build and version commands end their argument with a newline.
The first number of the version is the major revision and this is important,
at it marks a compatibility region.
This software also can only handle minor versions lower than itself.
\begin{code}
majorVersion,minorVersion :: String -> Int

majorVersion arg = read prefix
 where prefix = getPrefix arg
       getPrefix "" = ""
       getPrefix (c:cs)
         | c == '.'   =  ""
         | otherwise  =  c:(getPrefix cs)

minorVersion arg = read suffix
 where suffix = getSuffix arg
       getSuffix "" = ""
       getSuffix (c:cs)
         | c == '.'   =  cs
         | otherwise  =  getSuffix cs
\end{code}


We use a form of reverse polish notation, were we have a stream
of tokens, each comprising a command-argument pair. At present
we have the following commands:
\begin{description}
  \item[Version] indicates the version in use
  \item[Push] push the argument onto the stack
  \item[Build] build an instance of the argument using the
  appropriate number of stack items (all popped), and push
  result onto stack.
  \item[End] Stop building objects of the current type
  and return stack and remaining text (this has no argument).
\end{description}
\begin{code}
versionCmd = 'v'
versionTok = versionCmd:versionArg
pushCmd    = '^'
buildCmd   = '!'
endCmd     = '.'
\end{code}

All argument are text-strings, interpreted in different ways.
\begin{code}
type IECmd = Char
type IEArg = String
type IECAPair = (IECmd,IEArg)
\end{code}

The stack is a mixture of argument strings and results
of various types:
\begin{code}
data IEelem = Txt String | Count Int | Flag Bool
            | Telem  Type
            | TVelem (String,[Type])
            | OCelem OClass
            | OVelem ObsKind
            | Qelem  QVars
            | SEelem ESubst
            | SPelem PSubst
            | Eelem  Expr
            | Pelem  Pred
            | LEelem LElem
            | SSelem SynSpec
            | SCelem SideCond
            | ASelem Assertion
            | PVelem Provenance
            | LWelem Law
            | RLelem (Rank,Assertion)
            | MTelem MatchType
            | IFelem Inference
            | PRelem ProofRel
            | LTelem LawTable
            | ATelem (Trie Alphabet)
            | KTelem (Trie Type)
            | VTelem (Trie ObsKind)
            | PTelem (Trie Pred)
            | ETelem (Trie Expr)
            | QTelem (Trie QVars)
            | UTelem (Trie Variable)
            | RLTelem (Trie [GenRoot])
            | VLTelem (Trie [Variable])
            | ELTelem (Trie [Expr])
            | TLTelem (Trie [TVar])
            | TSelem TidySpec
            | Belem  Binding
            | Jelem  Justification
            | STelem ProofStep
            | ARelem Argument
            | PCelem ProofCase
            | PSelem ProofSection
            | SGelem Strategy
            | PFelem Proof
            | TTelem [Proof]
            | CTelem (Trie Assertion)
            | THelem Theory
            | ALelem Alphabet
            | OPelem Precs
            | OTelem (Trie Precs)
            | GTelem (Trie LangSpec)
            | PLTelem (Proof,[Theory])
            -- deriving (Eq,Ord,Show)
            deriving Show
type IEStack = [IEelem]

styp (Txt s) = "Str'"++s++"'"
styp (Count i) = "Int."++show i
styp (Flag b) = "Bool."++show b
styp (Telem t) = "Type."++show t
styp (TVelem (n,_)) = "Variant'"++n++"'"
styp (OCelem ocls) = "OClass:"++show ocls
styp (OVelem (_,ocls,_)) = "ObsKind:"++show ocls
styp (Qelem  q) = "QVars("++show q++")"
styp (SEelem _) = "ESubst"
styp (SPelem _) = "PSubst"
styp (Eelem  _) = "Expr"
styp (Pelem  _) = "Pred"
styp (LEelem _) = "LElem"
styp (SSelem _) = "SynSpec"
styp (SCelem _) = "SideCond"
styp (ASelem _) = "Assertion"
styp (PVelem _) = "Provenance"
styp (LWelem _) = "Law"
styp (RLelem _) = "Ranked-Assertion"
styp (MTelem _) = "MatchType"
styp (IFelem _) = "Inference"
styp (PRelem _) = "ProofRel"
styp (LTelem _) = "LawTable"
styp (ATelem _) = "(Trie Alphabet)"
styp (KTelem _) = "(Trie Type)"
styp (VTelem _) = "(Trie ObsKind)"
styp (PTelem _) = "(Trie Pred)"
styp (ETelem _) = "(Trie Expr)"
styp (QTelem _) = "(Trie QVars)"
styp (UTelem _) = "(Trie Variable)"
styp (RLTelem _) = "(Trie [GenRoot])"
styp (VLTelem _) = "(Trie [Variable])"
styp (ELTelem _) = "(Trie [Expr])"
styp (TLTelem _) = "(Trie [Tvar])"
styp (TSelem _) = "TidySpec"
styp (Belem  _) = "Binding"
styp (Jelem  _) = "Justification"
styp (STelem _) = "ProofStep"
styp (ARelem _) = "Argument"
styp (PCelem _) = "ProofCase"
styp (PSelem _) = "ProofSection"
styp (SGelem _) = "Strategy"
styp (PFelem p) = "Proof'"++pname p++"'"
styp (TTelem _) = "[Proof]"
styp (CTelem _) = "(Trie Assertion)"
styp (THelem c) = "Theory'"++thryName c++"'"
styp (ALelem _) = "Alphabet"
styp (OPelem _) = "Precs"
styp (OTelem _) = "(Trie Precs)"
styp (GTelem _) = "(Trie LangSpec)"
styp (PLTelem _) = "(Proof,[Theory])"

-- toptyp = styp . head
toptyp = ('\n':) . (++ "\n") . concat . intersperse "\n:" . map styp . take 5

s5 stk = concat (intersperse "," (map styp (take 5 stk)))
\end{code}

We provide one-character code to identify each of the supported
datatypes:
\begin{code}
charType          = 'T'
charTV            = 'V'
charOC            = 'c'
charOV            = 'o'
charQuant         = 'Q'
charSubstn        = 'S'
charExpr          = 'E'
charPred          = 'P'
charHP            = 'H'
charLE            = '"'
charSS            = '\''
charSC            = 'C'
charAsn           = 'L'
charProv          = 'O'
charLaw           = 'l'
charTrie          = 'M'
charMatchType     = 'm'
charInfer         = 'I'
charTidySpec      = 'r'
charProofRel      = 'R'
charBinding       = 'B'
charJustification = 'j'
charProofStep     = 's'
charCaseType      = 'x'
charArgument      = 'A'
charProofCase     = 'J'
charProofSec      = 'X'
charStrategy      = '?'
charProof         = '!'
charTheory        = '@'
charAlpha         = 'a'
charPrecs         = 'p'
charPLT           = '#'
\end{code}

A command is denoted by a single character,
and is immediately followed by a string argument, terminated by
a single white-space character.

We push text arguments onto the stack:
\begin{code}
getArg :: String -> (String,String)
getArg txt
  = gA "" txt
  where
    gA gra "" = (reverse gra,"")
    gA gra (c:cs)
      | isSpace c  =  (reverse gra,cs)
      | otherwise  =  gA (c:gra) cs

pushArg :: String -> IEStack -> IEStack
pushArg "" stk = (Txt ""):stk
pushArg arg stk
  | arg == "-"  =  (Txt arg):stk
  | isNum       =  (Count n):stk
  | isFlag arg  =  (Flag b):stk
  | otherwise   =  (Txt arg):stk
  where

    (isNum,n) = getNum1 arg
    getNum1 arg@(c:cs)
     | c == '-'   =  getNum negative 0 cs
     | otherwise  =  getNum positive 0 arg
    positive = True
    negative = False
    getNum True n "" = (True,n)
    getNum False n "" = (True,-n)
    getNum sign n (c:cs)
      | isDigit c  =  getNum sign (10*n+digitToInt c) cs
      | otherwise  =  (False,-1)

    isFlag "$F" = True
    isFlag "$T" = True
    isFlag _    = False
    b  =  arg == "$T"
\end{code}

\subsection{Popping the Stack}

We have many ways to pop arguments off the stack,
but we need here to report errors:
\begin{code}
data ImportReport = ImportOK | ImportFail String deriving (Eq,Ord,Show)
\end{code}

(Given a correctly exported file, none of these should ever occur,
but we can't stop
the user from picking a dud file !)

Before we pop stacks, we should have some error combinators handy:
\begin{code}
popNone what
 = (ImportFail msg,error msg,[])
 where msg = "pop-"++what++": empty stack"
popWrong what stk
 = (ImportFail msg,error msg,stk)
 where msg = "pop-"++what++" found "++toptyp stk++" instead."
popFail stk popfn what
  = (ImportFail msg,error msg,stk)
  where msg = popfn
              ++ ": stack top ("
              ++ toptyp stk
              ++ ") not a "
              ++ what
\end{code}

Now a long list of type-sensitive poppers:
\begin{code}
popStr :: IEStack -> (ImportReport,String,IEStack)
popStr [] = popNone "Str"
popStr ((Txt str):stk) = (ImportOK,str,stk)
popStr stk = popWrong "Str" stk

popVar :: IEStack -> (ImportReport,Variable,IEStack)
popVar [] = popNone "Var"
popVar ((Txt txt):stk) = (ImportOK,parseVariable txt,stk)
popVar stk = popWrong "Var" stk

popGR :: IEStack -> (ImportReport,GenRoot,IEStack)
popGR [] = popNone "GenRoot"
popGR ((Txt txt):stk) = (ImportOK,parseGenRoot txt,stk)
popGR stk = popWrong "GenRoot" stk

popVarL :: IEStack -> (ImportReport,Variable,IEStack)
popVarL [] = popNone "Var"
popVarL ((Txt pr):stk) = (ImportOK,parseVariable $ repSbyDollar pr,stk)
popVarL stk = popWrong "Var" stk

-- for old 'xs' that should now be 'x$'
repSbyDollar str
 = case reverse str of
    ('s':cs)  ->  reverse ('$':cs)
    _         ->  str

popNum :: IEStack -> (ImportReport,Int,IEStack)
popNum [] = popNone "popNum"
popNum ((Count n):stk) = (ImportOK,n,stk)
popNum stk = popFail stk "popNum" ("num : "++s5 stk)

popFlag :: IEStack -> (ImportReport,Bool,IEStack)
popFlag [] = popNone "popFlag"
popFlag ((Flag b):stk) = (ImportOK,b,stk)
popFlag stk = popFail stk "popFlag" "flag"

popType :: IEStack -> (ImportReport,Type,IEStack)
popType [] = popNone "popType"
popType ((Telem typ):stk) = (ImportOK,typ,stk)
popType stk = popFail stk "popType" "type"

popTV :: IEStack -> (ImportReport,(String,[Type]),IEStack)
popTV [] = popNone "popTV"
popTV ((TVelem tv):stk) = (ImportOK,tv,stk)
popTV stk = popFail stk "popTV" "type-variant"

popOClass :: IEStack -> (ImportReport,OClass,IEStack)
popOClass [] = popNone "popOClass"
popOClass ((OCelem ocls):stk) = (ImportOK,ocls,stk)
popOClass stk = popFail stk "popOClass" "obs-class"

popOV :: IEStack -> (ImportReport,ObsKind,IEStack)
popOV [] = popNone "popOV"
popOV ((OVelem ov):stk) = (ImportOK,ov,stk)
popOV stk = popFail stk "popOV" "obs-var"

popQVars :: IEStack -> (ImportReport,QVars,IEStack)
popQVars [] = popNone "popQVars"
popQVars ((Qelem qs):stk) = (ImportOK,qs,stk)
popQVars stk = popFail stk "popQVars" "q-var"

popESubst :: IEStack -> (ImportReport,ESubst,IEStack)
popESubst [] = popNone "popESubst"
popESubst ((SEelem sub):stk) = (ImportOK,sub,stk)
popESubst stk = popFail stk "popESubst" "expr-subst"

popPSubst :: IEStack -> (ImportReport,PSubst,IEStack)
popPSubst [] = popNone "popPSubst"
popPSubst ((SPelem sub):stk) = (ImportOK,sub,stk)
popPSubst stk = popFail stk "popPSubst" "pred-subst"

popExpr :: IEStack -> (ImportReport,Expr,IEStack)
popExpr [] = popNone "popExpr"
popExpr ((Eelem ex):stk) = (ImportOK,ex,stk)
popExpr stk = popFail stk "popExpr" "q-var"

popPred :: IEStack -> (ImportReport,Pred,IEStack)
popPred [] = popNone "popPred"
popPred ((Pelem pr):stk) = (ImportOK,pr,stk)
popPred stk = popFail stk "popPred" "predicate"

-- popHP :: IEStack -> (ImportReport,PredSet,IEStack)
-- popHP [] = popNone "popPredSet"
-- popHP ((HPelem pr):stk) = (ImportOK,pr,stk)
-- popHP stk = popFail stk "popPredSet" "predicate-set"

popLE :: IEStack -> (ImportReport,LElem,IEStack)
popLE [] = popNone "popLE"
popLE ((LEelem le):stk) = (ImportOK,le,stk)
popLE stk = popFail stk "popLE" "lang. elem"

popSS :: IEStack -> (ImportReport,SynSpec,IEStack)
popSS [] = popNone "popSS"
popSS ((SSelem ss):stk) = (ImportOK,ss,stk)
popSS stk = popFail stk "popSS" "syntax-spec"

popLS :: IEStack -> (ImportReport,LangSpec,IEStack)
popLS [] = popNone "popLS"
popLS ((Txt str):stk)
  = case parseLangSpec str of
      Left msg     ->  popFail stk ("popLS:invalid lang. spec '"++str++"'")
                                   "lang-spec"
      Right lspec  ->  (ImportOK,lspec,stk)
popLS stk = popFail stk "popLS" "lang-spec"

popSC :: IEStack -> (ImportReport,SideCond,IEStack)
popSC [] = popNone "popSC"
popSC ((SCelem sc):stk) = (ImportOK,sc,stk)
popSC stk = popFail stk "popSC" "side-condition"

popAsn :: IEStack -> (ImportReport,Assertion,IEStack)
popAsn [] = popNone "popAsn"
popAsn ((ASelem asn):stk) = (ImportOK,asn,stk)
popAsn stk = popFail stk "popAsn" "assertion"

popRawAsn :: IEStack -> (ImportReport,Assertion,IEStack)
popRawAsn [] = popNone "popRawAsn"
popRawAsn [x] = popFail [x] "popRawAsn(singleton stack)" "(pred,sc)-pair"
popRawAsn ((SCelem sc):(Pelem pr):stk) = (ImportOK,(pr,sc),stk)
popRawAsn stk = popFail stk "popRawAsn(stack top-2)" "(pred,sc)-pair"

popProv :: IEStack -> (ImportReport,Provenance,IEStack)
popProv [] = popNone "popProv"
popProv ((PVelem prov):stk) = (ImportOK,prov,stk)
popProv stk = popFail stk "popProv" "provenance"

popLaw :: IEStack -> (ImportReport,Law,IEStack)
popLaw [] = popNone "popLaw"
popLaw ((LWelem law):stk) = (ImportOK,law,stk)
popLaw stk = popFail stk "popLaw" "law"

popRawLaw :: IEStack -> (ImportReport,Law,IEStack)
popRawLaw [] = popNone "popRawLaw"
popRawLaw ((PVelem prov):(SCelem sc):(Pelem pr):stk) = (ImportOK,((pr,sc),prov,Bnil),stk)
popRawLaw stk = popFail stk "popLaw(stack top-3)" "law"

popRL :: IEStack -> (ImportReport,(Rank,Assertion),IEStack)
popRL [] = popNone "popRL"
popRL ((RLelem rlaw):stk) = (ImportOK,rlaw,stk)
popRL stk = popFail stk "popRL" "ranked-law"

popLawTable :: IEStack -> (ImportReport,LawTable,IEStack)
popLawTable [] = popNone "popLawTable"
popLawTable ((LTelem lawt):stk) = (ImportOK,lawt,stk)
popLawTable stk = popFail stk "popLawTable" "lawtable"

popMT :: IEStack -> (ImportReport,MatchType,IEStack)
popMT [] = popNone "popMT"
popMT ((MTelem mt):stk) = (ImportOK,mt,stk)
popMT stk = popFail stk "popMT" "match type"

popTS :: IEStack -> (ImportReport,TidySpec,IEStack)
popTS [] = popNone "popTS"
popTS ((TSelem ts):stk) = (ImportOK,ts,stk)
popTS stk = popFail stk "popTS" "tidy-spec"

popIF :: IEStack -> (ImportReport,Inference,IEStack)
popIF [] = popNone "popIF"
popIF ((IFelem ts):stk) = (ImportOK,ts,stk)
popIF stk = popFail stk "popIF" "tidy-spec"

popPR :: IEStack -> (ImportReport,ProofRel,IEStack)
popPR [] = popNone "popPR"
popPR ((PRelem ts):stk) = (ImportOK,ts,stk)
popPR stk = popFail stk "popPR" "tidy-spec"

popB :: IEStack -> (ImportReport,Binding,IEStack)
popB [] = popNone "popB"
popB ((Belem b):stk) = (ImportOK,b,stk)
popB stk = popFail stk "popB" "binding"

popJ :: IEStack -> (ImportReport,Justification,IEStack)
popJ [] = popNone "popJ"
popJ ((Jelem j):stk) = (ImportOK,j,stk)
popJ stk = popFail stk "popJ" "justification"

popST :: IEStack -> (ImportReport,ProofStep,IEStack)
popST [] = popNone "popST"
popST ((STelem st):stk) = (ImportOK,st,stk)
popST stk = popFail stk "popST" "proof step"

popPS :: IEStack -> (ImportReport,ProofSection,IEStack)
popPS [] = popNone "popPS"
popPS ((PSelem ps):stk) = (ImportOK,ps,stk)
popPS stk = popFail stk "popPS" "proof section"

popAR :: IEStack -> (ImportReport,Argument,IEStack)
popAR [] = popNone "popAR"
popAR ((ARelem arg):stk) = (ImportOK,arg,stk)
popAR stk = popFail stk "popAR" "argument"

popPC :: IEStack -> (ImportReport,ProofCase,IEStack)
popPC [] = popNone "popPC"
popPC ((PCelem pc):stk) = (ImportOK,pc,stk)
popPC stk = popFail stk "popPC" "proof case"

popSG :: IEStack -> (ImportReport,Strategy,IEStack)
popSG [] = popNone "popSG"
popSG ((SGelem sg):stk) = (ImportOK,sg,stk)
popSG stk = popFail stk "popSG" "strategy"

popPF :: IEStack -> (ImportReport,Proof,IEStack)
popPF [] = popNone "popPF"
popPF ((PFelem pf):stk) = (ImportOK,pf,stk)
popPF stk = popFail stk "popPF" "proof"

popPX :: IEStack -> (ImportReport,Theory,IEStack)
popPX [] = popNone "popPX"
popPX ((THelem pc):stk) = (ImportOK,pc,stk)
popPX stk = popFail stk "popPX" "proof-context"

popPLT :: IEStack -> (ImportReport,(Proof,[Theory]),IEStack)
popPLT [] = popNone "popPLT"
popPLT ((PLTelem plt):stk) = (ImportOK,plt,stk)
popPLT stk = popFail stk "popPLT" "proof/theory-list pair"

popAL :: IEStack -> (ImportReport,Alphabet,IEStack)
popAL [] = popNone "popAL"
popAL ((ALelem alf):stk) = (ImportOK,alf,stk)
popAL stk = popFail stk "popAL" "alphabet"

popOP :: IEStack -> (ImportReport,Precs,IEStack)
popOP [] = popNone "popOP"
popOP ((OPelem prec):stk) = (ImportOK,prec,stk)
popOP stk = popFail stk "popOP" "precedence"

\end{code}

We need to check a list of import-reports for errors:
\begin{code}
checkreports f [] = (True,error "checkreports found no errors")
checkreports f (ImportOK:rest) = checkreports (f+1) rest
checkreports f (ImportFail _:_) = (False,f)
\end{code}

Aggregates:
\begin{code}

popList pop n stk
 = plist [] n stk
 where
   plist xs 0 stk = (ImportOK,xs,stk)
   plist xs n []  = (ImportFail msg1,error msg1,[])
   plist xs n stk
    | rep==ImportOK  =  plist (x:xs) (n-1) stk'
    | otherwise      =  (rep,error $ msg2 n,stk)
    where (rep,x,stk') = pop stk
   msg1 = "popList: too few stack items"
   msg2 n = "popList: pop failed for item "++show n

popPList :: Int -> IEStack -> (ImportReport,[Pred],IEStack)
popPList n stk
 = plist [] n stk
 where
   plist prs 0 stk = (ImportOK,prs,stk)
   plist prs n []  = (ImportFail msg,error msg,[])
   plist prs n ((Pelem pr):stk) = plist (pr:prs) (n-1) stk
   plist prs n stk = popFail stk "popPList" "predicate"
   msg = "popPList: too few stack items"

popNList pop stk
 = case rep of
     ImportOK  ->  popList pop n stk'
     _         ->  (rep,error "popNList: bad popNum",stk')
 where
   (rep,n,stk') = popNum stk

popAList (popk,popv) n stk
 = palist [] n stk
 where
   palist as 0 stk = (ImportOK,as,stk)
   palist as n []  = (ImportFail msg1,error msg1,[])
   palist as n stk
    | repok      =  palist ((k,v):as) (n-1) stk2
    | otherwise  =  (failure!!f,error $ msg2 n,stk)
    where
     (repv,v,stk1) = popv stk
     (repk,k,stk2) = popk stk1
     failure = [repv,repk]
     (repok,f) = checkreports 0 failure
   msg1 = "popAList: too few stack items"
   msg2 n = "popAList: failure at item " ++ show n

popNAList (popk,popv) stk
 = case rep of
     ImportOK  ->  popAList (popk,popv) n stk'
     _         ->  (rep,error "popNAList: bad popNum",stk')
 where
   (rep,n,stk') = popNum stk


popATrie :: IEStack -> (ImportReport,Trie Alphabet,IEStack)
popATrie [] = popNone "popATrie"
popATrie ((ATelem trie):stk) = (ImportOK,trie,stk)
popATrie stk = popFail stk "popATrie" "alphabet-trie"

popKTrie :: IEStack -> (ImportReport,Trie Type,IEStack)
popKTrie [] = popNone "popKTrie"
popKTrie ((KTelem trie):stk) = (ImportOK,trie,stk)
popKTrie stk = popFail stk "popKTrie" "type-trie"

popVTrie :: IEStack -> (ImportReport,Trie ObsKind,IEStack)
popVTrie [] = popNone "popVTrie"
popVTrie ((VTelem trie):stk) = (ImportOK,trie,stk)
-- legacy to handle old obs tables
popVTrie ((KTelem trie):stk) = (ImportOK,tmap (\t->(predVar "?",Script,t)) trie,stk)
popVTrie stk = popFail stk "popVTrie" "obsvar-trie"

popPTrie :: IEStack -> (ImportReport,Trie Pred,IEStack)
popPTrie [] = popNone "popPTrie"
popPTrie ((PTelem trie):stk) = (ImportOK,trie,stk)
popPTrie stk = popFail stk "popPTrie" "pred-trie"

popETrie :: IEStack -> (ImportReport,Trie Expr,IEStack)
popETrie [] = popNone "popETrie"
popETrie ((ETelem trie):stk) = (ImportOK,trie,stk)
popETrie stk = popFail stk "popETrie" "expr-trie"

popQTrie :: IEStack -> (ImportReport,Trie QVars,IEStack)
popQTrie [] = popNone "popQTrie"
popQTrie ((QTelem trie):stk) = (ImportOK,trie,stk)
popQTrie stk = popFail stk "popQTrie" "qvars-trie"

popUTrie :: IEStack -> (ImportReport,Trie Variable,IEStack)
popUTrie [] = popNone "popUTrie"
popUTrie ((UTelem trie):stk) = (ImportOK,trie,stk)
popUTrie stk = popFail stk "popUTrie" "var-trie"

popRLTrie :: IEStack -> (ImportReport,Trie [GenRoot],IEStack)
popRLTrie [] = popNone "popRLTrie"
popRLTrie ((RLTelem trie):stk) = (ImportOK,trie,stk)
popRLTrie stk = popFail stk "popRLTrie" "[g-root]-trie"

popVLTrie :: IEStack -> (ImportReport,Trie [Variable],IEStack)
popVLTrie [] = popNone "popVLTrie"
popVLTrie ((VLTelem trie):stk) = (ImportOK,trie,stk)
popVLTrie stk = popFail stk "popVLTrie" "[var]-trie"

popELTrie :: IEStack -> (ImportReport,Trie [Expr],IEStack)
popELTrie [] = popNone "popELTrie"
popELTrie ((ELTelem trie):stk) = (ImportOK,trie,stk)
popELTrie stk = popFail stk "popELTrie" "[expr]-trie"

popTLTrie :: IEStack -> (ImportReport,Trie [TVar],IEStack)
popTLTrie [] = popNone "popTLTrie"
popTLTrie ((TLTelem trie):stk) = (ImportOK,trie,stk)
popTLTrie stk = popFail stk "popTLTrie" "[tvar]-trie"

-- theorems are now [Proof], not Trie Proof
popTTrie :: IEStack -> (ImportReport,[Proof],IEStack)
popTTrie [] = popNone "popTTrie"
popTTrie ((TTelem trie):stk) = (ImportOK,trie,stk)
popTTrie stk = popFail stk "popTTrie" "proof-trie"

popLTrie :: IEStack -> (ImportReport,Trie Assertion,IEStack)
popLTrie [] = popNone "popLTrie"
popLTrie ((CTelem trie):stk) = (ImportOK,trie,stk)
popLTrie stk = popFail stk "popLTrie" "law-trie"

popOTrie :: IEStack -> (ImportReport,Trie Precs,IEStack)
popOTrie [] = popNone "popOTrie"
popOTrie ((OTelem trie):stk) = (ImportOK,trie,stk)
popOTrie stk = popFail stk "popOTrie" "precs-trie"

popGTrie :: IEStack -> (ImportReport,Trie LangSpec,IEStack)
popGTrie [] = popNone "popGTrie"
popGTrie ((GTelem trie):stk) = (ImportOK,trie,stk)
popGTrie stk = popFail stk "popGTrie" "lang-spec-trie"


\end{code}

\subsection{String Encoding}

Any argument containing white-space or non-printables
has it entered using `\&' as an escape character,
followed by the character code in decimal and a semicolon.
The escape character itself is rendered as ``\&\&;''
The only things escaped are whitespace, non-printables and the escape character
itself. All other things, including quotes appear `as-is'.
\begin{code}
escChar = '&'
cseChar = ';'

encodeString :: String -> String
encodeString "" = ""
encodeString (c:cs)
 | isSpace c  =  escChar:(show (ord c)) ++ cseChar:encodeString cs
 | c == escChar   =  escChar:(show (ord c)) ++ cseChar:encodeString cs
 | isPrint c  =  c:(encodeString cs)
 | otherwise  =  escChar:(show (ord c)) ++ cseChar:encodeString cs

decodeString :: String -> String
decodeString "" = ""
decodeString (c:cs)
 | c == escChar   =  decodeStringEscape 0 cs
 | otherwise  =  c:(decodeString cs)

decodeStringEscape n ""  =  [chr n]
decodeStringEscape n (c:cs)
 | isDigit c  =  decodeStringEscape (10*n+digitToInt c) cs
 | c == escChar   =  (decodeStringEscape (ord escChar) cs)
 | c == cseChar   =  (chr n):(decodeString cs)
 | otherwise  =  '?':(decodeString cs)

{-
instance Arbitrary Char where
  arbitrary = fmap chr $ elements [0..255]
  coarbitrary c = coarbitrary (ord c)
decode_encode_is_id s = decodeString (encodeString s) == s
-}
\end{code}

We encode any string arguments we write:
\begin{code}
wrArg s = [pushCmd:(encodeString s)]

wrVar = wrArg . varKey
wrRoot = wrArg . rootString
wrGenRoot = wrArg . genRootString
wrTVar = wrArg

wrNum n = wrArg (show (n :: Int))

wrArgs ss = wr 0 ss
 where
   wr n [] = wrNum n
   wr n (s:ss) = wrArg s ++ wr (n+1) ss

wrVars = wrArgs . map varKey

wrFlag True  = wrArg "$T"
wrFlag False = wrArg "$F"
\end{code}

\subsection{Generic Builders}

The following are polymorphic
builders that take a number of stack pop
and type constructor arguments,
and then pop stuff off the stack, build a type
and push the result back on, and then continue
processing using \texttt{importScan}.
\begin{code}
type Pop t = IEStack -> (ImportReport,t,IEStack)
type Builder = IEStack -> [IECAPair] -> (ImportReport,IEStack,[IECAPair])

build :: t -> (t -> IEelem) -> Builder
build item elem stk cmds = importScan (((elem item):stk),cmds)

build1 :: Pop t -> (t -> s)
       -> (s -> IEelem) -> Builder
build1 pop cons elem stk cmds
  | repok  =  importScan (((elem (cons x)):stk'),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where (rep1,x,stk') = pop stk
        failure = [rep1]
        (repok,f) = checkreports 0 failure

build2 :: Pop t -> (t -> t -> s)
       -> (s -> IEelem) -> Builder
build2 pop cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2)):stk''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep2,x2,stk') = pop stk
    (rep1,x1,stk'') = pop stk'
    failure = [rep2,rep1]
    (repok,f) = checkreports 0 failure

build11 :: Pop t -> Pop u -> (u -> t -> s)
        -> (s -> IEelem) -> Builder
build11 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2)):stk''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep2,x2,stk') = pop2 stk
    (rep1,x1,stk'') = pop1 stk'
    failure = [rep2,rep1]
    (repok,f) = checkreports 0 failure


build3 :: Pop t -> (t -> t -> t -> s)
       -> (s -> IEelem) -> Builder
build3 pop cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3)):stk'''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep3,x3,stk') = pop stk
    (rep2,x2,stk'') = pop stk'
    (rep1,x1,stk''') = pop stk''
    failure = [rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build111 :: Pop s -> Pop t -> Pop u -> (u -> t -> s -> v)
         -> (v -> IEelem) -> Builder
build111 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3)):stk3),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep3,x3,stk1) = pop3 stk
    (rep2,x2,stk2) = pop2 stk1
    (rep1,x1,stk3) = pop1 stk2
    failure = [rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build21 :: Pop s -> Pop u -> (u -> s -> s -> v)
        -> (v -> IEelem) -> Builder
build21 pop32 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons y x1 x2)):stk3),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep3,x2,stk1) = pop32 stk
    (rep2,x1,stk2) = pop32 stk1
    (rep1,y,stk3)  = pop1  stk2
    failure = [rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build1111 :: Pop t -> Pop u -> Pop v -> Pop w -> (w -> v -> u -> t -> s)
          -> (s -> IEelem) -> Builder
build1111 pop4 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3 x4)):stk4),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep4,x4,stk1) = pop4 stk
    (rep3,x3,stk2) = pop3 stk1
    (rep2,x2,stk3) = pop2 stk2
    (rep1,x1,stk4) = pop1 stk3
    failure = [rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build211 :: Pop s -> Pop t -> Pop u -> (u -> t -> s -> s -> v)
         -> (v -> IEelem) -> Builder
build211 pop43 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons z y x1 x2)):stk4),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep4,x2,stk1) = pop43 stk
    (rep3,x1,stk2) = pop43 stk1
    (rep2,y,stk3)  = pop2 stk2
    (rep1,z,stk4)  = pop1 stk3
    failure = [rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build11111 pop5 pop4 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3 x4 x5)):stk5),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep5,x5,stk1) = pop5 stk
    (rep4,x4,stk2) = pop4 stk1
    (rep3,x3,stk3) = pop3 stk2
    (rep2,x2,stk4) = pop2 stk3
    (rep1,x1,stk5) = pop1 stk4
    failure = [rep5,rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure


buildn :: Pop t -> ([t] -> s)
       -> (s -> IEelem) -> Builder
buildn pop cons elem stk cmds
  | repok  =  importScan (((elem (cons xs)):stk''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep2,n,stk') = popNum stk
   (rep1,xs,stk'') = popList pop n stk'
   failure = [rep2,rep1]
   (repok,f) = checkreports 0 failure

build1n :: Pop t -> Pop u -> ([u] -> t -> s)
        -> (s -> IEelem) -> Builder
build1n pop1 popn cons elem stk cmds
  | repok  =  importScan (((elem (cons xs y)):stk3),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep3,y,stk1)  = pop1 stk
   (rep2,n,stk2)  = popNum stk1
   (rep1,xs,stk3) = popList popn n stk2
   failure = [rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

buildn1 :: Pop t -> Pop u -> (u -> [t] -> s)
        -> (s -> IEelem) -> Builder
buildn1 popn pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons y xs)):stk3),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep3,n,stk1)  = popNum stk
   (rep2,xs,stk2) = popList popn n stk1
   (rep1,y,stk3)  = pop1 stk2
   failure = [rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

buildnn popn2 popn1 cons elem stk cmds
  | repok  =  importScan (((elem (cons xs rs)):stk4),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep4,n,stk1)  = popNum stk
   (rep3,rs,stk2) = popList popn2 n stk1
   (rep2,m,stk3)  = popNum stk2
   (rep1,xs,stk4) = popList popn1 m stk3
   failure = [rep4,rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

buildnn1 popn3 popn2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons s xs ys)):stk5),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep5,n,stk1)  = popNum stk
   (rep4,ys,stk2) = popList popn3 n stk1
   (rep3,m,stk3)  = popNum stk2
   (rep2,xs,stk4) = popList popn2 m stk3
   (rep1,s,stk5)  = pop1 stk4
   failure = [rep5,rep4,rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

buildnn11 popn4 popn3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons s p xs ys)):stk6),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep6,n,stk1)  = popNum stk
   (rep5,ys,stk2) = popList popn4 n stk1
   (rep4,m,stk3)  = popNum stk2
   (rep3,xs,stk4) = popList popn3 m stk3
   (rep2,p,stk5)  = pop2 stk4
   (rep1,s,stk6)  = pop1 stk5
   failure = [rep6,rep5,rep4,rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure


buildn11 popn pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons z y xs)):stk4),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep4,n,stk1)  = popNum stk
   (rep3,xs,stk2) = popList popn n stk1
   (rep2,y,stk3)  = pop2 stk2
   (rep1,z,stk4)  = pop1 stk3
   failure = [rep4,rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

build11n pop3 pop2 pop1n cons elem stk cmds
  | repok  =  importScan (((elem (cons ys x v)):stk4),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep4,v,stk1) = pop3 stk
   (rep3,x,stk2) = pop2 stk1
   (rep2,n,stk3) = popNum stk2
   (rep1,ys,stk4) = popList pop1n n stk3
   failure = [rep4,rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

build11n1 pop4 pop3 pop2n pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons z ys x v)):stk5),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep5,v,stk1) = pop4 stk
   (rep4,x,stk2) = pop3 stk1
   (rep3,n,stk3) = popNum stk2
   (rep2,ys,stk4) = popList pop2n n stk3
   (rep1,z,stk5) = pop1 stk4
   failure = [rep5,rep4,rep3,rep2,rep1]
   (repok,f) = checkreports 0 failure

build11111111 pop8 pop7 pop6 pop5 pop4 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3 x4 x5 x6 x7 x8)):stk8),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep8,x8,stk1) = pop8 stk
    (rep7,x7,stk2) = pop7 stk1
    (rep6,x6,stk3) = pop6 stk2
    (rep5,x5,stk4) = pop5 stk3
    (rep4,x4,stk5) = pop4 stk4
    (rep3,x3,stk6) = pop3 stk5
    (rep2,x2,stk7) = pop2 stk6
    (rep1,x1,stk8) = pop1 stk7
    failure = [rep8,rep7,rep6,rep5,rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build1n111111 pop8 pop7n pop6 pop5 pop4 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3 x4 x5 x6 ys7 x8)):stk8),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep8,x8,stk1) = pop8 stk
    (rep7n,n,stk2a) = popNum stk1
    (rep7,ys7,stk2) = popList pop7n n stk2a
    (rep6,x6,stk3) = pop6 stk2
    (rep5,x5,stk4) = pop5 stk3
    (rep4,x4,stk5) = pop4 stk4
    (rep3,x3,stk6) = pop3 stk5
    (rep2,x2,stk7) = pop2 stk6
    (rep1,x1,stk8) = pop1 stk7
    failure = [rep8,rep7,rep7n,rep6,rep5,rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build_IX pop9 pop8 pop7 pop6 pop5 pop4 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3 x4 x5 x6 x7 x8 x9 )):stk9),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep9 ,x9 ,stk1) = pop9  stk
    (rep8 ,x8 ,stk2) = pop8  stk1
    (rep7 ,x7 ,stk3) = pop7  stk2
    (rep6 ,x6 ,stk4) = pop6  stk3
    (rep5 ,x5 ,stk5) = pop5  stk4
    (rep4 ,x4 ,stk6) = pop4  stk5
    (rep3 ,x3 ,stk7) = pop3  stk6
    (rep2 ,x2 ,stk8) = pop2  stk7
    (rep1 ,x1 ,stk9) = pop1  stk8
    failure = [rep9,rep8,rep7,rep6,rep5,rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure

build_XIV pop14 pop13 pop12 pop11 pop10 pop9 pop8 pop7 pop6 pop5 pop4 pop3 pop2 pop1 cons elem stk cmds
  | repok  =  importScan (((elem (cons x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)):stk14),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
    (rep14,x14,stk1 ) = pop14 stk
    (rep13,x13,stk2 ) = pop13 stk1
    (rep12,x12,stk3 ) = pop12 stk2
    (rep11,x11,stk4 ) = pop11 stk3
    (rep10,x10,stk5 ) = pop10 stk4
    (rep9 ,x9 ,stk6 ) = pop9  stk5
    (rep8 ,x8 ,stk7 ) = pop8  stk6
    (rep7 ,x7 ,stk8 ) = pop7  stk7
    (rep6 ,x6 ,stk9 ) = pop6  stk8
    (rep5 ,x5 ,stk10) = pop5  stk9
    (rep4 ,x4 ,stk11) = pop4  stk10
    (rep3 ,x3 ,stk12) = pop3  stk11
    (rep2 ,x2 ,stk13) = pop2  stk12
    (rep1 ,x1 ,stk14) = pop1  stk13
    failure = [rep14,rep13,rep12,rep11,rep10,rep9,rep8,rep7,rep6,rep5,rep4,rep3,rep2,rep1]
    (repok,f) = checkreports 0 failure
\end{code}

Numbered lists/tries:
\begin{code}
buildna (popk,popv) cons elem stk cmds
  | repok  =  importScan (((elem $ cons as):stk''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep1,n,stk') = popNum stk
   (rep2,as,stk'') = popAList (popk,popv) n stk'
   failure = [rep2,rep1]
   (repok,f) = checkreports 0 failure

buildnt
  :: (IEStack -> (ImportReport,t,IEStack))
     -> (Trie t -> IEelem)
     -> IEStack
     -> [IECAPair]
     -> (ImportReport,IEStack,[IECAPair])
buildnt pop elem stk cmds
  | repok  =  importScan (((elem $ lupdate tnil as):stk''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep2,n,stk') = popNum stk
   (rep1,as,stk'') = popAList (popStr,pop) n stk'
   failure = [rep2,rep1]
   (repok,f) = checkreports 0 failure

buildnlt
  :: (IEStack -> (ImportReport,t,IEStack))
     -> (Trie [t] -> IEelem)
     -> IEStack
     -> [IECAPair]
     -> (ImportReport,IEStack,[IECAPair])
buildnlt pop elem stk cmds
  | repok  =  importScan (((elem $ lupdate tnil as):stk''),cmds)
  | otherwise = (failure!!f,stk,cmds)
  where
   (rep2,n,stk') = popNum stk
   (rep1,as,stk'') = popAList (popStr,popNList pop) n stk'
   failure = [rep2,rep1]
   (repok,f) = checkreports 0 failure
\end{code}

Alternative builds:
\begin{code}
popAlt :: (IEStack -> (ImportReport,a,IEStack))
          -> (a -> b)
          -> IEStack -> (Bool,b,IEStack)
popAlt pop totype stk
 | repok      =  (repok,totype x,stk')
 | otherwise  =  (repok,error "popAlt failed.",stk)
 where
   (rep,x,stk') = pop stk
   (repok,_) = checkreports 0 [rep]

buildalt [] cons elem stk cmds
 = (ImportFail "builda2: no viable pop alternative",stk,cmds)
buildalt (popf:rest) cons elem stk cmds
 | repok      =  importScan ((elem $ cons $ x):stk',cmds)
 | otherwise  =  buildalt rest cons elem stk cmds
 where
   (repok,x,stk') = popf stk
\end{code}

\subsection{Export}

This is largely data-structure specific.
One generic structure is a Trie mapping code-strings
to functions that manipulate a stack and command-list:
\begin{code}

type BuildMap = Trie Builder
btable0 :: BuildMap
btable0 = tnil

\end{code}

\subsubsection{Types}

\begin{code}

codeType typ = charType:typ

--constructor   build-arg        stack arguments, top first

codeB      = codeType "B"
codeZ      = codeType "Z"
codeTprod  = codeType "P"  -- k ts.n ... ts.1
codeTfun   = codeType "F" -- t2 t1
codeTpfun  = codeType "f" -- t2 t1
codeTmap   = codeType "M" -- t2 t1
codeTset   = codeType "S" -- t
codeTseq   = codeType "L" -- t
codeTseqp  = codeType "l" -- t
codeTApp   = codeType "@" -- n ts.n ... ts.1 nm
codeTfree  = codeType "A" -- n css.n ... css.1 nm
codeTvar   = codeType "v" -- s
codeTenv   = codeType "E"
codeTerror = codeType "?" -- s
codeTarb   = codeType "*"

\end{code}
\begin{code}

buildType typ = [buildCmd:typ]

exportType(B) = buildType codeB
exportType(Z) = buildType codeZ
exportType(TApp n ts) = wrArg n ++ exportList exportType ts ++ buildType codeTApp
exportType(Tfun t1 t2) = exportType t1 ++ exportType t2 ++ buildType codeTfun
exportType(Tfree n css) = wrArg n ++ exportList exportTV css ++ buildType codeTfree
exportType(Tvar s) = wrArg s ++ buildType codeTvar
exportType(Tenv) = buildType codeTenv
exportType(Terror s _) = wrArg s ++ buildType codeTerror
exportType(Tarb) = buildType codeTarb

\end{code}
\begin{code}
btable0'
 = lupdate btable0
     [(codeB,      build  B Telem)
     ,(codeZ,      build  Z Telem)
     ,(codeTfun,   build2 popType Tfun Telem)
     ,(codeTfree,  buildn1 popTV popStr Tfree Telem)
     -- ,(codeTApp,   buildn1 popStr popStr TApp Telem)
     ,(codeTvar,   build1 popStr Tvar Telem)
     ,(codeTenv,   build  Tenv Telem)
     ,(codeTerror, build1 popStr terr Telem)
     ,(codeTarb,   build  Tarb Telem)
     ]
 where terr s = Terror s Tarb
\end{code}


\subsubsection{Type Variants}

\begin{code}
codeVariant tv = charTV:tv

--constructor   build-arg        stack arguments, top first

codeTV  = codeVariant "" -- n t.n ... t.1 c
\end{code}
\begin{code}
buildTV tv = [buildCmd:tv]

exportTV (cons,ts) = wrArg cons ++ exportList exportType ts ++ buildTV codeTV
\end{code}
\begin{code}
btable0''
 = lupdate btable0'
    [ (codeTV    , buildn1  popType popStr  (,) TVelem)
    ]
\end{code}

\subsubsection{Observation Class}
\begin{code}
codeOClass oc = charOC:oc

--constructor   build-arg        stack arguments, top first

codeOCM  = codeOClass "M"
codeOCS  = codeOClass "S"
\end{code}
\begin{code}
buildOC oc = [buildCmd:oc]

exportOClass Model = buildOC codeOCM
exportOClass Script = buildOC codeOCS
\end{code}
\begin{code}
btable0'''
 = lupdate btable0''
    [ (codeOCM, build Model OCelem)
    , (codeOCS, build Script OCelem)
    ]
\end{code}

\subsubsection{Observation Variables}
\begin{code}
codeObsVar ov = charOV:ov

--constructor   build-arg        stack arguments, top first

codeOV   = codeObsVar ""  -- typ ocls
codeOV2  = codeObsVar "2" -- typ ocls var
\end{code}
\begin{code}
buildOV ov = [buildCmd:ov]

exportObsVar (var,ocls,typ)
 = wrVar var ++ exportOClass ocls ++ exportType typ ++ buildOV codeOV2
\end{code}
\begin{code}
btable0''''
 = lupdate btable0'''
    [ (codeOV    , build11  popType popOClass        (,)  oldovelem)
    , (codeOV2   , build111 popType popOClass popVar (,,) OVelem)
    ]
 where oldovelem (ocls,typ) = OVelem (predVar "?",ocls,typ)
\end{code}

\subsubsection{Quantifier Variables}

Although the definition of \texttt{QVars} has been simplified,
we maintain backward compatibility below, hence the apparent
redundancy and mismatches in the code below.
\begin{code}
codeQuant qtype = charQuant:qtype

--constructor   build-arg        stack arguments, top first

codeQvar    = codeQuant "V" -- v
codeQlist   = codeQuant "L" -- vs
codeQqvar   = codeQuant "Q" -- q
codeQqlist  = codeQuant "S" -- q'
codeQqpair  = codeQuant "P" -- q vs
codeVlist   = codeQuant "P" -- vs
\end{code}

\begin{code}
buildQVar qtype = [buildCmd:qtype]

exportVars vs      = wrVars vs ++ buildQVar codeVlist
exportQVars ( vs) = wrVars vs ++ buildQVar codeQlist
\end{code}

\begin{code}
btable1 -- now only 1 uniform variable list.
 = lupdate btable0''''
    [ (codeQlist , buildn  popVar  id  Qelem)
    , (codeVlist , buildn  popVar  id  Qelem)
    , (codeQvar  , build1  popVar  q1 Qelem)
    , (codeQqvar , build1  popVarL q1 Qelem)
    , (codeQqlist, buildn  popVarL id  Qelem)
    , (codeQqpair, buildnn popVarL popVar q2 Qelem)
    ]
 where
  q1 v =  [v]
  q2 rs vs =  (rs++vs)
\end{code}



\subsubsection{Substitutions}

The substitution format was designed for an old version
of the datatype:
\begin{verbatim}
newtype Substn a = Substn (Int,[a],QVars)
\end{verbatim}
Which is why things are so convoluted here.
\begin{code}
codeSubstn stype = charSubstn:stype

--constructor   build-arg        stack arguments, top first

codeTSubst  = codeSubstn "T" -- qv n ts.n ... ts.1
codeESubst  = codeSubstn "E" -- qv n es.n ... es.1
codePSubst  = codeSubstn "P" -- qv n ps.n ... ps.1
\end{code}

\begin{code}
buildSubstn stype = [buildCmd:stype]

exportESubst (Substn sub)
 = exportList exportExpr es ++ exportQVars qv ++ buildSubstn codeESubst
 where
   es = map snd sub
   qv =  (map fst sub)

exportPSubst (Substn sub)
 = exportList exportPred prs ++ exportQVars qv ++ buildSubstn codePSubst
 where
   prs = map snd sub
   qv =  (map (rootVar . Gen . fst) sub)
\end{code}

\begin{code}
btable2
 = lupdate btable1
    [ (codeESubst, build1n popQVars popExpr (mksub id) SEelem)
    , (codePSubst, build1n popQVars popPred (mksub varGenRoot) SPelem)
    ]
 where mksub drop as ( vs) = mkQsubst as $ map drop vs
\end{code}

\subsubsection{Expressions}

\begin{code}
codeExpr etype = charExpr:etype

--constructor   build-arg         stack arguments, top first

codeNum    =  codeExpr "N"   --  i
codeVar    =  codeExpr "V"   --  s
codeApp    =  codeExpr "AP"  --  es s
codeAbs    =  codeExpr "AB"  --  es qs s
codeESub   =  codeExpr "S"   --  sub e
codeEPred  =  codeExpr "P"   --  p
\end{code}

\begin{code}
bExpr etype = [buildCmd:etype]

exportExpr :: Expr -> [String]
exportExpr (Num i)
 = wrNum i
   ++ bExpr codeNum
exportExpr (Var s)
 = wrVar s
   ++ bExpr codeVar
exportExpr (App nm es)
 = wrArg nm
   ++ exportList exportExpr es
   ++ bExpr codeApp
exportExpr (Abs nm _ qs es)
 = wrArg nm
   ++ exportQVars qs
   ++ exportExpr e
   ++ bExpr codeAbs
exportExpr (ESub e sub)
 = exportExpr e
   ++ exportESubst sub
   ++ bExpr codeESub
exportExpr (EPred pr)
 = exportPred pr
   ++ bExpr codeEPred
\end{code}

\begin{code}
btable3
 = lupdate btable2
    [ (codeNum   , build1 popNum Num Eelem )
    , (codeVar   , buildalt [ popAlt popVar id
                            , popAlt popNum (parseVariable . show)
                            ]
                            Var Eelem )
    , (codeApp   , buildn1 popExpr popStr App Eelem )
    , (codeAbs   , buildn11 popExpr popQVars popStr abs Eelem )
    , (codeESub  , build11 popESubst popExpr ESub Eelem )
    , (codeEPred , build1 popPred EPred Eelem )
    ]
 where abs nm qs es = Abs nm 0 qs es
\end{code}

\subsubsection{Polarity}

to be done \ldots

\subsubsection{Contexts}

to be done \ldots

\subsubsection{Predicates}

For predicates we have the following build and stack arguments:
\begin{code}
codePred ptype = charPred:ptype

--constructor   build-arg           stack arguments, top first

codeTRUE    =  codePred "T"   --
codeFALSE   =  codePred "F"   --
codePVar    =  codePred "V"   -- s
codePApp    =  codePred "AP"  -- n prs.n ... prs.1 s
codePAbs    =  codePred "AB"  -- n prs.n .. prs.1 qs s
codeSub     =  codePred "S"   -- sub pr
codePExpr   =  codePred "E"   -- e
codeLang    =  codePred "L"   -- n ss.n m les.m s
codeTypeOf  =  codePred ":"   -- t e
\end{code}

\begin{code}
bPred ptype = [buildCmd:ptype]

exportPred :: Pred -> [String]

exportPred TRUE = bPred codeTRUE
exportPred FALSE = bPred codeFALSE
exportPred (PVar v)
 = wrArg (show v)
   ++ bPred codePVar
exportPred (PApp nm prs)
 = wrArg nm
   ++ exportList exportPred prs
   ++ bPred codePApp
exportPred (PAbs nm  _ qs pr)
 = wrArg nm
   ++ exportQVars qs
   ++ exportList exportPred pr
   ++ bPred codePAbs
exportPred (Sub pr sub)
 = exportPred pr
   ++ exportESubst sub
   ++  bPred codeSub
exportPred (PExpr e)
 = exportExpr e
   ++ bPred codePExpr
exportPred (Lang s p les ss)
  = wrArg s ++ wrNum p
            ++ exportList exportLE les
            ++ exportList exportSS ss
            ++ bPred codeLang
exportPred (TypeOf e t)
 = exportExpr e ++ exportType t
   ++ bPred codeTypeOf
\end{code}

\begin{code}
btable4a
 = lupdate btable3
    [ (codeTRUE   , build TRUE Pelem  )
    , (codeFALSE  , build FALSE Pelem  )
    , (codePExpr  , build1  popExpr PExpr Pelem )
    , (codeTypeOf , build11 popType popExpr TypeOf Pelem )
    , (codePApp   , buildn1  popPred popStr PApp Pelem )
    , (codeLang   , buildnn11 popSS popLE popNum popStr Lang Pelem )
    , (codePAbs   , buildn11 popPred popQVars popStr pabs Pelem )
    , (codeSub    , build11 popESubst popPred Sub Pelem )
    , (codePVar   , build1 popStr  (PVar . parseVariable) Pelem )
    ]
 where pabs nm qs prs = PAbs nm 0 qs prs
\end{code}

\subsubsection{Syntax Specifications}

\begin{code}
codeSS sstype = charSS:sstype

codeSSNull  =  codeSS "0"   --
codeSSTok   =  codeSS "T"   --  s
codeSSSep   =  codeSS "S"   --  s

bSS sstype = [buildCmd:sstype]

exportSS SSNull    = bSS codeSSNull
exportSS (SSTok s)   = wrArg s ++ bSS codeSSTok
exportSS (SSSep s)   = wrArg s ++ bSS codeSSSep

btable4''
 = lupdate btable4a
    [ (codeSSNull , build SSNull SSelem )
    , (codeSSTok  , build1 popStr SSTok SSelem )
    , (codeSSSep  , build1 popStr SSSep SSelem )
    ]
\end{code}

We export language specifications by converting them
to string and pushing those:
\begin{code}
exportLS lspec = wrArg (show lspec)
\end{code}


\subsubsection{Side-Conditions}

\begin{code}
codeSC qtype = charSC:qtype

--constructor   build-arg       stack arguments, top first

codeSCtrue            = codeSC "T"
codeSCisCond          = codeSC "c" -- now obsolete
codeSCisCondP         = codeSC "X" -- pname
codeSCisCondE         = codeSC "Y" -- ename
codeSCnotFreeInP      = codeSC "P" -- pname n qvs.n ... qvs.1
codeSCnotFreeInE      = codeSC "E" -- ename n qvs.n ... qvs.1
codeSCareTheFreeOfP   = codeSC "F" -- pname n qvs.n ... qvs.1
codeSCareTheFreeOfE   = codeSC "f" -- ename n qvs.n ... qvs.1
codeSCcoverTheFreeOfP = codeSC "C" -- pname n qvs.n ... qvs.1
codeSCcoverTheFreeOfE = codeSC "D" -- ename n qvs.n ... qvs.1
codeSCfreshP          = codeSC "N" -- qv
codeSCfreshE          = codeSC "n" -- qv
codeSCAnd             = codeSC "A" -- n scs.n ... scs.1
\end{code}

\begin{code}
bSC sctype = [buildCmd:sctype]

exportSC SCtrue = bSC codeSCtrue

exportSC (SCisCond PredM pname) = wrArg pname ++ bSC codeSCisCondP
exportSC (SCisCond ExprM ename) = wrArg ename ++ bSC codeSCisCondE

exportSC (SCnotFreeIn PredM qvs pname)
      = exportList wrVar qvs ++ wrArg pname ++ bSC codeSCnotFreeInP
exportSC (SCnotFreeIn ExprM qvs ename)
      = exportList wrVar qvs ++ wrArg ename ++ bSC codeSCnotFreeInE

exportSC (SCareTheFreeOf PredM qvs pname)
   = exportList wrVar qvs ++ wrArg pname ++ bSC codeSCareTheFreeOfP
exportSC (SCareTheFreeOf ExprM qvs ename)
   = exportList wrVar qvs ++ wrArg ename ++ bSC codeSCareTheFreeOfE

exportSC (SCcoverTheFreeOf PredM qvs pname)
 = exportList wrVar qvs ++ wrArg pname ++ bSC codeSCcoverTheFreeOfP
exportSC (SCcoverTheFreeOf ExprM qvs ename)
 = exportList wrVar qvs ++ wrArg ename ++ bSC codeSCcoverTheFreeOfE

exportSC (SCfresh PredM qv)  =  wrVar qv ++ bSC codeSCfreshP
exportSC (SCfresh ExprM qv)  =  wrVar qv ++ bSC codeSCfreshE

exportSC (SCAnd scs) = exportList exportSC scs ++ bSC codeSCAnd
\end{code}
\begin{code}

btable5
 = lupdate btable4''
    [ (codeSCtrue            , build                 SCtrue                   SCelem )
    , (codeSCisCond          , build1         popStr (SCisCond PredM)         SCelem )
    , (codeSCisCondP         , build1         popStr (SCisCond PredM)         SCelem )
    , (codeSCisCondE         , build1         popStr (SCisCond ExprM)         SCelem )
    , (codeSCnotFreeInP      , build1n popStr popVar (SCnotFreeIn PredM)      SCelem )
    , (codeSCnotFreeInE      , build1n popStr popVar (SCnotFreeIn ExprM)      SCelem )
    , (codeSCareTheFreeOfP   , build1n popStr popVar (SCareTheFreeOf PredM)   SCelem )
    , (codeSCareTheFreeOfE   , build1n popStr popVar (SCareTheFreeOf ExprM)   SCelem )
    , (codeSCcoverTheFreeOfP , build1n popStr popVar (SCcoverTheFreeOf PredM) SCelem )
    , (codeSCcoverTheFreeOfE , build1n popStr popVar (SCcoverTheFreeOf ExprM) SCelem )
    , (codeSCfreshP          , build1 popVar (SCfresh PredM) SCelem)
    , (codeSCfreshE          , build1 popVar (SCfresh ExprM) SCelem)
    , (codeSCAnd             , buildn  popSC         scand                    SCelem )
    ]
 where
   fresh m [] = SCtrue
   fresh m [v] = SCfresh m v
   fresh m vs = scand $ map (SCfresh m) vs

\end{code}


\subsubsection{Assertions (which were laws)}

\begin{code}
codeA ltype = charAsn:ltype

--constructor   build-arg       stack arguments, top first

codeAsn          = codeA ""  -- sc pr
codeAsnTable     = codeA "M" -- n asn.n k.n ... asn.1 k.1

bA ltype = [buildCmd:ltype]

exportAsnRaw (pr,sc) -- no builder, useful for tables/lists
 = exportPred pr ++ exportSC sc

exportAsn asn = exportAsnRaw asn ++ bA codeAsn

exportLawTableAsAsn :: LawTable -> [String]
exportLawTableAsAsn laws
 = exportAList (wrArg,exportAsnRaw) (mapsnd fst3 laws) ++ bA codeAsnTable

btable6a
 = lupdate btable5
    [ (codeAsn , build11 popSC popPred  (,) ASelem )
    , (codeAsnTable , buildna (popStr,popRawAsn)
                              (map (wrapProv preProv)) LTelem )
    ]
 where preProv = FromUSER ("@PRE@"++versionProv++"@IMPORT")
\end{code}

\subsubsection{Provenance}

\begin{code}
codePV ltype = charProv:ltype

--constructor   build-arg       stack arguments, top first

codeFU = codePV "U"  -- user
codeVP = codePV "P"  -- n pv.n ... pv.1
codeUD = codePV "D"  -- user
codeFS = codePV "S"  -- src


bPV pvtype = [buildCmd:pvtype]

exportPV (FromUSER user) = wrArg user ++ bPV codeFU
exportPV (ViaPROOF pvs) = exportList exportPV pvs ++ bPV codeVP
exportPV (UserDEFN user) = wrArg user ++ bPV codeUD
exportPV (FromSOURCE src) = wrArg src ++ bPV codeFS

btable6b
 = lupdate btable6a
    [ (codeFU , build1 popStr  FromUSER   PVelem )
    , (codeVP , buildn popProv ViaPROOF   PVelem )
    , (codeUD , build1 popStr  UserDEFN   PVelem )
    , (codeFS , build1 popStr  FromSOURCE PVelem )
    ]
\end{code}

\subsubsection{Laws}

\begin{code}
codeL ltype = charLaw:ltype

--constructor   build-arg       stack arguments, top first

codeLaw          = codeL ""  -- prov sc pr
codeLawTable     = codeL "M" -- n lw1.n k.n ... lw.1 k.1

bL ltype = [buildCmd:ltype]

exportLawRaw ((pr,sc),prov,_)  -- no builder, useful for tables/lists
 = exportPred pr ++ exportSC sc  ++ exportPV prov

exportLaw law = exportLawRaw law ++ bL codeLaw

exportLawTable :: LawTable -> [String]
exportLawTable laws
 = exportAList (wrArg,exportLawRaw) laws ++ bL codeLawTable

btable6
 = lupdate btable6b
    [ (codeLaw , build111 popProv popSC popPred mklaw LWelem )
    , (codeLawTable , buildna (popStr,popRawLaw) id LTelem )
    ]
 where mklaw pr sc prv = ((pr,sc),prv,Bnil)
\end{code}

\subsubsection{MatchType}

\begin{code}

codeMType mtype = charMatchType:mtype

--constructor   build-arg        stack arguments, top first

codeAll   = codeMType "al"
codeLEqv  = codeMType "le"
codeREqv  = codeMType "re"
codeAnte  = codeMType "an"
codeCnsq  = codeMType "cn"
codeLCEqv = codeMType "lc"
codeRCEqv = codeMType "rc"
codeTREqv = codeMType "tv"

\end{code}
\begin{code}

bMT mtype = [buildCmd:mtype]

exportMT All  = bMT codeAll
exportMT LEqv = bMT codeLEqv
exportMT REqv = bMT codeREqv
exportMT Ante = bMT codeAnte
exportMT Cnsq = bMT codeCnsq
exportMT LCEqv = bMT codeLCEqv
exportMT RCEqv = bMT codeRCEqv
exportMT TREqv = bMT codeTREqv

\end{code}
\begin{code}

btable7
 = lupdate btable6
    [ (codeAll  , build All   MTelem )
    , (codeLEqv , build LEqv  MTelem )
    , (codeREqv , build REqv  MTelem )
    , (codeAnte , build Ante  MTelem )
    , (codeCnsq , build Cnsq  MTelem )
    , (codeLCEqv, build LCEqv MTelem )
    , (codeRCEqv, build RCEqv MTelem )
    , (codeTREqv, build TREqv MTelem )
    ]

\end{code}

\subsubsection{Tidy-up Specifications}

\begin{code}

codeTS tspec = charTidySpec:tspec

codeTflt = codeTS "A"
codeTsrt = codeTS "C"
codeTrdp = codeTS "I"
codeTsf  = codeTS "N"
codeTall = codeTS "T"

bTS ts = [buildCmd:ts]

exportTS Tflt = bTS codeTflt
exportTS Tsrt = bTS codeTsrt
exportTS Trdp = bTS codeTrdp
exportTS Tsf  = bTS codeTsf
exportTS Tall = bTS codeTall

btable8
 = lupdate btable7
    [ (codeTflt, build Tflt TSelem)
    , (codeTsrt, build Tsrt TSelem)
    , (codeTrdp, build Trdp TSelem)
    , (codeTsf , build Tsf  TSelem)
    , (codeTall, build Tall TSelem)
    ]

\end{code}



\subsubsection{Inferences}

\begin{code}
codeInfer qtype = charInfer:qtype

--constructor   build-arg        stack arguments, top first

codeNamedLaw      = codeInfer "L" -- name mtype
codeNamedLaw2     = codeInfer "l" -- prov name mtype
codeInstantLaw    = codeInfer "I" -- prov name
codeNameReplace   = codeInfer "R"
codeNameFold      = codeInfer "F"
codeRecExpand     = codeInfer "X"
codeISubstitute   = codeInfer "S"
codeAlphaSubs     = codeInfer "a" -- subs
codeITidy         = codeInfer "T" -- ts
codeISimplify     = codeInfer "V"
codeINorm         = codeInfer "N"
codeISplit        = codeInfer "Y" -- n ixs.n ... ixs.1
codeIApply        = codeInfer "A"
codeUName         = codeInfer "U" -- name
codeWitness       = codeInfer "W" -- subs
codeBinderSplit   = codeInfer "B"
codeAssertDefined = codeInfer "D"
codeStripForall   = codeInfer "u"
codePropagateEq   = codeInfer "="

\end{code}

\begin{code}
bIF iftype = [buildCmd:iftype]

exportIF (NamedLaw mtype name prov)
 = exportMT mtype ++ wrArg name ++ exportPV prov ++ bIF codeNamedLaw2
exportIF (InstantLaw name prov)
 = wrArg name ++ exportPV prov ++ bIF codeInstantLaw
exportIF NameReplace    = bIF codeNameReplace
exportIF (NameFold name) = wrArg name ++ bIF codeNameFold
exportIF RecExpand      = bIF codeRecExpand
exportIF ISubstitute    = bIF codeISubstitute
exportIF (AlphaSubs subs) = exportESubst subs ++ bIF codeAlphaSubs
exportIF (ITidy ts)     = exportTS ts ++ bIF codeITidy
exportIF ISimplify      = bIF codeISimplify
exportIF (INorm name)   = wrArg name ++ bIF codeINorm
exportIF (ISplit ixs)   = exportList wrNum ixs ++ bIF codeISplit
exportIF IApply         = bIF codeIApply
exportIF (UName name)   = wrArg name ++ bIF codeUName
exportIF (Witness subs) = exportESubst subs ++ bIF codeWitness
exportIF BinderSplit    = bIF codeBinderSplit
exportIF AssertDefined  = bIF codeAssertDefined
exportIF ForallStrip    = bIF codeStripForall
exportIF PropagateEq    = bIF codePropagateEq
\end{code}
\begin{code}

btable9
 = lupdate btable8
    [ (codeNamedLaw   , build11 popStr popMT unprovNLaw IFelem)
    , (codeNamedLaw2  , build111 popProv popStr popMT NamedLaw IFelem)
    , (codeInstantLaw , build11 popProv popStr InstantLaw IFelem)
    , (codeNameReplace, build NameReplace IFelem)
    , (codeNameFold, build1 popStr NameFold IFelem)
    , (codeRecExpand, build RecExpand IFelem)
    , (codeISubstitute, build ISubstitute IFelem)
    , (codeAlphaSubs, build1 popESubst AlphaSubs IFelem)
    , (codeITidy, build1 popTS ITidy IFelem)
    , (codeISimplify, build ISimplify IFelem)
    , (codeINorm, build1 popStr INorm IFelem)
    , (codeISplit, buildn popNum ISplit IFelem)
    , (codeIApply, build IApply IFelem)
    , (codeUName, build1 popStr UName IFelem)
    , (codeWitness, build1 popESubst Witness IFelem)
    , (codeBinderSplit, build BinderSplit IFelem)
    , (codeAssertDefined, build AssertDefined IFelem)
    , (codeStripForall, build ForallStrip IFelem)
    , (codePropagateEq, build PropagateEq IFelem)
    ]
 where
  unprovNLaw mtyp name = NamedLaw mtyp name (FromUSER "@UNKNOWN")

\end{code}


\subsubsection{Proof Relations}

\begin{code}

codePR prel = charProofRel:prel

codeIMP = codePR "I"
codeEQV = codePR "E"
codePMI = codePR "P"

bPR prtype = [buildCmd:prtype]

exportPR IMP = bPR codeIMP
exportPR EQV = bPR codeEQV
exportPR PMI = bPR codePMI

btable10
 = lupdate btable9
    [ (codeIMP, build IMP PRelem)
    , (codeEQV, build EQV PRelem)
    , (codePMI, build PMI PRelem)
    ]

\end{code}

\subsubsection{Binding}

We have to support backward compatibility,
now that bindings have four components instead of three.
Make that five, and note that the four components
have now each acquired two-subcomponents, with standard and
list variables given their own \texttt{Trie}s.

\begin{code}
codeBnd bnds = charBinding:bnds

codeBinding = codeBnd "" -- qtrie etrie ptrie
codeBinding4 = codeBnd "4" -- qtrie ttrie etrie ptrie
codeBinding9 = codeBnd "9" -- qlist qstd tlist tstd estrie elist estd plist pstd

bB bnd = [buildCmd:bnd]

exportB :: Binding -> [String]
exportB (gpbind,vebind,ttbind)
  =    exportPTrie pstd
    ++ exportRLTrie plist
    ++ exportETrie estd
    ++ exportVLTrie elist
    ++ exportELTrie estrie
    ++ exportKTrie tstd
    ++ exportTLTrie tlist
    ++ exportUTrie qstd
    ++ exportVLTrie qlist
    ++ bB codeBinding9
  where
    pstd = justTO gpbind
    plist = justVSO gpbind
    estd = justTO vebind
    elist = justVSO vebind
    estrie = justTSO vebind
    tstd = justTO ttbind
    tlist = justVSO ttbind
    qstd = justVO vebind
    qlist = tnil -- already in elist

btable11
 = lupdate btable10
    [ (codeBinding, build111 popQTrie popETrie popPTrie mkB3 Belem)
    , (codeBinding4, build1111 popQTrie popKTrie popETrie popPTrie mkB4 Belem)
    , (codeBinding9, build_IX popVLTrie popUTrie
                              popTLTrie popKTrie
                              popELTrie
                              popVLTrie popETrie
                              popRLTrie popPTrie
                              mkB9 Belem)
    ]
 where
   mkB3 :: Trie Pred -> Trie Expr -> Trie QVars -> Binding
   mkB3 p e q = mkB4 p e tnil q
   mkB4 :: Trie Pred -> Trie Expr -> Trie Type -> Trie QVars -> Binding
   mkB4 p e t q
    = mkB9 (lbuild p1) (lbuild pl)
           (lbuild e1) (lbuild el) (lbuild es)
           (lbuild t1) (lbuild tl)
           (lbuild q1) (lbuild ql)
    where
      (p1,pl)    = bsplit (isStdG . parseGenRoot) getGenRootList p
      (e1,el,es) = esplit $ bsplit (isStdV . parseVariable) getExprList e
      (t1,tl)    = bsplit (const True) (const []) t -- Lst vars not supported
      (q1,ql)    = qsplit q
   mkB9 :: Trie Pred     -> Trie [GenRoot]
        -> Trie Expr     -> Trie [Variable]
        -> Trie [Expr]
        -> Trie Type     -> Trie [TVar]
        -> Trie Variable -> Trie [Variable]
        -> Binding
   mkB9 p1 pl e1 el es t1 tl q1 ql
    = ( tmap TO p1 `tmerge` tmap VSO pl
      , tmap TO e1 `tmerge` tmap VSO el
        `tmerge`
        tmap TSO es `tmerge` tmap VO q1 `tmerge` tmap VSO ql
      , tmap TO t1 `tmerge` tmap VSO tl
      )
\end{code}
And now, the legacy splitting:
\begin{code}
   bsplit :: (String -> Bool) -> (t -> [v]) -> Trie t
          -> ([(String,t)],[(String,[v])])
   bsplit isStd getList trie
    = (sngl,mapsnd getList list)
    where (sngl,list) = partition (isStd . fst) $ flattenTrie trie

   getGenRootList (PApp nm prs)
    | nm == n_And  =   getGenRoot' prs
    | nm == n_Or   =  getGenRoot' prs
   getGenRootList _ = []
   getGenRoot' [] = []
   getGenRoot' ((PVar v):prs) = (varGenRoot v):getGenRoot' prs
   getGenRoot' (_:prs) = getGenRoot' prs

   getExprList (App nm es)
    | nm `elem` [n_tuple,n_set,n_seq]  = es
   getExprList _ = []

   qsplit :: Trie QVars -> ([(String,Variable)],[(String,[Variable])])
   qsplit qtrie
    = (mapsnd (thead verr) sngl,list)
    where
      (sngl,list) = partition (isStdV . parseVariable . fst) $ flattenTrie qtrie
      verr = preVar "singleBoundToNothing"

   esplit :: ([(String,Expr)],[(String,[Expr])])
          -> ([(String,Expr)],[(String,[Variable])],[(String,[Expr])])
   esplit (sngl,list)
     = (sngl,mapsnd (map getVar) vslist,eslist)
     where
       (vslist,eslist) = partition (all isVar . snd) list
\end{code}


\subsubsection{Justification}

\begin{code}

codeJ j = charJustification:j

codeJustification = codeJ "" -- bnds infer n fp.n ... fp.1 prel

bJ j = [buildCmd:j]

exportJ :: Justification -> [String]
exportJ (prel,fpath,infer,bnds)
  = exportPR prel
    ++ exportList wrNum fpath
    ++ exportIF infer
    ++ exportB bnds
    ++ bJ codeJustification

btable12
 = lupdate btable11
    [ (codeJustification, build11n1 popB popIF popNum popPR (,,,) Jelem)
    ]

\end{code}

\subsubsection{Proof Step}

\begin{code}
codeST st = charProofStep:st

codeProofStep = codeST "" -- pr just

bST st = [buildCmd:st]

exportST :: ProofStep -> [String]
exportST (just,pred)
  = exportJ just ++ exportPred pred ++ bST codeProofStep

btable13
 = lupdate btable12
    [ (codeProofStep, build11 popPred popJ (,) STelem)
    ]
\end{code}

\subsubsection{Argument}

\texttt{Argument} is now deprecated, and has been replaced
by \texttt{ProofStep}. For backward compatibility for now,
we take a \texttt{ProofStep} value, rather than an \texttt{Argument} one,
and
each \texttt{ProofStep} is wrapped
in a ``\texttt{Justify}'' using \texttt{codeJustify}.
\begin{code}
codeAR arg = charArgument:arg

codeJustify      = codeAR "J" -- ps
codeCaseAnalysis = codeAR "C" -- n pcs.n ... pcs.1 open

bAR arg = [buildCmd:arg]

exportAR :: ProofStep -> [String]
exportAR ps  =  exportST ps ++ bAR codeJustify

btable15
 = lupdate btable13 -- btable14 has gone!
    [ (codeJustify,      build1 popST id STelem)
    --, (codeCaseAnalysis, buildn1 popPC popFlag mkCaseAnalysis ARelem)
    ]
\end{code}

\subsubsection{Proof Case}

\begin{code}
codePC ps = charProofCase:ps

codeProofCase = codePC "" -- psec pr

bPC ps = [buildCmd:ps]

exportPC (pred,psteps,_)
  = exportPred pred ++ exportPS psteps ++ bPC codeProofCase

btable16
 = lupdate btable15
    [ (codeProofCase, build11 popPS popPred mkProofCase PCelem)
    ]
 where mkProofCase pr psec = (pr,psec,[]) -- TheoryStack done later
\end{code}

\subsubsection{Proof Section}

\begin{code}
codePS ps = charProofSec:ps

codeProofSec = codePS "" -- n ps.n ... ps.1 pr

bPS ps = [buildCmd:ps]

exportPS :: ProofSection -> [String]
exportPS (fpr,_,_,psteps)
  = exportPred (clearPFocus fpr) ++ exportList exportAR psteps ++ bPS codeProofSec

btable17
 = lupdate btable16
    [ (codeProofSec, buildn1 popST popPred mkPS PSelem)
    ]
 where mkPS pr psteps = (setPFocus pr,fvClosed,Bnil,psteps)
\end{code}

\subsubsection{Strategy}

\begin{code}

codeSG sg = charStrategy:sg

codeNoStrategy  = codeSG "x" -- ps
codeReduce      = codeSG "R" -- ps
codeLhs2Rhs     = codeSG "l" -- ps
codeRhs2Lhs     = codeSG "r" -- ps
codeRedBoth     = codeSG "B" -- rhs lhs brno
codeLawReduce   = codeSG "W" -- ps sc ln
codeAssume      = codeSG "A" -- sg cnsq

bSG sg = [buildCmd:sg]

exportSG :: Strategy -> [String]
exportSG NoStrategy   = bSG codeNoStrategy
exportSG (Reduce ps)  = exportPS ps ++ bSG codeReduce
exportSG (Lhs2Rhs ps) = exportPS ps ++ bSG codeLhs2Rhs
exportSG (Rhs2Lhs ps) = exportPS ps ++ bSG codeRhs2Lhs
exportSG (RedBoth brno lhs rhs) = wrNum brno ++ exportPS lhs ++ exportPS rhs ++ bSG codeRedBoth
exportSG (LawReduce ln sc ps) = wrArg ln ++ exportSC sc ++ exportPS ps ++  bSG codeLawReduce
exportSG (Assume cnsq strategy) = exportPred cnsq ++ exportSG strategy ++ bSG codeAssume

btable18
 = lupdate btable17
    [ (codeNoStrategy, build NoStrategy  SGelem)
    , (codeReduce , build1 popPS Reduce  SGelem)
    , (codeLhs2Rhs, build1 popPS Lhs2Rhs SGelem)
    , (codeRhs2Lhs, build1 popPS Rhs2Lhs SGelem)
    , (codeRedBoth, build21 popPS popNum RedBoth SGelem)
    , (codeLawReduce, build111 popPS popSC popStr LawReduce SGelem)
    , (codeAssume , build11 popSG popPred Assume SGelem)
    ]

\end{code}

\subsubsection{Proof}

Due to changes in the proof format,
particularly with respect to the use of special proof-local theories (PLT),
there are some strange artifacts in how proofs are saved.
We write out the theory context as a list of names.
We import the list of names and store as such.
The replacement of these names by the corresponding theories
has to be done at a higher level
\begin{code}
codePF pf = charProof:pf
codePLT plt = charPLT:plt

codeProof = codePF "" --  prover ctxt done plan side goal pname thname
codeSPC  = codePLT "" --  n thry.n ... thry.1 proof

bPF pf = [buildCmd:pf]

exportPF prf -- old version, proof only.
  = wrArg (thname prf)
  ++ wrArg (pname prf)
  ++ exportPred (goal prf)
  ++ exportSC (side prf)
  ++ exportSG (plan prf)
  ++ wrFlag (done prf)
  ++ exportList wrArg (map thryName $ context prf)
  ++ wrArg (twiddleup (prover prf))
  ++ bPF codeProof

exportPLT (prf,spcs) -- new version, proof and special theories.
  = exportPF prf ++ exportList exportTH spcs ++ bPF codeSPC

btable18a
 = lupdate btable18
    [ (codeProof, build1n111111 popStr popStr popFlag popSG popSC popPred popStr popStr mkProof PFelem)
    ]
 where
   mkProof thnm prfn gpred gsc pln dn cnms uid
      = Proof thnm prfn gpred gsc pln dn
              [] cnms (twiddledown uid) []

btable19
 = lupdate btable18a
    [ (codeSPC, buildn1 popPX popPF (,) PLTelem)
    ]

twiddleup [] = []
twiddleup [c] = [succ c]
twiddleup (c:d:cs) = (succ d):(succ c):(twiddledown cs)

twiddledown [] = []
twiddledown [c] = [pred c]
twiddledown (c:d:cs) = (pred d):(pred c):(twiddleup cs)
\end{code}


\subsubsection{Theories}

\begin{code}
codeTH px = charTheory:px

codeTheory = codeTH "" --  thms conj laws
                             --  types obs
                             --  preds exprs consts typedefs
                             --  syndeps seqno name

bPX px = [buildCmd:px]

exportTH pc
  = wrArg (thryName pc)
  ++ wrNum (thrySeqNo  pc) --  Int
  ++ exportList wrArg (syntaxDeps pc) -- List of String
  ++ exportKTrie (typedefs pc) --  Trie Type
  ++ exportETrie (consts pc) --  Trie Expr
  ++ exportETrie (exprs   pc) --  Trie Expr
  ++ exportPTrie (preds   pc) --  Trie Pred
  ++ exportVTrie (obs pc) --  Trie ObsKind
  ++ exportOTrie (precs pc) --  Trie Precs
  ++ exportGTrie (lang pc) --  Trie LangSpec
  ++ exportKTrie (types pc) --  Trie Type
  ++ exportLawTable (laws pc) --  LawTable
  ++ exportLTrie (conjectures  pc) --  Trie Assertion
  ++ exportTTrie (theorems pc) -- [Proof]
  ++ bPX codeTheory
  where
    mka prf = (pname prf,prf)

btable19a
 = lupdate btable19
    [ (codeTheory,
       build_XIV popTTrie popLTrie popLawTable
                 popKTrie popGTrie popOTrie popVTrie
                 popPTrie popETrie popETrie popKTrie
                 (popNList popStr) popNum popStr mkPC THelem)
    ]
 where mkPC a b c d e f g h i j k l m n
        = markTheoryDeps
            (Theory a b c
                    d e f g
                    h i j
                    k l m n
                    Transient [] tnil)
\end{code}

\subsubsection{Alphabet}

\begin{code}
codeAL alf = charAlpha:alf

codeAlphabet  = codeAL "" -- v.1 ... v.n n

bAL alf = [buildCmd:alf]

exportAL alpha   = exportList wrArg (trieDom alpha) ++ bSG codeAlphabet

btable19b
 = lupdate btable19a
    [ (codeAlphabet, buildn popStr mkAlpha ALelem)
    ]
\end{code}

\subsubsection{Precedence}

\begin{code}
codeOP pr = charPrecs:pr

codePrecs  = codeOP "" -- a p

bOP prc = [buildCmd:prc]

exportOP (p,AssocNone)   = wrNum p ++ wrNum 0 ++ bOP codePrecs
exportOP (p,AssocLeft)   = wrNum p ++ wrNum 1 ++ bOP codePrecs
exportOP (p,AssocRight)  = wrNum p ++ wrNum 2 ++ bOP codePrecs

btable19c
 = lupdate btable19b
    [ (codePrecs, build2 popNum mkPrecs OPelem)
    ]
 where
    mkPrecs p 0 = (p,AssocNone)
    mkPrecs p 1 = (p,AssocLeft)
    mkPrecs p 2 = (p,AssocRight)
    mkPrecs p _ = (p,AssocNone)
\end{code}


\subsection{Aggregates}

\subsubsection{List}


\begin{code}
exportList export es -- es.1 ... es.n n
 = expLst 0 es
 where
   expLst n [] = wrNum n
   expLst n (e:es) = export e ++ expLst (n+1) es

exportRawPair (exp1,exp2) (x,y) = exp1 x ++ exp2 y   --- x y

exportAList (exp1,exp2) = exportList (exportRawPair (exp1,exp2))  -- x.1 y.1  ... x.n y.n n
\end{code}


\subsubsection{Tries}

\begin{code}
codeTrie ttype = charTrie:ttype

--constructor   build-arg        stack arguments, top first

codeATrie  = codeTrie "A" -- n al.n k.n ... al.1 k.1     (Trie Alphabet)
codeKTrie  = codeTrie "K" -- n ty.n k.n ... ty.1 k.1     (Trie Type)
codeVTrie  = codeTrie "V" -- n ov.n k.n ... ov.1 k.1     (Trie ObsKind)
codePTrie  = codeTrie "P" -- n pr.n k.n ... pr.1 k.1     (Trie Pred)
codeETrie  = codeTrie "E" -- n e.n k.n ... e.1 k.1       (Trie Expr)
codeQTrie  = codeTrie "Q" -- n q.n k.n ... q.1 k.1       (Trie QVars)
codeUTrie  = codeTrie "U" -- n v.n k.n ... v.1 k.1       (Trie Variable)

codeRLTrie  = codeTrie "RL" -- n gs.n k.n ... gs.1 k.1   (Trie [GenRoot])
codeVLTrie  = codeTrie "VL" -- n vs.n k.n ... vs.1 k.1   (Trie [Variable])
codeELTrie  = codeTrie "EL" -- n es.n k.n ... es.1 k.1   (Trie [Expr])
codeTLTrie  = codeTrie "TL" -- n ts.n k.n ... ts.1 k.1   (Trie [Tvar])

codeTTrie  = codeTrie "T" -- n prf.n k.n ... prf.1 k.1   (Trie Proof)
codeLTrie  = codeTrie "L" -- n law.n k.n ... law.1 k.1   (Trie Assertion)
codeOTrie  = codeTrie "O" -- n prec.n k.n ... prec.1 k.1 (Trie Precs)
codeGTrie  = codeTrie "G" -- n ls.n k.n ... ls.1 k.1 (Trie LangSpec as String)
\end{code}

\begin{code}
buildTrie ttype = [buildCmd:ttype]

exportTrie t export trie
 = exportAList (wrArg,export) (flattenTrie trie) ++ buildTrie t

exportListTrie t export trie
 = exportAList (wrArg,exportList export) (flattenTrie trie) ++ buildTrie t

exportATrie = exportTrie codeATrie exportAL
exportKTrie = exportTrie codeKTrie exportType
exportVTrie = exportTrie codeVTrie exportObsVar
exportPTrie = exportTrie codePTrie exportPred
exportETrie = exportTrie codeETrie exportExpr
exportQTrie = exportTrie codeQTrie exportQVars
exportUTrie = exportTrie codeUTrie wrVar

exportRLTrie = exportListTrie codeRLTrie wrGenRoot
exportVLTrie = exportListTrie codeVLTrie wrVar
exportELTrie = exportListTrie codeELTrie exportExpr
exportTLTrie = exportListTrie codeTLTrie wrTVar

exportLTrie = exportTrie codeLTrie exportAsn
exportOTrie = exportTrie codeOTrie exportOP
exportGTrie = exportTrie codeGTrie exportLS

-- since theorems changed from Trie Proof to [Proof]:
exportTTrie thms
 = exportAList (wrArg,exportPF) (map mkA thms) ++ buildTrie codeTTrie
 where mkA prf = (pname prf, prf)
\end{code}

\begin{code}
btable20
 = lupdate btable19c
    [ (codeATrie, buildnt popAL     ATelem)
    , (codeKTrie, buildnt popType   KTelem)
    , (codeVTrie, buildnt popOV     VTelem)
    , (codePTrie, buildnt popPred   PTelem)
    , (codeETrie, buildnt popExpr   ETelem)
    , (codeQTrie, buildnt popQVars  QTelem)
    , (codeUTrie, buildnt popVar    UTelem)

    , (codeRLTrie, buildnlt popGR   RLTelem)
    , (codeVLTrie, buildnlt popVar    VLTelem)
    , (codeELTrie, buildnlt popExpr  ELTelem)
    , (codeTLTrie, buildnlt popStr   TLTelem)

    , (codeTTrie, buildna (popStr,popPF) id thelem)
    , (codeLTrie, buildnt popAsn    CTelem)
    , (codeOTrie, buildnt popOP     OTelem)
    , (codeGTrie, buildnt popLS     GTelem)
    ]
 where thelem = TTelem . map snd         -- now [Proof], not Trie Proof
\end{code}


\subsection{Top-Level}

Builder as a Trie returning the relevant call

\begin{code}

buildTree = btable20

buildIt carg stk cmds
 = case tlookup buildTree carg of
     (Just b) ->  b stk cmds
     Nothing  ->  ( ImportFail
                    (  "importScan failed: bad build code: "
                    ++ (show carg)
                    ++ ", stack(" ++ toptyp stk ++ ")"
                    )
                  , stk,cmds
                  )

\end{code}

\subsubsection{Exporting it all}

We limit the number of tokens per line,
and break after every build command.

\begin{code}

tokLmt = 25

exportIt export x = versionTok ++ '\n':(format 0 (export x))
 where
   format n [] = ""
   format n (tok:rest)
    | n >= tokLmt || head tok == buildCmd  =  tok ++ '\n':(format 0 rest)
    | otherwise                            =  tok ++  ' ':(format (n+1) rest)

dumpQuant     = exportIt exportQVars
dumpESubst    = exportIt exportESubst
dumpExpr      = exportIt exportExpr
dumpPred      = exportIt exportPred
dumpSC        = exportIt exportSC
dumpLaw       = exportIt exportAsn
dumpLawTable  = exportIt exportLawTable
dumpPT        = exportIt exportPTrie
dumpMT        = exportIt exportMT
dumpTS        = exportIt exportTS
dumpIF        = exportIt exportIF
dumpPR        = exportIt exportPR
dumpJ         = exportIt exportJ
dumpST        = exportIt exportST
dumpAR        = exportIt exportAR
dumpPC        = exportIt exportPC
dumpPS        = exportIt exportPS
dumpSG        = exportIt exportSG
dumpPF        = exportIt exportPF
dumpTT        = exportIt exportTTrie
dumpLT        = exportIt exportLTrie
dumpPX        = exportIt exportTH
dumpPLT       = exportIt exportPLT

\end{code}

\subsection{Import}

\subsubsection{Top Level Processing}

\begin{code}

importIt txt = importScan ([],importParse txt)

loadIt pop txt
  = let (rep,stk,rest) = importIt txt
    in  case rep of
          (ImportFail _)  ->  (rep,error "loadIt - import failed")
          ImportOK        ->  let (rep',it,_) = pop stk in (rep',it)

loadQuant    = loadIt popQVars
loadESubst   = loadIt popESubst
loadExpr     = loadIt popExpr
loadPred     = loadIt popPred
loadSC       = loadIt popSC
loadLaw      = loadIt popAsn
loadLawTable = loadIt popLawTable
loadPT       = loadIt popPTrie
loadMT       = loadIt popMT
loadTS       = loadIt popTS
loadIF       = loadIt popIF
loadPR       = loadIt popPR
loadJ        = loadIt popJ
loadST       = loadIt popST
loadAR       = loadIt popAR
loadPC       = loadIt popPC
loadPS       = loadIt popPS
loadSG       = loadIt popSG
loadPF       = loadIt popPF
loadTT       = loadIt popTTrie
loadLT       = loadIt popLTrie
loadPX       = loadIt popPX

loadPLT txt
 = let (rep,stk,rest) = importIt txt
    in  case rep of
          (ImportFail _)  ->  (rep,err "import failed")
          ImportOK
            ->  let (rep',plt',_) = popPLT stk -- try full plt
                 in case rep' of
                  ImportOK  ->  (rep',plt')
                  (ImportFail _)
                    -> let (rep'',prf'',_) = popPF stk -- try proof only
                        in case rep'' of
                          (ImportFail _)  ->  (rep'',err "both 'pop's failed")
                          ImportOK        ->  (rep'',(prf'',[]))
 where
   err msg = error ("loadPLT - "++msg)

\end{code}

\subsubsection{Parsing}

We initially parse input text into a list of command/argument
pairs:
\begin{code}
importParse :: String -> [IECAPair]
importParse "" = []
-- importParse [c] = [] -- ignore last command char (TEST)
importParse (c:cs)
  | isSpace c  =  importParse cs
  | otherwise
      = getArg c "" cs -- c is not a space character
      where
        getArg c gra ""  = [(c,decodeString (reverse gra))]
        getArg c gra (a:as)
         | isSpace a  =  (c,decodeString (reverse gra)):(importParse as)
         | otherwise  =  getArg c (a:gra) as
\end{code}

We then scan the command/argument pairs in conjunction with a stack:
\begin{code}
importScan :: (IEStack,[IECAPair]) -> (ImportReport,IEStack,[IECAPair])
importScan (stk,[])  =  (ImportOK,stk,[])
importScan (stk,cmds@((cmd,arg):rest))
  | cmd == pushCmd     =  importScan ((pushArg arg stk),rest)
  | cmd == buildCmd    =  buildIt arg stk rest
  | cmd == endCmd      =  (ImportOK,stk,rest)
  | cmd == versionCmd  = checkVersion arg (stk,rest)
  | otherwise  =  (ImportFail (msg cmd),stk,cmds)
  where
    msg cmd = "importScan("++versionArg++") failed -- bad command: "++[cmd]
\end{code}

Versions are compatible provided the major version number matches that
with which this instance of \texttt{importScan} was compiled
(i.e. the value of \texttt{versionArg}),
and the minor version number is less than or equal to the compiled one:
\begin{code}
checkVersion arg (stk,cmds)
 | majorVersion arg /= majorVersion versionArg
   = (ImportFail (msg versionArg arg),stk,cmds)
 | minorVersion arg > minorVersion versionArg
   = (ImportFail (msg versionArg arg),stk,cmds)
 | otherwise  =  importScan (stk,cmds)
 where
   msg v a = "importScan("++versionArg++") failed -- incompatible version: "++arg
\end{code}
