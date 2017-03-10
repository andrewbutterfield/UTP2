\section{Document Text Parser}

\begin{code}
{-# LANGUAGE CPP #-}
module DocTextParser where
import Data.Char
import Data.List
import Data.Maybe
import Data.Either

import Tables
import Datatypes
import Precedences
import Focus
import DataText
import Utilities
--import Invariants
import Proof
import Theories
import DSL
import RootTheory
import MatchTypes
import Types

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error
\end{code}


\subsection{Document Structure}

A theory text-document has the following format:

\texttt{
\begin{tabular}{l}
\textit{Name [ Number ]  }
\\ SYNTAXFROM
\\   \textit{Name${}_1$} \textit{Name${}_2$} \ldots \textit{Name${}_n$}
\\ \textit{HEADER${}_1$}
\\\$ \textit{Entry${}_{11}$}
\\\$ \textit{Entry${}_{12}$}
\\\$ \vdots
\\\$ \textit{Entry${}_{1k_1}$}
\\ \textit{HEADER${}_2$}
\\\$ \textit{Entry${}_{21}$}
\\\$ \textit{Entry${}_{22}$}
\\\$ \vdots
\\\$ \textit{Entry${}_{2k_2}$}
\\ \vdots
\\ \textit{HEADER${}_h$}
\\\$ \textit{Entry${}_{h1}$}
\\\$ \textit{Entry${}_{h2}$}
\\\$ \vdots
\\\$ \textit{Entry${}_{hk_h}$}
\end{tabular}
}

The \texttt{\textit{HEADER}} values
and the format of the corresponding \texttt{\emph{Entry}} are as follows:

\texttt{
\begin{tabular}{l}
PRECEDENCES
\\\$	\textit{Symbol} \textit{Number}  \textit{( Left | Right | None )}
\\TYPEDEF
\\\$	\textit{Name} $\hat{}=$ \textit{Type}
\\CONSTDEF
\\\$	\textit{Name} $\hat{}=$ \textit{Expr}
\\EXPRDEF
\\\$	\textit{Name} $\hat{}=$ \textit{Expr}
\\PREDDEF
\\\$	\textit{Name} $\hat{}=$ \textit{Pred}
\\OBSVAR
\\\$	\textit{Name} : \textit{Type}
\\TYPES
\\\$	\textit{Name} : \textit{Type}
\\CONJECTURES
\\\$	\textit{String} :: \textit{Pred} \textit{[} ,- \textit{SideCond ] }
\\LAWS
\\\$  \textit{String} :: \textit{Pred} \textit{[} ,-  \textit{SideCond ] }
\end{tabular}
}

\subsection{Document Concrete Parser}

First, build name and symbol token tables
from DataText pe-stuff:
\begin{code}

peNameToks = mkTokTable TKey  pe_keywords
peSymToks  = mkTokTable TKSym (pe_keysymbols ++ pe_brackets)
             `toverride`
             mkTokTable TName pe_symasnames

teNameToks = mkTokTable TKey  te_keywords
teSymToks  = mkTokTable TKSym te_keysymbols

\end{code}


We address those keywords used in a theory document
\begin{code}

keySYNTAXFROM  = "SYNTAXFROM"
keyPRECEDENCES = "PRECEDENCES"
keyLANGUAGE    = "LANGUAGE"
keyENDSYNTAX   = "ENDSYNTAX"
keyOBSVAR      = "OBSVAR"
keyTYPEDEF     = "TYPEDEF"
keyCONSTDEF    = "CONSTDEF"
keyEXPRDEF     = "EXPRDEF"
keyPREDDEF     = "PREDDEF"
keyTYPES       = "TYPES"
keyCONJECTURES = "CONJECTURES"
keyTHEOREMS    = "THEOREMS"
keyLAWS        = "LAWS"
keyEND         = "END"


sec_keywords
 = [keySYNTAXFROM
   ,keyENDSYNTAX
   ,keyOBSVAR
   ,keyLANGUAGE
   ,keyPRECEDENCES
   ,keyTYPEDEF
   ,keyCONSTDEF
   ,keyEXPRDEF
   ,keyPREDDEF
   ,keyTYPES
   ,keyCONJECTURES
   ,keyTHEOREMS
   ,keyLAWS
   ,keyEND
   ]

secKeywords = sbuild sec_keywords
secNameToks = mkTokTable TKey sec_keywords

[ docreqrs
 , docendsyn
 , docobs
 , doclang
 , docprecs
 , doctypedef
 , docconst
 , docexpr
 , docpred
 , doctypes
 , docconjs
 , doctheorems
 , doclaws
 ] = map keyword sec_keywords

ksymDEFEQ = "^="
ksymIS = "|"
ksymSCSEP = ",-"   -- side-condition separator

symHASTYPE = ":"

sec_keysymbols
 = [ ksymDEFEQ
   , ksymIS
   , ksymSCSEP
   ]

secKeysymbols = sbuild sec_keysymbols
secSymToks = mkTokTable TKSym sec_keysymbols

[ defeq
 , is
 , scsep
 ] = map keysym sec_keysymbols

syn_keywords
 = [
   ]
synKeywords = sbuild syn_keywords
synNameToks = mkTokTable TKey syn_keywords

syn_keysymbols
 = [ ksymIS
   ]
synKeySymbols = sbuild syn_keysymbols
synSymToks = mkTokTable TKSym syn_keysymbols
\end{code}

We define document-level tables
\begin{code}

docKeyWords = secKeywords `tmerge` peKeywords
docKeySyms = secKeysymbols  `tmerge` peKeysymbols


docNameToks = peNameToks `tmerge` secNameToks
docSymToks = peSymToks `tmerge` secSymToks

typeKeyWords = teKeywords `tmerge` secKeywords
typeKeySyms = teKeysymbols `tmerge` secKeysymbols

\end{code}

\subsubsection{Splitting up token sections}
We take the list of tokens and split into sections by
document-section keywords:
\begin{code}

splitTokenSections :: (Trie ()) -> [Token] -> [(String,[Token])]
splitTokenSections keys toks = splitToks [] [] "" toks
 where
   splitToks sces ces name [] = reverse (mkSec name ces sces)
   splitToks sces ces name (tok@(_,TName tnm):toks)
    = case tlookup keys tnm of
       Nothing  ->  splitToks sces (tok:ces) name toks
       (Just _) ->  splitToks (mkSec name ces sces) [] tnm toks
   splitToks sces ces name (tok:toks)
    = splitToks sces (tok:ces) name toks
   mkSec ""   _   sces = sces -- drop unnamed sections
   mkSec _    []  sces = sces -- drop empty sections
   mkSec name ces sces = (name,reverse ces):sces

lookupSection kword [] = []
lookupSection kword ((name,toks):rest)
 | kword == name  =  toks
 | otherwise      =  lookupSection kword rest

\end{code}
Because I can't get Parsec to act the way way it should%
\footnote{Have I ever said how much I hate parser combinators?}%
, I need to split law and conjecture sections on defnsep and
side-cond tokens. We expect entries of the form:
\begin{verbatim}
 name :: pred .
 name :: pred ,- sidecond .
\end{verbatim}
with the trailing \verb"." being optional on the last entry.

\begin{code}

splitPredsWithSideConds :: [Token] -> [([Token],[Token])]
splitPredsWithSideConds toks = splitPWSC [] [] toks
 where
  splitPWSC acc [] []  =  reverse acc
  splitPWSC acc predskot []  =  reverse ((reverse predskot,[]):acc)
  splitPWSC acc predskot ((_,TSep):rest)
    = splitPWSC ((reverse predskot,[]):acc) [] rest
  splitPWSC acc predskot ((_,TKSym ks):rest)
    | ks == ksymSCSEP  = splitPWSC' acc predskot [] rest
  splitPWSC acc predskot (tok:rest) =  splitPWSC acc (tok:predskot) rest


-- Seen (TKSym ksymSCSEP):

  splitPWSC' acc predskot scskot []
     = reverse ((reverse predskot,reverse scskot):acc)
  splitPWSC' acc predskot scskot ((_,TSep):rest)
     = splitPWSC ((reverse predskot,reverse scskot):acc) [] rest
  splitPWSC' acc predskot scskot (tok:rest)
     = splitPWSC' acc predskot (tok:scskot) rest

tpsshow tokps = ' ':(concat (intersperse "\n," (map tpshow tokps)))
tpshow (ptoks,ctoks)
 = "["++tsshow ptoks++" IF "++tsshow ctoks++"]"

\end{code}

\subsection{Parsers for sections of theory document}

First a generic parser for a table entry
\begin{code}

parseEntry pkey plink pthing
 = do skipWhite
      k <- pkey
      plink
      t <- pthing
      return (k, t)

\end{code}
Then a generic parser for  an entire table:
\begin{code}

parseTable pkey plink pthing what
 = do entries <- (parseEntry pkey plink pthing) `sepBy` defnsep
      skipWhite
      optional defnsep
      return entries
   <?> what

\end{code}

\subsubsection{Section Parsers}

\begin{code}

dlang   = parseTable (lexify p_string) is parseLSpec "Language specifications"

dtypdef = parseTable name defeq tepType "Type definitions"

dtypes  = parseTable nameOrKey tcolon tepType "Types"

dobs    = parseTable nameOrKey tcolon tepType "Observation Variables"

dconst ptlt = parseTable name defeq (parseTEP ptlt) "Constants"

dexpr  ptlt = parseTable name defeq (parseTEP ptlt) "Expressions"

dpred  ptlt = parseTable name defeq (parseTEP ptlt) "Predicates"

\end{code}


\subsubsection{Parsing Language Specifications}

\begin{code}

parseLSpec
 = do (TEPname lspec) <- strng
      case parseLangSpec lspec of
        Left msg    ->  fail msg
        Right lspc  -> return lspc

\end{code}


\subsubsection{Parsing Side-Condition Lists}

\begin{code}

parseSCList
 = do sc <- parseSC
      scs <- option [] (try parseSCrest)
      return (sc:scs)
   <?> "side-conds"

parseSCrest
 = do p_thenamesym scKeyAnd
      parseSCList

parseSC
 = (try parseSCtrue)
   <|>
   (try parseSCnotFreeInP)
   <|>
   (try parseSCnotFreeInE)
   <|>
   (try parseSCareTheFreeOfP)
   <|>
   (try parseSCareTheFreeOfE)
   <|>
   (try parseSCcoverTheFreeOfP)
   <|>
   (try parseSCcoverTheFreeOfE)
   <|>
   (try parseSCfreshP)
   <|>
   (try parseSCfreshE)
   <|>
   (try parseSCcondP)
   <|>
   (try parseSCcondE)
   <?> "side-cond"

tepSCnotinP = 1
tepSCnotinE = 2
tepSCfreeP  = 3
tepSCfreeE  = 4
tepSCcoverP = 5
tepSCcoverE = 6
tepSCfreshP = 7
tepSCfreshE = 8
tepSCcondP  = 9
tepSCcondE  = 10

parseSCtrue
 = do p_thename "true"
      return TEPnull

parseSCnotFreeInP
 = do p <- p_name
      p_thenamesym scKeyNFI
      vs <- variable `sepBy` cmma
      return (TEPprod [TEPnum tepSCnotinP,TEPname p,TEPseq vs])

parseSCnotFreeInE
 = do e <- p_name
      p_thenamesym scKeyNfi
      vs <- variable `sepBy` cmma
      return (TEPprod [TEPnum tepSCnotinE,TEPname e,TEPseq vs])

parseSCareTheFreeOfP
 = do p <- p_name
      p_thenamesym scKeyTFO
      vs <- variable `sepBy` cmma
      return (TEPprod [TEPnum tepSCfreeP,TEPname p,TEPseq vs])

parseSCareTheFreeOfE
 = do p <- p_name
      p_thenamesym scKeyTfo
      vs <- variable `sepBy` cmma
      return (TEPprod [TEPnum tepSCfreeE,TEPname p,TEPseq vs])

parseSCcoverTheFreeOfP
 = do p <- p_name
      p_thenamesym scKeyCOV
      vs <- variable `sepBy` cmma
      return (TEPprod [TEPnum tepSCcoverP,TEPname p,TEPseq vs])

parseSCcoverTheFreeOfE
 = do p <- p_name
      p_thenamesym scKeyCov
      vs <- variable `sepBy` cmma
      return (TEPprod [TEPnum tepSCcoverE,TEPname p,TEPseq vs])

parseSCfreshP
 = do p_thename scKeyFRS
      v <- variable
      return (TEPprod [TEPnum tepSCfreshP,v])

parseSCfreshE
 = do p_thename scKeyFrs
      v <- variable
      return (TEPprod [TEPnum tepSCfreshE,v])

parseSCcondP
 = do p_thename scKeyCND
      p <- p_name
      return (TEPprod [TEPnum tepSCcondP,TEPname p])

parseSCcondE
 = do p_thename scKeyCnd
      p <- p_name
      return (TEPprod [TEPnum tepSCcondE,TEPname p])

\end{code}


\subsection{Transforming Predicates}

Given a string like ``P''
or ``/='' we need to lookup the type and predicate tables to see
what kind of entity we have, and,  if lacking entries in those
table, we must adopt a convention to distinguish
differing variables
In order to construct \texttt{PVar}s,
we need to know the relevant free variables,
which shall always be the observation variables
associated with a designated theory.

Hence, the parser is parameterised by the tables
tables of the proof context corresponding to a specified theory,
and those on which it depends.

We have a number of classes of entities: values, types,
expressions, and predicates.
All variables name a member of one of those classes.
We define a type to denote these classes,
useful later on for context-dependent parsing:
\begin{code}
data SynClass = SynValu | SynType | SynExpr | SynPred deriving (Eq,Ord,Show)
\end{code}

We lookup a name in a theory
and return the relevant class:
\begin{code}
blookup :: Theory -> String -> Maybe SynClass
blookup thr name
 | isJust $ tlookup (obs thr) name       =  Just SynValu
 | isJust $ tlookup (precs thr) name     =  Just SynValu
 | isJust $ tlookup (consts thr) name    =  Just SynValu
 | isJust $ tlookup (types thr) name     =  Just SynValu
 | isJust $ tlookup (typedefs thr) name  =  Just SynType
 | isJust $ tlookup (exprs thr) name     =  Just SynExpr
 | isJust $ tlookup (preds thr) name     =  Just SynPred
 | isJust $ tlookup (consts thr) name    =  Just SynValu
 | otherwise                             =  Nothing
\end{code}

When we look up a theory stack, we stop at the first success:
\begin{code}
bslookup name [] = Nothing
bslookup name (thry:thrs)
 = case blookup thry name of
     Nothing  ->  bslookup name thrs
     res      ->  res
\end{code}

We want to add \texttt{QVar}s to the start of a name/syntax-class association list:
\begin{code}
qcat :: [Variable] -> [(Variable,SynClass)] -> [(Variable,SynClass)]
vs `qcat` vss = (map (\v -> (v,SynValu)) (filter isStdV vs)) ++ vss
\end{code}

We are also going to find it useful to have \texttt{Either ParseError}
as an instance of \texttt{Monad}:
\begin{code}
#if __GLASGOW_HASKELL__ < 700
instance Monad (Either ParseError) where
  return x = Right x
  m >>= f
    = case m of
        (Left pe) -> (Left pe)
        (Right x) -> f x
  fail s = Left (newErrorMessage (Message s) (newPos "" 0 0))
#endif
\end{code}


\subsubsection{TEP Conversion}

First, getting a (gen-root) string:
\begin{code}
tep2groot :: TEP -> Either String GenRoot
tep2groot (TEPname nm)         =  Right $ Std nm
tep2groot (TEPvar (Gen g,_,_)) =  Right g
tep2groot tep                  =  Left ("Expected genroot, not "++show tep)
\end{code}

Next, getting a (variable) string:
\begin{code}
tep2var :: TEP -> Either String Variable
tep2var (TEPname nm)  =  Right $ preVar nm
tep2var (TEPvar v)    =  Right v
tep2var tep           =  Left ("Expected variable, not "++show tep)
\end{code}

An important feature is the handling of \texttt{TEPname}s,
whose handling depends on context.

When we encounter a name,
at the predicate/expression level,
we check through the tables and quantifier lists
to see if it is known:
\begin{description}
  \item[is a List-Variable:]
    return as an observation/expression variable;
  \item[is Quantified at a higher level:]
    return the appropriate variable;
  \item[is a known type/expr/pred :]
    return the appropriate variable;
  \item[otherwise: ]
    apply the appropriate defaults:
    \begin{description}
      \item[at predicate level:]
        upper case are predicate variables, lower case are expression variables;
      \item[at expression level:]
         all are expression variables.
    \end{description}
    Expression variables are considered to be \texttt{Var}s
    unless they are `known' as \texttt{Evar}s
\end{description}
The exception are the names ``TRUE'' and ``FALSE''
that always denote the corresponding predicates.

\begin{code}
str2predvar
  :: [Theory]              --  theories : parsing context
  -> [(Variable,SynClass)] --  qvs  :  quantified variables at this level
  -> (String -> Type)      --  thetypeof
  -> Variable              --  v
  -> Either String Pred

str2predvar theories qvs thetypeof v
 | null s        =  fail "Null Name"
 | s == "TRUE"   =  return TRUE
 | s == "FALSE"  =  return FALSE
 | isLstV v      =  return $ buildVar SynValu
 | otherwise
    = case alookup qvs v of
        Just sc -> return (buildVar sc)
        Nothing
         -> case bslookup s theories of
              Just sc -> return (buildVar sc)
              Nothing -> return (if isUpper (head s)
                                  then buildVar SynPred
                                  else buildVar SynValu)
 where
   s = varKey v
   buildVar SynValu = PExpr (Var v)
   buildVar SynExpr = PExpr (Var v)
   buildVar SynPred = PVar v
   buildVar SynType = PVar v -- shouldn't happen
\end{code}


We also need to take a generic TEP expression
and turn it into a Predicate,
or error.
This function (\texttt{tep2pred})
performs semantic processing,
using all the available theories,
and keeping track of quantified variables.
\begin{code}
tep2pred
  :: [Theory] -- parsing context
  -> [(Variable,SynClass)] -- quantified variables at this level
  -> TEP
  -> Either String Pred
tep2pred theories qvs tep = t2p qvs tep
 where
   typof = tslookup (map types theories)
   getlang = tslookup (map lang theories)
   thetypeof s
     = case typof s of
         Nothing   ->  Tarb
         (Just t)  ->  t
\end{code}

\subsubsection{Converting \texttt{TEPnull}}

The null case may now arise!
\begin{code}
   t2p :: [(Variable,SynClass)] -> TEP -> Either String Pred

   t2p qvs (TEPnull)                 = Left "naked null TEP !"

   t2p qvs (TEPperr string) = Right (PExpr (eerror ("PRD:"++string)))
   t2p qvs (TEPeerr string) = Right (PExpr (eerror string))
   t2p qvs (TEPterr string) = Right (PExpr (eerror ("TYP:"++string)))
\end{code}

\subsubsection{Converting \texttt{TEPnum}}

We simply return an ill-typed (numeric) atomic predicate,
which should end up inside a well-typed atomic predicate later on.
\begin{code}
   t2p qvs (TEPnum i) = Right (PExpr (Num i))
\end{code}

\subsubsection{Converting \texttt{TEPname}}


\begin{code}
   t2p qvs (TEPname s) = str2predvar theories qvs thetypeof $ preVar s
\end{code}

\subsubsection{Converting \texttt{TEPvar}}


\begin{code}
   t2p qvs (TEPvar v) = str2predvar theories qvs thetypeof v
\end{code}

\subsubsection{Converting \texttt{TEPprefix}}

\begin{code}
   t2p qvs (TEPprefix tep1 tep2)
    = do f <- t2p qvs tep1
         a <- t2p qvs tep2
         return (apply2p f a)
\end{code}

\subsubsection{Converting \texttt{TEPfactor}}

We accept factor lists of the following forms:
\begin{eqnarray*}
 (\texttt{TName}~\mbox{``DEFD''}) ~ tep
\\
 tep_1 ~ (\texttt{TEPtype}~tep_2)
 && \mbox{expr type}
\\
 tep_1 \ldots tep_{k-1}
 ~tep_k~
 \underbrace{tep_{k+1} \ldots tep_n}_{\texttt{TEPsub ksymESUB}}
 && n \geq 1, 1 \leq k \leq n
\end{eqnarray*}
We split the factor list into two components,
with the first being reversed (see \texttt{factor2p} for why).
\begin{code}
   t2p qvs (TEPfactor [])
    = return (perror "Empty-Predicate")

   t2p qvs (TEPfactor [tep]) = t2p qvs tep

   t2p qvs (TEPfactor [TEPname defd,tep])
    | defd == keyDEFD
        = do e <- tep2expr theories qvs tep
             return (mkDefd e)

   t2p qvs (TEPfactor [tepe,TEPtype tept])
    = do e <- tep2expr theories qvs tepe
         t <- tep2type theories tept
         return (TypeOf e t)

   t2p qvs (TEPfactor teps)
    = do let res = fsplit [] teps
         case res of
           Left msg -> return (perror msg)
           Right ([],subt) -> return (perror ("Naked-Substitutions:"++show subt))
           Right (terp,subt)
            -> factor2p qvs terp subt
    where

      fsplit terp [] = Right (terp,[])
      fsplit terp (sub@(TEPsub sep _ _):rest)
       | sep == ksymESUB  =  fsplit' terp [sub] rest
      fsplit terp (tep:rest) = fsplit (tep:terp) rest

      fsplit' terp tbus [] = Right (terp,reverse tbus)
      fsplit' terp tbus (sub@(TEPsub sep _ _):rest)
        | sep == ksymESUB  =  fsplit' terp (sub:tbus) rest
      fsplit' terp tbus (tep:_)
        = Left ("Substitution followed by "++show tep)
\end{code}

\subsubsection{Converting \texttt{TEPinfix}}

\begin{code}
   t2p qvs (TEPinfix p opname tep1 tep2)
    = case getlang opname of

        Just ls@(LangSpec [ltep1,ltep2] ss)
         -> do le1 <- letep2le qvs ltep1 tep1
               le2 <- letep2le qvs ltep2 tep2
               -- return $ Lang opname p [le1,le2] ss
               return $ mkBinLang ls p le1 le2

        _ -> do p1 <- t2p qvs tep1
                p2 <- t2p qvs tep2
                case typof opname of
                 Just optype  ->   buildOp optype p1 p2
                 Nothing
                   -> buildOp (Terror ("Operator '"++opname++"' has no known type") Tarb) p1 p2
    where

      buildOp optyp p1 p2
        | optyp == tBoolBinOp  =  buildPredOp p1 p2
        | isbin                =  buildExprOp ((lat,rat),rst) p1 p2
        | otherwise            =  buildPredOp p1 p2
        where
          (isbin,lat,rat,rst) = isBinOp optyp
          isBinOp (Tfun (TApp tcn [t1,t2]) t3)
           | tcn==n_Tprod     = (True,t1,t2,t3)
          isBinOp t           = (False,t,t,t)

      buildPredOp p1 p2
        | opname == andName    =  return (p1 /\ p2)
        | opname == orName     =  return (p1 \/ p2)
        | opname == ndcName    =  return (mkNDC p1 p2)
        | opname == impName    =  return (p1 ==> p2)
        | opname == rbyName    =  return (mkRfdBy p1 p2)
        | opname == compName   =  return (p1 >>> p2)
        | opname == equivName  =  return (p1 === p2)
        -- | opname == psinName   =  return (mkPsin p1 p2)
        | otherwise            =  return (mklang opname p1 p2)

      buildExprOp ((lat,rat),rst) (PExpr e1) (PExpr e2) -- we expect both arguments to be PExpr
        | opname == "="  =  return (PExpr (mkEqual e1 e2)) -- assuming lat=rat
        | otherwise      =  return (PExpr (mkBin opname p e1 e2))
      buildExprOp optyp p1 p2  = return (mklang opname p1 p2)

      mklang op p1 p2 = Lang op p [LPred p1, LPred p2] [SSNull,SSTok op,SSNull]

      -- mkPsin pr (Psapp (PVar (Std "_")) pset) = Psin pr pset
      -- mkPsin pr pq = Psin pr (PSet [pq])
\end{code}

\subsubsection{Converting \texttt{TEPpostifx}}

\begin{code}
   t2p qvs (TEPpostfix tep1 tep2)
    = do f <- t2p qvs tep2
         a <- t2p qvs tep1
         return (apply2p f a)
\end{code}

\subsubsection{Converting \texttt{TEPbind}}

\begin{code}
   t2p qvs (TEPbind q dcls rtep btep)
    | q == keyFORALL             =  bldLQ mkForall mkImp dcls' rtep btep
    | q == keyEXISTS             =  bldLQ mkExists and2 dcls' rtep btep
    | q == keyEXISTS1            =  bldLQ mkExists1 and2 dcls' rtep btep
    | q == keyTHE && just1 dcls  =  bldTHE (head dcls) rtep btep
    -- | q == ksymPEABS  && nor     =  bldMQ Peabs   dcls btep
    -- | q == keyPFORALL && nor     =  bldMQ Pforall dcls' btep
    -- | q == keyPEXISTS && nor     =  bldMQ Pexists dcls' btep
    -- | q == ksymPPABS  && nor     =  bldMQ Ppabs   dcls btep
    -- | q == ksymEABS   && nor     =  bldEQ Eabs dcls btep
    | otherwise                  =  Left ("t2p bind---unknown quantifier: "++q)
    where

     dcls' = lnorm dcls
     nor   =  rtep == TEPnull
     just1 [_]  =  True
     just1 _    =  False

     and2 r p = mkAnd [r,p]

     bldLQ quant f dcls rtep btep
      | rtep == TEPnull = do let qvs' = dcls `qcat` qvs
                             p <- t2p qvs' btep -- predicate
                             return (quant ( dcls) p)
      | otherwise       = do let qvs' = dcls `qcat` qvs
                             r <- t2p qvs' rtep -- range
                             p <- t2p qvs' btep -- predicate
                             return (quant ( dcls) (f r p))

     bldTHE v rtep btep
      | rtep == TEPnull = do p <- t2p ([v] `qcat` qvs) btep -- predicate
                             return $ PExpr $ mkThe v p
      | otherwise       = do let qvs' = [v] `qcat` qvs
                             r <- t2p qvs' rtep -- range
                             p <- t2p qvs' btep -- predicate
                             return $ PExpr $ mkThe v (and2 r p)

     bldMQ quant dcls btep
       = do let qvs' = dcls `qcat` qvs
            p <- t2p qvs' btep -- predicate
            return (quant ( dcls) p)

     bldHQ quant dcls btep
       = do p <- t2p qvs btep
            return (quant dcls p)

     bldEQ quant dcls btep
      = do let qvs' = dcls `qcat` qvs
           e <- tep2expr theories qvs' btep
           return (PExpr (quant 0 ( dcls) e))
\end{code}

\subsubsection{Converting \texttt{TEPuniv}}

\begin{code}
   t2p qvs (TEPuniv tep)
    = do p <- t2p qvs tep
         return (mkUniv p)
\end{code}

\subsubsection{Converting \texttt{TEPcond}}

\begin{code}
   t2p qvs (TEPcond t c f)
    = do cond <- t2p qvs c
         pred1 <- t2p qvs t
         pred2 <- t2p qvs f
         return (mkIf cond pred1 pred2)
\end{code}

\subsubsection{Converting \texttt{TEPcomp}}

\begin{code}
   t2p qvs (TEPcomp tep1 tep2)
    = do p <- t2p qvs tep1
         q <- t2p qvs tep2
         return (p >>> q)
\end{code}

\subsubsection{Converting \texttt{TEPsub}}

\begin{code}
   t2p qvs (TEPsub sep repl repld)
    | lr /= lrd
       = fail ("bad substition: repl/target lists of different lengths")
    | otherwise
       = do rs <- mapM (t2p qvs) repl
            t2sub sep rs repld
    where
     lr = length repl
     lrd = length repld
     t2sub sep rs repld
      | sep == ksymESUB = do let es = map p2e rs
                             let sub = Substn $ zip repld es
                             return (Sub (PVar $ parseVariable "_") sub)
      -- | sep == ksymPSUB = do let sub = Substn $ zip (map varGenRoot repld) rs
      --                        return (Psub (PVar $ Std "") sub)
      | otherwise       = fail ("t2p:substition - unknown sep '"++sep++"'.")
\end{code}

\subsubsection{Converting \texttt{TEPlang}}

For the rest, they stay as language constructs:
\begin{code}
   t2p qvs (TEPlang nm teples ss)
    = do les <- t2les qvs teples
         return (Lang nm precMidLang les ss)
\end{code}

\subsubsection{Converting \texttt{TEPtype}}
\begin{code}
   t2p qvs (TEPtype _)
    = Left ("Type assertion without expression")
\end{code}

\subsubsection{Converting \texttt{TEPpset},\texttt{TEPpsetc}}
\begin{code}
   t2p qvs (TEPpset teps)
    = do prs <- mapM (t2p qvs) teps
         --return (Psapp (PVar $ Std "_") (PSet prs))
         fail "t2p pset - not supported"
   t2p qvs (TEPpsetc ns tep1 tep2)
    = do pr1 <- t2p qvs tep1
         pr2 <- t2p qvs tep2
         -- return (Psapp (PVar $ Std "_") (PSetC ( $ map predVar ns) pr1 pr2))
         fail "t2p setc -- not supported"
\end{code}

\subsubsection{Converting other TEPs}

If we have exhausted the options above,
then we must have some form of (atomic) expression.

\begin{code}
   t2p qvs tep = do e <- tep2expr theories qvs tep
                    p <- Right (PExpr e)
                    return p
-- end tep2pred
\end{code}


\newpage
\subsubsection{Converting Factors}

A valid predicate factor has the form $Pred^+[PSet]~Subs^*$,
whilst a valid expression factor has one of the
forms  $Name~Subs^*$ or $Name~Expr~Subs^*$.
We split (\texttt{fsplit}) the list into
pre-substitutions (\texttt{serp}, reversed)
and substitutions (\texttt{subs}).


We have a factor list of the following form:
\begin{eqnarray*}
 tep_1 \ldots tep_{k-1}
 ~tep_k~
 \overbrace{tep_{k+1} \ldots tep_n}^{\texttt{TEPsub}}
 && n \geq 1, 1 \leq k \leq n
\end{eqnarray*}
\begin{enumerate}
  \item
    We use \texttt{qvs} to convert $tep_1 \ldots tep_{k-1}$
    to $p_1 \ldots p_{k-1}$ respectively.
  \item
    Starting with \texttt{qvs} and $tep_n$ we produce $s_n$,
    and then extend \texttt{qvs} with those variables in $s_n$
    and use that to convert $tep_{n-1}$, and so on downto $tep_{k+1}$
  \item
    We use the final \texttt{qvs} value obtained from all the $s_{k+1}\ldots s_n$
    to convert $tep_k$ to $p_k$.
\end{enumerate}
We want to build an expression of the form:
\\
\begin{tikzpicture}
  \matrix [matrix of math nodes,column sep=1cm,row sep=0.5cm]
  {
             &           &           & |(A)| \at   \\
             &           & |(B)| \at &               &           &              & |(C)| /\!\!/               \\
             & |(D)| \at &           & |(E)| p_{k-1} &           & |(F)| /\!\!/ &               & |(G)| s_n  \\
   |(H)| p_1 &           & |(I)|p_2  &               & |(J)| p_k &              & |(K)| s_{k+1}              \\
  } ;
  \draw [->]        (A) -- (B);
  \draw [->]        (A) -- (C);
  \draw [->,dotted] (B) -- (D);
  \draw [->]        (B) -- (E) ;
  \draw [->]        (C) -- (G) ;
  \draw [->,dotted] (C) -- (F) ;
  \draw [->]        (D) -- (H);
  \draw [->]        (D) -- (I);
  \draw [->]        (F) -- (J);
  \draw [->]        (F) -- (K);
\end{tikzpicture}
\\
where $\at$ and $/\!\!/$ are \texttt{Papp} and \texttt{Sub}
nodes respectively. In effect we capture the fact that
(post-)substitution binds more tightly than (prefix) functional
application. We then post-process to convert to Expression
forms, where possible.

In addition to to splitting, we need to bind applications
of logical negation (\texttt{bindNot}) tightly,
this best being done to the reversed pre-substitution list
(giving a reversed predicate list \texttt{sperp}).
\begin{code}
   factor2p qvs terp tsub
    = do
        sperp <- mapM (t2p qvs) terp
        let (prmid:sperp') = bindNot sperp
        (subs,qvs') <- subt2subs qvs tsub
        let prmid' = foldl mksub prmid subs
        return $ forceExpr $ foldl1 mkPapp (prmid':sperp')

   subt2subs qvs [] = return ([],qvs)
   subt2subs qvs (subt:subts)
     = do (subs',qvs') <- subt2subs qvs subts
          sub'' <- getsub (t2p qvs' subt)
          return (sub'':subs',mkSubQ sub'' `qcat` qvs)
     where
       getsub (Right (Sub _ sub@(Substn _))) = Right sub
       getsub (Left msg) = Left msg
       getsub x = Left ("factor2p - not a substitution : " ++ show x)

   -- NOT NOW?
   --mksub (PExpr e) sub  =  PExpr Tarb (Esub e sub)
   mksub pr        sub  =  Sub pr sub
\end{code}


\newpage
\subsubsection{Converting Language Elements}

\begin{code}
   t2les qvs les = mapM (t2le qvs) les

   t2le qvs (what,TEPllist teps)
    | what' == lslVar   =  wrap LList LVar tep2groot teps
    | what' == lslType  =  wrap LList LType (tep2type theories) teps
    | what' == lslExpr  =  wrap LList LExpr (tep2expr theories qvs) teps
    | what' == lslPred  =  wrap LList LPred (t2p qvs) teps
    | what' == lscVar   =  wrap LCount LVar tep2groot teps
    | what' == lscType  =  wrap LCount LType (tep2type theories) teps
    | what' == lscExpr  =  wrap LCount LExpr (tep2expr theories qvs) teps
    | what' == lscPred  =  wrap LCount LPred (t2p qvs) teps
    where
      what' = take 2 what
      wrap lst elm p teps = fmap lst (sequence (map (fmap elm . p) teps))
   t2le qvs (what,tep)
    | what == lsVar   =  fmap LVar (tep2groot tep)
    | what == lsType  =  fmap LType (tep2type theories tep)
    | what == lsExpr  =  fmap LExpr (tep2expr theories qvs tep)
    | what == lsPred  =  fmap LPred (t2p qvs tep)
    | otherwise = return $ LVar $ Std ("t2le "++what++" MISMATCH")

   letep2le qvs (LVar _) (TEPname nm) = return $ LVar $ Std nm
   letep2le qvs (LVar _) (TEPvar (Gen g,_,_)) = return $ LVar g
   letep2le qvs (LVar _) tep = fail (show tep ++ " not a groot")
   letep2le qvs (LType _) tep = fmap LType $ tep2type theories tep
   letep2le qvs (LExpr _) tep = fmap LExpr $ tep2expr theories qvs tep
   letep2le qvs (LPred _) tep = fmap LPred $ tep2pred theories qvs tep
   letep2le qvs _ tep = return $ LVar $ Std (show (dbg xxx tep))

   xxx   = "letep2le_other"
\end{code}




\subsubsection{top-level conversions}

Negation (prefix) binds tighter than (prefix-)function application.
\begin{code}
bindNot [] = []
bindNot ((PExpr (Var f)):rest) | varKey f == keyLNOT
     = bindNot' [] (perror "dangling NOT at end") rest
bindNot (pr:rest) = bindNot' [] pr rest

bindNot' pres pr [] = (pr:pres)
bindNot' pres pr ((PExpr (Var f)):rest) | varKey f == keyLNOT
     = bindNot' pres (mkNot pr) rest
bindNot' pres pr (pr':rest) = bindNot' (pr:pres) pr' rest
\end{code}

We need an auxilliary to convert a list of \verb"Either String t"
into a list of \verb"t", given a function \verb"String -> t":
\begin{code}
either2x :: (String -> t) -> Either String t -> t
either2x f (Left s)   =  f s
either2x _ (Right x)  =  x
\end{code}

\subsection{Converting Applications}


\begin{code}
apply2p (PExpr (Var f)) (PExpr e2) = PExpr (App (varKey f) [e2])
apply2p f a = mkPapp f a

tapp (Tfun tf tr) ta
 | tf `tlequiv` ta  =  tr
tapp tf ta = Terror "ill-typed application " (mkTprod [tf,ta])
\end{code}

\subsection{Forcing Expressions}

Some predicates are in fact expressions in disguise.
This function tries to force a predicate into expression form,
applying some heuristics.
We also map predicates applied to partial predicate-sets
into proper applications.
\begin{code}
forceExpr (PApp nm [f@(PExpr _), a@(PExpr _)])
 | nm == n_Papp  =  frcPapp2Expr f a
forceExpr (Sub p sub) = frcSub2Expr (forceExpr p) sub
forceExpr pr = pr
\end{code}

If we are applying a expression variable to an expression,
then we return an expression application:
\begin{code}
frcPapp2Expr f@(PExpr (Var v))  (PExpr a) = PExpr (App (varKey v) [a])
frcPapp2Expr f a                          = mkPapp f a
\end{code}

If we are substituting into an expression,
we make it an expression substitution
(NOT FOR NOW !):
\begin{code}
--frcSub2Expr (PExpr e) sub = PExpr Tarb (Esub e sub)
frcSub2Expr pr sub        = Sub pr sub
\end{code}

\subsection{Converting Predicates to Expressions}

We convert a list of predicates to a list of expressions,
as far as is possible.
\begin{code}
p2es es [] = reverse es
p2es es ((Right e):ps) = p2es ((p2e e):es) ps

p2e (PExpr e) = e
p2e (PApp nm [prc,prt,pre])
 | nm == n_If  =  (mkCond prc (p2e prt) (p2e pre))
p2e (Sub pr sub) = (ESub (p2e pr) sub)
p2e pr = eerror ("Pred-not-Expr:"++show pr)
\end{code}

\subsection{Converting TEP to Expression}

This is used for the expression parser

\begin{code}
tep2expr
  :: [Theory] -- available theories
  -> [(Variable,SynClass)]  -- quantified variables
  -> TEP
  -> Either String Expr
tep2expr theories qvs tep = t2e qvs tep
 where
   typof = tslookup (map types theories)
   thetypeof s
    = case typof s of
       Nothing  ->  Tarb
       Just t   ->  t
   precof = tslookup (map precs theories)
\end{code}

\subsubsection{Converting \texttt{TEPnull}}

This case should not arise~!

\begin{code}
   t2e qvs (TEPnull) = Left "null TEP"

   t2e qvs (TEPperr string) = Right (eerror ("PREDERR "++string))
   t2e qvs (TEPeerr string) = Right (eerror string)
   t2e qvs (TEPterr string) = Right (eerror ("TYPERR "++string))
\end{code}

\subsubsection{Converting \texttt{TEPnum}}

\begin{code}
   t2e qvs (TEPnum i) = Right (Num i)
\end{code}

\subsubsection{Converting \texttt{TEPname}}
\begin{code}
   t2e qvs (TEPname s)
    = do pr <- str2predvar theories qvs thetypeof $ preVar s
         case pr of
           TRUE     ->  return $ EPred TRUE
           FALSE    ->  return $ EPred FALSE
           PExpr e  ->  return e
           PVar p   ->  return (Var p) -- "demote"
           pr       ->  fail ("Not Expr-Var : "++show pr)
\end{code}

\subsubsection{Converting \texttt{TEPvar}}
\begin{code}
   t2e qvs (TEPvar v)
    = do pr <- str2predvar theories qvs thetypeof v
         case pr of
           TRUE     ->  return $ EPred TRUE
           FALSE    ->  return $ EPred FALSE
           PExpr e  ->  return e
           PVar p   ->  return (Var p) -- "demote"
           pr       ->  fail ("Not Expr-Var : "++show pr)
\end{code}

\subsubsection{Converting \texttt{TEPfactor}}

A valid expression factor has the form $Name^*~Expr~Subs^*$.

\begin{code}
   t2e qvs tepfac@(TEPfactor _)
    = do p <- tep2pred theories qvs tepfac
         return (p2e p)
\end{code}

\subsubsection{Converting \texttt{TEPinfix}}

\begin{code}
   t2e qvs (TEPinfix p opname tep1 tep2)
    = do p1 <- t2e qvs tep1
         p2 <- t2e qvs tep2
         return $ buildOp p p1 p2
    where
      buildOp p e1 e2
        | opname == "="  =  mkEqual e1 e2
        | otherwise      =  mkBin opname p e1 e2
\end{code}

\subsubsection{Converting \texttt{TEPprod}}

\begin{code}
   t2e qvs (TEPprod tep) = do let p = map (tep2pred theories qvs) tep
                              let es = p2es [] p
                              return (mkProd es)
\end{code}

\subsubsection{Converting \texttt{TEPset}}


\begin{code}
   t2e qvs (TEPset teps) = do es <- sequence (map (t2e qvs) teps)
                              return (mkSet es)
\end{code}

\subsubsection{Converting \texttt{TEPsetc}}

\begin{code}
   t2e qvs (TEPsetc decls tep1 tep2)
    = do let qvs' = decls `qcat` qvs
         p <- tep2pred theories qvs' tep1 -- range
         e <- t2e qvs' tep2 -- expression
         -- return (Setc 0 ( decls) p e)
         fail "t2e setc -- not supported"
\end{code}

\subsubsection{Converting \texttt{TEPseq}}

\begin{code}
   t2e qvs (TEPseq teps)
     = do es <- sequence (map (t2e qvs) teps)
          return (mkSeq es)
\end{code}

\subsubsection{Converting \texttt{TEPsetq}}

\begin{code}
   t2e qvs (TEPseqc decls tep1 tep2)
    = do let qvs' = decls `qcat` qvs
         p <- tep2pred theories qvs' tep1 -- range
         e <- t2e qvs' tep2 -- expression
         -- return (Seqc 0 ( decls) p e)
         fail "t2e seqc -- not supported"
\end{code}

\subsubsection{Converting \texttt{TEPmap}}
\begin{code}
   t2e qvs (TEPmap teps)
    = do let p = tup2list [] teps
         es <- sequence $ map (t2e qvs) p
         let m = t2m [] es
         -- return (Map m)
         fail "t2e map -- not supported"
\end{code}


\subsubsection{Converting \texttt{TEPbind}}
\begin{code}
   t2e qvs (TEPbind q dcls rtep btep)
    | q == keyTHE   && just1 dcls  =  bldTHE (head dcls) rtep btep
    -- | q == ksymEABS && nor         =  bldEQ Eabs dcls btep
    | otherwise                    =  Left ("t2e bind---unknown quantifier: "++q)
    where

     nor   =  rtep == TEPnull

     just1 [_]  =  True
     just1 _    =  False

     and2 r p = mkAnd [r,p]

     bldTHE v rtep btep
      | rtep == TEPnull = do p <- tep2pred theories ([v] `qcat` qvs) btep
                             return $ mkThe v p
      | otherwise       = do let qvs' = [v] `qcat` qvs
                             r <- tep2pred theories qvs' rtep -- range
                             p <- tep2pred theories qvs' btep -- predicate
                             return $ mkThe v (and2 r p)

     bldEQ quant dcls btep
      = do let qvs' = dcls `qcat` qvs
           e <- t2e qvs' btep
           return (quant 0 ( dcls) e)
\end{code}


\subsubsection{Converting \texttt{TEPcond}}
\begin{code}
   t2e qvs (TEPcond t c f)
    = do cond <- tep2pred theories qvs c
         expr1 <- t2e qvs t
         expr2 <- t2e qvs f
         return (mkCond cond expr1 expr2)
\end{code}

\subsubsection{Final Catch-all}
\begin{code}
   t2e qvs tep = fail ("t2e NYI - "++show tep)
-- end tep2expr
\end{code}

Helpers:
\begin{code}
tup2list acc [] = acc
tup2list acc ((p,q):rest) = tup2list (p:q:acc) rest

t2m m [] = m
t2m m (e1:e2:rest) = t2m ((e1, e2):m) rest
\end{code}



\subsection{Converting TEP to Type Expression}

This is used for the type expression parser

\begin{code}

tep2type :: [Theory] -> TEP -> Either String Type
tep2type theories tep = t2t tep
 where

\end{code}

\subsubsection{Converting \texttt{TEPnull}}

This case should not arise~!

\begin{code}

   t2t (TEPnull) = Left "null TEP"

   t2t (TEPperr string) = Right (Terror ("PREDERR "++string) Tarb)
   t2t (TEPeerr string) = Right (Terror ("EXPERR "++string) Tarb)
   t2t (TEPterr string) = Right (Terror string Tarb)


\end{code}

\subsubsection{Converting \texttt{TEPname}}
\begin{code}

   t2t (TEPname s)
    | s == tkeyBOOL  =  Right B
    | s == tkeyINT   =  Right Z
    | s == tksymARB  =  Right Tarb
    | otherwise      =  Right (Tvar s)

   t2t (TEPtprod teps)
    = do let p = map t2t teps
         let q = either2val [] p
         return (mkTprod q)

   t2t (TEPtfun tep1 tep2)
    = do p <- t2t tep1
         q <- t2t tep2
         return (Tfun p q)

   t2t (TEPtpfun tep1 tep2)
    = do p <- t2t tep1
         q <- t2t tep2
         return (Tfun p q)

   t2t (TEPtmap tep1 tep2)
    = do p <- t2t tep1
         q <- t2t tep2
         return (Tfun p q)

   t2t (TEPtset tep)
    = do p <- t2t tep
         return (mkTset p)

   t2t (TEPtseq tep)
    = do p <- t2t tep
         return (mkTseq p)

   t2t (TEPtseqp tep)
    = do p <- t2t tep
         return (mkTseqp p)

   t2t (TEPtfree tn []) = Right (Tvar tn)
   t2t (TEPtfree tn cls)
    = do ps <- mapM t2cls cls
         return (Tfree tn ps)
    where
      t2cls (n,teps)
       = do ts <- mapM t2t teps
            return (n,ts)

either2val acc [] = reverse acc
either2val acc ((Right x):rest) = either2val ((x):acc) rest

\end{code}


\subsection{Parsing a Theory Document}

A document is laid out in sections based on the keywords
in list \verb"sec_keywords":
\begin{verbatim}
PRECEDENCES
prec1
prec2
OBSVARS
ob1
ob2
\end{verbatim}
   ...etc

We need to process all entries belonging to the \texttt{PRECEDENCE}
section of the document.
These are entries of the form: \verb" * num assoc".

\verb'*' is the name of the symbol,
\texttt{num} is the precedence and \texttt{assoc} will be either
\texttt{Left}, \texttt{Right}, or \texttt{None}.

\begin{code}
checkPrecs :: [(String, Precs)] -> [Token] -> [(String, Precs)]
checkPrecs newPrecs [] = reverse newPrecs
checkPrecs newPrecs toks
 = case entry of
     Left newPrec -> checkPrecs (newPrec:newPrecs) rest
     Right msg      -> reverse (("PREC-ERROR:"++msg,(0,AssocNone)):newPrecs)
 where entry = checkSym toks
       (_:_:_:rest) = toks

checkSym ((sp, (TName n)):toks)  =  checkPrec n toks
checkSym ((sp, (TSym s)):toks)   =  checkPrec s toks
checkSym ((sp, (TKSym k)):toks)  =  checkPrec k toks
checkSym ((_,tok):_)             =  Right ("invalid binop: '"++show tok++"'")

checkPrec s ((sp, (TNum num)):toks) = checkAssoc s (read num) toks
checkPrec _ ((_,tok):_)             = Right ("num exp., not "++show tok)

checkAssoc s n ((sp, (TName "Left")):_)  = Left (s, (n, AssocLeft))
checkAssoc s n ((sp, (TName "Right")):_) = Left (s, (n, AssocRight))
checkAssoc s n ((sp, (TName "None")):_)  = Left (s, (n, AssocNone))
checkAssoc _ _ ((_,tok):_)               = Right ("assoc exp., not "++show tok)

\end{code}




\subsection{Parsing Context}

We package all the theory-related stuff that affects parsing
of expressions and predicates
(but not types)
into a context, that singles out the precedences and language
tables for prominence,
as well as classification functions for name and symbol tokens.
\begin{code}
data ParseContext
 = ParseCtxt
    { precTable :: Trie Precs
    , langTable :: LParseTree
    , nameMap :: String -> Tok
    , symMap :: String -> Tok
    , theoryCtxt :: [Theory]
    }
\end{code}

\subsubsection{Building a Parse Context}

The precedence and language tables are simply the merging of all
those found in the involved theories.
The mapping functions are derived from the builtin
tables regarding key-words and -symbols,
plus data extracted from the theories.
All \texttt{SSTok} entries in language tables are
mapped to \texttt{TKey} or \texttt{TKSym} as appropriate
All entries in precedence tables are mapped to \texttt{TSym},
overriding any \texttt{SSTok}-based classification.

\begin{code}
buildParseContext basenamemap basesynmap theories
 = let synprec = foldl tmerge tnil (map precs theories)
       synlang = foldl tmerge tnil (map lang theories)
       langtable = langTable2LPTree synlang
       (langkeys,langksyms) = languageKeys langtable
       langnamemap = mkTokTable TKey langkeys
       langsymmap  = mkTokTable TKSym langksyms
       precmap = mkTokTable TSym (trieDom synprec)
       namemap = foldl1 toverride [langnamemap,precmap,basenamemap]
       symmap  = foldl1 toverride [langsymmap,precmap,basesynmap]
   in ParseCtxt { precTable = synprec
                , langTable = langtable
                , nameMap = mkNameMap namemap
                , symMap = mkSymMap symmap
                , theoryCtxt = theories
                }
\end{code}

From a context, we build two mapping functions

All names and symbols found are then mapped, if required,
to other token types by the functions \texttt{nameMap} and \texttt{symMap} respectively.

These mapping functions are implemented in terms
of \texttt{Trie Tok} tables in a straightforward manner.
The first argument says what form of token to construct
if the string was not found in the table.
\begin{code}
tokMap :: (String -> Tok) -> Trie Tok -> String -> Tok
tokMap tcons tmap str
 = case tlookup tmap str of
    Nothing   ->  tcons str
    Just tok  ->  tok

mkNameMap = tokMap TName
mkSymMap  = tokMap TSym
\end{code}

Given a list of strings to be turned into tokens of a known
type, we can easily build a corresponding token table:
\begin{code}
mkTokTable :: (String->Tok) -> [String] -> Trie Tok
mkTokTable tcons
 = lbuild . map mkentry
 where
   mkentry s = (s,tcons s)
\end{code}



\subsubsection{Scanning w.r.t. a Parse Context}

Very simple --- just extract, from the contexts,
 all the information we have about
symbols and pass it to the scanner
\begin{code}
contextScan :: ParseContext -> [Token] -> [Token]
contextScan pctxt
 = symbolSplit knownSyms
 where langksyms = sbuild $ snd $ languageKeys $ langTable pctxt
       precksyms = tmap (const ()) $ precTable pctxt
       knownSyms = foldl1 toverride [docKeySyms,langksyms,precksyms]
\end{code}


\subsubsection{Classifying w.r.t. a Parse Context}

Also simple.
\begin{code}
contextClassify pctxt fname
  =  map (tokClassify fname (nameMap pctxt) (symMap pctxt))
\end{code}

Token classification maps name and symbol tokens
as specified by the renaming functions,
as well as replacing the source-position name by that given.
\begin{code}
tokClassify name namemap symmap (sp, TName s)
 = (setSourceName sp name,namemap s)
tokClassify name namemap symmap  (sp, TSym s)
 = (setSourceName sp name,symmap s)
tokClassify name namemap symmap (sp,tok)
 = (setSourceName sp name,tok)

\end{code}
Useful tests
\begin{code}

stdScan ops text
 = displayToks toks'
 where
  toks = scanner "<test>" text
  toks' = symbolSplit (docKeySyms `tmerge` (sbuild ops)) toks
\end{code}





\newpage
\subsection{Top-Level Assertion Parser}

\begin{code}
type AsnParser = String -> String -> Either String Assertion

asnTextParser
 ::  [Theory]        -- named predicates
  -> AsnParser

asnTextParser theories file str
 = convert presult
 where

   tdbg = dbgsh (show . map snd)

   toks = scanner file str
   docSymToks' = tupdate scKeyCOV (TKSym scKeyCOV) docSymToks
   predCtxt = buildParseContext docNameToks docSymToks' theories
   toks' = contextScan predCtxt toks
   (nprecs, toks'') = checkInfix [] [] (removeWhite toks')
   prec' = (lbuild nprecs) `tmerge` precTable predCtxt
   predCtxt' = predCtxt{precTable=prec'}
   toks''' = contextClassify predCtxt' file toks''

   lng = langTable predCtxt'
   presult = runParser (asnParser (prec',lng)) () file $ tdbg "toks'''=" toks'''

   convert (Left err)   =  Left (show err)
   convert (Right (tep,scteps))
    = do pr <- tep2pred theories [] tep
         let sc = getSCs [] scteps
         let fpr' = addUType (map types theories) (setPFocus pr)
         return (clearPFocus fpr',sc)

asnParser (prec,lng)
 = do tep <- parseTEP (prec,lng)
      scteps <- option [] (try parseAsnSC)
      return (tep,scteps)

parseAsnSC
 = do scsep
      parseSCList
\end{code}

\newpage
\subsection{Top-Level Predicate(s) Parser}


\begin{code}
type PredicateParser = String -> String -> Either String Pred

predTextParser
 ::  [Theory]        -- named predicates
  -> PredicateParser

predTextParser theories file str
 = convert presult
 where

   toks = scanner file str
   predCtxt = buildParseContext docNameToks docSymToks theories
   toks' = contextScan predCtxt toks
   (nprecs, toks'') = checkInfix [] [] (removeWhite toks')
   prec' = (lbuild nprecs) `tmerge` precTable predCtxt
   predCtxt' = predCtxt{precTable=prec'}
   toks''' = contextClassify predCtxt' file toks''

   lng = langTable predCtxt'
   parser = do { tep <- parseTEP (prec',lng); eof; return tep}
   presult = runParser parser () file toks'''

   convert (Left err)   =  Left (show err)
   convert (Right tep)
    = do pr <- tep2pred theories [] tep
         let pr' = clearPFocus $ addUType (map types theories) $ setPFocus pr
         return pr'
\end{code}


\begin{code}
type PredicateSParser = String -> String -> Either String [Pred]

predsTextParser
 ::  [Theory]        -- named predicates
  -> PredicateSParser

predsTextParser theories file "" = Right []
predsTextParser theories file str
 = convert presult
 where

   toks = scanner file str
   predCtxt = buildParseContext docNameToks docSymToks theories
   toks' = contextScan predCtxt toks
   (nprecs, toks'') = checkInfix [] [] (removeWhite toks')
   prec' = (lbuild nprecs) `tmerge` precTable predCtxt
   predCtxt' = predCtxt{precTable=prec'}
   toks''' = contextClassify predCtxt' file toks''

   lng = langTable predCtxt'
   parser = do { teps <- parseTEPs (prec',lng); eof; return teps}
   presult = runParser parser () file toks'''

   convert (Left err)   =  Left (show err)
   convert (Right teps)
    = cvt teps
    where
      cvt [] = return []
      cvt (tep:teps)
       = do pr <- tep2pred theories [] tep
            let pr' = clearPFocus $ addUType (map types theories) $ setPFocus pr
            prs' <- cvt teps
            return (pr':prs')
\end{code}

\subsection{Expression Parser}

\begin{code}
type ExpressionParser = String -> String -> Either String Expr

exprTextParser
 ::  [Theory]   -- theory context
  -> ExpressionParser

exprTextParser theories file str
 = convert (runParser parser () file toks''')
 where
   -- lexical analysis
   exprCtxt = buildParseContext peNameToks peSymToks theories
   toks = scanner file str
   toks' = contextScan exprCtxt toks
   (newPrecs, toks'') = checkInfix [] [] (removeWhite toks')
   prec' = (lbuild newPrecs) `tmerge` (foldr tmerge tnil (map precs theories))

   ksyms = peKeysymbols
   kwords = peKeywords

   toks''' = contextClassify exprCtxt file toks''

   -- parsing
   parser = do { tep <- parseTEP (prec',LPNil); eof; return tep}
   -- tep/error conversion
   convert (Left err)   =  Left (show err)
   convert (Right tep)  =  tep2expr theories [] tep

-- a fudge for finaliseMatch
exprsTextParser theories file "" = Right []
exprsTextParser theories file str
 = convert (runParser parser () file toks''')
 where
   -- lexical analysis
   exprCtxt = buildParseContext peNameToks peSymToks theories
   toks = scanner file str
   toks' = contextScan exprCtxt toks
   (newPrecs, toks'') = checkInfix [] [] (removeWhite toks')
   prec' = (lbuild newPrecs) `tmerge` (foldr tmerge tnil (map precs theories))

   ksyms = peKeysymbols
   kwords = peKeywords

   toks''' = contextClassify exprCtxt file toks''

   -- parsing
   parser = do { teps <- parseTEPs (prec',LPNil); eof; return teps}
   -- tep/error conversion
   convert (Left err)   =  Left (show err)
   convert (Right teps)
    =  cvt teps
    where
      cvt [] = return []
      cvt (tep:teps)
        = do e <- tep2expr theories [] tep
             es <- cvt teps
             return (e:es)
\end{code}

\subsection{QVars Parser}

\begin{code}
type QVarsParser = String -> String -> Either String QVars

-- need to elevate comma from a symbol to a keysymbol
mkCommaKey (sp,(TSym ",")) = (sp,(TKSym ","))
mkCommaKey tok = tok

qvarsTextParser :: QVarsParser

qvarsTextParser file "" = Right $  []
qvarsTextParser file str
 = convert (runParser parser () file toks)
 where
   toks = map mkCommaKey $ scanner file str
   parser = do { tep <- parseQVars undefined; eof; return tep}
   convert (Left err)   =  Left (show err)
   convert (Right (TEPqvars xs))  =  Right $  xs
\end{code}

We now want one that returns a list (No \texttt{Q}):
\begin{code}
type VarsParser = String -> String -> Either String [Variable]

varsTextParser :: VarsParser

varsTextParser file "" = Right []
varsTextParser file str
 = convert (runParser parser () file $ dbg "vsTP.toks=" toks)
 where
   toks = map mkCommaKey $ scanner file str
   parser = do { tep <- parseQVars undefined; eof; return tep}
   convert (Left err)   =  Left (show err)
   convert (Right (TEPqvars xs))  =  Right xs
\end{code}
and a single variable:
\begin{code}
type VarParser = String -> String -> Either String Variable

varTextParser :: VarParser

varTextParser file str
 = convert (runParser parser () file toks)
 where
   toks = map mkCommaKey $ scanner file str
   parser = do { tep <- parseQVars undefined; eof; return tep}
   convert (Left err)   =  Left (show err)
   convert (Right (TEPqvars [v]))  =  Right v
   convert (Right (TEPqvars vs))  =  Left "exactly ONE variable wanted"
\end{code}

Also, it'd be nice to get a list of \texttt{GenRoot}s as well:
\begin{code}
type GenRootsParser = String -> String -> Either String [GenRoot]

genRootsTextParser :: GenRootsParser

genRootsTextParser file "" = Right []
genRootsTextParser file str
 = convert (runParser parser () file toks)
 where
   toks = map mkCommaKey $ scanner file str
   parser = do { tep <- parseQVars undefined; eof; return tep}
   convert (Left err)   =  Left (show err)
   convert (Right (TEPqvars xs))  =  Right $ map varGenRoot xs
\end{code}
and a single \texttt{GenRoot}:
\begin{code}
type GenRootParser = String -> String -> Either String GenRoot

genRootTextParser :: GenRootParser

genRootTextParser file str
 = convert (runParser parser () file toks)
 where
   toks = map mkCommaKey $ scanner file str
   parser = do { tep <- parseQVars undefined; eof; return tep}
   convert (Left err)   =  Left (show err)
   convert (Right (TEPqvars [x]))  =  Right $ varGenRoot x
   convert (Right (TEPqvars xs))  =  Left "exactly ONE GenRoot wanted"
\end{code}

\subsection{Type expression Parser}

\begin{code}
type TypeExpressionParser = String -> String -> Either String Type

typeTextParser
 ::  [Theory]
  -> TypeExpressionParser

typeTextParser theories file str
 = convert (runParser parser () file toks'')
 where
   -- lexical analysis
   typeCtxt = buildParseContext teNameToks teSymToks []
   toks = scanner file str
   toks' = symbolSplit typeKeySyms toks
   toks'' = contextClassify typeCtxt file (removeWhite toks')

   -- parsing
   parser = do { tep <- tepType; eof; return tep}
   -- tep/error conversion
   convert (Left err)   =  Left (show err)
   convert (Right tep)  =  tep2type theories tep

typesTextParser theories file "" = Right []
typesTextParser theories file str
 = convert (runParser parser () file toks'')
 where
   -- lexical analysis
   typeCtxt = buildParseContext teNameToks teSymToks []
   toks = scanner file str
   toks' = symbolSplit typeKeySyms toks
   toks'' = contextClassify typeCtxt file (removeWhite toks')

   -- parsing
   parser = do { teps <- tepTypes; eof; return teps}
   -- tep/error conversion
   convert (Left err)   =  Left (show err)
   convert (Right teps)
    = cvt teps
    where
      cvt [] = return []
      cvt (tep:teps)
       = do t <- tep2type theories tep
            ts <- cvt teps
            return (t:ts)
\end{code}

Type variable parsers:
\begin{code}
tvarTextParser file str
 = case genRootTextParser file str of
    Left msg  ->  Left msg
    Right gr  ->  Right $ genRootString gr

tvarsTextParser file "" = Right []
tvarsTextParser file str
 = case genRootsTextParser file str of
    Left msg  ->  Left msg
    Right grs  ->  Right $ map genRootString grs
\end{code}

\newpage
\subsection{Observation Kind Parser}

\begin{code}
type ObsKindParser = String -> String -> Either String ObsKind

obsKindTextParser
 ::  [Theory]
  -> ObsKindParser

obsKindTextParser theories file str
 = convert (runParser parser () file toks'')
 where
   -- lexical analysis
   typeCtxt = buildParseContext teNameToks teSymToks []
   toks = scanner file str
   toks' = symbolSplit typeKeySyms toks
   toks'' = contextClassify typeCtxt file (removeWhite toks')

   -- parsing
   parser = do { v <- p_variable; tep <- tepType; eof; return (varKey v,tep)}
   -- tep/error conversion
   convert (Left err)   =  Left (show err)
   convert (Right ("M",tep))  =  mark Model (tep2type theories tep)
   convert (Right ("S",tep))  =  mark Script (tep2type theories tep)
   convert (Right (c,tep))  =  Left ("obsKind: invalid (not M,S) - "++c)
   mark k (Left err) = Left (show err)
   mark k (Right typ) = Right (preVar "",k,typ)

showKindType (_,k,t) = show k ++ ' ':show t

\end{code}



\subsection{Theory Top-level Parser}


\begin{code}
type TheoryTextParser = [Theory]  -- pre-existing theory context
                         -> String      -- filename
                         -> String      -- file contents
                         -> Either String Theory

theoryTextParser :: TheoryTextParser
theoryTextParser theories fname text
 | null sections  =  Left "No theory sections found"
 | k /= keySYNTAXFROM  =  Left ("First section must be "++ keySYNTAXFROM)
 | cantParse  =  Left ("Can't parse: "++ because)
 | isLeft synres  = synres
 | otherwise  =  errConvert buildLangDefinitions bodyparse
 where

     -- scan text into raw tokens, strip header and split remaining sections
     toks = scanner fname text
     (name,no,toks') = stripTheoryId toks
     sections = splitTokenSections secKeywords toks'

     -- expect and process required theories section, setting up new theory
     ((k,reqsec):sections') = sections
     (reqTheories,cantParse,because) = checkRequired theories reqsec
     synpctxt = buildParseContext synNameToks synSymToks reqTheories
     newTheory = (nmdNullPrfCtxt name)
                     { thrySeqNo = no
                     , syntaxDeps = map thryName reqTheories}

     (synsections,bodysections) = partition isSynSection sections'
     isSynSection (k,_) = k `elem` [keyLANGUAGE,keyPRECEDENCES,keyENDSYNTAX]

     synres = errConvert id (parseSections fname synpctxt newTheory synsections)
     (Right synTheory) = synres

     -- build parse tables for rest of document sections
     bodypctxt = buildParseContext docNameToks docSymToks (synTheory:reqTheories)

     -- process rest of the document
     bodyparse = parseSections fname bodypctxt synTheory bodysections
\end{code}

\subsubsection{Stripping off theory name tokens}

We try to be a liberal as possible, looking for a leading
name and number (separated by whitespace), or just a name.
\begin{code}
stripTheoryId ((_,TName name):(_,TWht _):(_,TNum nums):toks)
 = (name,read nums,toks)
stripTheoryId ((_,TName name):toks)
 = (name,0,toks)
stripTheoryId toks = ("UnNamed",0,toks)
\end{code}

\subsubsection{Checking required theories}

We limit the theory context to those theories
explicitly required, and report failure if any are missing.
The \texttt{SYNTAXFROM} section should only contain
theories whose definitions are required for correct parsing of this theory.
These are the
\texttt{PRECEDENCE}, \texttt{LANGUAGE}, \texttt{TYPEDEF},
\texttt{EXPRDEF}, \texttt{PREDDEF},
\texttt{OBSVAR}, \texttt{TYPES}
sections of those theories, but not the \texttt{CONJECTURE} or \texttt{LAWS} parts.
\begin{code}
checkRequired theories reqsec
 | not (null missingNames)  =  ([],True,msg)
 | otherwise                =  (reqTheories,False,"")
 where

   reqNames = rootName : (map (nameOf . snd) (filter isName reqsec))
   isName (_,TName _) = True
   isName _ = False
   nameOf (TName s) = s

   reqTheories = filter (hasNameIn reqNames) theories
   hasNameIn names theory = thryName theory `elem` names

   haveNames = map thryName reqTheories
   missingNames = reqNames \\ haveNames

   msg = "Theories "++show missingNames++" needed to parse"
\end{code}

\subsubsection{Parsing Sections}

We process the sections, one-by-one, updating as we go.
Note that the tokens here are raw, with no symbol-splitting
or classification having occurred.
\begin{code}
parseSections fname pctxt thry [] = Right thry
parseSections fname pctxt thry (sec:secs)
 = do (pctxt',thry') <- parseSection fname pctxt thry sec
      parseSections fname pctxt' thry' secs
\end{code}
This function is the big section-name based dispatcher.
It needs to be rewritten as a lookup on the section name
in order to get all the parameters for the relevant scan/classify/parse
behaviour, in order to improve maintability.
\begin{code}
parseSection fname pctxt thry (k,toks) | k==keyPRECEDENCES
 = do let prec = precTable pctxt
      let sname = fname ++ "#" ++ k
      let nprec = lbuild (checkPrecs [] (removeWhite toks))
      let prec' = nprec `tmerge` prec
      return ( pctxt{ precTable=prec' }
             , thry{ precs=nprec `tmerge` precs thry } )

parseSection fname pctxt thry (k,toks) | k==keyLANGUAGE
 = do let prec = precTable pctxt
      let sname = fname ++ "#" ++ k
      let parseLang = do { lng <- dlang; eof; return lng}
      let toks' = contextClassify pctxt sname toks
      nlangl <- runParser parseLang () sname (removeWhite toks')
      let nlangtree = langList2LPTree nlangl
      let lang' = langTable pctxt `lptmerge` nlangtree
      let prec' = prec `precDownDate` nlangl
      return ( pctxt{ precTable=prec', langTable=lang' }
             , thry{ precs = precs thry `precDownDate` nlangl
                   , lang  = lang thry `tmerge` lbuild nlangl } )

parseSection fname pctxt thry (k,toks) | k==keyTYPEDEF
 = do let typeCtxt = buildParseContext teNameToks teSymToks []
      let sname = fname ++ "#" ++ k
      let toks' = symbolSplit typeKeySyms toks
      let toks'' = contextClassify typeCtxt sname toks'
      let parsetd = do { td <- dtypdef; eof; return td}
      tep <- runParser parsetd () sname toks''
      let ths = thry:(theoryCtxt pctxt)
      let ntd =  lbuild (t2ty ths [] tep)
      return (pctxt,thry{typedefs=ntd `tmerge` typedefs thry})

parseSection fname pctxt thry (k,toks) | k==keyCONSTDEF
 = do let prec = precTable pctxt
      let ptlt = (prec,langTable pctxt)
      let sname = fname ++ "#" ++ k
      let toks' = contextScan pctxt toks
      let toks'' = contextClassify pctxt sname toks'
      let parsecnst = do { cnst <- dconst ptlt; eof; return cnst}
      tep <- runParser parsecnst () sname toks''
      let ob = obs thry
      let ths = thry:(theoryCtxt pctxt)
      let nconst =  lbuild (t2es ths [] tep)
      return (pctxt,thry{consts=nconst `tmerge` consts thry})

parseSection fname pctxt thry (k,toks) | k==keyEXPRDEF
 = do let prec = precTable pctxt
      let ptlt = (prec,langTable pctxt)
      let sname = fname ++ "#" ++ k
      let toks' = contextScan pctxt toks
      let toks'' = contextClassify pctxt sname toks'
      let parseexps = do { exps <- dexpr ptlt; eof; return exps}
      tep <- runParser parseexps () sname toks''
      let ob = obs thry
      let ths = thry:(theoryCtxt pctxt)
      nexps <- exprTypeCheck ths $ t2es ths [] tep
      return (pctxt,thry{exprs = lbuild nexps `tmerge` exprs thry})

parseSection fname pctxt thry (k,toks) | k==keyPREDDEF
 = do let prec = precTable pctxt
      let ptlt = (prec,langTable pctxt)
      let sname = fname ++ "#" ++ k
      let toks' = contextScan pctxt toks
      let toks'' = contextClassify pctxt sname toks'
      let parsepreds = do { prds <- dpred ptlt; eof; return prds}
      tep <- runParser parsepreds () sname toks''
      let ob = obs thry
      let ths = thry:(theoryCtxt pctxt)
      npreds <- predTypeCheck ths $ t2ps ths [] tep
      return (pctxt,thry{preds = lbuild npreds `tmerge` preds thry})

parseSection fname pctxt thry (k,toks) | k==keyOBSVAR
 = do let sname = fname ++ "#" ++ k
      let typeCtxt = buildParseContext teNameToks teSymToks []
      let toks' = contextScan typeCtxt toks
      let toks'' = contextClassify typeCtxt sname toks'
      let parseobs = do { obsv <- dobs; eof; return obsv}
      tep <- runParser parseobs () sname toks''
      let ths = thry:(theoryCtxt pctxt)
      let nobs = lbuild $ map script (t2ty ths [] tep)
      return (pctxt,thry{obs = nobs `tmerge` obs thry})
 where script (v,t) = (v,(preVar v,Script,t))

parseSection fname pctxt thry (k,toks) | k==keyTYPES
 = do let sname = fname ++ "#" ++ k
      let typeCtxt = buildParseContext teNameToks teSymToks []
      let toks' = contextScan typeCtxt toks
      let toks'' = contextClassify typeCtxt sname toks'
      let parsets = do { ts <- dtypes; eof; return ts}
      tep <- runParser parsets () sname toks''
      let ths = thry:(theoryCtxt pctxt)
      let nts =  lbuild (t2ty ths [] tep)
      return (pctxt,thry{types = nts `tmerge` types thry})

parseSection fname pctxt thry (k,toks) | k==keyCONJECTURES
 = do let prec = precTable pctxt
      let ptlt = (prec,langTable pctxt)
      let sname = fname ++ "#" ++ k
      let toks' = contextScan pctxt toks
      let toks'' = contextClassify pctxt sname toks'
      let toks''' = splitPredsWithSideConds (removeWhite toks'')
      let tep = map (parsePredSideCondPair sname ptlt) toks'''
      let ob = obs thry
      let ths = thry:(theoryCtxt pctxt)
      let nconjtmp = getAssertions ths [] tep
      let nconjs1 = mapsnd (conditionAsn ths) nconjtmp
      nconjs <- asnTypeCheck ths nconjs1
      return (pctxt,thry{conjectures = lbuild nconjs `tmerge` conjectures thry})

parseSection fname pctxt thry (k,toks) | k==keyLAWS
 = do let prec = precTable pctxt
      let ptlt = (prec,langTable pctxt)
      let sname = fname ++ "#" ++ k
      let toks' = contextScan pctxt toks
      let toks'' = contextClassify pctxt sname toks'
      let toks''' = splitPredsWithSideConds (removeWhite toks'')
      let tep = map (parsePredSideCondPair sname ptlt) toks'''
      let ob = obs thry
      let ths = thry:(theoryCtxt pctxt)
      let nlawtmp =  getAssertions ths [] tep
      let nlawtmp1 = mapsnd (conditionAsn ths) nlawtmp
      nlawtmp2 <- asnTypeCheck ths nlawtmp1
      let nlaws = reverse $ map (wrapProv (FromUSER fname)) $ nlawtmp2
      return (pctxt,thry{laws = nlaws ++ laws thry})

parseSection fname pctxt thry (unksec,_)
 = return (pctxt,thry)
\end{code}


\subsubsection{Predicate/Side-Condition Handling}

The law and conjecture sections have been turned
into lists of pairs of token-lists,
each pair being a named predicate and a side-condition.
We need to parse these pairs into a TEP:
\begin{code}
parsePredSideCondPair sname ptlt (predtoks,sctoks)
 | null sctoks  =  (pName,(predTEP,[]))
 | otherwise    =  (pName,(predTEP,scTEPs))
 where
   (pName,predTEP) = parseNamedPredicate sname ptlt predtoks
   scTEPs  = parseSideConditions sname sctoks

-- no longer have TStr (why not?)
-- not sure what should happen here
-- parseNamedPredicate sname ptlt ((_,TStr nm):(_,TKSym issym):predtoks)
parseNamedPredicate sname ptlt ((_,TName nm):(_,TKSym issym):predtoks)
 | issym == ksymIS
 = case runParser (parseTEP ptlt) () sname predtoks of
    Left err  ->  (TEPname nm,TEPperr ("parseTEP error :"++show err))
    Right tep  ->  (TEPname nm,tep)

parseNamedPredicate sname ptlt badtoks
 = ( TEPname "???"
   , TEPperr ("Bad Named Predicate : "++show (take 3 badtoks)++" .."))

parseSideConditions sname sctoks
 = case res of
    Left err   ->  []
    Right scs  ->  scs
 where
   res = runParser parseSCList () sname sctoks
\end{code}

A standalone side-condition parser:
\begin{code}
type SideCondParser = String -> String -> Either String SideCond

sidecondTextParser file str
 = convert $ runParser parseSCList () "?" toks''
 where
   -- lexical analysis
   scCtxt = buildParseContext peNameToks peSymToks []
   toks = scanner file str
   toks' = symbolSplit peSymToks toks
   toks'' = contextClassify scCtxt file (removeWhite toks')

   convert (Left err)      =  Left $ show err
   convert (Right scteps)  =  Right $ getSCs [] scteps
\end{code}

Error Conversion:
\begin{code}
errConvert _ (Left err)     =  Left (show err)
errConvert f (Right thing)  =  Right (f thing)

errshow err
     = cShowPos epos ++ " ? " ++ show su ++ " ! " ++ show ex
     where
       epos = errorPos err
       emsgs = errorMessages err
       su = map messageString (filter isSU emsgs)
       ex = map messageString (filter isEX emsgs)
       unk = errorIsUnknown err
       isSU (SysUnExpect _) = True
       isSU _               = False
       isEX (Expect _)      = True
       isEX _               = False
\end{code}

Links to TEP conversions:
\begin{code}
t2ty thrs acc [] = getVals [] acc
t2ty thrs acc (((TEPname name),t):ts) = t2ty thrs ((name, tep2type thrs t):acc) ts

getVals acc [] = acc
getVals acc ((name, (Right x)):xs) = getVals ((name, x):acc) xs

t2es thrs acc [] = reverse acc
t2es thrs acc (((TEPname name),e):es)
   = t2es thrs ((name, tp2e (tep2pred thrs [] e)):acc) es

tp2e (Right (PExpr e1)) = e1

t2ps thrs acc [] = getVals [] acc
t2ps thrs acc (((TEPname name),pr):ps)
 = t2ps thrs ((name, tep2pred thrs [] pr):acc) ps

getAssertions thrs acc [] = getLawVals [] acc
getAssertions thrs acc (((TEPname name), (tepr, sc)):rest)
 = getAssertions thrs ((name,((tep2pred thrs [] tepr), sc)):acc) rest

-- pull law predicate out of Either monad
getLawVals acc [] = acc
getLawVals acc ((name, ((Right pr),sc)):xs)
 = getLawVals ((name, (pr, getSCs [] sc)):acc) xs
getLawVals acc ((name, ((Left msg),sc)):xs)
 = getLawVals ((name, (perror msg, getSCs [] sc)):acc) xs

getSCs scs [] = scand scs
getSCs scs (tep:teps)
 | sc == SCtrue  =  getSCs scs teps
 | otherwise     =  getSCs (sc:scs) teps
 where sc = getSC tep

getSC TEPnull = SCtrue

getSC (TEPprod [TEPnum scid,TEPname v])
 | scid == tepSCcondP  =  SCisCond PredM v
 | scid == tepSCcondE  =  SCisCond ExprM v

getSC (TEPprod [TEPnum scid,TEPname v])
 | scid == tepSCfreshP  =  SCfresh PredM $ predVar v
 | scid == tepSCfreshE  =  SCfresh ExprM $ preVar v

getSC (TEPprod [TEPnum scid,TEPname v,TEPseq teps])
 | scid == tepSCnotinP  =  SCnotFreeIn PredM (teps2vs teps) v
 | scid == tepSCnotinE  =  SCnotFreeIn ExprM (teps2vs teps) v
 | scid == tepSCfreeP   =  SCareTheFreeOf PredM (teps2vs teps) v
 | scid == tepSCfreeE   =  SCareTheFreeOf ExprM (teps2vs teps) v
 | scid == tepSCcoverP  =  SCcoverTheFreeOf PredM (teps2vs teps) v
 | scid == tepSCcoverE  =  SCcoverTheFreeOf ExprM (teps2vs teps) v

getSC _ = SCtrue

teps2vs []                =  []
teps2vs (TEPname n:rest)  =  preVar n:(teps2vs rest)
teps2vs (TEPvar v:rest)   =  v:(teps2vs rest)
teps2vs (_:rest)          =  teps2vs rest
\end{code}

\subsubsection{Type Checking}

\begin{code}
exprTypeCheck ths rawexprs = etc [] rawexprs
 where
  mctxt = mkMatchContext ths
  etc chkdexprs [] = return chkdexprs
  etc chkdexprs (ne@(name,ex):rest)
    = case typeCheckPred mctxt $ PExpr ex of
       Right (_, _) ->  etc (ne:chkdexprs) rest
       Left  msg
         ->  fail ("Expr '"++name++"' has type errors :\n"++msg)

predTypeCheck ths rawpreds = ptc [] rawpreds
 where
  mctxt = mkMatchContext ths
  ptc chkdpreds [] = return chkdpreds
  ptc chkdpreds (np@(name,pr):rest)
    = case typeCheckPred mctxt pr of
       Right (_, _) ->  ptc (np:chkdpreds) rest
       Left  msg
         ->  fail ("Pred '"++name++"' has type errors :\n"++msg)


asnTypeCheck ths rawlaws = ltc [] rawlaws
 where
  mctxt = mkMatchContext ths
  tts = map types ths
  ltc chkdlaws [] = return chkdlaws
  ltc chkdlaws (nl@(name,(pr,sc)):rest)
    = case typeCheckPred mctxt pr of
       Right (_, _) ->  ltc (nl:chkdlaws) rest
       Left  msg
         ->  fail ("Law '"++name++"' has type errors :\n"++msg)
\end{code}

\section{Text Rendering of a Theory}

\begin{code}
theory2txt :: [Theory] -> Theory -> String
theory2txt theories theory
 = unlines (th2txt theory)
 where

  th2txt theory
   = (thryName theory ++ " " ++ show (thrySeqNo theory))
     : keySYNTAXFROM
     : (concat $ intersperse " "
        $ filter (not . isSPTName) $ syntaxDeps theory)
     : concat (map totxt slist)
     ++ keyENDSYNTAX
     : concat (map totxt plist)
     ++ [keyEND]

  totxt f = f theory

  slist = [ nndo keyPRECEDENCES precs2txt . flattenTrie . precs
          , nndo keyLANGUAGE lang2txt . flattenTrie . lang
          ]

  plist = [ nndo keyTYPEDEF typedefs2txt . flattenTrie . typedefs
          , nndo keyCONSTDEF consts2txt . flattenTrie . consts
          , nndo keyEXPRDEF exprs2txt . flattenTrie . exprs
          , nndo keyPREDDEF preds2txt. flattenTrie . preds
          , nndo keyOBSVAR obs2txt . flattenTrie . obs
          , nndo keyTYPES types2txt . flattenTrie . types
          , nndo keyCONJECTURES conjs2txt . flattenTrie . conjectures
          , nndo keyLAWS laws2txt . laws
          ]

  nndo k f [] = [] -- start section only if something to say ...
  nndo k f xs = k : f xs

  precs2txt list = map (triple2txt showPrec) list
  lang2txt list = addSep $ map (sentry2txt ksymIS (show . show)) list

  typedefs2txt list = addSep $ map (entry2txt ksymDEFEQ show) list
  consts2txt list = addSep $ map (entry2txt ksymDEFEQ show) list
  exprs2txt list = addSep $ map (entry2txt ksymDEFEQ show) list
  preds2txt list = addSep $ map (entry2txt ksymDEFEQ show) list
  obs2txt list = addSep $ map (entry2txt tksymHASTYPE show) list
  types2txt list = addSep $ map (entry2txt tksymHASTYPE show) list
  conjs2txt list = addSep $ map (sentry2txt ksymIS showAssertion) list
  laws2txt list = addSep $ map (sentry2txt ksymIS showLaw) list

  triple2txt showthing (name,thing)
   = ' ' : name ++ ' ' :  showthing thing

  entry2txt sep showthing (name,thing)
   = ' ' : name ++ ' ' : sep ++  ' ' : showthing thing

  sentry2txt sep showthing (name,thing)
   = ' ' : '"' : name ++ '"' : ' ' : sep ++  ' ' : showthing thing

  addSep [] = []
  addSep [x] = [x]
  addSep (x:xs) = (x ++ [' ',chrSEP]):addSep xs

  showPrec (i,assoc) = show i ++ ' ' : showAssoc assoc

  showAssoc AssocLeft  = "Left"
  showAssoc AssocRight = "Right"
  showAssoc AssocNone  = "None"

showAssertion (pr,SCtrue) = show pr
showAssertion (pr,sc) = show pr ++ ' ' : ksymSCSEP ++ ' ' : show sc
showLaw (ass,_,_) = showAssertion ass -- we don't output provenance/types.
\end{code}
