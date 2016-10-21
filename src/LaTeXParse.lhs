\section{\LaTeX\ Parser}

\begin{haskell}

> module LaTeXParse
>   (-- For convenience, we export some error handling functions
>    -- (from module Errors) that are needed to interpret parser results.
>    ErrorOr(..),
>    isOk,  notOk, fromOk, error_message,
>    -- These are the top-level parsers, of type String -> ErrorOr ast
>    parseZspec,   -- a whole spec
>    parseZpara,   -- one paragraph only
>    parseZsexpr,  -- a single schema expression (no \begin..\end needed)
>    parseZexpr,   -- a single expression (no \begin..\end needed)
>    parseZpred,   -- a single predicate (no \begin..\end needed)
>    parseZident,  -- a single identifier (perhaps decorated)
>    -- This lower-level paragraph-parsing function is for testing only
>    pzp
>   )

\end{haskell}
This Z parser is based closely upon the LL(infinity) Z grammar
in \cite{BB:concrete:Z:95} and the (more informal)
grammar in the appendix of \cite{Spivey92}.

It is reasonably complete, except that generics are not handled
and global definitions and let definitions cannot (yet) define
operators.

Note: paragraphs are flattened as much as possible.
      In other words, a given set declaration, $[A,B,C]$ is expanded
      out into three separate given set declarations.  Similarly,
      abbreviations ($a==\ldots$), free type definitions etc. are all
      expanded out into separate paragraphs.  This makes the
      abstract syntax trees simpler (each paragraph generally
      defines just one name).
      However, \texttt{axdef} and \texttt{gendef} paragraphs are not expanded,
      even when they define multiple names, because we assume that
      the names and associated predicates are grouped together for
      some semantic reason.  E.g. It is good style for all the
      constraints on a declared constant to be given in the \texttt{axdef}
      paragraph where the constant is declared.

\begin{haskell}

> where
> import EParseLib
> import LaTeXLexer
> import LaTeXAST
> import Control.Monad
> import LaTeXErrors
> import Data.List
> import Data.Maybe
> import LaTeXSetup


\end{haskell}

\subsection{Parsers Top-Level Calls}

This shows you the whole result (all parses and all errors).
It is for debugging and testing only.
\begin{haskell}

> pzp :: LaTeXLayout -> String -> ParseResult ZToken ZSpec
> pzp ll = epapply zparagraph . zlex (ltx2sym ll) lexstate0

\end{haskell}
The following checks a parsing result to
see if it contains any errors that need reporting.
\begin{haskell}

> check_parse :: ParseResult ZToken ast -> ErrorOr ast
> check_parse ParseResult{parses=[], besterror=err}
>   = SyntaxErrors [mkParseError err]
> check_parse ParseResult{parses=[(t,[],[])]}
>   = Ok t
> check_parse ParseResult{parses=[(t,errs,[])]}
>   = SyntaxErrors errs
> check_parse ParseResult{parses=[(t,[],toks)], besterror=err}
>   = SyntaxErrors [mkParseError (toks,"valid syntax upto here"),
> 		  mkParseError err]
> check_parse ParseResult{}
>   = SyntaxErrors [(0,0,"ambiguous parse!")]
>
>

\end{haskell}
\begin{haskell}

> parseZspec :: LaTeXLayout -> String -> ErrorOr ZSpec
> parseZspec ll = check_parse . epapply zspec . zlex (ltx2sym ll) lexstate0

> parseZpara :: LaTeXLayout -> String -> ErrorOr ZSpec
> parseZpara ll = check_parse . epapply zparagraph . zlex (ltx2sym ll) lexstate0

> parseZsexpr :: LaTeXLayout -> String -> ErrorOr ZSExpr
> parseZsexpr ll = check_parse . epapply zschema_exp . zlexz (ltx2sym ll) 0 lexstate0

> parseZexpr :: LaTeXLayout -> String -> ErrorOr ZExpr
> parseZexpr ll = check_parse . epapply zexpression . zlexz (ltx2sym ll) 0 lexstate0

> parseZpred :: LaTeXLayout -> String -> ErrorOr ZPred
> parseZpred ll = check_parse . epapply zpredicate . zlexz (ltx2sym ll) 0 lexstate0

> parseZident :: LaTeXLayout -> String -> ErrorOr ZVar
> parseZident ll = check_parse . epapply zident . zlexz (ltx2sym ll) 0 lexstate0

\end{haskell}
\subsection{Top-Level Parsers}
\begin{haskell}

> zspec :: EParser ZToken ZSpec
> zspec		= do	ps <- many zparagraph
>			return (concat ps)

\end{haskell}
Paragraphs:
\begin{haskell}

> zparagraph :: EParser ZToken [ZPara]
> zparagraph
>   = cconstbox +++	
>     cexprbox +++	
>     cpredbox +++
>     ctypedefbox +++
>     ctypesbox  +++
>     clawsbox +++
>     cconjectbox +++
>     theoryid

zunboxed_para +++
    zaxiomatic_box +++
     zschema_box +++
     zmachine_box   +++ -- an extension for defining state machines.
\end{haskell}

\subsection{Environment (a.k.a. ``Paragraph'') Parsers}

The following are parsers for multiple named predicates/type definitions
and the like.
The \texttt{*box} parsers parse multiple items separated by "\\" or ";".

\Saoithin\ extension
(Simon Dardis, Summer 2008, modified Summer 2009)
We need to parse a begin/end token for a specified environment:
\begin{haskell}

> tokbegin ename
>  = do L_BEGIN env <- satm ("\\begin{"++ename++"} expected") (isBeginEnv ename)
>       return env

> isBeginEnv ename (L_BEGIN env)  =  env == ename
> isBeginEnv ename _              =  False


> tokend ename
>  = do L_END env <- satm ("\\end{"++ename++"} expected") (isEndEnv ename)
>       return env

> isEndEnv ename (L_END env)  =  env == ename
> isEndEnv ename _            =  False

\end{haskell}
Parsing most of the environments follows a standard pattern,
which can be viewed as having three parameters:
\begin{itemize}
  \item the environment name
  \item the parser for the contents
  \item something to wrap the final result up
\end{itemize}
\begin{haskell}

> paraEnv ename cparser wrapper
>  = do tokbegin ename
>       cut
>       thing <- cparser
>       optnls
>       tokend ename
>       return (wrapper thing)

\end{haskell}
The \texttt{theoryid} environment.
\begin{haskell}

> theoryid :: EParser ZToken [ZPara]
> theoryid = paraEnv "theoryid"
>               theoryarg (\x -> [CTheory x])

%> theoryid
%>   = do tok L_BEGIN_THEORYID
%>        cut
%>        thstr <- theoryarg
%>        optnls
%>        tok L_END_THEORYID
%>        return [CTheory thstr]

> theoryarg :: EParser ZToken String
> theoryarg
>   = do L_THEORYID s <- satm "theoryid expected" isTidVal
>        return s
>   where
>      isTidVal (L_THEORYID _) = True
>      isTidVal _              = False

\end{haskell}
\begin{haskell}

> cpredbox :: EParser ZToken [ZPara]
> cpredbox = paraEnv "preds"
>              (cpred `sepby1` many1 zsep) concat

%>  = do tok L_BEGIN_CIRCUS_PRED
%>       cut
%>       s <- cpred `sepby1` many1 zsep
%>       optnls
%>       tok L_END_CIRCUS_PRED
%>       return (concat s)

\end{haskell}
\begin{haskell}

> cconstbox :: EParser ZToken [ZPara]
> cconstbox = paraEnv "consts"
>               (cconst `sepby1` many1 zsep) concat

\end{haskell}
\begin{haskell}

> cexprbox :: EParser ZToken [ZPara]
> cexprbox = paraEnv "exprs"
>               (cexpr `sepby1` many1 zsep) concat

%>	= do	tok L_BEGIN_CIRCUS_EXPR
%>		cut
%>		s <- cexpr `sepby1` many1 zsep
%>		optnls
%>		tok L_END_CIRCUS_EXPR
%>		return (concat s)

\end{haskell}
\begin{haskell}

> ctypedefbox :: EParser ZToken [ZPara]
> ctypedefbox = paraEnv "typedefs"
>                  (ctypedef `sepby1` many1 zsep) concat

%>	= do	tok L_BEGIN_CIRCUS_TYPEDEF
%>		cut
%>		s <- ctypedef `sepby1` many1 zsep
%>		optnls
%>		tok L_END_CIRCUS_TYPEDEF
%>		return (concat s)

\end{haskell}
\begin{haskell}

> ctypesbox :: EParser ZToken [ZPara]
> ctypesbox = paraEnv "types"
>                  (ctypes `sepby1` many1 zsep) concat

%>	= do	tok L_BEGIN_CIRCUS_TYPES
%>		cut
%>		s <- ctypes `sepby1` many1 zsep
%>		optnls
%>		tok L_END_CIRCUS_TYPES
%>		return (concat s)

\end{haskell}
\begin{haskell}

> clawsbox :: EParser ZToken [ZPara]
> clawsbox = paraEnv "laws"
>                  (claws `sepby1` many1 zsep) concat

%>	= do	tok L_BEGIN_CIRCUS_LAWS
%>		cut
%>		s <- claws `sepby1` many1 zsep
%>		optnls
%>		tok L_END_CIRCUS_LAWS
%>		return (concat s)


\end{haskell}
\begin{haskell}

> cconjectbox :: EParser ZToken [ZPara]
> cconjectbox = paraEnv "conjectures"
>                  (cconject `sepby1` many1 zsep) concat

%>	= do	tok L_BEGIN_CIRCUS_CONJECT
%>		cut
%>		s <- cconject `sepby1` many1 zsep
%>		optnls
%>		tok L_END_CIRCUS_CONJECT
%>		return (concat s)

\end{haskell}


\subsection{Table Entry Parsers}

The parsers below invoke the relevant subparsers for predicates,
expressions...

\begin{haskell}

> cconject :: EParser ZToken [ZPara]
> cconject
>	= do	name <- clawarg
>		tok (L_SYM NAMES)
>		optnls;
>		p <- zpredicate
>		return [CConject (make_zvar name []) p]
>

\end{haskell}
\begin{haskell}

> claws :: EParser ZToken [ZPara]
> claws = do name <- clawarg
>            tok (L_SYM NAMES)
>            optnls
>            p <- zpredicate
>            return [CLaw (make_zvar name []) p]

\end{haskell}
\begin{haskell}

> ctypes ::EParser ZToken [ZPara]
> ctypes = do name <- zdef_lhs
>             optnls
>             tok (L_SYM COLON)
>             cut
>             optnls
>             e <- ctype
>             return [(CTypes name e)]

\end{haskell}
\begin{haskell}

> ctypedef :: EParser ZToken [ZPara]
> ctypedef
>	=  zitem_givensets +++
>	zitem_freetype +++
>	do	zname <- zdef_lhs;
>		optnls;
>		tok (L_SYM DEFS);
>		cut;
>		optnls;
>		e <- ctype;
>		return [CTypedef zname e]
>

\end{haskell}
\begin{haskell}

> cpred :: EParser ZToken [ZPara]
> cpred
>  = do zname <- zdef_lhs
>       optnls
>       tok (L_SYM DEFS)
>       cut
>       optnls
>       e <- zpredicate
>       return [CNPred zname e]

\end{haskell}
\begin{haskell}

> cconst :: EParser ZToken [ZPara]
> cconst
>	= do	zdef <- zdef_lhs
>		optnls
>		tok (L_SYM DEFS)
>		cut
>		optnls
>		e <- zexpression
>		return [CNConst zdef e] -- ????
>

\end{haskell}
\begin{haskell}

> cexpr :: EParser ZToken [ZPara]
> cexpr
>	= do	zdef <- zdef_lhs
>		optnls
>		tok (L_SYM DEFS)
>		cut
>		optnls
>		e <- zexpression
>		return [CNExpr zdef e]
>

\end{haskell}
\begin{haskell}

> zunboxed_para :: EParser ZToken [ZPara]
> zunboxed_para = paraEnv "zed"
>                   (zitem `sepby1` many1 zsep) concat

%do	tok L_BEGIN_ZED
%> 		cut
%> 		s <- zitem `sepby1` many1 zsep
%> 		optnls
%>		tok L_END_ZED
%>		return (concat s)


\end{haskell}
\begin{haskell}

> zitem :: EParser ZToken [ZPara]
> zitem = zitem_givensets +++
> 	zitem_sdef +++
> 	zitem_abbrev +++
> 	zitem_freetype +++
> 	zitem_pred

\end{haskell}
\begin{haskell}

> zitem_givensets
>	= do	tok (L_SYM OPENBRACKET)
>		gs <- zident `sepby1` comma
>	 	tok (L_SYM CLOSEBRACKET)
>	 	return (map ZGivenSetDecl gs)

\end{haskell}
\begin{haskell}

> zitem_sdef :: EParser ZToken [ZPara]
> zitem_sdef
>	= do	name <- zschema_name
>	 	optnls
>		tok (L_SYM DEFS)
>		cut
>		optnls
>		se <- zschema_exp
> 		return [ZSchemaDef name se]

\end{haskell}
\begin{haskell}

> zitem_abbrev :: EParser ZToken [ZPara]
> zitem_abbrev
>	= do	zdef <- zdef_lhs
>		optnls
>		tok (L_SYM ABRDEF)
>		cut
>		optnls
>		e <- zexpression
>		return [ZAbbreviation zdef e]
>

\end{haskell}
\begin{haskell}

> zitem_freetype :: EParser ZToken [ZPara]
> zitem_freetype
>	= do	zdef <- zdef_lhs
>		optnls
>		tok (L_SYM COLONCOLONEQUALS)
>		cut
>		optnls
>		b <- zbranch `sepby1` do {optnls; tok (L_SYM VERT); optnls}
> 		return [ZFreeTypeDef zdef b]

\end{haskell}

\subsection{Z ``Paragraph'' Parsers}

\begin{haskell}

> zitem_pred :: EParser ZToken [ZPara]
> zitem_pred = do {p <- zpredicate; return [ZPredicate p]}
>
> zdef_lhs :: EParser ZToken ZVar
> zdef_lhs	= do	var_name <- zword
> 			dec <- zdecoration
> 			return (make_zvar var_name dec)
> -- TODO Pre_Gen_Decor Ident, Ident In_Gen_decor Ident and generic formals
>

\end{haskell}
\begin{haskell}

> zbranch :: EParser ZToken ZBranch
> zbranch
>	= do	{vn <- zvar_name;
>		tok (L_SYM LDATA);
>		e <- zexpression;
>		tok (L_SYM RDATA);
>		return (ZBranch1 vn e)} +++
>		do	{i <- zident;
> 			return (ZBranch0 i)}
>

\end{haskell}
\begin{haskell}

> zschema_exp :: EParser ZToken ZSExpr
> zschema_exp
>   = do	{tok (L_SYM FORALL);
>		st <- zschema_text;
>		optnls;
>		tok (L_SYM AT);
>		optnls;
>		se <- zschema_exp;
>		return (ZSForall st se)} +++
>	     do	{tok (L_SYM EXISTS);
> 		st <- zschema_text;
> 		optnls;
> 		tok (L_SYM AT);
> 		optnls;
> 		se <- zschema_exp;
> 		return (ZSExists st se)} +++
>	    do	{tok (L_SYM EXISTS1);
> 		st <- zschema_text;
> 		optnls;
> 		tok (L_SYM AT);
> 		optnls;
> 		se <- zschema_exp;
> 		return (ZSExists_1 st se)} +++
>		zschema_exp_1
>
>

\end{haskell}
\begin{haskell}

> zschema_exp_1 :: EParser ZToken ZSExpr
> zschema_exp_1
>   = chainl1 zschema_exp_1a (do {optnls; tok (L_SYM PIPE); optnls; return (ZS2 ZSPipe)})
>
> -- Note this differs from the Breuer/Bowen grammar because
> --  \implies binds tighter than \iff and the precedence of
> --  schema operators is respected as in zrm.
>
> zschema_exp_1a :: EParser ZToken ZSExpr
> zschema_exp_1a
>   = chainl1 zschema_exp_1b (do {optnls; tok (L_SYM SEMICOLON); optnls; return (ZS2 ZSSemi)})
>
> zschema_exp_1b :: EParser ZToken ZSExpr
> zschema_exp_1b
>   = chainl1 zschema_exp_1c (do {optnls; tok (L_SYM PROJECT); optnls; return (ZS2 ZSProject)})
>
> zschema_exp_1c :: EParser ZToken ZSExpr
> zschema_exp_1c
>   = chainl1 zschema_exp_1d (do {optnls; tok (L_SYM IFF); optnls; return (ZS2 ZSIff)})
>
> zschema_exp_1d :: EParser ZToken ZSExpr
> zschema_exp_1d
>   = chainr1 zschema_exp_1e (do {optnls; tok (L_SYM IMPLIES); optnls; return (ZS2 ZSImplies)})
>
> zschema_exp_1e :: EParser ZToken ZSExpr
> zschema_exp_1e
>   = chainl1 zschema_exp_1f (do {optnls; tok (L_SYM LOR); optnls; return (ZS2 ZSOr)})
>
> zschema_exp_1f :: EParser ZToken ZSExpr
> zschema_exp_1f
>   = chainl1 zschema_exp_3 (do {optnls; tok (L_SYM LAND); optnls; return (ZS2 ZSAnd)})
>
>

\end{haskell}
\begin{haskell}

> zschema_exp_3 :: EParser ZToken ZSExpr
> zschema_exp_3
>   = do { se <- zschema_exp_u;
> 	 se2 <- opt se (do {hidel <- zit_hiding;
> 			   return (ZSHide se hidel)});
> 	 return se2 }
>

\end{haskell}
\begin{haskell}

> zit_hiding :: EParser ZToken [ZVar]
> zit_hiding
>   = do  {hidel <- many1 zhide;
> 	 return (concat hidel)}
>

\end{haskell}
\begin{haskell}

> zhide :: EParser ZToken [ZVar]
> zhide
>   = do  optnls
>   	  tok (L_SYM HIDE)
>   	  optnls
> 	  tok (L_SYM OPENPAREN)
> 	  dn <- zdecl_name `sepby1` comma
> 	  tok (L_SYM CLOSEPAREN)
> 	  return dn
>

\end{haskell}
\begin{haskell}

> zschema_exp_u :: EParser ZToken ZSExpr
> zschema_exp_u
>   = do  {tok (L_SYM OPENBRACKET);
> 	 st <- zschema_text;
> 	 tok (L_SYM CLOSEBRACKET);
> 	 return (ZSchema st)} +++
>     do  {tok (L_SYM LNOT);
> 	 se <- zschema_exp_u;
> 	 return (ZS1 ZSNot se)} +++
>     do  {tok (L_SYM PRE);
> 	 se <- zschema_exp_u;
> 	 return (ZS1 ZSPre se)} +++
>     do  {tok (L_SYM OPENPAREN);
> 	 se <- zschema_exp;
> 	 tok (L_SYM CLOSEPAREN);
> 	 return se} +++
>     zschema_ref
>

\end{haskell}
\begin{haskell}

> zschema_ref :: EParser ZToken ZSExpr
> zschema_ref
>   = do  {zn <- zschema_name;
> 	 dec <- zdecoration;
> 	 reps <- opt [] zreplace;
> 	 return (ZSRef zn dec reps)}
> -- TODO Gen_Actuals
>

\end{haskell}
\begin{haskell}

> zreplace :: EParser ZToken [ZReplace]
> zreplace
>   = do  {tok (L_SYM OPENBRACKET);
> 	 reps <- zrename_or_repl `sepby1` comma;
> 	 tok (L_SYM CLOSEBRACKET);
> 	 return reps}
>

\end{haskell}
\begin{haskell}

> zrename_or_repl :: EParser ZToken ZReplace
> zrename_or_repl
>   = do  {dn1 <- zdecl_name;
> 	 tok (L_SYM SLASH);
> 	 dn2 <- zdecl_name;
> 	 return (ZRename dn2 dn1)} +++
>     do  {dn1 <- zdecl_name;
> 	 tok (L_SYM ASSIGN);
> 	 dn2 <- zexpression;
> 	 return (ZAssign dn1 dn2)}
>

\end{haskell}
\begin{haskell}

> zschema_name :: EParser ZToken ZSName
> zschema_name
>   = do  {tok (L_SYM DELTA); name <- zword; return (ZSDelta name)} +++
>     do  {tok (L_SYM XI); name <- zword; return (ZSXi name)} +++
>     do  {name <- zword; return (ZSPlain name)}
>
>

\end{haskell}
\begin{haskell}

> zschema_text :: EParser ZToken [ZGenFilt]
> zschema_text
>   = do  d <- zdeclaration
> 	  p <- opt [] (do {optnls;
> 			  tok (L_SYM VERT);
> 			  optnls;
> 			  p <- zpredicate;
> 			  return [Check p]})
> 	  return (concat d ++ p)
>

\end{haskell}
\begin{haskell}

> zdeclaration :: EParser ZToken [[ZGenFilt]]
> zdeclaration = zbasic_decl `sepby1` do {optnls; tok (L_SYM SEMICOLON); optnls}
>

\end{haskell}
\begin{haskell}

> zsep :: EParser ZToken ZToken
> zsep
>   = tok (L_SYM DBLBACKSLASH) +++ tok (L_SYM SEMICOLON) +++ tok (L_SYM ALSO)
>

\end{haskell}
\begin{haskell}

> opt ::  a -> EParser ZToken a -> EParser ZToken a
> opt def p = p +++ return def
>
> optnls :: EParser ZToken [ZToken]
> optnls = many (tok (L_SYM DBLBACKSLASH))
>
> optbracket :: EParser ZToken ZToken
> optbracket = tok (L_SYM OPENPAREN) +++ tok (L_SYM CLOSEPAREN)
>

\end{haskell}
\begin{haskell}

> comma = do {optnls; tok (L_SYM COMMA); optnls}

\end{haskell}
\begin{haskell}

> zaxiomatic_box :: EParser ZToken [ZPara]
> zaxiomatic_box = paraEnv "axdef"
>                    parse_decls_ax
>                    (\(d,a) -> [ZAxDef (concat d ++ a)])

> parse_decls_ax
>  = do decls <- zdecl_part
>       ax <- opt [] (do {optnls; tok (L_SYM WHERE); cut; optnls; zaxiom_part })
>       return (decls,ax)

%>   = do  tok L_BEGIN_AXDEF
%>   	  cut
%> 	  decls <- zdecl_part
%> 	  ax <- opt [] (do {optnls; tok (L_SYM WHERE); cut; optnls; zaxiom_part })
%> 	  optnls
%> 	  tok L_END_AXDEF
%> 	  return [ZAxDef (concat decls ++ ax)]


\end{haskell}
\begin{haskell}

> zschema_box :: EParser ZToken [ZPara]
> zschema_box = paraEnv "schema"
>                 parse_schema
>                 (\(n,d,a) -> [ZSchemaDef n (ZSchema (concat d ++ a))])

> parse_schema
>  = do tok (L_SYM OPENBRACE)
>       name <- zschema_name
>       tok (L_SYM CLOSEBRACE)
>       -- TODO: add generic formals
>       decls <- zdecl_part
>       ax <- opt [] (do {optnls; tok (L_SYM WHERE); cut; optnls; zaxiom_part })
>       return (name,decls,ax)


%>   = do  tok L_BEGIN_SCHEMA
%> 	  cut
%> 	  tok (L_SYM OPENBRACE)
%> 	  name <- zschema_name
%> 	  tok (L_SYM CLOSEBRACE)
%> 	  -- TODO: add generic formals
%> 	  decls <- zdecl_part
%> 	  ax <- opt [] (do {optnls; tok (L_SYM WHERE); cut; optnls; zaxiom_part })
%> 	  optnls
%> 	  tok L_END_SCHEMA
%> 	  return [ZSchemaDef name (ZSchema (concat decls ++ ax))]


\end{haskell}
\begin{haskell}

> zmachine_box :: EParser ZToken [ZPara]
> zmachine_box = paraEnv "machine"
>                  parse_machine
>                  (\(n,s,i,o) -> [ZMachineDef{machName=n,machState=s,machInit=i,machOps=o}])

> parse_machine
>  = do tok (L_SYM OPENBRACE)
>       name <- zword
>       tok (L_SYM CLOSEBRACE)
>       -- TODO: add generic formals?
>       state <- zword
>       tok ( L_WORD "\\machineInit" )
>       init <- zword
>       tok ( L_WORD "\\machineOps" )
>       ops <- zword `sepby1` zsep
>       return (name,state,init,ops)


%>   -- Eg: \begin{machine}{foo} State \init Init \ops Op1; Op2 \end{machine}
%>   -- Note: All names must be undecorated schema names.
%>   = do  tok L_BEGIN_MACHINE
%> 	  cut
%> 	  tok (L_SYM OPENBRACE)
%> 	  name <- zword
%> 	  tok (L_SYM CLOSEBRACE)
%> 	  -- TODO: add generic formals?
%> 	  state <- zword
%> 	  tok (L_WORD "\\machineInit")
%> 	  init <- zword
%> 	  tok (L_WORD "\\machineOps")
%> 	  ops <- zword `sepby1` zsep
%> 	  tok L_END_MACHINE
%> 	  return [ZMachineDef{machName=name,
%> 			      machState=state,
%> 			      machInit=init,
%> 			      machOps=ops}]
%>

\end{haskell}
\begin{haskell}

> zgeneric_box :: EParser ZToken [ZPara]
> zgeneric_box = paraEnv "gendef"
>                  parse_zgeneric
>                  (\(d,a) -> [ZGenDef (concat d ++ a)])

> parse_zgeneric
>  = do decls <- zdecl_part
>       ax <- opt [] (do {optnls; tok (L_SYM WHERE); cut; optnls; zaxiom_part })
>       return (decls,ax)


%>   = do  tok L_BEGIN_GENDEF
%> 	  cut
%> 	  decls <- zdecl_part
%> 	  ax <- opt [] (do {optnls; tok (L_SYM WHERE); cut; optnls; zaxiom_part })
%> 	  optnls
%> 	  tok L_END_GENDEF
%> 	  return [ZGenDef (concat decls ++ ax)]
%> -- TODO Gen_Actuals

\end{haskell}
\begin{haskell}

> zdecl_part :: EParser ZToken [[ZGenFilt]]
> zdecl_part = zbasic_decl `sepby1` many1 zsep

\end{haskell}
\begin{haskell}

> zaxiom_part :: EParser ZToken [ZGenFilt]
> zaxiom_part
>   = do  ps <- zpredicate `sepby1` many1 zsep
> 	  return (map Check ps)

\end{haskell}
\begin{haskell}

> zbasic_decl :: EParser ZToken [ZGenFilt]
> zbasic_decl
>   = do  {ws <- zdecl_name `sepby1` comma;
> 	  optnls;
> 	  tok (L_SYM COLON);
> 	  optnls;
> 	  e <- zexpression;
> 	  return [Choose (make_zvar w d) e | (w,d) <- ws]} +++
>     do  {sr <- zschema_ref;
> 	  return [Include sr]}

\end{haskell}

\subsection{Parsing Expressions}


The following are the expression parsers, refer to the grammar
for a clearer view on the ordering and productions.

\begin{haskell}

> zexpression :: EParser ZToken ZExpr
> zexpression
>   = do  {e1 <- zexpression_1;
> 	 zif <- opt e1 (do {tok (L_SYM RHD);
> 	                        p <- zpredicate;
>                               tok (L_SYM LHD);
> 	                        optnls;
> 	                        e2 <- zexpression_1;
>                               return (ZIf_Then_Else p e1 e2)});
> 	 return (zif)}

\end{haskell}
\begin{haskell}

> zexpression_1 :: EParser ZToken ZExpr
> zexpression_1
>   = chainr1 zexpression_1a (do {op <- zin_gen_decor;
> 				return (infixop((ZVar op)))})
>
> zexpression_1a :: EParser ZToken ZExpr
> zexpression_1a
>   = do  {e <- (zexpression_2 1);
> 	 ce <- opt e (do {cel <- many1 (do {optnls;
> 					    tok (L_SYM CROSS);
> 					    optnls;
> 					    e2 <- zexpression_2 1;
> 					    return e2});
> 			  return (ZCross (e:cel))});
> 	 return (ce)}

\end{haskell}
\begin{haskell}

> zexpression_2 :: Int -> EParser ZToken ZExpr
> zexpression_2 7 = zexpression_2a
> zexpression_2 p
>   = chainl1 (zexpression_2 (p+1)) (do {optnls;
> 				       op <- (zin_fun_decor p);
> 				       optnls;
> 				       return (infixop (ZVar op))})
>
> infixop :: ZExpr -> ZExpr -> ZExpr -> ZExpr
> infixop op a b = ZCall op (ZTuple [a,b])
>
> zexpression_2a :: EParser ZToken ZExpr
> zexpression_2a
>   = do  {tok (L_SYM SET);
> 	  e <- zexpression_3;
> 	  return (ZCall (ZVar (make_zvar "\\power" [])) e)} +++
>     do  {e4 <- zexpression_3;
> 	  do {es <- many zexpression_3;
> 	     return (foldl1 ZCall (e4:es)) }}

\end{haskell}
\begin{haskell}

> zexpressions :: EParser ZToken [ZExpr]
> zexpressions
>   = do  {e <- zexpression;
> 	 el <- many (do {comma;
> 			 e1 <- zexpression;
> 			 return e1});
> 	 return (e : el)}

\end{haskell}
\begin{haskell}

> zexpression_3 :: EParser ZToken ZExpr
> zexpression_3 =
>    do {e <- zexpression_4;
>       psub <- opt e (do {tok (L_SYM OPENBRACKET);
>	                        e1 <- zexpression_4 `sepby1` comma;
>	                        tok (L_SYM SLASH);
>	                        v1 <- zident `sepby1` comma;
>	                        tok (L_SYM CLOSEBRACKET);
>                               return (CESub e e1 v1)});
>	return psub}

\end{haskell}
\begin{haskell}

> zexpression_4 :: EParser ZToken ZExpr
> zexpression_4
>   = do  {vn <- zvar_name; return (ZVar vn)} +++
> -- TODO Gen_Actuals
>     do  {i <- znumber; return (ZInt i)} +++
>     do  {s <- zgivenval; return (ZGiven s)} +++
>     do  {zset_exp} +++
>     do  {tok (L_SYM LANGLE);
> 	 el <- opt [] zexpressions;
> 	 tok (L_SYM RANGLE);
> 	 return (ZSeqDisplay el)} +++
>     do  {tok (L_SYM LANGLE);
>        e1 <- cAllQvar;
>        tok (L_SYM VERT);
>        pred <- zpredicate;
>        tok (L_SYM AT);
>        expr <- zexpression;
>        tok (L_SYM RANGLE);
>        return (CSeqCompre e1 pred expr)} +++
>     zexpression_4a

> zexpression_4a :: EParser ZToken ZExpr
> zexpression_4a
>   = do  {tok (L_SYM OPENPAREN);
> 	 es <- zexpressions;
> 	 tok (L_SYM CLOSEPAREN);
> 	 return (if length es == 1 then head es else ZTuple es)} +++
>     do  {tok (L_SYM OPENPAREN);
> 	 tok (L_SYM LAMBDA);
>        vlist <- zident `sepby1` comma;
>        tok (L_SYM AT);
>        e <- zexpression_1;
> 	 tok (L_SYM CLOSEPAREN);
>        return (CEEabs vlist e)} +++
>     do  {sr <- zschema_ref;
> 	 return (ZESchema sr)}

\end{haskell}
\begin{haskell}

> zset_exp ::  EParser ZToken ZExpr
> zset_exp
>   = do  {tok (L_SYM OPENSET);
> 	 el <- opt [] zexpressions;
> 	 tok (L_SYM CLOSESET);
> 	 return (ZSetDisplay el) } +++
>     do  {tok (L_SYM OPENSET);
>        e1 <- cAllQvar;
>        tok (L_SYM VERT);
>        pred <- zpredicate;
>        tok (L_SYM AT);
>        expr <- zexpression;
>        tok (L_SYM CLOSESET);
>        return (CSetComp e1 pred expr)}
>
> altzbasic_decl :: EParser ZToken [ZGenFilt]
> altzbasic_decl
>   = do  {ws <- zdecl_name `sepby1` comma;
> 	  return [AltChoose (make_zvar w d) | (w,d) <- ws]}

\end{haskell}

\subsection{Parsing Predicates}

Predicate parsers, see grammar for productions.

\begin{haskell}

> zpredicate :: EParser ZToken ZPred
> zpredicate
>   = do  {tok (L_SYM FORALL);
> 	 st <- cAllQvar;
> 	 optnls;
> 	 tok (L_SYM AT);
> 	 optnls;
> 	 p <- zpredicate;
> 	 return (ZForall st p)} +++
>     do  {tok (L_SYM EXISTS);
> 	 st <- cAllQvar;
> 	 optnls;
> 	 tok (L_SYM AT);
> 	 optnls;
> 	 p <- zpredicate;
> 	 return (ZExists st p)} +++
>     do  {tok (L_SYM EXISTS1);
> 	 st <- cAllQvar;
> 	 tok (L_SYM AT);
> 	 optnls;
> 	 p <- zpredicate;
> 	 return (ZExists_1 st p)} +++
>    do  {tok (L_SYM OPENBRACKET);
>        p <- zpredicate;
>        tok (L_SYM CLOSEBRACKET);
>        return (CUniv p)} +++ zpredicate_1

\end{haskell}
\begin{haskell}

> zpredicate_1 :: EParser ZToken ZPred
> zpredicate_1 =
>    do  {e1 <- zpredicate_2;
> 	 pif <- opt e1 (do {optnls;
> 	                   tok (L_SYM LHD);
> 	                   optnls;
> 	                   c <- zpredicate_2;
> 	                   optnls;
> 	                   tok (L_SYM RHD);
> 	                   optnls;
> 	                   e2 <- zpredicate_2;
>                          return (CIfThenElse c e1 e2)});
>       return pif}

\end{haskell}
Below is the parser chain for parsing expressions. 1b, 1c, 1d, 1f, 1g
are extended to handle \Circus\ base composite predicates
(Simon Dardis, Summer  2008).
\begin{haskell}

> zpredicate_2 :: EParser ZToken ZPred
> zpredicate_2 =
>     do {tok (L_SYM ELAMBDA);
>        names <- zident `sepby1` comma;
>        tok (L_SYM AT);
>        p <- zpredicate;
>        return (CEabs names p)}+++
>     do {tok (L_SYM PLAMBDA);
>        names <- zident `sepby1` comma;
>        tok (L_SYM AT);
>        p <- zpredicate;
>        return (CPabs names p)} +++ zpredicate_3

\end{haskell}
\begin{haskell}

> zpredicate_3 :: EParser ZToken ZPred
> zpredicate_3
>   = chainl1 zpredicate_3a (do {optnls; tok (L_SYM IFF); optnls; return ZIff})
>
> zpredicate_3a :: EParser ZToken ZPred
> zpredicate_3a
>   = chainr1 zpredicate_3b (do {optnls; tok (L_SYM IMPLIES); optnls; return ZImplies})
>
> zpredicate_3b :: EParser ZToken ZPred
> zpredicate_3b
>   = chainr1 zpredicate_3c (do {optnls; tok (L_SYM SEQ); optnls; return CSeqComp})
>
> zpredicate_3c :: EParser ZToken ZPred
> zpredicate_3c
>   = chainl1 zpredicate_3d (do {optnls; tok (L_SYM LOR); optnls; return ZOr} +++
> 				do {optnls; tok (L_SYM NDETC); optnls; return CIntChoice})
>
> zpredicate_3d :: EParser ZToken ZPred
> zpredicate_3d
>   = chainl1 zpredicate_3g (do {optnls; tok (L_SYM LAND); optnls; return ZAnd} +++
> 				do {optnls; tok (L_SYM EC); optnls; return CExtChoice} +++
> 				do {optnls; tok (L_SYM GUARD); optnls; return CGuard})
>
> zpredicate_3g :: EParser ZToken ZPred
> zpredicate_3g
>    = do {p <- zpredicate_4;
>         ph <- opt p (do {p2 <- zpredicate_u;
>                                return (CHPred p p2)});
>         return ph}

\end{haskell}

\texttt{zpredicate\_1h} is a parser for predicates that have a substitution attached
(Simon Dardis, Summer 2008).

\begin{haskell}

> zpredicate_4 :: EParser ZToken ZPred
> zpredicate_4
>   = (do	{p <- zpredicate_5;
>		sub <- opt p (do  {tok (L_SYM OPENBRACKET);
>                                 e1 <- zexpression `sepby1` comma;
>                                 tok (L_SYM SLASH);
>                                 v1 <- zident `sepby1` comma;
>                                 tok (L_SYM CLOSEBRACKET);
>                                 return (CSub p e1 v1)});
>		return sub})

\end{haskell}
\begin{haskell}

> zpredicate_5 :: EParser ZToken ZPred
> zpredicate_5
>    =  do {tok (L_SYM LNOT);
> 	   p <- zpredicate;
> 	   return (ZNot p)} +++ zpredicate_u

\end{haskell}
\begin{haskell}

> zpredicate_u :: EParser ZToken ZPred
> zpredicate_u
>     =  do  {e1 <- zexpression;
> 	   es <- opt [] (many1 (do {optnls;
> 			    r <- zaltrel;
> 			    optnls;
> 			    e2 <- zexpression;
> 			    return (r,e2)}));
> 	   return (CObs e1 es)} +++
>       do  {tok (L_SYM PTRUE); return ztrue} +++
>       do  {tok (L_SYM PFALSE); return zfalse} +++
>       do  {tok (L_SYM OPENPAREN);
> 	   p <- zpredicate;
> 	   tok (L_SYM CLOSEPAREN);
> 	   return p}

\end{haskell}
\begin{haskell}

> it_pred :: ZExpr -> [(ZExpr -> ZExpr -> ZPred, ZExpr)] -> ZPred
> it_pred e1 [(f,e2)]    = f e1 e2
> it_pred e1 ((f,e2):fs) = f e1 e2 `ZAnd` it_pred e2 fs

\end{haskell}
\begin{haskell}

> zlet_def :: EParser ZToken (ZVar,ZExpr)
> zlet_def
>   = do  {vn <- zvar_name;
> 	 optnls;
> 	 tok (L_SYM ABRDEF);
> 	 optnls;
> 	 e <- zexpression;
> 	 return (vn,e)}

\end{haskell}

\texttt{zrel} is a parser for handling relational tokens. The last handles
\verb"\inrel{...}" constructs.

\begin{haskell}

> zaltrel :: EParser ZToken ZVar
> zaltrel
>   = do {r <- zin_rel; return (make_zvar r [])}
>     +++
>     do tok (L_ERROR "What was L_REL ?")
>        tok (L_SYM OPENBRACE)
>        r2 <- zident
>        tok (L_SYM CLOSEBRACE)
>        return r2

\end{haskell}
\begin{haskell}

> zrel :: EParser ZToken (ZExpr -> ZExpr -> ZPred)
> zrel
>   = do  {tok (L_IN_FUN 3 "=") ; return ZEqual} +++
>     do  {tok (L_SYM IN); return ZMember} +++
>     do  {tok (L_SYM NEQ); return (\e1 e2 -> (ZNot (ZEqual e1 e2)))} +++
>     do  {tok (L_SYM NOTIN); return (\e1 e2 -> (ZNot (ZMember e1 e2)))} +++
>     do  {ir <- zin_rel_decor; return (member_of_in_rel (ZVar ir))} +++
>     do  {i <- zword; return (member_of_in_rel (ZVar (make_zvar i [])))}
>   where
>   -- Translate (x R y) into (x,y) \in R.
>   member_of_in_rel r e1 e2 = ZMember (ZTuple [e1,e2]) r

\end{haskell}
\begin{haskell}

> zvar_name :: EParser ZToken ZVar
> zvar_name
>   = do  {tok (L_SYM OPENPAREN); vn <- zop_name; tok (L_SYM CLOSEPAREN); return vn} +++
>     zident
>
> zdecl_name :: EParser ZToken ZVar
> zdecl_name = zop_name +++ zident
>
> zop_name :: EParser ZToken ZVar
> zop_name =
>   do  {tok (L_SYM UNDERSCORE);
>        is <- zin_sym_decor;
>        tok (L_SYM UNDERSCORE);
>        return is} +++
>   do  {ps <- zpre_sym_decor;
>        tok (L_SYM UNDERSCORE);
>        return ps} +++
>   do  {tok (L_SYM UNDERSCORE);
>        w <- zpost_fun;
>        d <- zdecoration;
>        return (make_zvar w d)} +++
>   do  {tok (L_SYM UNDERSCORE);
>        tok (L_SYM LIMG);
>        tok (L_SYM UNDERSCORE);
>        tok (L_SYM RIMG);
>        dec <- zdecoration;
>        return (make_zvar "\\relimg" dec)} +++
>   do  {tok (L_SYM HYPHEN);
>        dec <- zdecoration;
>        return (make_zvar "\\negate" dec)}
>
> zin_sym_decor :: EParser ZToken ZVar
> zin_sym_decor
>   = do  iop <- zin_fun_decor 0 +++ zin_gen_decor +++ zin_rel_decor
> 	  return iop
>
> zpre_sym_decor :: EParser ZToken ZVar
> zpre_sym_decor = zpre_gen_decor +++ zpre_rel_decor
>
> zident :: EParser ZToken ZVar
> zident = do {w <- zword; d <- zdecoration; return (make_zvar w d)}
>
>
> zdecoration :: EParser ZToken [ZDecor]
> zdecoration = many zstroke
>
> zstroke :: EParser ZToken ZDecor
> zstroke
>   = do  L_STROKE w <- satm "stroke expected" isStroke
> 	  return w
>     where
>     isStroke (L_STROKE _) = True
>     isStroke _            = False
>
> zword :: EParser ZToken String
> zword =
>   do L_WORD w <- satm "word expected" isWord
>      return [ x | x <- w, x /= '\\']
>   where
>   isWord (L_WORD _) = True
>   isWord _          = False

\end{haskell}
\begin{haskell}

> zpre_rel_decor :: EParser ZToken ZVar
> zpre_rel_decor
>   = do  {prs <- zpre_rel;
> 	 dec <- zdecoration;
> 	 return (make_zvar prs dec)}
>
> zpre_rel :: EParser ZToken String
> zpre_rel =
>   do (L_PRE_REL w) <- satm "pre-rel expected" isPre_Rel
>      return w
>   where
>   isPre_Rel (L_PRE_REL _)  = True
>   isPre_Rel _             = False
>
> zin_rel_decor :: EParser ZToken ZVar
> zin_rel_decor
>   = do  {irs <- zin_rel;
> 	 dec <- zdecoration;
> 	 return (make_zvar irs dec)}
>
> zin_rel :: EParser ZToken String
> zin_rel =
>   do  optnls
>       (L_IN_REL w) <- satm "in-rel expected" isIn_Rel
>       optnls
>       return w
>   where
>   isIn_Rel (L_IN_REL _)  = True
>   isIn_Rel _             = False
>
> zpost_fun_decor :: EParser ZToken ZVar
> zpost_fun_decor
>   = do  {pfs <- zpost_fun;
> 	 dec <- zdecoration;
> 	 return (make_zvar pfs dec)}
>
> zpost_fun :: EParser ZToken String
> zpost_fun =
>   do L_POST_FUN w <- satm "post-fun expected" isPost_Fun
>      return w
>   where
>   isPost_Fun (L_POST_FUN _)  = True
>   isPost_Fun _                = False
>
> zin_gen_decor :: EParser ZToken ZVar
> zin_gen_decor
>   = do  {igs <- zin_gen;
> 	 dec <- zdecoration;
> 	 return (make_zvar igs dec)}
>
> zin_gen :: EParser ZToken String
> zin_gen =
>   do  optnls
>       (L_IN_GEN w) <- satm "in-gen expected" isIn_Gen
>       optnls
>       return w
>   where
>   isIn_Gen (L_IN_GEN _)  = True
>   isIn_Gen _             = False
>
> zpre_gen_decor :: EParser ZToken ZVar
> zpre_gen_decor
>   = do  {pgs <- zpre_gen;
> 	 dec <- zdecoration;
> 	 return (make_zvar pgs dec)}
>
> zpre_gen :: EParser ZToken String
> zpre_gen =
>   do (L_PRE_GEN w) <- satm "pre-gen expected" isPre_Gen
>      return w
>   where
>   isPre_Gen (L_PRE_GEN _) = True
>   isPre_Gen _             = False

\end{haskell}
\begin{haskell}

> zin_fun_decor :: Int -> EParser ZToken ZVar
> zin_fun_decor p
>   = do  {ifs <- zin_fun p;
> 	 dec <- zdecoration;
> 	 return (make_zvar ifs dec)}
>
> zin_fun :: Int -> EParser ZToken String
> zin_fun p =
>   do {optnls;
>       (L_IN_FUN _ w) <- satm "in-fun expected" (isIn_Fun p);
>       optnls;
>       return w} +++
>   do {guard (p==4 || p==0);
>       -- p==3 is when infix - appears within expressions: x - 2
>       -- p==0 is when it appears in declarations:  _ - _ : Type
>       optnls;
>       tok (L_SYM HYPHEN);
>       optnls;
>       return ("-")}
>   where
>   isIn_Fun p2 (L_IN_FUN p _) = p == p2 || p2 == 0
>   isIn_Fun p2 _              = False
> -- calling this function with  an argument of zero will
> -- match in_fun's with any precedence value i.e. 1-6

\end{haskell}

\subsection{Parsing Types}
\Saoithin\ extension (Simon Dardis, Summer 2008)

The type grammar is loosely described as:
\begin{eqnarray*}
   Type &::=& TProd [\fun Type]
\\        &|& TProd [\pfun Type]
\\        &|& TProd [\ffun Type]
\\ TProd &::=& TFunctor [ \cross TProd ]
\\ TFunctor &::=& TBasic | \power~TBasic | \seq~TBasic
\\TBasic &::=& \Bool | \num  | t |  TFree | ( Type )
\\ TFree &::=& TVariant [ \mbox{`|'} TFree ]
\\ TVariant &::=& name \ldata Type \rdata
\end{eqnarray*}
Here $[\ldots]$ denotes an optional component.
\begin{haskell}

> ctype :: EParser ZToken ZPred

> ctype
>  = do tprod <- ctprod
>       rest tprod
>  where
>    rest t = do tok (L_SYM FUN)
>                typ <- ctype
>                return (CtFun t typ)
>             +++
>             do tok (L_SYM MAP)
>                typ <- ctype
>                return (CtMap t typ)
>             +++
>             return t

\end{haskell}
\begin{eqnarray*}
   TProd &::=& TFunctor [ \cross TProd ]
\end{eqnarray*}
\begin{haskell}

> ctprod :: EParser ZToken ZPred

> ctprod
>  = do tfunc <- ctypeFunc
>       rest tfunc
>  where
>    rest t = do tok (L_SYM CROSS)
>                tp <- ctprod
>                return (mkCtProd t tp)
>             +++
>             return t
>    mkCtProd t (CtProd ts) = CtProd (t:ts)
>    mkCtProd t tp = CtProd [t,tp]


\end{haskell}
\begin{eqnarray*}
   TFunctor &::=& TBasic | \power~TBasic | \seq~TBasic
\end{eqnarray*}
\begin{haskell}

> ctypeFunc :: EParser ZToken ZPred
> ctypeFunc = ctypeSet +++ ctypeSeq +++ ctypebasic

> ctypeSet
>  = do tok (L_SYM SET)
>       t <- ctypebasic
>       return (CtSet t)

> ctypeSeq :: EParser ZToken ZPred
> ctypeSeq
>  = do tok (L_SYM SEQ)
>       t <- ctypebasic
>       return (CtSeq t)

\end{haskell}
\begin{eqnarray*}
   TBasic &::=& \Bool | \num  | t |  TFree | ( Type )
\end{eqnarray*}
\begin{haskell}

> ctypebasic :: EParser ZToken ZPred
> ctypebasic
>  = do w <- zword; return (CtBasic (TVar w))
>    +++
>    do tok (L_SYM TARB); return (CtBasic TArb)
>    +++
>    do tok (L_SYM TENV); return (CtBasic TEnv)
>    +++
>    do tok (L_SYM BOOL); return (CtBasic TBool)
>    +++
>    do tok (L_SYM INTEGER); return (CtBasic TInteger)
>    +++
>    do L_TVARNAME e <- satm "tvarname expected" isTVARNAME
>       return (CtBasic (TVar [ x | x <- e , x /= '{', x /= '}']))
>    +++
>    ctypenested
>    +++
>    ctypefree
>  where
>    isTVARNAME (L_TVARNAME _) = True
>    isTVARNAME _ = False

\end{haskell}
\begin{eqnarray*}
   TBasic &::=& \ldots |  ( Type )
\end{eqnarray*}
\begin{haskell}

> ctypenested :: EParser ZToken ZPred
> ctypenested =
>    do { tok (L_SYM OPENPAREN);
>       e <- ctype;
>       tok (L_SYM CLOSEPAREN);
>       return e}

\end{haskell}
\begin{eqnarray*}
   TFree &::=& TVariant [ \mbox{`|'} TFree ]
\\ TVariant &::=& name \ldata Type \rdata
\end{eqnarray*}
\begin{haskell}

> ctypefree :: EParser ZToken ZPred
> ctypefree =
>  do {L_TFREENAME x <- satm "freename expected" isTFREENAME;
>     tok (L_SYM COLONCOLONEQUALS);
>     c <- many ctypefreecomp;
>     return (CtFree x c)}
>     where
>        isTFREENAME (L_TFREENAME _ )	= True
>        isTFREENAME _			= False

> ctypefreecomp :: EParser ZToken ZPred
> ctypefreecomp =
>   do {tok (L_SYM OPENPAREN);
>      n <- zident;
>      tok (L_SYM COLON);
>      t <- many ctype;
>      tok (L_SYM CLOSEPAREN);
>      return (CtFreeComp n t)}

\end{haskell}
TYPE PARSER JUNK BELOW


NOT VALID MAP TYPE SYNTAX!!!
\begin{eqnarray*}
   Type &::=& TProd [\fun Type]
\\        &|& TProd [\pfun Type]
\\        &|& TProd [\ffun Type]
\\ TProd &::=& TFunctor [ \cross TProd ]
\\ TFunctor &::=& TBasic | \power~TBasic | \seq~TBasic
\\TBasic &::=& \Bool | \num  | t |  TFree | ( Type )
\\ TFree &::=& TVariant [ \mbox{`|'} TFree ]
\\ TVariant &::=& name \ldata Type \rdata
\end{eqnarray*}
\begin{haskell}

> ctypeMap :: EParser ZToken ZPred
> ctypeMap =
>  do {tok (L_SYM OPENBRACE);
>     t1  <- ctype;
>     tok (L_IN_FUN 1 "\\mapsto");
>     t2 <- ctype;
>     tok (L_SYM CLOSEBRACE);
>     return (CtMap t1 t2)}

\end{haskell}
THIS NEEDS TO BE DONE PROPERLY.
\begin{eqnarray*}
   Type &::=& TProd [\fun Type]
\\        &|& TProd [\pfun Type]
\\        &|& TProd [\ffun Type]
\\ TProd &::=& TFunctor [ \cross TProd ]
\\ TFunctor &::=& TBasic | \power~TBasic | \seq~TBasic
\\TBasic &::=& \Bool | \num  | t |  TFree | ( Type )
\\ TFree &::=& TVariant [ \mbox{`|'} TFree ]
\\ TVariant &::=& name \ldata Type \rdata
\end{eqnarray*}
\begin{haskell}

> ctypeFun :: EParser ZToken ZPred
> ctypeFun =
>  do {t1  <- ctype;
>     tok (L_IN_GEN "\\fun");
>     t2 <- ctype;
>     return (CtFun t1 t2)}

\end{haskell}
\begin{haskell}

\texttt{cqvar} to \texttt{cAllQvar} parse all forms that the current
pretty printer produces. \texttt{cAllQvar} is the entry point.

\begin{haskell}

> cqvar :: EParser ZToken ZExpr
> cqvar =
>   do L_QVAR e <- satm "qvarname expected" isQVAR
>      return (CQVar [ x | x <- e , x /= '{', x /= '}'])
>   where
>      isQVAR (L_QVAR _) = True
>      isQVAR _          = False
>
> cqqvar :: EParser ZToken ZExpr
> cqqvar =
>   do L_QQVAR e <- satm "qqvarname expected" isQQVAR
>      return (CQQVar [ x | x <- e , x /= '{', x /= '}'])
>   where
>      isQQVAR (L_QQVAR _) = True
>      isQQVAR _          = False
>
> cqqvarlist :: EParser ZToken ZExpr
> cqqvarlist =
>   do L_QQVARLIST e <- satm "qvarlist expected" isQQVARLIST
>      return (CQQVar [ x | x <- e , x /= '{', x /= '}'])
>   where
>      isQQVARLIST (L_QQVARLIST _) = True
>      isQQVARLIST _          = False

> cAllQvar :: EParser ZToken ZExpr
> cAllQvar =
>   do { e <- zident `sepby1` comma;
>      return (CQVarlist e)}

\end{haskell}
\begin{haskell}

> znumber :: EParser ZToken ZInt
> znumber =
>   do L_NUMBER i <- satm "number expected" isNumber
>      return i
>   where
>   isNumber (L_NUMBER _) = True
>   isNumber _            = False

\end{haskell}
\begin{haskell}

> zgivenval :: EParser ZToken String
> zgivenval =
>   do L_GIVENVAL s <- satm "givenVal expected" isGivenVal
>      return s
>   where
>   isGivenVal (L_GIVENVAL _) = True
>   isGivenVal _              = False

\end{haskell}
\Saoithin\ extension (Simon Dardis, Summer 2008)
\begin{haskell}

> clawarg :: EParser ZToken String
> clawarg =
>    do L_PROPNAME s <- satm "propName expected" isLawVal
>       return [x | x <- s, x /= '{' , x /= '}']
>    where
>        isLawVal (L_PROPNAME _) = True
>        isLawVal _              = False

\end{haskell}
