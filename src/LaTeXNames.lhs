\section{Name Handling}

\begin{code}
module LaTeXNames where
import Data.Map(fromAscList,union,findWithDefault)
import Data.List(stripPrefix)
import Data.Char
import Tables
\end{code}

As a tool mediating between an ASCII syntax, a \LaTeX\ format,
and the variable decoration and typesetting conventions
of Z and UTP, we need to have a coherent and consistent policy
regarding how names (variables, functions, predicates, etc..)
are handled.
So, for example, we might want the Z/UTP variable $tr_0$
to appear in ASCII%
\footnote{Unicode? What about Unicode?}
form as \texttt{tr0}, and in \LaTeX\ as \verb"tr_0".
However, we don't want to hardwire a convention too deeply,
so representing a variable as having a root (string?)
and a decoration components (character? string? enumeration type?)
is probably too inflexible.
Ideally, a name should be a string for generality and ease of handling
but with a number of usage conventions that facilitate translation.
Fundamentally, this amounts to defining a general translation scheme
between names as ASCII character strings and names as \TeX\ macros.
The details of this translation may differ depending on the context
in which the names occurs --- expression vs. predicate vs. observational
variables, for example --- another reason for not having too much hardwiring.

For every identified naming-context (\texttt{nmCtxt})
we shall define at least two String conversion routines,
one from ASCII to \LaTeX\ (\texttt{nmCtxt\_AtoT}),
and the other (\texttt{nmCtxt\_TtoA}) in the converse direction.
We will often also give variants for \TeX\ in text-mode (\texttt{\_T})
vs. math-mode (\texttt{\_M}).
In addition we may define some naming-context specific string functions.

In particular, we note that this module contains translations that are
not user-configurable, largely because they depend on aspects of
\TeX/\LaTeX\ over which we have no control.


\newpage
\subsection{The Verbatim Naming Context}

The Verbatim naming context (\texttt{verb}) simply assumes an ASCII name should appear
as is in the \TeX\ form, so it amounts to escaping certain characters
that have meaning to \TeX (here n.a. means not allowed, in this mode):
\begin{center}
\begin{tabular}{|c|c|c|c||c|c|c|c|}
  \hline
    ASCII & \TeX & \multicolumn{2}{|c||}{mode}
    &
    ASCII & \TeX & \multicolumn{2}{|c|}{mode}
  \\\hline
    &  & text & math
    &
    &  & text & math
  \\\hline
    \verb"$" & \verb"\$"  & $\$ $ & \$
    &
    \verb"_" & \verb"\_"  & \_& $\_$
  \\\hline
    \verb"%" & \verb"\%" & \% & $\%$
    &
    \verb"\" & \verb"{\backslash}" & n.a. &  ${\backslash}$
  \\\hline
    \verb"@" & \verb"@" & @ & $@$
    &
    \verb"@" & \verb"\mbox{@}" & \mbox{@} & $\mbox{@}$
  \\\hline
    \verb"{" & \verb"\{" & \{ & $\{$
    &
    \verb"}" & \verb"\}" & \} & $\}$
  \\\hline
    \verb"<" & \verb"<" & < & $<$
    &
    \verb">" & \verb">" & > & $>$
  \\\hline
    \verb"|" & \verb"|" & | & $|$
    &
    \verb"#" & \verb"\#" & \# & $\#$
  \\\hline
    \verb"~" & \verb"\tilde{}" & n.a.  & $\tilde{}$
    &
    \verb"&" & \verb"\&" & \& & $\&$
  \\\hline
    \verb"^" & \verb"\^{}" & \^{} & n.a.
    &
    \verb"^" & \verb"\mbox{\^{}}" & \mbox{\^{}} & $\mbox{\^{}}$
  \\\hline
    \verb"'" & \verb"'" & ' & n.a.
    &
    \verb"'" & \verb"\mbox{'}" & \mbox{'} & $\mbox{'}$
  \\\hline
    \verb'"' & \verb'"' & " & n.a.
    &
    \verb'"' & \verb'\mbox{"}' & \mbox{"} & $\mbox{"}$
  \\\hline
    \verb"`" & \verb"`" & ` & n.a.
    &
    \verb"`" & \verb"\mbox{`}" & \mbox{`} & $\mbox{`}$
  \\\hline
    space & \verb"~" & x~x & $x~x$
    &
    &&&
  \\\hline
\end{tabular}
\end{center}
We can see a need to be aware of the \TeX-mode (math or text) we are
in when translating.
Note, however, in general we will be in math mode.
Also, we do not translate most whitespace.
From the above table we abstract the following translation schema:
\begin{center}
\begin{tabular}{|c||c|c|}
  \hline
    ASCII & text \TeX\ & math \TeX\
  \\\hline
    \multicolumn{3}{c}{same translation in either mode}
  \\\hline
    \verb"$" & \verb"\$" & \verb"\$"
  \\\hline
    \verb"_" & \verb"\_" & \verb"\_"
  \\\hline
    \verb"%" & \verb"\%" & \verb"\%"
  \\\hline
    \verb"{" & \verb"\{" & \verb"\{"
  \\\hline
    \verb"}" & \verb"\}" & \verb"\}"
  \\\hline
    \verb"#" & \verb"\#" & \verb"\#"
  \\\hline
    \verb"&" & \verb"\&" & \verb"\&"
  \\\hline
    space & \verb"~" & \verb"~"
  \\\hline
    \multicolumn{3}{c}{different translation in each mode}
  \\\hline
    \verb"\" & \verb"{$\backslash$}" & \verb"{\backslash}"
  \\\hline
    \verb"~" & \verb"{$\tilde{}$}" & \verb"\tilde{}"
  \\\hline
    \verb"^" & \verb"\^{}" & \verb"\mbox{\^{}}"
  \\\hline
    \multicolumn{3}{c}{translate in text mode only}
  \\\hline
    \verb"<" & \verb"{$<$}" & \verb"<"
  \\\hline
    \verb">" & \verb"{$>$}" & \verb">"
  \\\hline~
    \verb"|" & \verb"{$|$}" & \verb"|"
  \\\hline
    \multicolumn{3}{c}{translate in math mode only}
  \\\hline
    \verb"@" & \verb"@" & \verb"\mbox{@}"
  \\\hline
    \verb"'" & \verb"'" & \verb"\mbox{'}"
  \\\hline
    \verb'"' & \verb'"' & \verb'\mbox{"}'
  \\\hline
    \verb"`" & \verb"`" & \verb"\mbox{`}"
  \\\hline
\end{tabular}
\end{center}

\newpage
\subsubsection{Verbatim ASCII to \TeX\ Translation}

We start with the ASCII to \TeX\ translation by defining
two lookup tables mapping (ASCII) characters to (\TeX) strings
\begin{code}
a2lUniform = fromAscList ulist
 where ulist  = [ ( ' ' , "~"   ), ( '#' , "\\#" ), ( '$' , "\\$" )
                , ( '%' , "\\%" ), ( '&' , "\\&" ), ( '_' , "\\_" )
                , ( '{' , "\\{" ), ( '}' , "\\}" )
                ]

a2lTextOnly = fromAscList tlist
 where tlist  = [ ( '<'  , "{$<$}" ), ( '>' , "{$>$}" )
                , ( '\\' , "{$\\backslash$}" )
                , ( '^'  , "\\^{}" ), ( '|' , "{$|$}" )
                , ( '~'  , "{$\\tilde{}$}" )
                ]

a2lMathOnly = fromAscList mlist
 where mlist  = [ ( '"' , "\\mbox{\"}"    ), ( '\'' , "\\mbox{'}" )
                , ( '@' , "\\mbox{@}"     ), ( '\\' , "{\\backslash}" )
                , ( '^' , "\\mbox{\\^{}}" ), ( '`'  , "\\mbox{`}" )
                , ( '~' , "\\tilde{}" )
                ]

a2lTextMode = a2lUniform `union` a2lTextOnly

a2lMathMode = a2lUniform `union` a2lMathOnly
\end{code}

We then create a \texttt{charMap} function that given a lookup table
returns a function on character input that returns the table string if the
input is present,
otherwise the input char itself is returned as a singleton string.
We then lift this to a function \texttt{stringMap} on strings.
\begin{code}
charMap tbl c = findWithDefault [c] c tbl

stringMap tbl = concat . (map (charMap tbl))
\end{code}

Finally, we can use these to define our first two translation
functions:
\begin{code}
verb_AtoT_T = stringMap a2lTextMode

verb_AtoT_M = stringMap a2lMathMode
\end{code}

\newpage
\subsubsection{Verbatim \TeX\ to ASCII Translation}

The reverse translation is harder,
and only works for strings formatted as per the ASCII-to-\TeX\ translation.
If we encounter something unexpected, we simply copy its characters
across, so the \TeX\ source fragment  \verb"id\back{}$1"
will be translated to ASCII as \verb"id\back{}$1",
which when then translated back to \TeX\ will turn into
\verb"id{\backslash}back\{\}\$1".

We define a function that takes a mode-specific helper
function as argument, both of which are tail recursive,
accumulating the output string fragments:
\begin{code}
verbt2a :: (Char -> [String] -> String -> String) -- modef
        -> [String]                               -- iicsa
        -> String                                 -- cs
        -> String
verbt2a modef iicsa [] = concat (reverse iicsa)
verbt2a modef iicsa (c:cs)
 | c == '~'   =  verbt2a modef (" ":iicsa) cs
 | c == '\\'  =  seenbslash modef iicsa cs
 | c == '{'   =  modef c iicsa cs
 | otherwise  =  verbt2a modef ([c]:iicsa) cs
 where
   -- seen \
   seenbslash modef iicsa [] = concat (reverse ("\\":iicsa))
   seenbslash modef iicsa macro@(c:cs)
    | c == '$'  =  verbt2a modef ("$":iicsa) cs
    | c == '_'  =  verbt2a modef ("_":iicsa) cs
    | c == '%'  =  verbt2a modef ("%":iicsa) cs
    | c == '{'  =  verbt2a modef ("{":iicsa) cs
    | c == '}'  =  verbt2a modef ("}":iicsa) cs
    | c == '#'  =  verbt2a modef ("#":iicsa) cs
    | c == '&'  =  verbt2a modef ("&":iicsa) cs
    | otherwise  =  modef '\\' iicsa macro
\end{code}

The mode-specific helpers are called if a left brace (\{)
has been seen,
or a macro that is not one of the seven uniform ones.
Its first argument is either the left brace or macro backslash.
If the first argument is a backslash
then the string argument is non-empty.

\newpage
\subsubsection{Verbatim \TeX\ to ASCII Translation (math-mode)}

In math-mode, a left-brace should be followed by \verb"backslash}",
whilst a backslash may be followed by \verb"tilde{}"
or \verb"mbox{"\ldots\verb"}",
where ``\ldots'' is one of \verb"@", \verb"'", \verb'"', \verb"`" or \verb"\^{}".
\begin{code}
verbMhelp :: Char 
          -> [String] -- iicsa
          -> String   -- cs
          -> String
          
-- seen {  expect \backslash}
verbMhelp '{' iicsa cs
 = case stripPrefix "\\backslash}"  cs of
     Nothing      ->  verbt2a verbMhelp ("{":iicsa) cs
     (Just rest)  ->  verbt2a verbMhelp ("\\":iicsa) rest

-- seen \  expect tilde{}  or  mbox{...}
verbMhelp '\\' iicsa (c:cs) -- we know string is non-empty
 | c == 't'   -- tilde case
     = case stripPrefix "ilde{}"  cs of
         Nothing      ->  verbt2a verbMhelp ("\\t":iicsa) cs
         (Just rest)  ->  verbt2a verbMhelp ("~":iicsa) rest
 | c == 'm'   -- mbox case
     = case stripPrefix "box{"  cs of
         Nothing      ->  verbt2a verbMhelp ("\\m":iicsa) cs
         (Just rest)  ->  verbmbox iicsa rest
 | otherwise  =  verbt2a verbMhelp ("\\":iicsa) (c:cs)

-- seen \mbox{   expect  @}  \}  "}  `}  '}   or ^{}}
verbmbox iicsa [] = concat (reverse ("\\mbox{":iicsa))
verbmbox iicsa (c:cs)
  | c == '@'   =  verbmboxc c iicsa cs
  | c == '\''  =  verbmboxc c iicsa cs
  | c == '"'   =  verbmboxc c iicsa cs
  | c == '`'   =  verbmboxc c iicsa cs
  | c == '\\'
      = case stripPrefix "^{}}"  cs of
         Nothing      ->  verbt2a verbMhelp ("\\mbox{\\":iicsa) cs
         (Just rest)  ->  verbt2a verbMhelp ("^":iicsa) rest
  | otherwise  =  verbt2a verbMhelp ([c]:"\\mbox{":iicsa) cs

-- seen \mbox{x  expect }
verbmboxc x iicsa [] = concat (reverse ([x]:"\\mbox{":iicsa))
verbmboxc x iicsa (c:cs)
 = if c == '}' then verbt2a verbMhelp ([x]:iicsa) cs
               else verbt2a verbMhelp ([x]:"\\mbox{":iicsa) (c:cs)
\end{code}

We can now define the top-level verb math-mode translation:
\begin{code}
verb_TtoA_M = verbt2a verbMhelp []
\end{code}

\newpage
\subsubsection{Verbatim \TeX\ to ASCII Translation (text-mode)}

In text-mode, a left-brace should be followed by \verb"$"\ldots\verb"$}",
where ``\ldots'' is one of \verb"<", \verb">", \verb"|", \verb"\backslash"
or \verb"\tilde{}".
In the other case a backslash may be followed by \verb"^{}".
\begin{code}
verbThelp :: Char
          -> [String] -- iicsa
          -> String   -- cs
          -> String

-- seen \   expect ^{}
verbThelp '\\' iicsa cs -- we know string is non-empty
 = case stripPrefix "^{}"  cs of
     Nothing      ->  verbt2a verbThelp ("\\":iicsa) cs
     (Just rest)  ->  verbt2a verbThelp ("^":iicsa) rest

-- seen {   expect  $...$}
verbThelp '{' iicsa [] = concat (reverse ("{":iicsa))
verbThelp '{' iicsa rest@(c:cs)
 = if c == '$' then verbmint iicsa cs
               else verbt2a verbThelp ("{":iicsa) rest

-- seen {$  expect  <$}  >$}  |$}  \tilde{}$}  \backslash$}
verbmint iicsa [] = concat (reverse ("{$":iicsa))
verbmint iicsa rest@(c:cs)
 | c == '<'   =  verbmintc c iicsa cs
 | c == '>'   =  verbmintc c iicsa cs
 | c == '|'   =  verbmintc c iicsa cs
 | c == '\\'  =  verbmintm iicsa cs
 | otherwise  =  verbt2a verbThelp ("{$":iicsa) rest

-- seen {$x   expect $}
verbmintc x iicsa cs
 = case stripPrefix "$}" cs of
    Nothing  ->  verbt2a verbThelp ("{$":iicsa) (x:cs)
    (Just rest)  ->  verbt2a verbThelp ([x]:iicsa) rest

-- seen {$\  expect tilde{}$}  or  backslash$}
verbmintm iicsa [] = concat (reverse ("{$\\":iicsa))
verbmintm iicsa (c:cs)
 | c == 't'   -- tilde case
     = case stripPrefix "ilde{}$}"  cs of
         Nothing      ->  verbt2a verbThelp ("{$\\t":iicsa) cs
         (Just rest)  ->  verbt2a verbThelp ("~":iicsa) rest
 | c == 'b'   -- backslash case
     = case stripPrefix "ackslash$}"  cs of
         Nothing      ->  verbt2a verbThelp ("{$\\b":iicsa) cs
         (Just rest)  ->  verbt2a verbThelp ("\\":iicsa) rest
 | otherwise  =  verbt2a verbThelp ("{$\\":iicsa) (c:cs)
\end{code}

We can now define the top-level verbatim math-mode translation:
\begin{code}
verb_TtoA_T = verbt2a verbThelp []
\end{code}

\newpage
\subsection{The Decorated Naming Context}

Variables in UTP have a root, typically alphabetical,
and some decoration, comprising primes, numeric subscripts
and occasionally superscripts. These comprise the Decoration
naming context (\texttt{decor}).

The code at present is not robust in the sense that if
an input does not correspond to the specified grammar
we do not attempt to flag an error or fix things.

\subsubsection{Decor ASCII to \TeX}

A root contains alphanumerics, dots, and underscores.
A suffix is a decoration if it consists solely of
quotes, or digits, optionally followed by a superscript,
which is a caret followed by alphanumerics, dots and underscores.
\begin{eqnarray*}
   \langle root\rangle
   &::=&
     ( \langle alpha\rangle
     | \langle digit\rangle
     | \mbox{`.'}
     | \mbox{`\_'} )^*
\\ \langle decor\rangle
   &::=&
     \langle quote\rangle ^* | \langle digit\rangle ^*
\\ \langle super\rangle
   &::=& \mbox{`\^{}'} \langle root\rangle
\\ \langle name\rangle
   &::=& \langle root\rangle
         [ \langle decor\rangle  ]
         [ \langle super\rangle  ]
\end{eqnarray*}
First, we parse a string into possibly three subcomponents:
\emph{root}, \emph{decor} and \emph{super}.
\\
\textbf{We should reconcile this with the more recent emergence of \texttt{parseVariable}}
\begin{code}
parseAdecor = pAname ""

pAname toor ""
  = (reverse toor, "", "")
pAname toor (c:cs)
 | c == '^'   =  (reverse toor, "", cs)
 | c == '\''  =  pAquotes (reverse toor) [c] cs
 | c == '"'   =  pAquotes (reverse toor) [c] cs
 | c == '_'   =  pAname (c:'\\':toor) cs
 | isDigit c  =  pAdigits toor [c] cs
 | otherwise  =  pAname (c:toor) cs

-- seen quote, looking for more, or ^
pAquotes root roced ""
  = (root, reverse roced, "")
pAquotes root roced (c:cs)
 | c == '^'   =  (root, reverse roced, cs)
 | otherwise  =  pAquotes root (c:roced) cs

-- seen digits, looking for more, or ^; may revert
pAdigits toor stigid ""
  = (reverse toor, reverse stigid, "")
pAdigits toor stigid (c:cs)
 | c == '^'   =  (reverse toor, reverse stigid, cs)
 | isDigit c  =  pAdigits toor (c:stigid) cs
 | otherwise  =  pAname (c:(stigid++toor)) cs

\end{code}

Generating the \TeX\ is easy:
\begin{code}
decor_AtoT ascii
  = root ++ a2tdecor decor ++ a2tsuper super
  where
    (root,decor,super) = parseAdecor ascii
    a2tdecor "" = ""
    a2tdecor [c]
      = if isDigit c then ['_',c] else [c]
    a2tdecor cs@(c:_)
      = if  isDigit c  then "_{" ++ cs ++ "}" else cs
    a2tsuper "" = ""
    a2tsuper [c] = ['^',c]
    a2tsuper cs = "^{" ++ cs ++ "}"
\end{code}


\subsubsection{Decor \TeX\ to ASCII}


The \TeX\ grammar is similar:
\begin{eqnarray*}
   \langle Root\rangle
   &::=&
     ( \langle alpha\rangle
     | \langle digit\rangle
     | \mbox{`.'}
     | \mbox{`$\backslash$\_'} )^*
\\ \langle Decor\rangle
   &::=& \langle quote\rangle ^*
        | \mbox{`\_\{'}\langle digit\rangle ^* \mbox{`\}'}
\\ \langle Super\rangle
   &::=& \mbox{`\^{}\{'} \langle Root\rangle \mbox{`\}'}
\\ \langle Name\rangle
    &::=& \langle Root\rangle
          [ \langle Decor\rangle  ]
          [ \langle Super\rangle  ]
\end{eqnarray*}
Parsing this is simpler (more left-deterministic).
\begin{code}
decor_TtoA = pTname ""

pTname toor "" = reverse toor
pTname toor (c:cs)
  | c == '_'   =  pTsubs toor cs
  | c == '\\'  =  pTname toor cs -- quick fix, just ignore it
  | c == '^'   =  pTsuper toor "" cs
  | otherwise  =  pTname (c:toor) cs

-- seen _, expecting single digit or { digits }
pTsubs toor "" = reverse toor
pTsubs toor (c:cs)
  | isDigit c  =  pTname (c:toor) cs
  | c == '{'   =  pTdigits toor "" cs
  | otherwise  =  pTname toor cs -- broken, try to make sense of rest

-- seen _{, expecting  digits }
pTdigits toor stigid "" = reverse (stigid++toor)
pTdigits toor stigid (c:cs)
  | isDigit c  =  pTdigits toor (c:stigid) cs
  -- | c == '}'   =  pTsuper toor stigid cs -- can skip this!
  | otherwise  =  pTname (stigid++toor) cs -- broken

-- seen ^, expecting single char or { chars }
pTsuper toor stigid []  = reverse (stigid ++ toor)
pTsuper toor stigid [c] = reverse (c:'^':stigid++toor)
pTsuper toor stigid (c:cs)
  | c == '{'   =  pTsup toor stigid "^" cs
  | otherwise  =  pTname (c:'^':stigid ++ toor) cs -- broken

-- seen ^{, expecting .... }
pTsup toor stigid pus [] = reverse(pus++stigid++toor)
pTsup toor stigid pus (c:cs)
  | c == '}'   =  pTsup toor stigid pus cs -- ignore these
  | otherwise  =  pTsup toor stigid (c:pus) cs
\end{code}

Generating the ASCII version is very easy.



