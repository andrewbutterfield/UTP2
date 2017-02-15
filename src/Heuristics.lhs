\section{Heuristics}

\begin{code}
module Heuristics where
import Utilities
import Tables
import Datatypes
import DataText
import MatchTypes

import Data.List
\end{code}

\subsection{Match Display Heuristics}

We develop some heuristics that aid in ranking law matches,
so those most likely to be useful in a proof are presented first.
From the matching system we want the results
as a list whose elements correspond to to each of the theories searched,
topmost first. The elements identify the theory by name,
contain the relevant matching context, and a list of
the successful law matches from that theory:
\begin{code}
type TheoryMatch = (String,MatchContext,[(LawMatch,String)])
\end{code}

Ranking is a three-step process:
\begin{enumerate}
  \item pre-filter the matches to discard some
  \item apply a ranking function to the filtered matches
  \item post-process the resulting ranking list
\end{enumerate}
The first two steps work with the list of theory matches
and so know the depth of the theory when making choices.
The final step is applied to a flattened and rank-sorted list

\subsubsection{Match Pre-Filtering}

A match filter is a function that given a
law match plus context information returns a boolean
indicating if it should be kept
\begin{code}
type MatchFilter
 =    Int           -- theory depth (0 topmost)
   -> String        -- theory name
   -> MatchContext  -- theory context
   -> ( LawMatch      -- matching details
      , String        -- (full) name of matched law
      )
   -> Bool
\end{code}
We provide an filter that retains every match:
\begin{code}
passAllMatches :: MatchFilter
passAllMatches _ _ _ _ = True
\end{code}


\subsubsection{Match Ranking}

Rankings are integers,
and a ranking heuristic is a function given
a law match along with context information,
that returns a ranked match.
\begin{code}
type Rank = Int

type RankedMatch
 = ( Rank      -- ranking
   , LawMatch  -- match details
   , String    -- (full) name of matched law
   )

type RankHeuristic
 =    Int           -- theory depth (0 topmost)
   -> String        -- theory name
   -> MatchContext  -- theory context
   -> LawMatch      -- matching details
   -> String        -- (full) name of matched law
   -> RankedMatch
\end{code}

\subsubsection{Match Post-Processing}

Match post-processing simply looks at the flattened, rank-sorted
match list as a whole, and does any cutting/re-arranging it sees fit:
\begin{code}
type RankedLaws = [RankedMatch]
type LawMatches = [(RankedMatch,MatchContext)]

noMatches :: LawMatches
noMatches = []

type MatchPostProcess = LawMatches -> LawMatches

idLawMatches :: MatchPostProcess
idLawMatches = id
\end{code}

\subsubsection{Ranking}

This function takes the three heuristics functions described above
plus the theory matches,
and returns the final ranked list
\begin{code}
rankMatches :: MatchFilter
               -> RankHeuristic
               -> MatchPostProcess
               -> [TheoryMatch]
               -> LawMatches

rankMatches mfilter rank postprocess rawmatches
 =  postprocess flattened
 where
   filtered = mapF mfilter 0 rawmatches
   ranked = mapH rank 0 filtered
   flattened = reverse $ foldl (ltmerge compare) [] $ ranked

   mapF _ _ [] = []
   mapF f d ((thnm,mctxt,mtches):rest)
    = (thnm,mctxt,filter (f d thnm mctxt) mtches) : mapF f (d+1) rest

   mapH _ _ [] = []
   mapH h d ((thnm,mctxt,mtches):rest)
    = sort (mapH' (h d) thnm mctxt mtches) : mapH h (d+1) rest
   mapH' h thnm mctxt [] = []
   mapH' h thnm mctxt ((mtch,lnm):rest)
    = (h thnm mctxt mtch lnm,mctxt) : mapH' h thnm mctxt rest

-- end rankMatches
\end{code}

Nice to report on matches:
\begin{code}
matchReport ms = showCount "Match" "es" ms
\end{code}



\newpage
\subsection{Match Filters}


\subsubsection{Match-Type Filtering}

This function will filter out the list to a specific match,
 i.e \texttt{LEqv} or \texttt{REqv}.
Will not filter out \texttt{True} or \texttt{False} though, so it is safe to use
\begin{code}
matchTypeFilterIn :: [MatchType] -> MatchFilter
matchTypeFilterIn mtypes d thname mctxt ((mtype, prov, bind, lsc, pred), lname)
 | pred == [TRUE]   =  True
 | pred == [FALSE]  =  True
 | otherwise        =  mtype `elem` mtypes

matchOnlyAll    = matchTypeFilterIn [All]
matchOnlyLEqv   = matchTypeFilterIn [LEqv]
matchOnlyREqv   = matchTypeFilterIn [REqv]
matchOnlyAnte   = matchTypeFilterIn [Ante]
matchOnlyCnsq   = matchTypeFilterIn [Cnsq]
matchOnlyLCEqv  = matchTypeFilterIn [LCEqv]
matchOnlyRCEqv  = matchTypeFilterIn [RCEqv]
matchOnlyTREqv  = matchTypeFilterIn [TREqv]

matchTypeFilterOut :: [MatchType] -> MatchFilter
matchTypeFilterOut mtypes _ _ _ ((mtype, _, _, _, pred), _)
 | pred == [TRUE]   =  True
 | pred == [FALSE]  =  True
 | otherwise        =  not (mtype `elem` mtypes)

matchNotTREqv  = matchTypeFilterOut [TREqv]
\end{code}

\newpage
\subsection{Ranking Heuristics}

\subsubsection{Predicate/Expression Sizing}
``Size'' is simply a measure of the depth and leafiness
of the predicate trees. Many heuristics will want
to use this measure as a base for their calculations.

\paragraph{Predicates}
\begin{code}
predSize TRUE                = 0
predSize FALSE               = 0
predSize (Obs e)           = 2
predSize (TypeOf e t)      = 4 + exprSize e
predSize (Defd e)          = 2 + exprSize e
predSize (Not pr)            = 2 + predSize pr
predSize (And prs)           = 2 + psSize prs
predSize (Or prs)            = 2 + psSize prs
predSize (Imp pr1 pr2)       = 3 + psSize [pr1,pr2]
predSize (NDC pr1 pr2)       = 3 + psSize [pr1,pr2]
predSize (RfdBy pr1 pr2)     = 3 + psSize [pr1,pr2]
predSize (Eqv pr1 pr2)       = 6 + (psSize [pr1,pr2])
predSize (If prc prt pre )   = 6 + psSize [prc,prt,pre]
predSize (Forall _ qs pr)      = 10 + qSize qs + predSize pr
predSize (Exists _ qs pr)      = 10 + qSize qs + predSize pr
predSize (Exists1 _ qs pr)     = 10 + qSize qs + predSize pr
predSize (Univ _ pr)           = 3 + predSize pr
predSize (Sub pr sub)        = 4 + predSize pr + sSize sub
predSize (Psub pr sub)       = 5 + predSize pr + sSize sub
predSize (Lang s p les ss)   = 1 -- want to encourage language matches
predSize (Pvar s)            = 2
predSize (Ppabs qs pr)       = 5 + qSize qs + predSize pr
predSize (Papp prf pra)      = 3 + psSize [prf,pra]
predSize (Psapp pr spr)      = 5 + predSize pr + psetRank spr
predSize (Psin pr spr)       = 5 + predSize pr + psetRank spr
predSize (Pforall qs pr)     = 10 + qSize qs + predSize pr
predSize (Pexists qs pr)     = 10 + qSize qs + predSize pr
predSize (Peabs qs pr)       = 5 + qSize qs + predSize pr
predSize _                   = 20
\end{code}

\paragraph{Predicate Sets}
\begin{code}
psetRank (PSName _)          =  2
psetRank (PSet prs)          =  2 + psSize prs
psetRank (PSetC qs pr1 pr2)  =  4 + qSize qs + psSize [pr1,pr2]
psetRank (PSetU s1 s2)       =  4 + psetRank s1 + psetRank s2
\end{code}

\paragraph{Expressions}
\begin{code}
exprSize T               = 1
exprSize F               = 1
exprSize (Num i)         = 2
exprSize (Var s)         = 2
exprSize (App s e)       = 2 + exprSize e
exprSize (Equal e1 e2)   = 2 + esSize [e1,e2]
exprSize (The _ x pr)      = 12 + predSize pr
exprSize (Eabs _ qs e)     = 2 + qSize qs + exprSize e
exprSize (Esub e sub)    = 2 + exprSize e + sSize sub
exprSize _               = 20
\end{code}
\paragraph{Bits and Pieces}
\begin{code}
psSize = sum . (map predSize)

esSize = sum . (map exprSize)

qSize (Q vs)  =  2 + length vs

sSize (Substn sub) = length sub
\end{code}

\subsubsection{RankHeuristic 1: simplicity/specificity}

This heuristic is a ranking of matches
based on simplicity and specificity.
Special prefixes get a fixed low (good) ranking,
while the others are ranked based on their contents
\begin{code}
hDsThenSimplicity depth thnm mctxt mtch lname
 | specialPrefix == "DEF"  =  (-1            ,mtch,lname)
 | specialPrefix == "DOD"  =  (-1            ,mtch,lname)
 | otherwise               =  (rankCS mtch,mtch,lname)
 where
   specialPrefix = take 3 lname
\end{code}
We rank the first replacement predicate,
and then apply modifiers for the match type and provenance.
\begin{code}
rankCS (mtyp,_,_,_,preds)
  = negate $ typeRank mtyp $ predSize $ head preds
\end{code}
Basically we put \texttt{TREqv} matches very low in the pecking order.
\begin{code}
typeRank TREqv rank = 50 * rank
typeRank All   rank = rank
typeRank _     rank = 2 * rank
\end{code}



\newpage
\subsubsection{RankHeuristic 2: equalit\'e, fraternit\'e, \ldots }

All matches are born equal:
\begin{code}
hEquality depth thnm mctxt mtch lname = (1,mtch,lname)
\end{code}

\subsubsection{RankHeuristic 3: top-most Theory}


RankHeuristic that favours theories from the top of the stack
i.e from the one we are currently working.
For now it also
favours the simplest within a theory.
\begin{code}
hTeoric depth thnm mctxt mtch lname
    | depth == 0 =  (((rankCS mtch)+100),mtch,lname)
    | depth == 1 =  (((rankCS mtch) + 50),mtch,lname)
    | otherwise =   (rankTeoric mtch, mtch, lname)
\end{code}

modifiedVersion of \texttt{rankCS}, it's necessary for Teoric to
allow for Trues and Falses to rank higher, then most.
It just gives very high numbers to singleton Trues and Falses
\begin{code}
rankTeoric (mtyp,_,_,_,preds)
  | preds == [TRUE] =  (100)
  | preds == [FALSE] = (100)
  | otherwise = negate $ typeRank mtyp $ predSize $ head preds
\end{code}

\subsubsection{RankHeuristic 4: complexity}


Heurisitic that organises the most complex items first.
It's basically going to be the reverse of the simplicity
heurisitic, except it doesn't favour any items. It of course
still needs to put true and false at the top.
\begin{code}
hExpansion depth thnm mctxt mtch lname
    | rank >= 30  = (rank, mtch, lname)
    | otherwise =   (negate rank, mtch, lname)
    where rank = rankComplex mtch
          rankComplex (mtyp,_,_,_,preds)
           | preds == [TRUE] =  (100)
           | preds == [FALSE] = (100)
           | otherwise = typeRank mtyp $ predSize $ head preds
\end{code}






\newpage
\subsection{Post Processing}


\subsubsection{Post-processing 1: top'n'tail}

This function shows the top $n$ and bottom $n$ of a list
Handy for those proofs that tend to put out a lot of items
\begin{code}
topAndTailed :: Int -> MatchPostProcess
topAndTailed number list = if  xs == ys then xs else xs ++ ys
 where
   xs =  take number $ filter treqv list
   ys =  reverse $ take number $ reverse $ filter treqv list
   treqv ((rank, lawmatch, string), mtxt) = compare lawmatch
            where compare (mtype, prov, bind, lsc, pred) =
                   if mtype /= TREqv then True else False

topAndTailed3  =  topAndTailed 3
topAndTailed4  =  topAndTailed 4
topAndTailed5  =  topAndTailed 5
\end{code}

\subsubsection{Post-processing 2: remove duplicates}

Removing Duplicates, new plan is to remove them after they
have been ranked, logically speaking for the most part after they
are ranked similiar theorems should be beside each other, so we
should be able to remove them easily
\begin{code}
removeDuplicates :: MatchPostProcess
removeDuplicates (x:[]) = (x:[])
removeDuplicates (x1:x2:xs)
    | comparePred x1 x2 == True = x1:(removeDuplicates' (x1:xs))
    | otherwise = x1:(removeDuplicates (x2:xs))
    where   removeDuplicates' (x1:[]) = []
            removeDuplicates' (x1:x2:xs)
              | comparePred x1 x2 == True = removeDuplicates' (x1:xs)
              | otherwise = removeDuplicates (x2:xs)
            comparePred ((rank1, lawMatch1, string1), match1)
                        ((rank2, lawMatch2, string2), match2)
              = compareLaw lawMatch1 lawMatch2
             where compareLaw (matchType1, prov1, bind1, lsc1, pred1)
                              (matchType2, prov2, bind2, lsc2, pred2) =
                    if pred1 == pred2 then True else False
\end{code}

\newpage
\subsection{Heuristics Function Lists}

We provide a mechanism for the user to select between available
heuristics functions by simply listing them here with
a short name, the heuristic function,
and a explanatory text:
\begin{code}
type MatchFilterDescr = (String, MatchFilter, String)
type RankHeuristicDescr = (String, RankHeuristic, String)
type MatchPostProcessDescr = (String, MatchPostProcess, String)

availableMatchFilters :: [MatchFilterDescr]
availableMatchFilters
 = [ ( "No Trivial Equiv"
     , matchNotTREqv
     , "discard any trivial equivalences"
     )
   , ( "All Matches"
     , passAllMatches
     , "let all matches get ranked"
     )
   ]

availableRankHeuristics :: [RankHeuristicDescr]
availableRankHeuristics
 = [ (  "Topmost Theory"
      , hTeoric
      , "First in the pile, first in our heart"
     )
   , (  "Simplicity"
     ,  hDsThenSimplicity
     ,  "Favours DEF, DOD laws, then simplest outcome"
     )
   , (  "Equality"
     ,  hEquality
     ,  "All laws are equal"
     )
   , (  "Expansion"
     ,  hExpansion
     ,  "The bigger the better"
     )
   ]

availableMatchPostProcess :: [MatchPostProcessDescr]
availableMatchPostProcess
 = [ ( "No change"
     , idLawMatches
     , "display all ranked matches"
     )
   , ( "Top'n'Tail 5"
     , topAndTailed5
     , "show top and bottom 5 in ranking"
     )
   , ( "No Dups"
     , removeDuplicates
     , "remove duplicate matches"
     )
   ]

\end{code}


\subsection{Errors as Identity Functions}

Rather than using \texttt{error} for unimplemented or unexpected errors,
and so crashing the program,
we choose to flag these with the application of a predicate-transformer
whose name signals the error, but whose definition
is that of the identity predicate transformer:
\begin{eqnarray*}
  BAD\_STUFF(P) &\defs& P
\end{eqnarray*}
\begin{code}
badRank :: Rank
badRank = (-666666)

errPMrk msg pred = Papp (Pvar $ Std msg) pred
mrkPDef msg = (msg,Ppabs (qvar "P") (Pvar $ Std "P"))
markP = Pvar $ Std " P"
mrkPLaw msg = (msg,(badRank,(Eqv (errPMrk msg markP) markP,SCtrue)))

errEMrk msg e = App msg e
markE = Var $ preVar " e"
mrkELaw msg = (msg,(badRank,(Obs (Equal (errEMrk msg markE) markE),SCtrue)))
\end{code}
