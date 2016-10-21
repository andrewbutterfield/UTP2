\section{Representation of Programs}
\begin{code}
module Program where
import Graphics.UI.WX
import Graphics.UI.WXCore
\end{code}

Representation of Programs in the proof assistant
\begin{code}
data Program = Program { ptext :: String
                       , pid  :: String
                       , prname :: String
                       , pthname :: String
                       }

instance Show Program where
  show prog = pid prog ++ " (" ++ prname prog ++ ")"

data ProgramGUI = ProgramGUI { progFrame :: Frame ()
                             , autosaveProg :: Bool
                             }

data ProgramSpace = ProgramSpace { progGUI :: ProgramGUI
                                 , prog :: Program
                                 }

progSetf f recd = recd{ prog = f $ prog recd}

instance Show ProgramSpace where
  show progsp = (pid $ prog progsp) ++ " (" ++ (prname $ prog progsp) ++ ")"
\end{code}

A program consists of the text of the program,
a unique program identifier, and a name and theory name.
Programs need to be represented at the top level
so that they can appear in an "Active Programs"
view, similar to "Active Proofs". What's actually
represented, though, is the entire state of work
in progress on a program, including the editing window,
which I've called the program space, borrowing from
the concept of the proof space.
\begin{code}
mkProgram progid prgname prgthname = Program { ptext = "", pid = progid, prname = prgname, pthname = prgthname}
--create a Program

ptextSetf f prog = prog{ ptext = f $ ptext prog }
\end{code}
