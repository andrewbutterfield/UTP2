module TTypes where
import Char
import List
import Maybe
import Monad
import Tables
import Datatypes
import DataText
import Utilities
import Focus
import AlphaSubs
import Matching
import FreeBound
import Types

kObs = lbuild [ ("ok",  (Model,B) )
              , ("ok'", (Model,B) )
              ]
kTypes = lbuild [ ("ok", B), ("ok'", B)
                , ("+",Tfun (Tprod [Z,Z]) Z)
                , ("<",Tfun (Tprod [Z,Z]) B)
                , ("in",Tfun (Tprod [Tvar "t",Tset $ Tvar "t"]) B)
                ]

mctxt
 = nullMatchContext
     { knownObs = [kObs]
     , knownTypes = [kTypes] 
     }

pr1 = Imp (And [Obs $ Var "ok", Obs $ Bin "<" 0 (Var "x") (Var "y")])
          (And [ Obs $ Var "ok'"
               , (Obs $ Bin "<" 0 (Num 0) (Var "y"))
               , (Obs $ Bin "<" 0 (Bin "+" 1 (Num 1) (Var "x"))
                                  (Bin "+" 1 (Num 1) (Var "y"))
                  )
               ])
(pr1',tts1,msgs1) = setPredTypes mctxt pr1
rep1 = putStrLn $ typeErrorDetails pr1' msgs1 tts1

pr2 = Imp (Forall 0 (qvar "x") $ And [Obs $ Var "ok", Obs $ Bin "<" 0 (Var "x") (Var "y")])
          (And [ Obs $ Var "ok'"
               , Exists 0 (qvar "y") (Obs $ Bin "<" 0 (Num 0) (Var "y"))
               , Forall 0 (qvars ["x","z"]) (Obs $ Bin "<" 0 (Bin "+" 1 (Num 1) (Var "x"))
                                                      (Bin "+" 1 (Num 1) (Var "y")))
               , Exists 0 (qvar "x") $ Obs $ Var "x"
               ])
(pr2',tts2,msgs2) = setPredTypes mctxt pr2
rep2 = putStrLn $ typeErrorDetails pr2' msgs2 tts2
               
pr3 = Not $ Obs $ Bin "in" 280 (Var "e1") $ Set []
(pr3',tts3,msgs3) = setPredTypes mctxt pr3
rep3 = putStrLn $ typeErrorDetails pr3' msgs3 tts3

pr4 = Eqv (Obs $ Bin "in" 280 (Var "e1") $ Set [Var "e2"])
          (Obs $ Equal (Var "e1") $ Var "e2") 
(pr4',tts4,msgs4) = setPredTypes mctxt pr4
rep4 = putStrLn $ typeErrorDetails pr4' msgs4 tts4

pr5 = And [ Obs $ Var "ok"
          , Obs $ Var "x"
          , Obs $ Bin "+" 0 (Var "y") (Var "z")
          , Obs $ Var "z"
          ]
(pr5',tts5,msgs5) = setPredTypes mctxt pr5
rep5 = putStrLn $ typeErrorDetails pr5' msgs5 tts5

pr6 = Obs $ Bin "<" 240 (Set [Var "x"])
                        $ Bin "+" 280 (Set [Var "x"]) $ Set []
(pr6',tts6,msgs6) = setPredTypes mctxt pr6
rep6 = putStrLn $ typeErrorDetails pr6' msgs6 tts6
