{-# LANGUAGE MultiParamTypeClasses #-}

module Graphics.UI.Abstract.Threepenny where

import           Graphics.UI.Abstract
import qualified Graphics.UI.Threepenny      as UI
import           Graphics.UI.Threepenny.Core

-- |Theepenny instance of abstract GUI.
instance GUI UI Window Element where
    gButton   = \t -> UI.button # set UI.text t
    gAdd e es = (element e) #+ map element es
    gGetBody  = getBody
    gLift     = element
    gRunIn    = runUI
