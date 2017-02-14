{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Graphics.UI.Abstract where

-- |A GUI consists of a collection of types and operations between them. These
-- types include the monad in which the GUI is built and things like windows.
-- Type variables:
--     m: monad in which a GUI runs
--     w: a window
--     e: an element
class Monad m => GUI m w e | m -> w e where
    gButton  :: String -> m e
    gAdd     :: e -> [e] -> m e
    gGetBody :: w -> m e
    gLift    :: e -> m e -- TODO remove
    gRunIn   :: w -> m a -> IO a

