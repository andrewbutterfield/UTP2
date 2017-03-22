{-# LANGUAGE CPP #-}

module Compatibility where

#if __GLASGOW_HASKELL__ < 700
import System.IO.Error (try)        -- needed with 6.10
utp2try = try
#else
import System.IO.Error (tryIOError) -- needed with 7.x
utp2try = tryIOError  -- for 7.x
#endif
