-- Build .app bundles with the cabal-macosx package
-- Modeled after the excellent documentation on
-- https://github.com/gimbo/cabal-macosx/tree/master/examples
{-# LANGUAGE CPP #-}

#if darwin_HOST_OS == 1

import Distribution.MacOSX as Mac
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo

main :: IO ()
main = defaultMainWithHooks $ simpleUserHooks
    { postBuild = Mac.appBundleBuildHook guiApps
    }

guiApps :: [MacApp]
guiApps =
    [MacApp "UTP2"
            (Just "resource/*.wav")
            Nothing
            []
            []
            DoNotChase
    ]

#else

import Distribution.Simple

main :: IO ()
main = defaultMain

#endif
