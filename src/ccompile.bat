ghc  --make -fglasgow-exts -i../nicesymbols/src -XUndecidableInstances -package wx UTP2.lhs -o UTP2.exe
del *.o
del *.hi
