ghc  --make -fglasgow-exts -XUndecidableInstances -package wx UTP2.lhs -o UTP2.exe
del *.o
del *.hi
