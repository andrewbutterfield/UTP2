#!/bin/bash
ghc -o moduledeps ModuleDeps.hs
ls ../src/*.lhs > _lhs.log
ack -w import ../src/*.lhs > _import.log
./moduledeps