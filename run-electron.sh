#!/bin/bash

set -eux

npm install
stack install --local-bin-path build-electron
./node_modules/.bin/electron electron.js
