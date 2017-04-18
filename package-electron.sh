#!/bin/bash

set -eux

npm install electron-packager
npm install
stack install --local-bin-path ./build-electron
./node_modules/.bin/electron-packager . --overwrite --ignore=app --ignore=src --ignore=.stack-work
