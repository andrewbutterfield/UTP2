#!/bin/bash

set -eux

npm install
stack build
./node_modules/.bin/electron electron.js
