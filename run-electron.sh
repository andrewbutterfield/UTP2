#!/bin/bash

npm install
stack build
./node_modules/.bin/electron electron.js
