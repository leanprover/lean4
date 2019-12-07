#!/usr/bin/env bash
set -e
mkdir build
cd build
eval cmake ../src $CMAKE_OPTIONS
cmake --build . -j4
cpack
