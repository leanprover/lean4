#!/usr/bin/env bash
set -e
mkdir build
cd build
eval cmake .. $CMAKE_OPTIONS
make
(cd stage0.5; cpack)
