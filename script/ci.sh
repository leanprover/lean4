#!/usr/bin/env bash
set -e
mkdir build
cd build
eval cmake ../src $CMAKE_OPTIONS
cmake --build .
# -T to create .xml file for CI display
# `<&-` to close stdin so that assertion dialog doesn't wait for input
ctest -j8 --output-on-failure --no-compress-output -T Test <&-
cpack
