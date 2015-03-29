#!/bin/bash
CXX=$1
GCOV_TOOL=$2
LCOV=~/bin/lcov
GENHTML=~/bin/genhtml

rm -rf build
mkdir -p build/testcov
cd build/testcov
cmake -DCMAKE_BUILD_TYPE=TESTCOV -DCMAKE_CXX_COMPILER="$CXX" ../../src
make
ctest
"$LCOV" -c -b ../../src -d . -o cov.info --no-external --gcov-tool "$GCOV_TOOL"
"$LCOV" --remove cov.info "tests/*" -o cov.info
"$GENHTML" cov.info --output-directory lcov
cd ../../
