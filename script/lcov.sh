#!/bin/bash
CXX=g++
GCOV_TOOL=gcov

rm -rf build
mkdir -p build/testcov
cd build/testcov
cmake -DCMAKE_BUILD_TYPE=TESTCOV -DCMAKE_CXX_COMPILER=$CXX -G Ninja ../../src
ninja
ctest
lcov -c -b ../../src -d . -o cov.info --no-external --gcov-tool $GCOV_TOOL
lcov --remove cov.info "tests/*" -o cov.info
genhtml cov.info --output-directory lcov
cd ../../
