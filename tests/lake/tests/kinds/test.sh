#!/usr/bin/env bash
source ../common.sh
./clean.sh

# setup directory structure
echo "# SETUP"
set -x
mkdir -p files
touch files/Lib.lean
echo "def main : IO Unit := pure ()" > files/exe.lean
touch files/test.txt
set +x

# Test that targets have their expected data kinds
echo "# TEST: Target query kinds"
test_eq "filepath" query-kind exe
test_eq "filepath" query-kind Lib:static
test_eq "dynlib" query-kind Lib:shared
test_eq "filepath" query-kind inFile
test_eq "[anonymous]" query-kind inDir
test_eq "filepath" query-kind pathTarget
test_eq "dynlib" query-kind dynlibTarget
