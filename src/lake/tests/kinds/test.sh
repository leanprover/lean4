#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# setup directory structure
mkdir -p files
touch files/Lib.lean
echo "def main : IO Unit := pure ()" > files/exe.lean
touch files/test.txt

# Test that targets have their expected data kinds
$LAKE query-kind exe | diff -u --strip-trailing-cr <(echo filepath) -
$LAKE query-kind Lib:static | diff -u --strip-trailing-cr <(echo filepath) -
$LAKE query-kind Lib:shared | diff -u --strip-trailing-cr <(echo dynlib) -
$LAKE query-kind inFile | diff -u --strip-trailing-cr <(echo filepath) -
$LAKE query-kind inDir | diff -u --strip-trailing-cr <(echo [anonymous]) -
$LAKE query-kind pathTarget | diff -u --strip-trailing-cr <(echo filepath) -
$LAKE query-kind dynlibTarget | diff -u --strip-trailing-cr <(echo dynlib) -
