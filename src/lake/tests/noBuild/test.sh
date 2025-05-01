#!/usr/bin/env bash
source ../common.sh

# Tests that Lake properly exits before normal builds occur
# when `--no-build` is passed on the command line.

./clean.sh

NO_BUILD_CODE=3

# Test `--no-build` for setup-file and module builds (`buildUnlessUpToDate`)
echo "# TEST: --no-build setup-file & modules"
test_status $NO_BUILD_CODE setup-file bogus Test --no-build
test ! -f .lake/build/lib/lean/Test.olean
test_run build Test
test -f .lake/build/lib/lean/Test.olean
test_run setup-file bogus Test --no-build

# Test `--no-build` for file builds (`buildFileUnlessUpToDate`)
echo "# TEST: --no-build file"
test_status $NO_BUILD_CODE build +Test:c.o.export --no-build
test ! -f .lake/build/ir/Test.c.o.export
test_run build +Test:c.o.export
test -f .lake/build/ir/Test.c.o.export
test_run build +Test:c.o.export --no-build

# cleanup
rm -f produced.out
