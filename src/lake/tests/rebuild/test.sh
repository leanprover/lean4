#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests that Lake rebuilds C files and relinks executables on changes
# See https://github.com/leanprover/lake/issues/75

# The exact issue is no longer applicable as Lake now always rebuilds C files
# with the other `lean` artifacts but the test is still nice to have

test_cmd mkdir -p Foo
echo $'def a := "a"' > Foo/Test.lean
echo $'import Foo.Test def hello := a' > Foo.lean
test_run build
test_cmd_eq "Hello, a!" ./.lake/build/bin/foo
echo $'def b := "b"' > Foo/Test.lean
echo $'import Foo.Test def hello := b' > Foo.lean
test_run build Foo
test_run build
test_cmd_eq "Hello, b!" ./.lake/build/bin/foo

# Cleanuo
rm -f produced.out
