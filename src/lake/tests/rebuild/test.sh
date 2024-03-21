#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Tests that Lake rebuilds C files and relinks executables on changes
# See https://github.com/leanprover/lake/issues/75

# The exact issue is no longer applicable as Lake now always rebuilds C files
# with the other `lean` artifacts but the test is still nice to have

mkdir -p Foo
echo $'def a := "a"' > Foo/Test.lean
echo $'import Foo.Test def hello := a' > Foo.lean
${LAKE} build
./.lake/build/bin/foo | grep -m1 a
echo $'def b := "b"' > Foo/Test.lean
echo $'import Foo.Test def hello := b' > Foo.lean
${LAKE} build Foo
${LAKE} build
./.lake/build/bin/foo | grep -m1 b
