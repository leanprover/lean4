#!/usr/bin/env bash
set -euxo pipefail

./clean.sh

LAKE=${LAKE:-../../build/bin/lake}

# test that directory information is preserved during glob recursion
# see https://github.com/leanprover/lake/issues/102

$LAKE build TBA
test -f build/lib/TBA.olean
test -f build/lib/TBA/Eulerian.olean
test -f build/lib/TBA/Eulerian/A.olean

# test that globs capture modules with non-Lean names
# see https://github.com/leanprover/lake/issues/174

# also test that globs capture files in directories without a corresponding `.lean` file
# see https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20build.20all/near/370788618

$LAKE build Test
test -f build/lib/Test/1.olean
test -f build/lib/Test/Subtest/1.olean

