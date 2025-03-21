#!/usr/bin/env bash
set -euxo pipefail

./clean.sh

LAKE=${LAKE:-../../.lake/build/bin/lake}

# test that directory information is preserved during glob recursion
# see https://github.com/leanprover/lake/issues/102

$LAKE build TBA
test -f .lake/build/lib/lean/TBA.olean
test -f .lake/build/lib/lean/TBA/Eulerian.olean
test -f .lake/build/lib/lean/TBA/Eulerian/A.olean
rm -rf .lake
$LAKE -f lakefile.toml build TBA
test -f .lake/build/lib/lean/TBA.olean
test -f .lake/build/lib/lean/TBA/Eulerian.olean
test -f .lake/build/lib/lean/TBA/Eulerian/A.olean

# test that globs capture modules with non-Lean names
# see https://github.com/leanprover/lake/issues/174

# also test that globs capture files in directories without a corresponding `.lean` file
# see https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20build.20all/near/370788618

$LAKE build Test
test -f .lake/build/lib/lean/Test/1.olean
test -f .lake/build/lib/lean/Test/Subtest/1.olean
rm -rf .lake
$LAKE -f lakefile.toml build Test
test -f .lake/build/lib/lean/Test/1.olean
test -f .lake/build/lib/lean/Test/Subtest/1.olean
