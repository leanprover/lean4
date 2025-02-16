#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# Tests aspects of Lake tracing
# ---

# Tests that a build produces a trace
test ! -f .lake/build/lib/lean/Foo.trace
$LAKE build | grep --color "Built Foo"
test -f .lake/build/lib/lean/Foo.trace

# Tests that a proper trace prevents a rebuild
$LAKE build --no-build

# Tests that Lake accepts pure numerical traces
if command -v jq > /dev/null; then # skip if no jq found
  jq -r '.depHash' .lake/build/lib/lean/Foo.trace > .lake/build/lib/lean/Foo.trace.hash
  mv .lake/build/lib/lean/Foo.trace.hash .lake/build/lib/lean/Foo.trace
  $LAKE build --no-build
fi

# Tests that removal of the trace does not cause a rebuild
# (if the modification time of the artifact is still newer than the inputs)
rm .lake/build/lib/lean/Foo.trace
$LAKE build --no-build

# Tests that an invalid trace does cause a rebuild
touch .lake/build/lib/lean/Foo.trace
$LAKE build | grep --color "Built Foo"
$LAKE build --no-build
