#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Work on a copy, as the test modifies `Foo.lean`
copy_to_work lakefile.toml Foo.lean

# ---
# Tests aspects of Lake tracing
# ---

# Tests that a build produces a trace
test_exp ! -f .lake/build/lib/lean/Foo.trace
test_out "Built Foo" build
test_exp -f .lake/build/lib/lean/Foo.trace

# Tests that a proper trace prevents a rebuild
test_run build --no-build

# Tests that Lake accepts pure numerical traces
if command -v jq > /dev/null; then # skip if no jq found
  jq -r '.depHash' .lake/build/lib/lean/Foo.trace > .lake/build/lib/lean/Foo.trace.hash
  test_cmd cat .lake/build/lib/lean/Foo.trace.hash
  perl -le "print hex('$(cat .lake/build/lib/lean/Foo.trace.hash)')" > .lake/build/lib/lean/Foo.trace
  test_cmd cat .lake/build/lib/lean/Foo.trace
  test_run build --no-build
fi

# Tests that removal of the trace causes a rebuild without `--old`
test_cmd rm .lake/build/lib/lean/Foo.trace
test_run build --old --no-build
test_out "Built Foo" build
test_run build --no-build

# Tests that an invalid trace causes a rebuild without `--old`
echo > .lake/build/lib/lean/Foo.trace
test_run build --old --no-build
test_out "Built Foo" build
test_run build --no-build

# Tests that a failed build does not leave behind the previous trace
test_exp -f .lake/build/lib/lean/Foo.trace
echo 'error' > Foo.lean
test_fails build
test_exp ! -f .lake/build/lib/lean/Foo.trace
