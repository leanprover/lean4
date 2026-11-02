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

# Tests that traces with legacy 64-bit hashes cause a rebuild without a warning
# (pure numerical traces and the `2025-09-10` schema)
echo 1234 > .lake/build/lib/lean/Foo.trace
test_out "Built Foo" build
no_match_text "warning" produced.out
test_run build --no-build
echo '{"schemaVersion":"2025-09-10","depHash":"0123456789abcdef"}' > .lake/build/lib/lean/Foo.trace
test_out "Built Foo" build
no_match_text "warning" produced.out
test_run build --no-build

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
