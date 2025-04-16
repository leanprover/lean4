#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test running a Lean file works and builds its imports
test_out 'Hello from the library foo!' lean Test.lean

set -x
test -f .lake/build/lib/lean/Lib.olean
set +x

# Test running a main function of a Lean file
test_out 'Hello Bob!' lean Test.lean -- --run Test.lean Bob

# Test that Lake uses module-specific configuration
# if the source file is a module in the workspace
test_out '-Dweak.foo="bar"' -v lean Lib/Basic.lean
