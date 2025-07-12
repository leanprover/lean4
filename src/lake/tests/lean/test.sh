#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test running a Lean file works and builds its imports
test_out 'Hello from the library foo!' lean Test.lean
test_exp -f .lake/build/lib/lean/Lib.olean

# Test running a main function of a Lean file
test_out 'Hello Bob!' lean Test.lean -- --run Test.lean Bob

# Test that Lake uses module-specific configuration
# if the source file is a module in the workspace
test_out '"options":{"weak.foo":"bar"}' -v lean Lib/Basic.lean

# Test that imported workspace modules are pre-resolved
# for both other workspace modules and external files
test_out '"importArts":{"Lib.Basic":["' -v lean Lib.lean
test_out '"importArts":{"Lib.Basic":["' -v lean Test.lean

# Test running a file works outside the workspace and working directory
test_out '"name":"_unknown"' -v lean ../../examples/hello/Hello.lean

# cleanup
rm -f produced.out
