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
test_out '"importArts":{"Lib' -v lean Test.lean

# Test running a file works outside the workspace and working directory
test_out '"name":"_unknown"' -v lean ../../examples/hello/Hello.lean

# Test running a library file with a `.` in its name works
test_out '"name":"Lib.«Foo.Bar»"' -v lean Lib/Foo.Bar.lean

# cleanup
rm -f produced.out
