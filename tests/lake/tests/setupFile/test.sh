#!/usr/bin/env bash
source ../common.sh

./clean.sh

#---
# Test `setup-file` functionality
#---

# Test that setup-file works on a file outside the workspace and working directory
test_out '"name":"_unknown"' setup-file ../../examples/hello/Hello.lean

# Test that setup-file works on library files with a `.` in their name
# https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Foo.2E.2Elean.20works.20when.20.60import.60ed.20but.20not.20in.20vscode/near/529702293
test_out '"name":"Test.«Foo.Bar»"' setup-file Test/Foo.Bar.lean

# Test that, by default, no plugins are used.
test_out '"plugins":[]' setup-file ImportFoo.lean

# Test that, by default, no dynlibs are used.
test_out '"dynlibs":[]' setup-file ImportFoo.lean

# Test that local imports are pre-resolved.
test_out '"importArts":{"Test":["' setup-file ImportTest.lean

# Test that external imports are left unhandled.
test_out '"importArts":{}' setup-file ImportFoo.lean

# Test that, generally, no options are set.
test_out '"options":{}' setup-file ImportFoo.lean

# Test that a more specific configuration will be used if
# Lake can identify the module corresponding to the path.
test_out '"options":{"weak.foo":"bar"}' setup-file Test.lean

# Test that `setup-file` on an invalid Lean configuration file succeeds.
test_run -f invalid.lean setup-file invalid.lean

# Test that `setup-file` on a configuration file uses the Lake plugin,
# even if the file is invalid and/or is not using a `Lake` import.
test_not_out '"plugins":[]' -f invalid.lean setup-file invalid.lean

# Test that when a header is provided (via CLI or stdin),
# it will be used instead of the file's header for an external module.
test_out '"isModule":false' setup-file ImportFoo.lean
HEADER_JSON='{"isModule":true,"imports":[]}'
test_out '"isModule":true' setup-file ImportFoo.lean "$HEADER_JSON"
echo "$HEADER_JSON" | test_out '"isModule":true' setup-file ImportFoo.lean -
BOGUS_JSON='{"isModule":false,"imports":[{"module":"Test.Bogus","isMeta":false,"isExported":true,"importAll":false}]}'
test_err 'no such file or directory' setup-file ImportFoo.lean "$BOGUS_JSON"

# Test that when a header is provided (via CLI or stdin),
# the header is used for an internal module and its imports are built.
test_out '"isModule":false' setup-file Test.lean
test_out '"isModule":true' setup-file Test.lean "$HEADER_JSON"
echo "$HEADER_JSON" | test_out '"isModule":true' setup-file Test.lean -
test_err 'no such file or directory' setup-file Test.lean "$BOGUS_JSON"

# Cleanup
rm -f produced.out
