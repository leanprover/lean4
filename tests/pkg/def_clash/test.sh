#!/usr/bin/env bash

# Tests the behavior of transitively importing multiple modules
# that define the same symbol.

# Currently, if two packages define the same Lean symbol (e.g., `foo`)
# they cannot be in the same transitive import graph, even if the no module
# can see both instances of the symbol.

# In the example in this directory, `fooA` and `fooB` both define `foo`.
# `useA` privately imports and uses `fooA`, and `useB` private imports and uses
# `fooB`. When `TestUse` imports `useA` and `useB`, the linker will complain
# even though the Lean file does not see both `foo` definitions.

# See also https://github.com/leanprover/lean4/issues/222

source ../../lake/tests/common.sh

./clean.sh

# Test the behavior when multiple copies of the same definition (`foo`)
# are seen by Lean (e.g., via importing two modules which define them).
test_err "environment already contains 'foo'" build TestFoo

# Test the behavior when multiple copies of the same definition (`foo`) exist
# but are not visible to any one module: a symbol clash between the two `foo`s.
test_err "l_foo" build TestUse
