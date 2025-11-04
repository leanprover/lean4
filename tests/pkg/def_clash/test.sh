#!/usr/bin/env bash

# The test covers the behavior of transitively importing multiple modules
# that have a definition with the same name.

# The native symbols Lean emits are prefixed with a package identifier
# received from Lake. Thus, symbol clashes should not occur between packages.
# However, they can still occur within them.

# Related Issues:
# https://github.com/leanprover/lean4/issues/222

# In the example in this directory, packages `fooA` and `fooB` both define `foo`.
# `useA` privately imports and uses `fooA`, and `useB` private imports and uses
# `fooB`. The executable `TestUse` then imports and uses `useA` and `useB`.

# Similarly, modules `Test.BarA` and `Test.BarB` both define `bar`.
# Modules `UseBarA` and `UseBarB` use them (privately), and `TestLocalUse`
# imports both.

source ../../lake/tests/common.sh

./clean.sh

# Test the behavior when multiple copies of the same definition (`foo`)
# are seen by Lean (e.g., via importing two modules which define them).
test_err "environment already contains 'foo'" build TestFoo

# Test the behavior when multiple copies of the same definition (`foo`) exist
# in different packages but are not visible to any one module.
test_out "fooA; fooB" exe TestUse

# Test the behavior when multiple copies of the same definition (`foo`) exist
# in the same package but are not visible to any one module.
test_err "lp_test_bar" build TestLocalUse
