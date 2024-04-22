#!/usr/bin/env bash

rm -rf .lake/build
lake build

# Check that we can compile a file which shares with the executable
# a common import using an initializer.
# Here the executable for `frontend_with_import1` imports `Frontend.Import2`.

# This is a minimisation of a situation in which we want to compile a file
# from a project (e.g. Mathlib), so that we can inject another tactic
# implemented in the same project into a goal state from the file.

# This already worked prior to lean4#2423.
lake exe frontend_with_import2 Frontend.Import1 &&

# Check that if we don't import `Frontend.Import2`, we can successfully run
#   #eval main ["Frontend.Import1"]
# in the interpreter

# This already worked prior to lean4#2423.
lake build Frontend.Main_with_eval &&

# However if `Main` has imported `Frontend.Import2`, then
#   #eval main ["Frontend.Import1"]
# fails to compile `Frontend.Import1` in the interpreter
# prior to lean4#2423.
lake build Frontend.Main_with_Import2_and_eval &&

# Compiling multiple files with a shared import with an initializer
# failed prior to lean4#2423:
lake exe frontend Frontend.Import1 Frontend.Import2
