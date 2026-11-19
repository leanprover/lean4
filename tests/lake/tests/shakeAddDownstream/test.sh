#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the `--add-downstream` and `--add-public-downstream` options of `lake shake` (#15593)

# `shake --fix` rewrites the sources it is given, so work on a copy
copy_to_work input/*
test_run build

# Without the options, the unused private import is the only finding
lake_out shake || true
match_pat 'remove.*import Lib.Init' produced.out
no_match_text '  add ' produced.out

# Check mode reports the missing imports and fails
test_status_out 1 'add #[public import Lib.Init]' shake --add-public-downstream Lib.Init
# `Lib.Linter` is imported by `Lib.Init` and must not import it back
no_match_text '/Linter.lean' produced.out

# `--add-public-downstream`: every module must reach the module publicly
test_run shake --add-public-downstream Lib.Init --fix
test_cmd diff -u --strip-trailing-cr ../expected-public/Lib.lean Lib.lean
test_cmd diff -ru --strip-trailing-cr ../expected-public/Lib Lib
# The result builds (no import cycle) and is stable
test_run build
test_run shake --add-public-downstream Lib.Init
# Only a single module is supported
test_err 'at most one of' shake --add-downstream Lib.Init --add-public-downstream Lib.Init
test_err 'at most one of' shake --add-downstream Lib.Init --add-downstream Lib.Linter

# `--add-downstream`: reaching the module privately is sufficient
cd ..
./clean.sh
copy_to_work input/*
test_run build
test_run shake --add-downstream Lib.Init --fix
test_cmd diff -u --strip-trailing-cr ../expected-private/Lib.lean Lib.lean
test_cmd diff -ru --strip-trailing-cr ../expected-private/Lib Lib
test_run build
test_run shake --add-downstream Lib.Init

# The module must already be imported somewhere
test_err 'is not imported by any of the checked modules' shake --add-downstream Extra.Tool
