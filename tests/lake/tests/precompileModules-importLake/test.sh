#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that precompiled modules can import Lake.
# Regression test for https://github.com/leanprover/lean4/issues/9420.
test_run -v build Foo
