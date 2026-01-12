#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the `postUpdate?` configuration option and the docstring example.
# If the Lake API experiences changes, this test and the docstring should be
# updated in tandem.

echo "root" > toolchain
echo "dep" > dep/toolchain
test_out "post-update hello w/ arguments: [get]" update
test_exp "`cat toolchain`" = dep

# Cleanup
rm -f produced.out
