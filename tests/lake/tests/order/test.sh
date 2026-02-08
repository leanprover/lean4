#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests that the order in which libraries are declared and required
# is properly preserved and effects which configuration is used for a module.
# Later packages and libraries in the dependency tree shadow earlier ones.
# https://github.com/leanprover/lean4/issues/2548

test_run update -v
test_out 222000 -v build +A
test_out 333000 -v build +A.B
test_out 333000 -v build +A.B.C
test_out 888000 -v build +X # bar
test_out 666000 -v build +Y # order
test_out 666000 -v build +Z # leaf from order
test_out root exe Y

# Tests that `lake update` does not reorder packages in the manifest
# (if there have been no changes to the order in the configuration)
# https://github.com/leanprover/lean4/issues/2664

test_cmd cp lake-manifest.json lake-manifest-1.json
test_run update foo
test_cmd diff -u --strip-trailing-cr lake-manifest-1.json lake-manifest.json

# Tests that order does not change in the presence of dep manifests
test_run -d foo update
test_run -d bar update
test_run update
test_cmd diff -u --strip-trailing-cr lake-manifest-1.json lake-manifest.json

# Cleanup
rm -f produced.out
