#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Tests that the order in which libraries are declared and required
# is properly preserved and effects which configuration is used for a module.
# Later packages and libraries in the dependency tree shadow earlier ones.
# https://github.com/leanprover/lean4/issues/2548

$LAKE update -v
$LAKE build +A -v | grep --color 222000
$LAKE build +A.B -v | grep --color 333000
$LAKE build +A.B.C -v | grep --color 333000
$LAKE build +X -v | grep --color 888000 # bar
$LAKE build +Y -v | grep --color 666000 # order
$LAKE build +Z -v | grep --color 666000 # leaf from order
$LAKE exe Y | grep --color root

# Tests that `lake update` does not reorder packages in the manifest
# (if there have been no changes to the order in the configuration)
# https://github.com/leanprover/lean4/issues/2664

cp lake-manifest.json lake-manifest-1.json
$LAKE update foo
diff --strip-trailing-cr lake-manifest-1.json lake-manifest.json

# Tests that order does not change in the presence of dep manifests
$LAKE -d foo update
$LAKE -d bar update
$LAKE update
diff --strip-trailing-cr lake-manifest-1.json lake-manifest.json
