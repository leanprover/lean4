#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Store Lake cache in a local directory
export LAKE_CACHE_DIR=

#-------------------------------------------------------------------------------
# The tests covers the (offline) use of `leantar` in Lake
#-------------------------------------------------------------------------------

# Test regular build does not produce an `ltar`
test_run build +Test -v
test_exp ! -f .lake/build/ir/Test.ltar

# Test use of `--no-build` with the `ltar` facet
test_err "archive does not exist and needs to be built" \
  build +Test:ltar --no-build -v

# Test the build of the `ltar` facet
test_run build +Test:ltar -v
test_exp -f .lake/build/ir/Test.ltar

# Test that Lake unpacks the archive if the module's artifacts are missing
test_cmd rm .lake/build/lib/lean/Test.olean
test_out "leantar" build +Test --no-build -v
test_exp -f .lake/build/lib/lean/Test.olean

# Test that Lake unpacks an modification time up-to-date archive
# when the module's artifacts and trace are missing with `--old`
test_cmd rm .lake/build/lib/lean/Test.olean .lake/build/lib/lean/Test.trace
test_fails build +Test --no-build -v
test_out "leantar" build +Test --no-build --old -v
test_exp -f .lake/build/lib/lean/Test.olean

# Test caching and restoring the `ltar`
LAKE_ARTIFACT_CACHE=true test_run build +Test -v
test_cmd ls .lake/cache/artifacts/*.ltar
rm -rf .lake/build
test_not_out "leantar" build +Test --no-build -v
test_exp -f .lake/build/ir/Test.ltar

# Test unpacking the archive from the cache
rm -rf .lake/build .lake/cache/artifacts/*.[!l]*
test_out "leantar" build +Test --no-build -v

# Test producing an `ltar` without already restored artifacts
rm -rf .lake/cache .lake/build
LAKE_ARTIFACT_CACHE=true test_run build +Test -v
rm -rf .lake/build
LAKE_ARTIFACT_CACHE=true test_run build +Test:ltar -v
test_exp -f .lake/build/lib/lean/Test.olean # forces restore
test_exp -f .lake/build/ir/Test.ltar
