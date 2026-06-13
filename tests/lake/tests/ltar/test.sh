#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Store Lake cache in a local directory
export LAKE_CACHE_DIR=

#-------------------------------------------------------------------------------
# This test suite covers the (offline) use of `leantar` in Lake
#-------------------------------------------------------------------------------

# Test regular build does not produce an `ltar`
test_run build +Test -v
test_exp ! -f .lake/build/ir/Test.ltar

# Test use of `--no-build` with the `ltar` facet
test_err "archive does not exist and needs to be built" \
  build +Test:ltar --no-build -v

# Test the build of the `ltar` facet
test_out "Built Test:ltar" build +Test:ltar -v
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

# Test caching an `ltar` through `-o` (with `restoreAllArtifacts = true`)
# This tests caching the ltar from within `Module.packLtar`
rm -rf .lake/cache .lake/build
test_run -f restoreAll.toml build +Test -v --wfail
test_exp ! -f .lake/build/ir/Test.ltar
test_run -f restoreAll.toml build +Test -v --wfail -o .lake/outputs.jsonl
test_cmd ls .lake/cache/artifacts/*.ltar
test_exp -f .lake/build/ir/Test.ltar

# Test that the cache input-to-output mapping is overwritten without
# `--no-overwrite`. Since the build mapping includes module outputs and the
# tracked mapping only includes the `ltar`, the tracking mapping should
# require an unpack, whereas the build mapping should not.
rm -rf .lake/build
no_match_text ltar .lake/cache/outputs/test/*.json
test_run cache add .lake/outputs.jsonl --no-overwrite
no_match_text ltar .lake/cache/outputs/test/*.json
LAKE_ARTIFACT_CACHE=true test_not_out "leantar" build +Test --no-build -v
rm -rf .lake/build
no_match_text ltar .lake/cache/outputs/test/*.json
test_run cache add .lake/outputs.jsonl --service reservoir --repo 'foo/bar'
match_text ltar .lake/cache/outputs/test/*.json
match_text reservoir .lake/cache/outputs/test/*.json
LAKE_ARTIFACT_CACHE=true test_out "leantar" build +Test --no-build -v
# Unpack should have updated the cached mapping: added module outputs,
# removed service metadata, and left the ltar.
rm -rf .lake/build
match_text ltar .lake/cache/outputs/test/*.json
match_text olean .lake/cache/outputs/test/*.json
no_match_text reservoir .lake/cache/outputs/test/*.json
LAKE_ARTIFACT_CACHE=true test_not_out "leantar" build +Test --no-build -v

# Test that Lake prefers the local trace outputs over the cache
rm -f .lake/build/lib/lean/*.[!t]*
test_run cache add .lake/outputs.jsonl
match_text ltar .lake/cache/outputs/test/*.json
LAKE_ARTIFACT_CACHE=true test_not_out "leantar" build +Test --no-build -v
# Test that the cache output is not overwritten without an unpack
match_text ltar .lake/cache/outputs/test/*.json

# Test producing an `ltar` without already restored artifacts
rm -rf .lake/cache .lake/build
LAKE_ARTIFACT_CACHE=true test_run build +Test -v
rm -rf .lake/build
LAKE_ARTIFACT_CACHE=true test_run build +Test:ltar -v
test_exp -f .lake/build/lib/lean/Test.olean # forces restore
test_exp -f .lake/build/ir/Test.ltar
