#!/usr/bin/env bash
source ../common.sh
NO_BUILD_CODE=3

./clean.sh

# Test the functionality of the Lake artifact cache

# Store Lake cache in a local directory
TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
CACHE_DIR="$TEST_DIR/.lake/cache"
export LAKE_CACHE_DIR="$CACHE_DIR"

# Verify packages without `enableArtifactCache` do not use the cache by default
test_run build -f unset.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify they also do not if `LAKE_ARTIFACT_CACHE` is set to `false`
LAKE_ARTIFACT_CACHE=false test_run build -f unset.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify packages with `enableArtifactCache` set to `false``
# also do not if `LAKE_ARTIFACT_CACHE` is set to `true`
LAKE_ARTIFACT_CACHE=true test_run build -f disabled.toml Test:static
test_exp ! -d "$CACHE_DIR"
# Verify that packages without `enableArtifactCache` and
# `LAKE_ARTIFACT_CACHE` is set to `true` do use the cache
LAKE_ARTIFACT_CACHE=true test_run build -f unset.toml Test:static
test_exp -d "$CACHE_DIR"
./clean.sh

# Ensure a build runs properly with some artifacts cached
test_run build Test:static
test_run build Test:static --no-build --wfail

# Test replay of a cached build
test_out 'Replayed Test:c.o' build +Test:o -v

# Verify that a rebuild with the cache disabled is a no-op
touch .lake/build/ir/Test.c # avoid mod time fallback if trace is missing
test_run -f disabled.toml build +Test:o --no-build --wfail
test_run -f disabled.toml build Test:static --no-build --wfail

# Verify the cache directory structure was created
test_exp -d "$CACHE_DIR"
test_exp -d "$CACHE_DIR/outputs"
test_exp -d "$CACHE_DIR/artifacts"

# Copy the basic mappings for later
test_cmd cp -r "$CACHE_DIR/outputs" .lake/backup-outputs

# Checked that the cached artifact is in the expected location
# and equivalent to the standard artifact
local_art="$($LAKE -f disabled.toml query +Test:o)"
cache_art="$($LAKE query +Test:o)"
test_exp "$(norm_dirname "$cache_art")" = "$CACHE_DIR/artifacts"
test_exp "$cache_art" != "$local_art"
test_cmd cmp -s "$cache_art" "$local_art"

# Verify supported artifacts end up in the cache directory
test_run build \
  test:exe Test:static Test:shared +Test:o.export +Test:o.noexport +Module
test_cached() {
  target="$1"; shift
  art="$($LAKE query $target)"
  echo "${1:-?} artifact cached: $target -> $art"
  test ${1:-} "$(norm_dirname "$art")" = "$CACHE_DIR/artifacts"
}
test_cached test:exe !
test_cached Test:static !
test_cached Test:shared !
test_cached +Test:o.export
test_cached +Test:o.noexport
test_cached +Test:dynlib !
test_cached +Test:olean
test_cached +Test:ilean !
test_cached +Test:c
test_cached +Module:olean
test_cached +Module:olean.server
test_cached +Module:olean.private
test_cached +Module:ir

# Verify no `.hash` files end up in the cache directory
check_diff /dev/null <(ls -1 "$CACHE_DIR/*.hash" 2>/dev/null)

# Verify that the executable has the right permissions to be run
test_run exe test

# Create a test module that can be arbitrarily edited and cached
# The `Test` module's artifacts are more carefully managed throught this test
touch Ignored.lean
test_run -v build +Ignored
test_cmd rm -f .lake/build/lib/lean/Ignored.trace

# Verify that fetching from the cache can be disabled
test_cmd rm -f .lake/build/lib/lean/Ignored.trace
test_status $NO_BUILD_CODE -v -f disabled.toml build +Ignored --no-build
LAKE_ARTIFACT_CACHE=false test_status $NO_BUILD_CODE -v \
  -f unset.toml build +Ignored --no-build

# Verify that fetching from the cache creates a trace file that does not replay
test_out "Fetched Ignored" -v build +Ignored
test_exp -f .lake/build/lib/lean/Ignored.trace
test_out "Fetched Ignored" -v build +Ignored

# Verify that modifications invalidate the cache
echo "def foo := ()" > Ignored.lean
test_out "Built Ignored" -v build +Ignored

# Test that repeated switching between different versions
# of a file works correctly with `restoreAllArtifacts = true`
test_run resolve-deps -R -KrestoreAll=true
echo "def bar := ()" > Ignored.lean
test_out "Built Ignored" -v build +Ignored
echo "def foo := ()" > Ignored.lean
test_out "restored artifact from cache" -v build +Ignored --no-build
echo "def bar := ()" > Ignored.lean
test_out "restored artifact from cache" -v build +Ignored --no-build
test_run -v build Test.ImportIgnored
test_run resolve-deps -R

# Test that outdated files are not stored in the cache with `--old`
echo "def baz := ()" > Ignored.lean
test_out "Built Ignored" -v build +Ignored --old
test_out "Replayed Test.ImportIgnored" -v build Test.ImportIgnored --no-build --old
test_err 'Unknown identifier `bar`' -v build Test.ImportIgnored

# Test that truly up-to-date files are still cached with `--old`
test_cmd rm .lake/build/lib/lean/Ignored.*
test_out "restored artifact from cache" -v build +Ignored --no-build

# Verify module ileans are restored from the cache
test_run build +Test --no-build
test_cmd rm .lake/build/lib/lean/Test.ilean
test_out "restored artifact from cache" -v build +Test --no-build
test_exp -f .lake/build/lib/lean/Test.ilean

# Verify that things work properly if the cached artifact is removed
test_cmd rm "$cache_art"
test_out "⚠ [4/4] Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached
test_cmd rm -r "$CACHE_DIR/outputs"
test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_exp -f "$cache_art" # artifact should be re-cached

# Verify that upstream cache mappings are restored
test_out "Replayed Test:c.o" build Test:static -v --no-build
ls .lake/backup-outputs > .lake/backup-outputs.txt
check_diff .lake/backup-outputs.txt <(ls "$CACHE_DIR/outputs")

# Verify that things work properly if the local artifact is removed
test_cmd rm "$local_art"
test_out "Replayed Test:c.o" build +Test:o -v --no-build
test_cmd rm "$local_art.trace"
test_out "Fetched Test:c.o" build +Test:o -v --no-build

# Verify that if the input cache is missing,
# the cached artifact is still used via the output hash in the trace
test_cmd rm -r "$CACHE_DIR/outputs" .lake/build/ir/Test.c
test_run -v build +Test:c --no-build

# Verify that the olean does need to be present in the build directory
test_cmd rm .lake/build/lib/lean/Test.olean .lake/build/lib/lean/Test/Imported.olean
test_run -v build +Test.Imported --no-build --wfail
test_run -v build +Test

# Test producing an output mappings file
test_lines() {
  expected=$1; file=$2
  actual=$(wc -l < $file)
  echo "? wc -l $file ($actual) = $expected"
  if test $actual = $expected; then
    return 0
  else
    cat "$file"
    return 1
  fi
}
test_run build Test -o .lake/outputs.jsonl
test_exp -f .lake/outputs.jsonl
test_lines 3 .lake/outputs.jsonl
test_run build Test:static -o .lake/outputs.jsonl
test_lines 6 .lake/outputs.jsonl

# Verify that `lake cache clean` deletes the cache directory
test_exp -d "$CACHE_DIR"
test_cmd cp -r "$CACHE_DIR" .lake/cache-backup
test_run cache clean
test_exp ! -d "$CACHE_DIR"

# Verify all artifacts end up in the cache directory with `restoreAllArtifacts`
test_cmd rm -rf "$CACHE_DIR" .lake/build
test_run build -R -KrestoreAll=true \
  test:exe Test:static Test:shared +Test:o.export +Test:o.noexport +Module
test_restored() {
  target="$1"; shift
  art="$($LAKE query $target)"
  echo "! artifact cached: $target -> $art"
  test ! "$(norm_dirname "$art")" = "$CACHE_DIR/artifacts"
  if [ -n "${1:-}" ]; then
    test "$(basename "$art")" = "$1"
  fi
}
test_restored test:exe
test_restored Test:static
test_restored Test:shared
test_restored +Test:o.export Test.c.o.export
test_restored +Test:o.noexport Test.c.o.noexport
test_restored +Test:dynlib
test_restored +Test:olean Test.olean
test_restored +Test:ilean Test.ilean
test_restored +Test:c Test.c
test_restored +Module:olean Module.olean
test_restored +Module:olean.server Module.olean.server
test_restored +Module:olean.private Module.olean.private
test_restored +Module:ir Module.ir

# Verify that invalid outputs do not break Lake
if command -v jq > /dev/null; then # skip if no jq found
  libPath=$($LAKE query Test:static)
  test_cmd rm -f $libPath
  inputHash=$(jq -r '.depHash' $libPath.trace)
  echo $inputHash
  echo bogus > "$CACHE_DIR/outputs/test/$inputHash.json"
  test_out 'invalid JSON' build Test:static
  test_cmd rm -f $libPath
  echo '"bogus"' > "$CACHE_DIR/outputs/test/$inputHash.json"
  test_out 'some output(s) have issues' build Test:static
  test_exp -f $libPath
fi

# Cleanup
rm -f produced.out Ignored.lean
