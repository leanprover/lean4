#!/usr/bin/env bash
source ../common.sh
set -x

./clean.sh

# Test that text mode hashing is correctly propagated for transitive dependencies
# https://github.com/leanprover/lean4/issues/11209
#
# This test creates three packages:
#   A: Has an input file with text mode hashing
#   B: Depends on A
#   C: Depends on B (transitive dependency on A)
#
# The issue reports that when files are accessed through transitive dependencies,
# the text mode parameter is not correctly propagated, causing Lake to hash files
# in binary mode instead of text mode. This leads to unnecessary rebuilds when
# only line endings change (e.g., CRLF vs LF).
#
# Expected behavior: With text mode hashing, changing CRLF to LF should NOT
# trigger a rebuild, since text mode normalizes line endings.

# Create package A with a built artifact using text mode
$LAKE new a lib.lean
pushd a
git init
git checkout -b master
git config user.name test
git config user.email test@example.com

# Create a JavaScript source file with CRLF line endings
mkdir -p src
printf "// Source\r\nconst x = 42;\r\n" > src/input.js

# Create a target that builds an artifact with text mode hashing
cat >>lakefile.lean <<'EOF'

open System in
target jsBundle pkg : FilePath := Job.async do
  let srcFile := pkg.dir / "src" / "input.js"
  let outFile := pkg.buildDir / "bundle.js"
  -- Build artifact with text mode hashing enabled
  let art ← buildArtifactUnlessUpToDate outFile (text := true) do
    -- Simple "build" step: just copy the file
    IO.FS.createDirAll outFile.parent.get!
    IO.FS.writeFile outFile (← IO.FS.readFile srcFile)
  return art.path
EOF

git add .
git commit -m 'package a with artifact using text mode'
popd

# Create package B that depends on A
$LAKE new b lib.lean
pushd b
git init
git checkout -b master
git config user.name test
git config user.email test@example.com

cat >>lakefile.lean <<'EOF'
require a from git "../a" @ "master"
EOF

$LAKE update -v
git add .
git commit -m 'package b depending on a'
popd

# Create package C that depends on B (transitive dependency on A)
$LAKE new c lib.lean
pushd c
git init
git checkout -b master
git config user.name test
git config user.email test@example.com

cat >>lakefile.lean <<'EOF'
require b from git "../b" @ "master"
EOF

$LAKE update -v
git add .
git commit -m 'package c depending on b'

# First, build the artifact directly from A to create the trace file
echo "Step 1: Building jsBundle from package A (to create trace)..."
pushd ../a
test_run build jsBundle
popd

# Build A's artifact from C (transitive dependency chain: C -> B -> A)
echo ""
echo "Step 2: Building a/jsBundle from package C (transitive dependency)..."
test_run build a/jsBundle

# Now verify the hash computation
echo ""
echo "===== Verifying Artifact ====="

# Get the path to the built artifact in the transitive dependency
artifact_file=".lake/packages/a/.lake/build/bundle.js"

if [ ! -f "$artifact_file" ]; then
  echo "ERROR: Built artifact not found at $artifact_file"
  exit 1
fi

echo "Artifact file found: $artifact_file"

# Verify it has CRLF line endings
if hexdump -C "$artifact_file" | grep -q "0d 0a"; then
  echo "✓ Artifact has CRLF line endings (as expected)"
else
  echo "WARNING: Artifact doesn't have CRLF - test may not be effective"
fi
echo ""

# Test for the bug by checking if line-ending changes trigger rebuilds
echo "Testing rebuild behavior with line ending changes..."
echo ""

# Build a second time - should be no-op
echo "Step 3: Building again (should be cached)..."
test_run build --no-build a/jsBundle
echo "No rebuild needed (good!)"
echo ""

# Now normalize the line endings (CRLF -> LF) in the BUILT ARTIFACT
echo "Step 4: Normalizing line endings CRLF -> LF in $artifact_file..."
# This should NOT trigger a rebuild if text mode is being used correctly
python3 <<'PYTHON'
with open('.lake/packages/a/.lake/build/bundle.js', 'rb') as f:
    content = f.read()
# Normalize line endings
normalized = content.replace(b'\r\n', b'\n')
with open('.lake/packages/a/.lake/build/bundle.js', 'wb') as f:
    f.write(normalized)
print("Line endings normalized in built artifact")
PYTHON

# Verify the artifact now has LF only
if ! hexdump -C "$artifact_file" | grep -q "0d 0a"; then
  echo "✓ Artifact now has LF-only line endings"
else
  echo "ERROR: Artifact still has CRLF"
  popd
  exit 1
fi
echo ""

# Force Lake to recompute the hash by deleting the hash file

echo "Step 5: Deleting hash file to force recomputation..."
hash_file=".lake/packages/a/.lake/build/bundle.js.hash"
if [ -f "$hash_file" ]; then
  old_hash=$(cat "$hash_file")
  echo "Old hash (CRLF): $old_hash"
  rm -f "$hash_file"
else
  echo "No hash file found at $hash_file"
fi
echo ""

echo "Step 6: Rebuilding to trigger hash recomputation..."
echo "The artifact file now has LF instead of CRLF"
echo "If bug exists: binary mode will compute different hash"
echo "If bug fixed: text mode normalizes endings → same hash"
echo ""

$LAKE build -v a/jsBundle 2>&1 | tee /tmp/build_output.txt

# Check if hash file was recreated and what hash it contains
if [ -f "$hash_file" ]; then
  new_hash=$(cat "$hash_file")
  echo ""
  echo "New hash (after LF conversion): $new_hash"
  echo ""

  # With text mode, hashes should be equal (normalizes CRLF to LF)
  # With binary mode, hashes will be different

  if [ "$new_hash" = "$old_hash" ]; then
    echo "✓ PASS - Hashes match!"
    echo "Old hash (CRLF): $old_hash"
    echo "New hash (LF):   $new_hash"
    echo "Text mode correctly normalized line endings"
  else
    echo "✗ FAIL - BUG DETECTED!"
    echo ""
    echo "Old hash (CRLF): $old_hash"
    echo "New hash (LF):   $new_hash"
    echo ""
    echo "The hashes are DIFFERENT, which proves binary mode was used."
    echo "With text mode, CRLF and LF should produce the SAME hash."
    echo ""
    echo "This demonstrates issue #11209"
    popd
    exit 1
  fi
fi

# Check if rebuild actually happened
if grep -q "Building\|built\|Ran" /tmp/build_output.txt; then
  echo "Build executed (artifact was rebuilt)"
else
  echo "Build was skipped (cached/up-to-date)"
fi

popd

echo ""
echo "====== Test Summary ======"
echo "This test detects issue #11209: text mode not propagated for transitive dependencies"
echo ""
echo "Test setup:"
echo "  - Package A builds an artifact with text := true"
echo "  - Package B depends on A"
echo "  - Package C depends on B (transitive dependency on A)"
echo "  - Artifact built with CRLF line endings"
echo ""
echo "Test verification:"
echo "  - Normalize line endings from CRLF to LF"
echo "  - Force hash recomputation by deleting .hash file"
echo "  - Compare old hash (CRLF) vs new hash (LF)"
echo "  - Expected: hashes should match (text mode normalizes line endings)"
echo "  - Actual (bug): hashes differ (binary mode used instead)"
echo ""

# Cleanup
rm -f produced.out /tmp/binary_hash_lf.txt
