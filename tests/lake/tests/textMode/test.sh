#!/usr/bin/env bash
source ../common.sh
set -x

./clean.sh

# Test that text mode hashing works correctly in buildArtifactUnlessUpToDate
# https://github.com/leanprover/lean4/issues/11209
#
# Expected behavior: With text mode hashing, changing CRLF to LF should NOT
# change the hash, since text mode normalizes line endings.

# Create a package with an artifact built using text mode
$LAKE new pkg lib.lean
pushd pkg

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
    IO.FS.createDirAll outFile.parent.get!
    IO.FS.writeFile outFile (← IO.FS.readFile srcFile)
  return art.path
EOF

# Build the artifact for the first time
echo "Step 1: Initial build with CRLF line endings..."
test_run build jsBundle

artifact_file=".lake/build/bundle.js"

# Verify it has CRLF line endings
if hexdump -C "$artifact_file" | grep -q "0d 0a"; then
  echo "✓ Artifact has CRLF line endings"
else
  echo "WARNING: Artifact doesn't have CRLF - test may not be effective"
fi
echo ""

# Build a second time - should be cached
echo "Step 2: Building again (should be cached)..."
test_run build --no-build jsBundle
echo "No rebuild needed"
echo ""

# Normalize the line endings (CRLF -> LF) in the built artifact
echo "Step 3: Normalizing line endings CRLF -> LF..."
python3 <<'PYTHON'
with open('.lake/build/bundle.js', 'rb') as f:
    content = f.read()
normalized = content.replace(b'\r\n', b'\n')
with open('.lake/build/bundle.js', 'wb') as f:
    f.write(normalized)
print("Line endings normalized")
PYTHON

# Verify the artifact now has LF only
if ! hexdump -C "$artifact_file" | grep -q "0d 0a"; then
  echo "✓ Artifact now has LF-only line endings"
else
  echo "ERROR: Artifact still has CRLF"
  exit 1
fi
echo ""

# Delete the hash file to force recomputation
echo "Step 4: Deleting hash file to force recomputation..."
hash_file=".lake/build/bundle.js.hash"
if [ -f "$hash_file" ]; then
  old_hash=$(cat "$hash_file")
  echo "Old hash (CRLF): $old_hash"
  rm -f "$hash_file"
else
  echo "ERROR: No hash file found at $hash_file"
  popd
  exit 1
fi
echo ""

echo "Step 5: Rebuilding to trigger hash recomputation..."
echo "The artifact file now has LF instead of CRLF"
echo "If bug exists: binary mode will compute different hash"
echo "If bug fixed: text mode normalizes endings → same hash"
echo ""

$LAKE build -v jsBundle 2>&1 | tee /tmp/build_output.txt

# Check the new hash
if [ ! -f "$hash_file" ]; then
  echo "ERROR: Hash file was not created after rebuild"
  popd
  exit 1
fi

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
  popd
  rm -f produced.out /tmp/build_output.txt
  exit 0
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
  rm -f produced.out /tmp/build_output.txt
  exit 1
fi
