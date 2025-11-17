# Text Mode Transitive Dependency Test

This test verifies that text mode hashing works correctly for files accessed through transitive dependencies.

## Related Issue

https://github.com/leanprover/lean4/issues/11209

## Issue Description

The reported bug is that Lake's `fetchFileHash` function at line 406 in `Lake/Build/Common.lean` does not correctly propagate the `text` parameter when files are accessed through transitive dependencies. This causes files that should be hashed in text mode (normalizing line endings) to be hashed in binary mode instead, leading to unnecessary rebuilds when only line endings change (e.g., CRLF ↔ LF).

## Test Setup

This test creates a three-package dependency chain:

```
C → B → A
```

- **Package A**: Contains a text file (`script.js`) with CRLF line endings, declared as an `input_file` with `text := true`
- **Package B**: Depends on package A
- **Package C**: Depends on package B (making A a transitive dependency)

## Test Procedure

1. Create the three packages with the dependency chain
2. Build a target from package C that depends on A's text file
3. Compute expected hashes in both text mode and binary mode (they differ for CRLF files)
4. Build again to ensure caching works
5. Normalize line endings (CRLF → LF) in the source file
6. Build again and verify no rebuild occurs (correct behavior with text mode)

## Expected Behavior

With text mode hashing working correctly:
- CRLF and LF versions of the same file should produce the **same hash**
- Changing only line endings should **not** trigger a rebuild

## Bug Confirmation

The bug **IS present** in the current codebase at two locations in `buildArtifactUnlessUpToDate`:

**Line 607** (replay path - when reusing existing artifacts):
```lean
else if (← savedTrace.replayIfUpToDate file depTrace) then
  computeArtifact file ext    -- ❌ Missing `text` parameter!
```

**Line 630** (build path - in the doBuild helper):
```lean
doBuild depTrace traceFile :=
  inline <| buildAction depTrace traceFile do
    build
    clearFileHash file
    removeFileIfExists traceFile
    computeArtifact file ext    -- ❌ Missing `text` parameter!
```

Both should be:
```lean
computeArtifact file ext text
```

## Test Successfully Detects the Bug!

The test **FAILS** (as expected), confirming the bug exists:

```
✗ FAIL - BUG DETECTED!

Old hash (CRLF): 4f971083309e5800
New hash (LF):   c671e9e54bab1647

The hashes are DIFFERENT, which proves binary mode was used.
```

**How the test works:**
1. Builds an artifact with CRLF line endings using `buildArtifactUnlessUpToDate` with `text := true`
2. Due to bug at line 630, the artifact is hashed in **binary mode**: `4f971083309e5800`
3. Manually changes the artifact to have LF line endings
4. Deletes the `.hash` file to force recomputation
5. Rebuilds, which goes through line 607 or 619 to recompute the hash
6. Due to bug at line 607 (or correct code at line 619), computes new hash in **binary mode**: `c671e9e54bab1647`
7. The hashes DIFFER, proving binary mode was used instead of text mode

**Expected behavior after fix:**
With `text` parameter correctly propagated:
- Both CRLF and LF versions would normalize to the same hash
- Test would PASS
- No unnecessary rebuilds would occur when only line endings change

## Running the Test

```bash
cd tests/lake/tests/textModeTransitive
./test.sh
```

## Future Improvements

To make this test actually **detect** the bug (not just serve as a regression test):

1. **Simulate cross-package hash verification**: Have package C explicitly rehash the artifact from A using the correct text mode and compare against the hash computed by A's build

2. **Use a hash verification tool**: Create a separate target that computes the hash independently and compares it

3. **Monitor actual rebuild behavior**: Track whether ProofWidgets-style JavaScript artifacts trigger rebuilds in mathlib when only line endings change

Example test enhancement:
```lean
-- In package C
target verifyHash pkg : Unit := do
  let artifactPath := pkg.dir / ".lake" / "packages" / "a" / ".lake" / "build" / "bundle.js"
  -- Compute hash the CORRECT way (with text mode)
  let correctHash ← computeFileHash artifactPath (text := true)
  -- Read hash that A computed (with the bug, used binary mode)
  let storedHash ← Hash.load? (artifactPath.toString ++ ".hash")
  if correctHash != storedHash then
    error "Hash mismatch: text mode not propagated!"
```
