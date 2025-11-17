# Text Mode Hashing Test

This test verifies that text mode hashing works correctly in `buildArtifactUnlessUpToDate`.

## Related Issue

https://github.com/leanprover/lean4/issues/11209

## Issue Description

The reported bug is that the `text` parameter is not correctly propagated in `buildArtifactUnlessUpToDate`. This causes files that should be hashed in text mode (normalizing line endings) to be hashed in binary mode instead, leading to unnecessary rebuilds when only line endings change (e.g., CRLF ↔ LF).

## Test Setup

This test creates a single package that builds an artifact with `text := true`.

## Test Procedure

1. Create a package with an artifact target that uses `buildArtifactUnlessUpToDate` with `text := true`
2. Build the artifact (contains CRLF line endings)
3. Verify build is cached on second build
4. Manually change the artifact's line endings from CRLF to LF
5. Delete the `.hash` file to force hash recomputation
6. Rebuild and compare the old hash (CRLF) vs new hash (LF)

## Expected Behavior

With text mode hashing working correctly:
- CRLF and LF versions of the same file should produce the **same hash**
- Changing only line endings should **not** trigger a rebuild

## Bug Location

The bug is in `Lake/Build/Common.lean` in the `buildArtifactUnlessUpToDate` function, where `computeArtifact` is called without propagating the `text` parameter.

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
2. The artifact is hashed in **binary mode**: `4f971083309e5800`
3. Manually changes the artifact to have LF line endings
4. Deletes the `.hash` file to force recomputation
5. Rebuilds, triggering hash recomputation
6. Computes new hash in **binary mode**: `c671e9e54bab1647`
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

The test will exit with code 1 (failure) when the bug is present, and code 0 (success) when the bug is fixed.
