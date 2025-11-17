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

## How the Test Works

1. Builds an artifact with CRLF line endings using `buildArtifactUnlessUpToDate` with `text := true`
2. Manually changes the artifact to have LF line endings
3. Deletes the `.hash` file to force recomputation
4. Rebuilds and compares the old hash (CRLF) vs new hash (LF)

The test verifies that both CRLF and LF versions produce the same hash when text mode is enabled. If the hashes differ, it indicates the `text` parameter is not being properly propagated.

## Running the Test

```bash
cd tests/lake/tests/textMode
./test.sh
```

The test will exit with code 1 (failure) when the bug is present, and code 0 (success) when the bug is fixed.
