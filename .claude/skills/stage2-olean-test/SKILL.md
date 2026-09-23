---
name: stage2-olean-test
description: Diagnose a spurious stage1 test failure caused by olean-persisted compiler changes. Use when a stage1 test fails unexpectedly and the change adds or modifies an environment extension or other information persisted into .olean files.
allowed-tools: Bash, Read
---

# Stage2 Is Required for Changes to Olean-Persisted Compiler Information

When a change alters information that is *persisted into `.olean` files* (e.g. a new or changed
environment extension that the compiler reads back), a stage1 test run can fail spuriously: stage1's
`src/` (including `Init`) is compiled by the **stage0** compiler, which lacks the change, so the
stage1 `lean` binary imports oleans that predate the change. In that situation the relevant tests
must be run against **stage2** instead, where the new compiler compiles everything consistently.

So: on a test failure, if the change depends on changed olean information, test stage2 instead.

## Procedure

Building stage2 is expensive, so **confirm with the user before switching to a stage2 build.**

For the actual build/test commands (`make stage2`, `clean-stdlib`, per-module Lake builds, and
running tests against stage2), use the **`stage2-build`** skill.
