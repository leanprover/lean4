rm -rf .lake/build
LEAN_ABORT_ON_PANIC=1 lake build

capture_fail lake lean Module/ConflictingImported.lean
check_out_contains "already contains 'f'"
