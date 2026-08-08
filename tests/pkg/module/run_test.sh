rm -rf .lake
LEAN_ABORT_ON_PANIC=1 lake build

capture_fail lake lean Module/ConflictingImported.lean
check_out_contains "already contains 'f'"

# Not part of the `Module` root: the failed declaration is recovered as an axiom of type `False`.
lake lean Module/PartialImported.lean
