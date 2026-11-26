rm -rf .lake

LEAN_ABORT_ON_PANIC=1 lake build SplitMod.Use SplitMod.UseAll

# Restore the edited private file afterwards.
cp SplitMod/Basic.private.lean .lake/Basic.private.lean.orig
trap 'cp .lake/Basic.private.lean.orig SplitMod/Basic.private.lean' EXIT

# Editing only the private half leaves plain importers up to date, but not `import all` ones.
echo '-- edit' >> SplitMod/Basic.private.lean
lake build --no-build SplitMod.Use
capture_fail lake build --no-build SplitMod.UseAll
lake build SplitMod.UseAll

# Bodiless declarations need a private file.
capture_fail lake build Errors.NoPrivate
check_out_contains "declaration 'x' has no body"

capture_fail lake build Errors.Missing
check_out_contains "'y₂' is declared in the public file but has no implementation"

capture_fail lake build Errors.Mismatch
check_out_contains "type mismatch"

capture_fail lake build Errors.PublicInPrivate
check_out_contains "private files cannot declare public declarations"

# The private build must reproduce the public `.olean` exactly.
capture_fail lake build Errors.Diverge
check_out_contains "elaborates differently"
