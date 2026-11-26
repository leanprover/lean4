# Work on a copy as the test edits its sources.
rm -rf produced.work .lake
mkdir produced.work
cp -r lakefile.toml lean-toolchain SplitMod Errors produced.work/
chmod -R u+w produced.work
cd produced.work

LEAN_ABORT_ON_PANIC=1 lake build SplitMod.Use SplitMod.UseAll
# The private file is not a module of its own.
capture_fail lake build SplitMod.Basic.private

# Changing only the private file leaves plain importers up to date, but not `import all` ones.
perl -p -i -e 's/n \+ implOffset/implOffset + n/' SplitMod/Basic.private.lean
lake build SplitMod.Basic
lake build --no-build SplitMod.Use
capture_fail lake build --no-build SplitMod.UseAll
lake build SplitMod.UseAll

# Bodiless declarations need a private file.
capture_fail lake build Errors.NoPrivate
check_out_contains "may only be omitted if the module has a private file"

capture_fail lake build Errors.Missing
check_out_contains "'y₂' is declared in the public file but has no implementation"

capture_fail lake build Errors.Mismatch
check_out_contains "type mismatch"

capture_fail lake build Errors.PublicInPrivate
check_out_contains "private files cannot declare public declarations"

# The private file must not change how the public file elaborates.
capture_fail lake build Errors.Diverge
check_out_contains "elaborates differently"

# Plain importers only wait for the public file: they are elaborated even if the private file fails.
capture_fail lake build Errors.UsePrivateFails
check_out_contains "Built Errors.UsePrivateFails"
check_out_contains "Building Errors.PrivateFails"
