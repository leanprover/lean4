#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests the `copy` option for path dependencies (`require foo from copy "foo"`).
# Such a dependency is materialized as a copy under the workspace's `packagesDir`
# rather than being loaded (and built) in place at the source path.

# Copy test data to a working directory, as the test mutates the dependency's source
copy_to_work foo lakefile.lean lakefile.toml CopyDep.lean

# Test `lake update` copies the dependency into `packagesDir`
# and records the source path and `copy` option in the manifest
test_run -f lakefile.lean update
test_exp -f .lake/packages/foo/lakefile.toml
test_exp -f .lake/packages/foo/Foo.lean
match_text '"dir": "foo"' lake-manifest.json
match_text '"copy": true' lake-manifest.json

# Test the dependency is built in the copy, not in place
test_run -f lakefile.lean build CopyDep
test_exp -f .lake/packages/foo/.lake/build/lib/lean/Foo.olean
test_exp ! -d foo/.lake

# Test the TOML configuration produces the same manifest and copy
test_cmd cp lake-manifest.json lake-manifest-1.json
rm -rf .lake lake-manifest.json
test_run -f lakefile.toml update
test_cmd diff -u --strip-trailing-cr lake-manifest-1.json lake-manifest.json
test_exp -f .lake/packages/foo/Foo.lean
test_run -f lakefile.toml build CopyDep
test_exp ! -d foo/.lake

# Test loading from the manifest reuses an existing copy
# (i.e., changes to the source are not picked up)
echo 'def Foo.hello := "hello"' > foo/Foo.lean
echo 'def Foo.bye := "bye"' > foo/Bye.lean
test_not_out "Built Foo" -f lakefile.lean build CopyDep
match_text '"foo"' .lake/packages/foo/Foo.lean
test_exp ! -f .lake/packages/foo/Bye.lean

# Test loading from the manifest recreates a missing copy from the source
rm -rf .lake/packages/foo
test_out "Built Foo" -f lakefile.lean build CopyDep
match_text '"hello"' .lake/packages/foo/Foo.lean
test_exp -f .lake/packages/foo/Bye.lean
test_exp ! -d foo/.lake

# Test `lake update` replaces the copy with a fresh one from the source
rm foo/Bye.lean
echo 'def Foo.hello := "hi"' > foo/Foo.lean
test_run -f lakefile.lean update
test_exp ! -f .lake/packages/foo/Bye.lean
test_exp ! -d .lake/packages/foo/.lake
match_text '"hi"' .lake/packages/foo/Foo.lean
test_out "Built Foo" -f lakefile.lean build CopyDep
test_exp ! -d foo/.lake

# Cleanup
rm -f produced.out
