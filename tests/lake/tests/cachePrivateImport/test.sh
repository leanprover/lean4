#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests that the server can import a module whose private imports are only
# available from the artifact cache.
# https://github.com/leanprover/lean4/issues/14435

TEST_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)"
export LAKE_CACHE_DIR="$(norm_path "$TEST_DIR")/.lake/cache"
export LAKE_ARTIFACT_CACHE=true
unset LAKE_RESTORE_ARTIFACTS

# Rebuild from the cache, which leaves only traces in the build directory
test_run build Lib
rm -rf .lake/build
test_run build Lib
test_exp ! -f .lake/build/lib/lean/Lib/A.ir.sig
test_exp ! -f .lake/build/lib/lean/Lib/C.ir.sig

# Without a setup, Lean can't find the imports in the build directory
test_fails env lean -DElab.inServer=true Test.lean

# Elaborate the header like the language server does, both for a file that is
# outside every library (`Test.lean`) and for a library module (`Lib/B.lean`)
for file in Test.lean Lib/B.lean; do
  echo "# TEST: $file"
  echo '$' lake setup-file "$file"
  "$LAKE" setup-file "$file" > .lake/setup.json
  test_cmd grep -qF '"Lib.A"' .lake/setup.json
  test_cmd grep -qF '"Lib.C"' .lake/setup.json
  test_run env lean --setup .lake/setup.json -DElab.inServer=true "$file"
done

# A command-line run doesn't load private imports of imports
test_not_out '"Lib.A"' lean -v Test.lean
match_text '"importArts":{"Lib"' produced.out

# Cleanup
./clean.sh
