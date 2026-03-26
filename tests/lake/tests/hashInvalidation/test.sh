#!/usr/bin/env bash
source ../common.sh

# ---
# Tests that stale `.hash` files are cleared when a git dependency
# is checked out to a new revision.
#
# `fetchFileHash` trusts cached `.hash` files unconditionally. After
# a dependency revision change, stale `.hash` files cause incorrect
# trace computations. This test verifies that `updateGitPkg` clears
# them.
#
# See: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/ProofWidgets.20not.20up-to-date
# ---

./clean.sh

# Create a git dependency that mirrors the ProofWidgets pattern:
# a `buildFileAfterDep` target whose output is a git-tracked file
# in the source tree. This creates a .hash file that becomes stale
# when the dependency is checked out to a new revision.
echo "# SETUP: Create dependency"
mkdir -p dep
pushd dep

cat > lakefile.lean << 'LAKEFILE'
import Lake
open Lake DSL System

package dep

-- An input file that triggers rebuilds
input_file depConfig where
  path := "config.txt"
  text := true

-- A target whose output (generated.txt) lives in the source tree,
-- mirroring ProofWidgets' widgetPackageLock pattern.
-- buildFileAfterDep calls fetchFileHash on the output, creating
-- a .hash file in the source tree.
target depGenerated pkg : FilePath := do
  let config ← depConfig.fetch
  let outFile := pkg.dir / "generated.txt"
  buildFileAfterDep (text := true) outFile config fun srcFile => do
    let contents ← IO.FS.readFile srcFile.path
    IO.FS.writeFile outFile s!"generated from: {contents}"

@[default_target]
lean_lib Dep where
  needs := #[depGenerated]
LAKEFILE

mkdir -p Dep
echo "def Dep.hello := \"world\"" > Dep/Basic.lean
echo "v1" > config.txt
echo "generated from: v1" > generated.txt

init_git
popd

# Create the test project
echo "# SETUP: Create test project"
mkdir -p test
cat > test/lakefile.lean << 'EOF'
import Lake
open Lake DSL

package test

require dep from git "../dep"

@[default_target]
lean_lib Test
EOF

mkdir -p test/Test
echo "def hello := \"world\"" > test/Test/Basic.lean

# Build — this creates generated.txt.hash in the dep source tree
echo "# TEST: Initial build"
pushd test
test_run update
test_run build

# Verify .hash file was created for the generated output
test_exp -f .lake/packages/dep/generated.txt.hash

popd

# Make a new commit that changes config.txt and generated.txt
echo "# SETUP: Update dependency"
pushd dep
echo "v2" > config.txt
echo "generated from: v2" > generated.txt
git add --all
git commit -m "update to v2"
popd

# Update the dependency — should clear stale .hash files
echo "# TEST: Update to new revision and rebuild"
pushd test
test_run update

# Verify the stale .hash file was cleared
test_exp ! -f .lake/packages/dep/generated.txt.hash

# Verify build succeeds (without the fix, the stale .hash would
# cause an incorrect trace, potentially failing the build)
test_run build

popd

# Cleanup
./clean.sh
rm -f produced.out
