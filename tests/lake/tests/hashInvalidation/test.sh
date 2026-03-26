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

# Create a simple git dependency
echo "# SETUP: Create dependency"
mkdir -p dep/Dep
cat > dep/lakefile.lean << 'LAKEFILE'
import Lake
open Lake DSL
package dep
@[default_target]
lean_lib Dep
LAKEFILE
echo "import Dep.Basic" > dep/Dep.lean
echo "def Dep.hello := \"world\"" > dep/Dep/Basic.lean
pushd dep
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
echo "import Dep" > test/Test.lean

# Build — creates .hash files for dep's olean outputs
echo "# TEST: Initial build"
pushd test
test_run update
test_run build

# Verify .hash files were created for dep build outputs
test_exp -f .lake/packages/dep/.lake/build/lib/lean/Dep/Basic.olean.hash

popd

# Make a new commit in the dependency
echo "# SETUP: Update dependency"
pushd dep
echo "def Dep.hello := \"updated\"" > Dep/Basic.lean
git add --all
git commit -m "update"
popd

# Update — should clear stale .hash files
echo "# TEST: Update to new revision and rebuild"
pushd test
test_run update

# Verify stale .hash files were cleared
test_exp ! -f .lake/packages/dep/.lake/build/lib/lean/Dep/Basic.olean.hash

# Verify build succeeds
test_run build

popd

# Cleanup
./clean.sh
rm -f produced.out
