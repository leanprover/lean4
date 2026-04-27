#!/usr/bin/env bash
source ../common.sh

# Tests that stale `.hash` files in the source tree are cleared
# when a git dependency is checked out to a new revision.
#
# `fetchFileHash` trusts cached `.hash` files (without `--rehash`).
# After a dependency revision change, stale `.hash` files in the source tree
# can  cause incorrect trace computations. This test verifies that
# `updateGitPkg` clears them.
#
# See: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/ProofWidgets.20not.20up-to-date

./clean.sh

# Copy test data to a working directory to avoid initializing a Git repository
# inside the checked-in source tree
WORK_DIR="$PWD/work"
mkdir -p "$WORK_DIR"
cp -r dep lakefile.toml "$WORK_DIR/"
cd "$WORK_DIR"

# Initialize the dependency
echo "# SETUP: Create v1"
pushd dep
init_git
echo "1" > a.txt
test_run build
git add --all
git commit -m "v1"
popd

# Build with v1
echo "# TEST: v1"
test_run update
test_cmd_eq "1" cat .lake/packages/dep/a.txt
test_cmd_eq "1b" cat .lake/packages/dep/b.txt
test_exp ! -f .lake/packages/dep/.lake/build/c.txt
test_run build dep
# verify that a `.hash` is emitted in the source tree
test_exp -f .lake/packages/dep/b.txt.hash
test_cmd_eq "1bc" cat .lake/packages/dep/.lake/build/c.txt

# Add a new version
echo "# SETUP: Add v2"
pushd dep
echo "2" > a.txt
test_run build
git commit -am "v2"
popd

# Build with v2
echo "# TEST: v2"
test_run update
test_cmd_eq "2" cat .lake/packages/dep/a.txt
test_cmd_eq "2b" cat .lake/packages/dep/b.txt
test_cmd_eq "1bc" cat .lake/packages/dep/.lake/build/c.txt
# verify the hash has been cleared
test_exp ! -f .lake/packages/dep/b.txt.hash
test_run build dep
# verify a rebuild occurred based on the new `b.txt`
test_cmd_eq "2bc" cat .lake/packages/dep/.lake/build/c.txt
