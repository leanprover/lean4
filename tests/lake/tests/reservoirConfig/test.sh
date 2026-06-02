#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Copy test data to a working directory to avoid initializing a Git repository
# inside the checked-in source tree
WORK_DIR="$PWD/work"
mkdir -p "$WORK_DIR"
cp -r lakefile.lean expected.json "$WORK_DIR/"
cd "$WORK_DIR"

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the repository on each test.
echo "# SETUP"
set -x
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "commit 1"
git tag v1
git commit --allow-empty -m "commit 2"
git tag v2
git commit --allow-empty -m "commit 3"
git tag etc
set +x

# Test that Lake produces the expected Reservoir configuration.
echo "# TEST"
test_out_diff expected.json reservoir-config
