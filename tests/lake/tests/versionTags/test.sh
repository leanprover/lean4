#!/usr/bin/env bash
source ../common.sh
source ./clean.sh

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the repository on each test.
echo "# SETUP"
set -x
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "commit v1"
git tag v1
git commit --allow-empty -m "commit v2"
git tag v2
git commit --allow-empty -m "commit venom"
git tag venom
git commit --allow-empty -m "commit etc"
git tag etc
set +x

# Test thae Lake returns the version-like tags
# (i.e., those matching `v[0-9].*`)
echo "# TEST"
test_out_diff <(cat << 'EOF'
v1
v2
EOF
) version-tags

# Cleanup
rm -f produced*
rm -rf .git
