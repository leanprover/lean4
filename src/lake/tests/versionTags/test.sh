#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

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

$LAKE version-tags | diff -u --strip-trailing-cr <(cat << 'EOF'
v1
v2
EOF
) -

# Cleanup git repo
rm -rf .git
