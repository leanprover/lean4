#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# Test Lake's behavior when failing to fetch a cloud release
# ---

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the bar repository on each test. This requires updating the
# locked manifest to the new hash to ensure things work properly.
pushd dep
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
git tag release
INIT_REV=`git rev-parse release`
git commit --allow-empty -m "second commit"
popd

# Clone dependency
$LAKE update
# Remove the release tag from the local copy
git -C .lake/packages/dep tag -d release

# Test that a direct invocation fo `lake build *:release` fails
($LAKE build dep:release && exit 1 || true) | diff -u --strip-trailing-cr <(cat << EOF
✖ [2/2] Running dep:release
error: failed to fetch GitHub release (run with '-v' for details)
Some required builds logged failures:
- dep:release
EOF
) -

# Test that an indirect fetch on the release does not cause the build to fail
$LAKE build Test | diff -u --strip-trailing-cr <(cat << EOF
⚠ [3/6] Ran dep:extraDep
warning: building from source; failed to fetch GitHub release (run with '-v' for details)
✔ [4/6] Built Dep
✔ [5/6] Built Test
Build completed successfully.
EOF
) -

# Test download failure
$LAKE update # re-fetch release tag
($LAKE -v build dep:release && exit 1 || true) | grep --color "curl"

# Test automatic cloud release unpacking
mkdir -p .lake/packages/dep/.lake/build
$LAKE -d .lake/packages/dep pack 2>&1 | grep --color "packing"
test -f .lake/packages/dep/.lake/release.tgz
echo 4225503363911572621 > .lake/packages/dep/.lake/release.tgz.trace
rm -rf .lake/packages/dep/.lake/build
$LAKE build dep:release -v | grep --color "tar"
test -d .lake/packages/dep/.lake/build

# Test that the job prints nothing if the archive is already fetched and unpacked
$LAKE build dep:release | diff -u --strip-trailing-cr <(cat << 'EOF'
Build completed successfully.
EOF
) -

# Test that releases do not contaminate downstream jobs
$LAKE build Test | diff -u --strip-trailing-cr <(cat << 'EOF'
Build completed successfully.
EOF
) -

# Test retagging
git -C dep tag -d release
git -C dep tag release
NEW_REV=`git -C dep rev-parse release`
test ! "$INIT_REV" = "$NEW_REV"
test `git -C .lake/packages/dep rev-parse HEAD` = "$INIT_REV"
$LAKE update
test `git -C .lake/packages/dep rev-parse HEAD` = "$NEW_REV"
$LAKE build dep:release

# Cleanup git repo
rm -rf dep/.git
