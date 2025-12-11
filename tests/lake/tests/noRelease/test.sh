#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Test Lake's behavior when failing to fetch a cloud release
# ---

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the bar repository on each test. This requires updating the
# locked manifest to the new hash to ensure things work properly.
echo "# SETUP"
set -x
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
set +x

# Test that a direct invocation of `lake build *:release` fails
echo "# TEST: Direct fetch"
test_err_diff <(cat << EOF
✖ [2/2] Running dep:release
error: failed to fetch GitHub release (run with '-v' for details)
Some required targets logged failures:
- dep:release
error: build failed
EOF
) build dep:release

# Test that an indirect fetch on the release does not cause the build to fail
echo "# TEST: Indirect fetch"
test_out_diff <(cat << EOF
⚠ [3/6] Ran dep:extraDep
warning: building from source; failed to fetch GitHub release (run with '-v' for details)
EOF
) build Test -q

# Test download failure
echo "# TEST: Download failure"
test_run update # re-fetch release tag
test_err "curl" -v build dep:release

# Test automatic cloud release unpacking
echo "# TEST: Automatic cloud release unpacking"
mkdir -p .lake/packages/dep/.lake/build
test_out "packing" -d .lake/packages/dep pack
test_exp -f .lake/packages/dep/.lake/release.tgz
echo 4225503363911572621 > .lake/packages/dep/.lake/release.tgz.trace
rm -rf .lake/packages/dep/.lake/build
test_out "tar" build dep:release -v
test_exp -d .lake/packages/dep/.lake/build

# Test that the job prints nothing if the archive is already fetched and unpacked
echo "# TEST: Quiet if fetched"
test_out_diff <(cat << 'EOF'
Build completed successfully (2 jobs).
EOF
) build dep:release

# Test that releases do not contaminate downstream jobs
echo "# TEST: Downstream job contamination"
test_out_diff <(cat << 'EOF'
Build completed successfully (5 jobs).
EOF
) build Test

# Test retagging
echo "# TEST: Retagging"
test_cmd git -C dep tag -d release
test_cmd git -C dep tag release
NEW_REV=`git -C dep rev-parse release`
test_exp ! "$INIT_REV" = "$NEW_REV"
test_cmd_eq "$INIT_REV" git -C .lake/packages/dep rev-parse HEAD
test_run update
test_cmd_eq "$NEW_REV" git -C .lake/packages/dep rev-parse HEAD
test_run build dep:release

# Cleanup
rm -rf dep/.git
rm -f produced*
