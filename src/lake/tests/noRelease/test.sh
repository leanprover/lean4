#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# Test Lake's behavior when failing to fetch a cloud release
# ---

# Test that a direct invocation fo `lake build *:release` fails
($LAKE build dep:release && exit 1 || true) | diff -u --strip-trailing-cr <(cat << 'EOF'
✖ [1/1] Fetching dep:release
info: dep: wanted prebuilt release, but could not find an associated tag for the package's revision
error: failed to fetch cloud release
Some builds logged failures:
- dep:release
EOF
) -

# Test that an indirect fetch on the release does not cause the build to fail
$LAKE build Test | diff -u --strip-trailing-cr <(cat << 'EOF'
⚠ [1/3] Fetched dep:optRelease
info: dep: wanted prebuilt release, but could not find an associated tag for the package's revision
warning: failed to fetch cloud release; falling back to local build
✔ [2/3] Built Test
Build completed successfully.
EOF
) -

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
popd

# Test download failure
($LAKE build dep:release && exit 1 || true) | grep --color "downloading"

# Test unpacking
mkdir -p dep/.lake/build
tar -cz -f dep/.lake/release.tgz -C dep/.lake/build .
echo 4225503363911572621 > dep/.lake/release.tgz.trace
rmdir dep/.lake/build
$LAKE build dep:release -v | grep --color "unpacking"
test -d dep/.lake/build

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

# Cleanup git repo
rm -rf dep/.git
