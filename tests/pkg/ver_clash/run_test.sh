# This directory contains a unified version of the "ring example"
# developed by Kim across the following 4 repositories:
#
# * https://github.com/kim-em/DiamondExample-A
# * https://github.com/kim-em/DiamondExample-B
# * https://github.com/kim-em/DiamondExample-C
# * https://github.com/kim-em/DiamondExample-D
#
# The top-level package, `D`, depends on two intermediate packages, `B` and `C`,
# which each require semantically different versions of another package, `A`.
# The portion of `A` that `B` and `C` publicly use (i.e., `Ring`) is unchanged
# across the versions, but they both privately make use of changed API (i.e.,
# `poorly_named_lemma` and its rename, `add_left_comm`).
#
# Currently, this causes a version clash, which is tested here.

# ---
# Setup
# ---

./clean.sh

# Copy test data to a working directory to avoid initializing Git repositories
# inside the checked-in source tree. Cleaned at the start so artifacts from a
# failed run remain available for inspection.
WORK_DIR="$PWD/work"
mkdir -p "$WORK_DIR"
cp -r DiamondExample-A DiamondExample-B DiamondExample-C DiamondExample-D lean-toolchain "$WORK_DIR/"
cd "$WORK_DIR"

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the repositories on each test.

# Stolen from the lake test suite
UNAME="$(uname)"
if [ "$UNAME" = Darwin ] || [ "$UNAME" = FreeBSD ]; then
  sed_i() { sed -i '' "$@"; }
else
  sed_i() { sed -i "$@"; }
fi

# Stolen from the lake test suite
init_git() {
  echo "# initialize test repository"
  set -x
  git init
  git checkout -b master
  git config user.name test
  git config user.email test@example.com
  git add --all
  git commit -m "initial commit"
  set +x
}

pushd DiamondExample-A
sed_i s/add_left_comm/poorly_named_lemma/ DiamondExampleA/Ring/Lemmas.lean
lake update
init_git
git tag v1
sed_i s/poorly_named_lemma/add_left_comm/ DiamondExampleA/Ring/Lemmas.lean
git commit -am "rename lemma"
git tag v2
popd

pushd DiamondExample-B
lake update
init_git
popd

pushd DiamondExample-C
sed_i s/v2/v1/ lakefile.toml
sed_i s/add_left_comm/poorly_named_lemma/ DiamondExampleC/MainResult.lean
lake update
init_git
git tag v1
sed_i s/v1/v2/ lakefile.toml
sed_i s/poorly_named_lemma/add_left_comm/ DiamondExampleC/MainResult.lean
lake update
git commit -am "use v2"
git tag v2
popd

pushd DiamondExample-D
sed_i s/v2/v1/ lakefile.toml
lake update
init_git
git tag v1
sed_i s/v1/v2/ lakefile.toml
lake update
git commit -am "use v2"
git tag v2
popd

# ---
# Main tests
# ---

pushd DiamondExample-D

# Test build succeeds on v1
git switch v1 --detach
run lake build

# Test build fails on v2
git switch v2 --detach
capture_fail lake build
check_out_contains 'Unknown identifier `poorly_named_lemma`'

# Test build with different package names
sed_i '/name/ s/A/A-v1/' .lake/packages/DiamondExample-B/lakefile.toml
sed_i '/name/ s/A/A-v2/' .lake/packages/DiamondExample-C/lakefile.toml
run lake update

capture_fail lake build
check_out_contains 'could not disambiguate the module `DiamondExampleA.Ring.Lemmas`'

popd
