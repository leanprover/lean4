#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that a Git dependency with a `subDir` is materialized as a cone-mode sparse checkout
# of that directory, extended to cover path dependencies on its siblings.

echo "# SETUP"
mkdir repo
pushd repo
mkdir a b c
cat > a/lakefile.toml <<'EOT'
name = "a"
[[require]]
name = "b"
path = "../b"
[[lean_lib]]
name = "A"
EOT
printf 'import B\ndef a := b\n' > a/A.lean
printf 'name = "b"\n[[lean_lib]]\nname = "B"\n' > b/lakefile.toml
echo 'def b := 1' > b/B.lean
printf 'name = "a"\n[[lean_lib]]\nname = "A"\n' > c/lakefile.toml
echo 'def a := 2' > c/A.lean
echo root > root.txt
init_git
# `--filter` is silently ignored by a server that does not allow it
git config uploadpack.allowFilter true
popd

mkdir test
pushd test
cat > lakefile.toml <<EOT
name = "test"
[[require]]
name = "a"
git = "file://$(pwd)/../repo"
rev = "master"
subDir = "a"
[[lean_lib]]
name = "Test"
EOT
printf 'import A\n#eval a\n' > Test.lean
PKG=.lake/packages/a
cone() { git -C $PKG sparse-checkout list | tr '\n' ' '; }

echo "# TEST: sparse checkout of subDir"
test_run update
test_cmd_eq "a b " cone
test_exp -f $PKG/root.txt
test_exp -f $PKG/b/B.lean
test_exp ! -e $PKG/c
test_out "1" build Test
test_not_out "has local changes" build Test

echo "# TEST: rematerialize from the manifest"
rm -rf $PKG
test_out "adding 'b' to the sparse checkout" build Test
test_cmd_eq "a b " cone

echo "# TEST: subDir change"
sed_i 's/subDir = "a"/subDir = "c"/' lakefile.toml
test_out "restricting the checkout to 'c'" update
test_cmd_eq "c " cone
# untracked build outputs (e.g., `a/.lake`) are left behind
test_exp ! -e $PKG/a/A.lean
test_out "2" build Test

echo "# TEST: LAKE_SPARSE_CHECKOUT=0"
LAKE_SPARSE_CHECKOUT=0 test_out "disabling sparse checkout" build Test
test_exp -f $PKG/a/A.lean
test_out "restricting the checkout to 'c'" build Test
# untracked build outputs (e.g., `a/.lake`) are left behind
test_exp ! -e $PKG/a/A.lean

echo "# TEST: no subDir"
sed_i 's/subDir = "c"//' lakefile.toml
cp $PKG/c/lakefile.toml $PKG/c/A.lean ../repo/
git -C ../repo add --all
git -C ../repo commit -q -m "root package"
test_out "disabling sparse checkout" update
test_exp -f $PKG/a/A.lean
test_out "2" build Test
rm -rf $PKG
test_run update
test_exp ! -e $PKG/.git/info/sparse-checkout
popd

# Cleanup
rm -rf repo/.git
rm -f produced.out test/produced.out
