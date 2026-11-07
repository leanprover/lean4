#!/usr/bin/env bash
source ../common.sh
./clean.sh

if ! command -v jq > /dev/null; then
  echo "Skipping test: jq not found"
  exit 0
fi

# This test covers issue 15761
# https://github.com/leanprover/lean4/issues/15761

# A revision the root pins in its own `require` should win over the one
# locked in another dependency's manifest, with or without `--keep-toolchain`.

mkdir work
cd work
cp ../expected-manifest.json lake-manifest.json

# foo: tags `v1` and `v2`
mkdir foo
pushd foo
printf 'name = "foo"\n' > lakefile.toml
init_git
git tag v1
echo '-- v2' > Foo.lean
git add Foo.lean
git commit -m "second commit"
git tag v2
FOO_V2_REV=$(git rev-parse v2)
popd

# bar: requires foo@v1 and commits the resulting manifest
mkdir bar
pushd bar
cat > lakefile.toml <<TOML
name = "bar"

[[require]]
name = "foo"
git = "../foo"
rev = "v1"
TOML
test_run update --keep-toolchain
echo /.lake > .gitignore
init_git
BAR_REV=$(git rev-parse HEAD)
popd

# root: requires foo@v2 before bar
mkdir root
pushd root
cat > lakefile.toml <<TOML
name = "root"

[[require]]
name = "foo"
git = "../foo"
rev = "v2"

[[require]]
name = "bar"
git = "../bar"
rev = "master"
TOML

FOO_TMP=ffffffffffffffffffffffffffffffffffffffff
sed_i s/$FOO_TMP/$FOO_V2_REV/g ../lake-manifest.json
BAR_TMP=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
sed_i s/$BAR_TMP/$BAR_REV/g ../lake-manifest.json

test_run update
test_cmd diff -u --strip-trailing-cr ../lake-manifest.json lake-manifest.json
rm -rf .lake lake-manifest.json
test_run update --keep-toolchain
test_cmd diff -u --strip-trailing-cr ../lake-manifest.json lake-manifest.json
