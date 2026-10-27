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
WORK=$(pwd)

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
popd

# bar: requires foo@v1 and commits the resulting manifest
mkdir bar
pushd bar
cat > lakefile.toml <<TOML
name = "bar"

[[require]]
name = "foo"
git = "$WORK/foo"
rev = "v1"
TOML
test_run update --keep-toolchain
echo /.lake > .gitignore
init_git
popd

# root: requires foo@v2 before bar
mkdir root
pushd root
cat > lakefile.toml <<TOML
name = "root"

[[require]]
name = "foo"
git = "$WORK/foo"
rev = "v2"

[[require]]
name = "bar"
git = "$WORK/bar"
rev = "master"
TOML

V2=$(git -C ../foo rev-parse v2)

check_foo() {
  test_cmd_eq "$V2" jq -r '.packages[] | select(.name == "foo") | .rev' lake-manifest.json
  test_cmd_eq "false" jq -r '.packages[] | select(.name == "foo") | .inherited' lake-manifest.json
}

test_run update
check_foo
rm -rf .lake lake-manifest.json
test_run update --keep-toolchain
check_foo
popd

# Cleanup
cd ..
./clean.sh
