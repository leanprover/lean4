#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Since committing a Git repository to a Git repository is not well-supported,
# We reinitialize the `bar1` repository on each test.
echo "# SETUP"
set -x
pushd bar1
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "initial commit"
popd
set +x

# Test the functionality of package overrides

echo "# Tests"

# Test dependency resolution without overrides
test_run resolve-deps -R
test_out "bar1" exe bar

# Test the `--packages` option
test_run resolve-deps -R -Kfoo --packages=packages.json
test_out "bar2" --packages=packages.json exe bar
test_out "foo" --packages=packages.json exe foo

# Test overrides are properly removed when reconfigured
test_run resolve-deps -R
test_out "bar1" exe bar

# Test the use of `.lake/package-overrides.json`
test_cmd cp packages.json .lake/package-overrides.json
test_run resolve-deps -R -Kfoo
test_out "bar2" exe bar
test_out "foo" exe foo

# Cleanup
rm -f produced.out
