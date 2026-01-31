#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test the functionality of `lake env`
# Also test https://github.com/leanprover/lake/issues/179

# Test `env` with no command
echo "# TEST: Bare lake env"
$LAKE env | grep ".*=.*"

echo "# TEST: Variables in lake env"
# Test installation variables are set
# NOTE: `printenv` exits with code 1 if the variable is not set
test_out "lake" env printenv LAKE
test_run env printenv LAKE_HOME
test_out "lean" env printenv LEAN
test_run env printenv LEAN_GITHASH
test_run env printenv LEAN_SYSROOT
test_out "ar" env printenv LEAN_AR
test_run env printenv LEAN_PATH
test_out "hello" -d ../../examples/hello env printenv LEAN_PATH
test_out "lake" env printenv LEAN_SRC_PATH
test_out "hello" -d ../../examples/hello env printenv LEAN_SRC_PATH
test_out "hello" -d ../../examples/hello env printenv PATH
LAKE_CACHE_DIR= test_out "hello" -d ../../examples/hello env printenv PATH

# Test other variables are set
test_eq "false" env printenv LAKE_NO_CACHE

# Test that a workspace always sets the cache directory
LAKE_CACHE_DIR= test_run env -d ../../examples/hello env printenv LAKE_CACHE_DIR

# Test that `env` preserves the input environment for certain variables
echo "# TEST: Setting variables for lake env"
test_eq "foo" env env ELAN_TOOLCHAIN=foo $LAKE env printenv ELAN_TOOLCHAIN
test_out "foo" env env -u LAKE_CACHE_DIR ELAN_HOME=/ ELAN_TOOLCHAIN=foo \
  $LAKE env printenv LAKE_CACHE_DIR
LAKE_CACHE_DIR=foo test_eq "foo" env printenv LAKE_CACHE_DIR
LEAN_GITHASH=foo test_eq "foo" env printenv LEAN_GITHASH
LEAN_AR=foo test_eq "foo" env printenv LEAN_AR
LEAN_CC=foo test_eq "foo" env printenv LEAN_CC

# Test `LAKE_ARTIFACT_CACHE` setting and default
LAKE_ARTIFACT_CACHE=true test_eq "true" env printenv LAKE_ARTIFACT_CACHE
LAKE_ARTIFACT_CACHE=false test_eq "false" env printenv LAKE_ARTIFACT_CACHE
LAKE_ARTIFACT_CACHE= test_eq "" env printenv LAKE_ARTIFACT_CACHE
LAKE_ARTIFACT_CACHE= test_eq "false" -d ../../examples/hello env printenv LAKE_ARTIFACT_CACHE
LAKE_ARTIFACT_CACHE= test_eq "true" -f enableArtifactCache.toml env printenv LAKE_ARTIFACT_CACHE
test_cmd rm lake-manifest.json

# Test `LAKE_PKG_URL_MAP` setting and errors
echo "# TEST: LAKE_PKG_URL_MAP"
LAKE_PKG_URL_MAP='{"a":"a"}' test_eq '{"a":"a"}' env printenv LAKE_PKG_URL_MAP
LAKE_PKG_URL_MAP=foo test_err "invalid" env
LAKE_PKG_URL_MAP=0 test_err "invalid" env

# Test that the platform-specific shared library search path is set
echo "# TEST: Platform-specific shared library search path"
if [ "$OS" = Windows_NT ]; then
test_run env which libleanshared.dll # DLL in `bin` directory is in `PATH`
elif [ "$UNAME" = Darwin ]; then
# MacOS's System Integrity Protection does not permit
# us to spawn a `printenv` process with `DYLD_LIBRARY_PATH` set
# https://apple.stackexchange.com/questions/212945/unable-to-set-dyld-fallback-library-path-in-shell-on-osx-10-11-1
set -x
$LAKE env | grep DYLD_LIBRARY_PATH | grep --color lib/lean
$LAKE -d ../../examples/hello env | grep DYLD_LIBRARY_PATH | grep --color examples/hello
set +x
else
test_out "lib/lean" env printenv LD_LIBRARY_PATH
test_out "examples/hello" -d ../../examples/hello env printenv LD_LIBRARY_PATH
fi

# Cleanup
rm -f produced.out
