#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

# Test the functionality of `lake env`
# Also test https://github.com/leanprover/lake/issues/179

# Test `env` with no command
$LAKE env | grep ".*=.*"

# Test installation variables are set
# NOTE: `printenv` exits with code 1 if the variable is not set
$LAKE env printenv LAKE
$LAKE env printenv LAKE_HOME
$LAKE env printenv LEAN
$LAKE env printenv LEAN_GITHASH
$LAKE env printenv LEAN_SYSROOT
$LAKE env printenv LEAN_AR | grep --color ar
$LAKE env printenv LEAN_PATH
$LAKE -d ../../examples/hello env printenv LEAN_PATH | grep --color hello
$LAKE env printenv LEAN_SRC_PATH | grep --color lake
$LAKE -d ../../examples/hello env printenv LEAN_SRC_PATH | grep --color hello
$LAKE -d ../../examples/hello env printenv PATH | grep --color hello

# Test that `env` preserves the input environment for certain variables
test "`$LAKE env env ELAN_TOOLCHAIN=foo $LAKE env printenv ELAN_TOOLCHAIN`" = foo
test "`LEAN_GITHASH=foo $LAKE env printenv LEAN_GITHASH`" = foo
test "`LEAN_AR=foo $LAKE env printenv LEAN_AR`" = foo
test "`LEAN_CC=foo $LAKE env printenv LEAN_CC`" = foo

# Test `LAKE_PKG_URL_MAP` setting and errors
test "`LAKE_PKG_URL_MAP='{"a":"a"}' $LAKE env printenv LAKE_PKG_URL_MAP`" = '{"a":"a"}'
(LAKE_PKG_URL_MAP=foo $LAKE env 2>&1 || true) | grep --color invalid
(LAKE_PKG_URL_MAP=0 $LAKE env 2>&1 || true) | grep --color invalid

# Test that the platform-specific shared library search path is set
if [ "$OS" = Windows_NT ]; then
$LAKE env which libleanshared.dll # DLL in `bin` directory is in `PATH`
elif [ "`uname`" = Darwin ]; then
# MacOS's System Integrity Protection does not permit
# us to spawn a `printenv` process with `DYLD_LIBRARY_PATH` set
# https://apple.stackexchange.com/questions/212945/unable-to-set-dyld-fallback-library-path-in-shell-on-osx-10-11-1
$LAKE env | grep DYLD_LIBRARY_PATH | grep --color lib/lean
$LAKE -d ../../examples/hello env | grep DYLD_LIBRARY_PATH | grep --color examples/hello
else
$LAKE env printenv LD_LIBRARY_PATH  | grep --color lib/lean
$LAKE -d ../../examples/hello env printenv LD_LIBRARY_PATH | grep --color examples/hello
fi
