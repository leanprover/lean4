#!/usr/bin/env bash
set -euo pipefail

# Deermine shared library extension
if [ "${OS:-}" = Windows_NT ]; then
LIB_PREFIX=
SHLIB_EXT=dll
elif [ "`uname`" = Darwin ]; then
LIB_PREFIX=lib
SHLIB_EXT=dylib
else
LIB_PREFIX=lib
SHLIB_EXT=so
fi

# Reset test
./clean.sh
lake update -q

# Build plugin
lake build
LIB_DIR=.lake/build/lib
SHLIB=$LIB_DIR/${LIB_PREFIX}UserPlugin.$SHLIB_EXT
test -f $SHLIB || {
  echo "Plugin library not found; $LIB_DIR contains:"
  ls $LIB_DIR
  exit 1
}
PLUGIN=$LIB_DIR/UserPlugin.$SHLIB_EXT
mv $SHLIB $PLUGIN

# Expected test output
EXPECTED_OUT="Ran builtin initializer"

# Test plugin via `lean`
echo | lean --plugin=$PLUGIN --stdin | diff <(echo "$EXPECTED_OUT") -

# Test plugin via `Lean.loadPlugin`
lean --run test.lean $PLUGIN | diff <(echo "$EXPECTED_OUT") -

# Print success
echo "Tests completed successfully."
