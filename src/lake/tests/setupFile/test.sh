#!/usr/bin/env bash
set -euo pipefail
LAKE=${LAKE:-../../.lake/build/bin/lake}

#---
# Test `setup-file` functionality
#---

# Test that, by default, no plugins are used.
$LAKE setup-file bogus Foo | grep -F --color '"pluginPaths":[]'

# Test that, by default, no dynlibs are used.
$LAKE setup-file bogus Foo | grep -F --color '"loadDynlibPaths":[]'

# Test that `setup-file` on an invalid Lean configuration file succeeds.
$LAKE -f invalid.lean setup-file invalid.lean Lake
