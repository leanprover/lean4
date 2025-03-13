#!/usr/bin/env bash
set -euo pipefail
LAKE=${LAKE:-../../.lake/build/bin/lake}

#---
# Test `setup-file` functionality
#---

# Test that, by default. no plugins are used.
$LAKE setup-file bogus Foo | grep -F --color '"pluginPaths":[]'

# Test that a Lake import uses the Lake plugin.
$LAKE setup-file bogus Lake | (grep -F --color '"pluginPaths":[]' && exit 1 || true)

# Test that `setup-file` on an invalid Lean configuration file succeeds.
$LAKE -f invalid.lean setup-file invalid.lean Lake
