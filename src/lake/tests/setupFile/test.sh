#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

#---
# Test `setup-file` functionality
#---

# Test that, by default, no plugins are used.
$LAKE setup-file bogus Foo | grep -F --color '"pluginPaths":[]'

# Test that, by default, no dynlibs are used.
$LAKE setup-file bogus Foo | grep -F --color '"loadDynlibPaths":[]'

# Test that `setup-file` on an invalid Lean configuration file succeeds.
$LAKE -f invalid.lean setup-file invalid.lean Lake

# Test that `setup-file` on a configuration file uses the Lake plugin,
# even if the file is invalid and/or is not using a `Lake` import.
$LAKE -f invalid.lean setup-file invalid.lean |
  (grep -F --color '"pluginPaths":[]' && exit 1 || true)
