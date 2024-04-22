#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test that `moreLinkArgs` are included when linking precompiled modules
($LAKE build +Foo:dynlib 2>&1 || true) | grep -- "-lBaz"
