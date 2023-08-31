#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

# Test that `moreLinkArgs` are included when linking precompiled modules
($LAKE build Foo 2>&1 || true) | grep -- "-lBaz"
