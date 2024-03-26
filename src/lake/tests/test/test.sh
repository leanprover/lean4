#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

# Script test runner
$LAKE -f script.lean test | grep -F "script: []"
$LAKE -f script.lean test -- hello | grep --color "hello"

# Executable test runner
$LAKE -f exe.lean test | grep -F "exe: []"
$LAKE -f exe.lean test -- hello | grep --color "hello"

# Test runner validation
($LAKE -f two.lean test 2>&1 && false || true) | grep --color "only one"
($LAKE -f none.lean test 2>&1 && false || true) | grep --color "package has no"

# Test runner checker
$LAKE -f exe.lean check-test
$LAKE -f script.lean check-test
($LAKE -f none.lean check-test && false || true)
($LAKE -f two.lean check-test && false || true)
