#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

# Script test runner
$LAKE -f script.lean test | grep --color -F "script: []"
$LAKE -f script.lean test -- hello | grep --color "hello"

# Executable test runner
$LAKE -f exe.lean test | grep --color -F "exe: []"
$LAKE -f exe.lean test -- hello | grep --color "hello"
$LAKE -f exe.toml test | grep --color -F "exe: []"
$LAKE -f exe.toml test -- hello | grep --color "hello"

# Test runner validation
($LAKE -f two.lean test 2>&1 && false || true) | grep --color "only one"
($LAKE -f none.lean test 2>&1 && false || true) | grep --color "no test runner"
($LAKE -f none.toml test 2>&1 && false || true) | grep --color "no test runner"

# Test runner checker
$LAKE -f exe.lean check-test
$LAKE -f exe.toml check-test
$LAKE -f script.lean check-test
($LAKE -f two.lean check-test && false || true)
($LAKE -f none.lean check-test && false || true)
($LAKE -f none.toml check-test && false || true)
