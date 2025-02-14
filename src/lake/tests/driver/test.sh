#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Script driver
$LAKE -f script.lean test | grep --color -F "script: []"
$LAKE -f script.lean lint | grep --color -F "script: []"
$LAKE -f script.lean test -- hello | grep --color "hello"
$LAKE -f script.lean lint -- hello | grep --color "hello"

# Executable driver
$LAKE -f exe.lean test | grep --color -F "exe: []"
$LAKE -f exe.toml test | grep --color -F "exe: []"
$LAKE -f exe.lean lint | grep --color -F "exe: []"
$LAKE -f exe.toml lint | grep --color -F "exe: []"
$LAKE -f exe.lean test -- hello | grep --color "hello"
$LAKE -f exe.toml test -- hello | grep --color "hello"
$LAKE -f exe.lean lint -- hello | grep --color "hello"
$LAKE -f exe.toml lint -- hello | grep --color "hello"

# Library test driver
rm -f .lake/build/lib/lean/Test.olean
$LAKE -f lib.lean test | grep --color -F "Built Test"
rm -f .lake/build/lib/lean/Test.olean
$LAKE -f lib.toml test | grep --color -F "Built Test"
($LAKE -f lib.lean test -- hello 2>&1 && exit 1 || true) | grep --color "arguments cannot be passed"
($LAKE -f lib.toml test -- hello 2>&1 && exit 1 || true) | grep --color "arguments cannot be passed"

# Upstream driver
rm -f lake-manifest.json
$LAKE -f dep.lean test | grep --color -F "dep: []"
$LAKE -f dep.toml test | grep --color -F "dep: []"
$LAKE -f dep.lean lint | grep --color -F "dep: []"
$LAKE -f dep.toml lint | grep --color -F "dep: []"
$LAKE -f dep.lean test -- hello | grep --color "hello"
$LAKE -f dep.toml test -- hello | grep --color "hello"
$LAKE -f dep.lean lint -- hello | grep --color "hello"
$LAKE -f dep.toml lint -- hello | grep --color "hello"

# Test runner
$LAKE -f runner.lean test 2>&1 | grep --color -F " @[test_runner] has been deprecated"
$LAKE -f runner.toml test
$LAKE -f runner.lean check-test
$LAKE -f runner.toml check-test

# Driver validation
($LAKE -f two.lean test 2>&1 && exit 1 || true) | grep --color "only one"
($LAKE -f none.lean test 2>&1 && exit 1 || true) | grep --color "no test driver"
($LAKE -f none.toml test 2>&1 && exit 1 || true) | grep --color "no test driver"
($LAKE -f unknown.lean test 2>&1 && exit 1 || true) | grep --color "invalid test driver: unknown"
($LAKE -f unknown.toml test 2>&1 && exit 1 || true) | grep --color "invalid test driver: unknown"
($LAKE -f dep-unknown.lean test 2>&1 && exit 1 || true) | grep --color "unknown test driver package"
($LAKE -f dep-unknown.toml test 2>&1 && exit 1 || true) | grep --color "unknown test driver package"
($LAKE -f dep-invalid.lean test 2>&1 && exit 1 || true) | grep --color "invalid test driver"
($LAKE -f dep-invalid.toml test 2>&1 && exit 1 || true) | grep --color "invalid test driver"
($LAKE -f two.lean lint 2>&1 && exit 1 || true) | grep --color "only one"
($LAKE -f none.lean lint 2>&1 && exit 1 || true) | grep --color "no lint driver"
($LAKE -f none.toml lint 2>&1 && exit 1 || true) | grep --color "no lint driver"
($LAKE -f unknown.lean lint 2>&1 && exit 1 || true) | grep --color "invalid lint driver: unknown"
($LAKE -f unknown.toml lint 2>&1 && exit 1 || true) | grep --color "invalid lint driver: unknown"
($LAKE -f dep-unknown.lean lint 2>&1 && exit 1 || true) | grep --color "unknown lint driver package"
($LAKE -f dep-unknown.toml lint 2>&1 && exit 1 || true) | grep --color "unknown lint driver package"
($LAKE -f dep-invalid.lean lint 2>&1 && exit 1 || true) | grep --color "invalid lint driver"
($LAKE -f dep-invalid.toml lint 2>&1 && exit 1 || true) | grep --color "invalid lint driver"

# Driver checker
$LAKE -f exe.lean check-test
$LAKE -f exe.toml check-test
$LAKE -f exe.lean check-lint
$LAKE -f exe.toml check-lint
$LAKE -f dep.lean check-test
$LAKE -f dep.toml check-test
$LAKE -f dep.lean check-lint
$LAKE -f dep.toml check-lint
$LAKE -f script.lean check-test
$LAKE -f script.lean check-lint
$LAKE -f lib.lean check-test
$LAKE -f two.lean check-test && exit 1 || true
$LAKE -f two.lean check-lint && exit 1 || true
$LAKE -f none.lean check-test && exit 1 || true
$LAKE -f none.toml check-test && exit 1 || true
$LAKE -f none.lean check-lint && exit 1 || true
$LAKE -f none.toml check-lint && exit 1 || true

# Build checker
$LAKE -f build.lean check-build
$LAKE -f build.toml check-build
$LAKE -f none.lean check-build && exit 1 || true
$LAKE -f none.toml check-build && exit 1 || true
