#!/usr/bin/env bash
set -euo pipefail

rm -rf .lake/build
lake build

for f in LeanCheckerTests/*.lean; do
    # It would be nicer if `common.sh` did not hardcode a single input file
    set -- "$f"
    source ../../common.sh

    module="LeanCheckerTests.$(basename "$f" .lean)"
    # Check for --fresh mode test
    if [ -f "$f.fresh.expected.out" ]; then
        # Test --fresh mode (expect failure)
        expected_ret=1
        exec_check lake env leanchecker --fresh "$module"
        # Use fresh expected output for comparison
        mv "$f.produced.out" "$f.fresh.produced.out"
        f_save="$f"
        f="$f.fresh"
        diff_produced
        f="$f_save"
    # Check for normal mode test
    elif [ -f "$f.expected.out" ]; then
        # Expect failure with specific output
        expected_ret=1
        exec_check lake env leanchecker "$module"
        diff_produced
    else
        # No expected output files - expect success (exit 0)
        expected_ret=0
        exec_check_raw lake env leanchecker "$module"
    fi
done
