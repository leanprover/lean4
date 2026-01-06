#!/usr/bin/env bash
source ../common.sh

# Derive module name from filename
module="${f%.lean}"

# Add current directory to LEAN_PATH so imports work
export LEAN_PATH=".:${LEAN_PATH:-}"

# Build all .lean files in dependency order
# Only do this once by checking if we've already built
if [ ! -f ".built_marker" ]; then
    # Multiple passes to handle dependencies (suppress all output)
    for pass in 1 2 3; do
        for leanfile in *.lean; do
            modname="${leanfile%.lean}"
            if [ ! -f "${modname}.olean" ]; then
                lean --root=../.. -Dlinter.all=false -o "${modname}.olean" "$leanfile" >/dev/null 2>&1 || true
            fi
        done
    done
    touch .built_marker
fi

# Now build our specific file (capture any build errors)
exec_check_raw lean --root=../.. -Dlinter.all=false -o "${module}.olean" "$f"

# Check for --fresh mode test
if [ -f "$f.fresh.expected.out" ]; then
    # Test --fresh mode (expect failure)
    expected_ret=1
    exec_check leanchecker --fresh "$module"
    # Use fresh expected output for comparison
    mv "$f.produced.out" "$f.fresh.produced.out"
    f_save="$f"
    f="$f.fresh"
    diff_produced
    f="$f_save"
fi

# Check for normal mode test
if [ -f "$f.expected.out" ]; then
    # Expect failure with specific output
    expected_ret=1
    exec_check leanchecker "$module"
    diff_produced
elif [ ! -f "$f.fresh.expected.out" ]; then
    # No expected output files - expect success (exit 0)
    exec_check_raw leanchecker "$module"
fi
