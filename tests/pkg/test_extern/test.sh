#!/usr/bin/env bash

# We need a package test because we need multiple files with imports.
# Currently the other package tests all succeed,
# but here we need to check for a particular error message.
# This is just an ad-hoc text mangling script to extract the error message
# and account for some OS differences.
# Ideally there would be a more principled testing framework
# that took care of all this!

rm -rf .lake/build

# Function to process the output
verify_output() {
    # Normalize path separators from backslashes to forward slashes
    sed 's#\\#/#g' |
    awk '/error: stdout:/, /error: external command/' |
    sed '/error: external command/d'
}

lake build 2>&1 | verify_output > produced.txt

# Compare the actual output with the expected output
if diff --strip-trailing-cr -q produced.txt expected.txt > /dev/null; then
    echo "Output matches expected output."
    rm produced.txt
    exit 0
else
    echo "Output differs from expected output:"
    diff --strip-trailing-cr produced.txt expected.txt
    rm produced.txt
    exit 1
fi
