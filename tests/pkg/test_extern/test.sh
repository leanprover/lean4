#!/usr/bin/env bash

#!/bin/bash

rm -rf .lake/build

# Function to process the output
verify_output() {
    awk '/error: stdout:/, /error: external command/' | sed '/error: external command/d'
}

lake build 2>&1 | verify_output > produced.txt

# Compare the actual output with the expected output
if diff -q produced.txt expected.txt > /dev/null; then
    echo "Output matches expected output."
    rm produced.txt
    exit 0
else
    echo "Output differs from expected output:"
    diff produced.txt expected.txt
    rm produced.txt
    exit 1
fi
