#!/usr/bin/env bash

# Usage:
#   ./run_all.sh file1 "args for file1" file2 "args for file2" ...

# Ensure arguments come in pairs
if (( $# % 2 != 0 )); then
    echo "Error: arguments must come in <file> <args> pairs."
    exit 1
fi

# Loop over pairs
while (( "$#" )); do
    file="$1"
    args="$2"
    shift 2

    echo "Processing file: $file"
    echo "Args: $args"

    for i in {1..3}; do
        echo "---- Run $i for $file ----"

        # Compile
        ./compile.sh "$file" || {
            echo "Compilation failed for $file"
            break
        }

        # Execute
        "./${file}.out" $args
    done

    echo "-------------------------"
done
