#!/usr/bin/env bash

# Process monads.txt to count lines and calculate portion with dependent motives

FILE="monads.txt"

if [ ! -f "$FILE" ]; then
    echo "Error: $FILE not found" >&2
    exit 1
fi

# Count total lines
total_lines=$(wc -l < "$FILE")

# Count lines with dependent motive (Is dependent: true)
dependent_count=$(grep -c "Is dependent: true" "$FILE")

# Calculate portion (as percentage) using awk
if [ "$total_lines" -eq 0 ]; then
    portion=0
    percentage=0
else
    portion=$(awk "BEGIN {printf \"%.4f\", $dependent_count / $total_lines}")
    percentage=$(awk "BEGIN {printf \"%.2f\", ($dependent_count / $total_lines) * 100}")
fi

# Output results
echo "Total lines: $total_lines"
echo "Matches with dependent motive: $dependent_count"
echo "Portion: $portion ($percentage%)"
