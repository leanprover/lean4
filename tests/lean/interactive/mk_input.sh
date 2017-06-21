#!/usr/bin/env bash
# generate server input from "--^" markers
INPUT="$(cat)"
ESC_INPUT="${INPUT//$'\n'/\\n}"
ESC_INPUT="${ESC_INPUT//$'\r'/}"
ESC_INPUT="${ESC_INPUT//\"/\\\"}"
echo "{\"seq_num\": 0, \"command\": \"sync\", \"file_name\": \"f\", \"content\": \"$ESC_INPUT\"}"
awk '{
    i = match($0, /--\^/);
    if (i > 0) {
        printf("{\"seq_num\": %s, %s, \"file_name\": \"f\", \"line\": %s, \"column\": %s}\n", NR, substr($0, i + 4), NR - 1, i + 1);
    }
}' <<< "$INPUT"
