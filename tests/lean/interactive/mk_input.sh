#!/usr/bin/env bash
# generate server input from "--^" markers
echo "{\"seq_num\": 0, \"command\": \"sync\", \"file_name\": \"$1\"}"
awk '{
    i = match($0, /--\^/);
    if (i > 0) {
        printf("{\"seq_num\": %s, %s, \"file_name\": \"'"$1"'\", \"line\": %s, \"column\": %s}\n", NR, substr($0, i + 4), NR - 1, i + 1);
    }
}' < "$1"
