#!/usr/bin/env bash
# Records each `bwrap` command line in `bwrap.log` next to this script, then defers to
# `../fake-bwrap.sh`. Lake starts the sandbox through `env -i`, so nothing here may rely on `PATH`.
# The values of the environment handed to the command are left out: they are the caller's.
dir="${BASH_SOURCE[0]%/*}"
line=()
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  line+=("${args[i]}")
  if [[ "${args[i]}" == --setenv ]]; then
    line+=("${args[i+1]}")
    i=$((i + 2))
  fi
done
echo "${line[*]}" >> "$dir/bwrap.log"
exec "$BASH" "$dir/../fake-bwrap.sh" "$@"
