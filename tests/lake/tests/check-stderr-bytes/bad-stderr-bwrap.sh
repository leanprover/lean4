#!/usr/bin/env bash
# A `bwrap` stand-in that writes a byte that is not UTF-8 to standard error when that is a pipe, that
# is, when Lake captures it rather than letting it through, and then runs the command as
# `../fake-bwrap.sh` does. Lake starts it through `env -i`, so only shell builtins are used here.
if [ -p /dev/stderr ]; then
  printf '\377\n' >&2
fi
exec "${0%/*}/../fake-bwrap.sh" "$@"
