#!/usr/bin/env bash
# Simulates a `lean` compile failure: writes a recognisable line to
# stderr and exits non-zero. Used to verify that wrapper exit code +
# stderr surface through Lake unchanged.
echo "error: simulated compile failure from wrapper" >&2
exit 1
