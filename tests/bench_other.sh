#!/usr/bin/env bash

# This script must be called from the repo root.
# The radar environment variables must be provided.
# See also the https://github.com/leanprover/radar readme.

cmake --preset release -DWFAIL=OFF
make -C build/release -j"$(nproc)" bench-part2
mv tests/part2.measurements.jsonl "$RADAR_OUT"
