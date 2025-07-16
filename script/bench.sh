#!/usr/bin/env bash
set -euo pipefail

cmake --preset release -DUSE_LAKE=ON 1>&2

# We benchmark against stage 2 to test new optimizations.
timeout -s KILL 1h time make -C build/release -j$(nproc) stage2 1>&2
export PATH=$PWD/build/release/stage2/bin:$PATH

# The extra opts used to be passed to the Makefile during benchmarking only but with Lake it is
# easier to configure them statically.
cmake -B build/release/stage2 -S src -DLEAN_EXTRA_LAKEFILE_TOML='weakLeanArgs=["-Dprofiler=true", "-Dprofiler.threshold=9999999", "--stats"]' 1>&2

cd tests/bench
timeout -s KILL 1h time temci exec --config speedcenter.yaml --in speedcenter.exec.velcom.yaml 1>&2
temci report run_output.yaml --reporter codespeed2
