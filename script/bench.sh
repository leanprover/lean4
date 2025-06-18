#!/usr/bin/env bash
set -euo pipefail

# We benchmark against stage 2 to test new optimizations.
timeout -s KILL 1h time bash -c 'mkdir -p build/release; cd build/release; cmake ../.. && make -j$(nproc) stage2' 1>&2
export PATH=$PWD/build/release/stage2/bin:$PATH
cd tests/bench
timeout -s KILL 1h time temci exec --config speedcenter.yaml --in speedcenter.exec.velcom.yaml 1>&2
temci report run_output.yaml --reporter codespeed2
