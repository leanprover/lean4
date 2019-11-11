#!/usr/bin/env bash
emulator=$1
lean_bin=$2
leanchecker_bin=$3
export_file=$4
export LEAN_PATH=$5

set -ex

cd "$LEAN_PATH"
# We pass "$LEAN_PATH" as a last argument here, because we don't have lrealpath on emscripten
$emulator "$lean_bin" --recursive --export="$export_file" "$LEAN_PATH"
$emulator "$leanchecker_bin" "$export_file" nat.add_assoc
