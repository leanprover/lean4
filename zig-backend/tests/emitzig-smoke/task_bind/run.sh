#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ZB_DIR="$(cd -- "$SCRIPT_DIR/../../.." && pwd)"
LEAN4_DIR="${LEAN4_DIR:-$(dirname "$ZB_DIR")}"
GMP_PREFIX="${GMP_PREFIX:-/opt/homebrew/opt/gmp}"
LIBUV_PREFIX="${LIBUV_PREFIX:-/opt/homebrew/opt/libuv}"
EMITZIG_DIR="$ZB_DIR/src/EmitZig"
COMMON_DIR="$ZB_DIR/tests/emitzig-smoke/common"
LAKE_BIN="$LEAN4_DIR/build/release/stage1/bin/lake"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/emitzig-smoke.task_bind.XXXXXX")"
TMP_INCLUDE_DIR="$TMP_DIR/include"
OUT_ZIG="$TMP_DIR/task_bind.zig"
EMITZIG_O="$TMP_DIR/task_bind.o"
DRIVER_O="$TMP_DIR/driver.o"
TASK_SHIMS_O="$TMP_DIR/task_api_shims.o"
COMPAT_O="$TMP_DIR/compat.o"
OUT_BIN="$TMP_DIR/task_bind"
ACTUAL_TXT="$TMP_DIR/actual.txt"

cleanup() {
  rm -rf "$TMP_DIR"
}

trap cleanup EXIT

if [ "${EMITZIG_SMOKE_SKIP_ZIG_BUILD:-0}" != "1" ]; then
  cd "$ZB_DIR"
  zig build
fi

"$COMMON_DIR/write_config_stub.sh" "$TMP_INCLUDE_DIR"

cd "$EMITZIG_DIR"
"$LAKE_BIN" exe emitzig "$SCRIPT_DIR/TaskBind.lean" -o "$OUT_ZIG"

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -DEMITZIG_INIT_FN=initialize_TaskBind \
  -DEMITZIG_MAIN_FN=l___private_TaskBind_0__main \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$COMMON_DIR/driver.c" \
  -o "$DRIVER_O"

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$COMMON_DIR/task_api_shims.c" \
  -o "$TASK_SHIMS_O"

c++ -Wall -Wextra -pedantic -std=c++17 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  -I "$LEAN4_DIR/src" \
  "$COMMON_DIR/compat.cpp" \
  -o "$COMPAT_O"

zig build-obj \
  "$OUT_ZIG" \
  -fno-entry \
  -femit-bin="$EMITZIG_O"

cc \
  "$EMITZIG_O" \
  "$DRIVER_O" \
  "$TASK_SHIMS_O" \
  "$COMPAT_O" \
  "$ZB_DIR/zig-out/lib/libleanrt-zig.a" \
  "$ZB_DIR/zig-out/lib/libleanrt_cpp_partial.a" \
  -L "$LEAN4_DIR/build/release/stage1/lib/lean" \
  -lleancpp \
  -lInit \
  -lStd \
  -lLean \
  -lLake \
  -L "$GMP_PREFIX/lib" \
  -lgmp \
  -L "$LIBUV_PREFIX/lib" \
  -luv \
  -lc++ \
  -lpthread \
  -lm \
  -o "$OUT_BIN"

"$OUT_BIN" > "$ACTUAL_TXT"
diff "$ACTUAL_TXT" "$SCRIPT_DIR/expected_stdout.txt"
