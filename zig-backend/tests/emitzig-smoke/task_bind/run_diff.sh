#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ZB_DIR="$(cd -- "$SCRIPT_DIR/../../.." && pwd)"
LEAN4_DIR="${LEAN4_DIR:-$(dirname "$ZB_DIR")}"
GMP_PREFIX="${GMP_PREFIX:-/opt/homebrew/opt/gmp}"
LIBUV_PREFIX="${LIBUV_PREFIX:-/opt/homebrew/opt/libuv}"
EMITZIG_DIR="$ZB_DIR/src/EmitZig"
COMMON_DIR="$ZB_DIR/tests/emitzig-smoke/common"
LEAN_BIN="$LEAN4_DIR/build/release/stage1/bin/lean"
LAKE_BIN="$LEAN4_DIR/build/release/stage1/bin/lake"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/emitzig-diff.task_bind.XXXXXX")"
TMP_INCLUDE_DIR="$TMP_DIR/include"
EMITC_C="$TMP_DIR/task_bind.c"
EMITC_O="$TMP_DIR/task_bind-emitc.o"
EMITC_DRIVER_C="$TMP_DIR/task_bind-emitc-driver.c"
EMITC_DRIVER_O="$TMP_DIR/task_bind-emitc-driver.o"
EMITZIG_ZIG="$TMP_DIR/task_bind.zig"
EMITZIG_O="$TMP_DIR/task_bind-emitzig.o"
EMITZIG_DRIVER_O="$TMP_DIR/task_bind-emitzig-driver.o"
TASK_SHIMS_O="$TMP_DIR/task_api_shims.o"
COMPAT_O="$TMP_DIR/compat.o"
EMITC_BIN="$TMP_DIR/task_bind-emitc"
EMITZIG_BIN="$TMP_DIR/task_bind-emitzig"
EMITC_STDOUT="$TMP_DIR/emitc.stdout"
EMITZIG_STDOUT="$TMP_DIR/emitzig.stdout"

cleanup() {
  rm -rf "$TMP_DIR"
}

trap cleanup EXIT

if [ "${EMITZIG_SMOKE_SKIP_ZIG_BUILD:-0}" != "1" ]; then
  cd "$ZB_DIR"
  zig build
fi

"$COMMON_DIR/write_config_stub.sh" "$TMP_INCLUDE_DIR"

cat > "$EMITC_DRIVER_C" <<'EOF'
#include <lean/lean.h>

char ** lean_setup_args(int argc, char ** argv);
void lean_initialize(void);

lean_object * initialize_TaskBind(uint8_t builtin);
lean_object * l___private_TaskBind_0__main(void);

static lean_object * run_main(int argc, char ** argv) {
  (void)argc;
  (void)argv;
  return l___private_TaskBind_0__main();
}

int main(int argc, char ** argv) {
  lean_object * res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = initialize_TaskBind(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    return 0;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
EOF

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$EMITC_DRIVER_C" \
  -o "$EMITC_DRIVER_O"

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -DEMITZIG_INIT_FN=initialize_TaskBind \
  -DEMITZIG_MAIN_FN=l___private_TaskBind_0__main \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$COMMON_DIR/driver.c" \
  -o "$EMITZIG_DRIVER_O"

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

"$LEAN_BIN" -R "$SCRIPT_DIR" -c "$EMITC_C" "$SCRIPT_DIR/TaskBind.lean"

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$EMITC_C" \
  -o "$EMITC_O"

cc \
  "$EMITC_O" \
  "$EMITC_DRIVER_O" \
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
  -o "$EMITC_BIN"

cd "$EMITZIG_DIR"
"$LAKE_BIN" exe emitzig "$SCRIPT_DIR/TaskBind.lean" -o "$EMITZIG_ZIG"

zig build-obj \
  "$EMITZIG_ZIG" \
  -fno-entry \
  -femit-bin="$EMITZIG_O"

cc \
  "$EMITZIG_O" \
  "$EMITZIG_DRIVER_O" \
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
  -o "$EMITZIG_BIN"

"$EMITC_BIN" > "$EMITC_STDOUT"
"$EMITZIG_BIN" > "$EMITZIG_STDOUT"
diff "$EMITC_STDOUT" "$EMITZIG_STDOUT"
