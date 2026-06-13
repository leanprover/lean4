#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ZB_DIR="$(cd -- "$SCRIPT_DIR/../.." && pwd)"
LEAN4_DIR="${LEAN4_DIR:-$(dirname "$ZB_DIR")}"
GMP_PREFIX="${GMP_PREFIX:-/opt/homebrew/opt/gmp}"
LIBUV_PREFIX="${LIBUV_PREFIX:-/opt/homebrew/opt/libuv}"
REFERENCE_BIN="$SCRIPT_DIR/reference/bignum_ref"
ZIG_BIN="$SCRIPT_DIR/zig/bignum_zig"
RESULTS_JSON="$SCRIPT_DIR/results.json"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/bignum-diff.XXXXXX")"
REFERENCE_STDOUT="$TMP_DIR/reference.stdout"
ZIG_STDOUT="$TMP_DIR/zig.stdout"
SUPPORT_OBJ="$TMP_DIR/mpz_alloc_support.o"

cleanup() {
  rm -rf "$TMP_DIR"
}

trap cleanup EXIT

if [ "${BIGNUM_DIFF_SKIP_ZIG_BUILD:-0}" != "1" ]; then
  cd "$ZB_DIR"
  zig build
fi

c++ -Wall -Wextra -pedantic -std=c++17 -c \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  -I "$LEAN4_DIR/src" \
  "$ZB_DIR/tests/abi-smoke/mpz_alloc_support.cpp" \
  -o "$SUPPORT_OBJ"

cc -Wall -Wextra -pedantic -std=c11 \
  -I "$GMP_PREFIX/include" \
  "$SCRIPT_DIR/common.c" \
  "$SCRIPT_DIR/reference/bignum_ref.c" \
  -L "$GMP_PREFIX/lib" \
  -lgmp \
  -lm \
  -o "$REFERENCE_BIN"

cc -Wall -Wextra -pedantic -std=c11 \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  -I "$GMP_PREFIX/include" \
  "$SCRIPT_DIR/common.c" \
  "$SCRIPT_DIR/zig/bignum_zig.c" \
  "$SUPPORT_OBJ" \
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
  -o "$ZIG_BIN"

"$REFERENCE_BIN" canonical > "$REFERENCE_STDOUT"
"$ZIG_BIN" canonical > "$ZIG_STDOUT"
cmp "$REFERENCE_STDOUT" "$ZIG_STDOUT"

"$ZIG_BIN" randomized "$RESULTS_JSON"

jq -e 'all(.ops[]; .pass == .total) and .allocator.net == 0' "$RESULTS_JSON" >/dev/null

ops_count="$(jq '.ops | length' "$RESULTS_JSON")"
total_cases="$(jq '[.ops[].total] | add' "$RESULTS_JSON")"
echo "bignum-diff: canonical=5 randomized_ops=${ops_count} total_cases=${total_cases} mismatches=0 leaks=0"
