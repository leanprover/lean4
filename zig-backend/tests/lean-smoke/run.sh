#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ZB_DIR="$(cd -- "$SCRIPT_DIR/../.." && pwd)"
LEAN4_DIR="${LEAN4_DIR:-$(dirname "$ZB_DIR")}"
GMP_PREFIX="${GMP_PREFIX:-/opt/homebrew/opt/gmp}"
LIBUV_PREFIX="${LIBUV_PREFIX:-/opt/homebrew/opt/libuv}"
LEAN_BIN="$LEAN4_DIR/build/release/stage1/bin/lean"
LEAN_SRC="$ZB_DIR/tests/lean-smoke/Hello.lean"
EXPECTED_STDOUT="Hello, world!"
CHECK_LEAKS="${LEAN_SMOKE_CHECK_LEAKS:-0}"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lean-smoke.XXXXXX")"
TMP_INCLUDE_DIR="$TMP_DIR/include"
TMP_INCLUDE_LEAN_DIR="$TMP_INCLUDE_DIR/lean"
DRIVER_C="$TMP_DIR/driver.c"
COMPAT_CPP="$TMP_DIR/compat.cpp"
OUT_C="$TMP_DIR/hello.c"
HELLO_O="$TMP_DIR/hello.o"
DRIVER_O="$TMP_DIR/driver.o"
COMPAT_O="$TMP_DIR/compat.o"
OUT_BIN="$TMP_DIR/hello"
LEAK_LOG="$TMP_DIR/leaks.log"
FILTERED_LEAK_LOG="$TMP_DIR/leaks.filtered.log"
SUPPRESSIONS_FILE="$ZB_DIR/tests/lean-smoke/leaks-suppressions.txt"

cleanup() {
  rm -rf "$TMP_DIR"
}

trap cleanup EXIT

if [ ! -x "$LEAN_BIN" ]; then
  echo "missing Lean binary: $LEAN_BIN" >&2
  exit 1
fi

cd "$ZB_DIR"
if [ "${LEAN_SMOKE_SKIP_ZIG_BUILD:-0}" != "1" ]; then
  zig build
fi

"$LEAN_BIN" -R "$ZB_DIR" -c "$OUT_C" "$LEAN_SRC"

if [ ! -f "$OUT_C" ]; then
  echo "Lean did not emit C output: $OUT_C" >&2
  exit 1
fi

C_SIZE="$(wc -c < "$OUT_C")"
if [ "$C_SIZE" -lt 100 ]; then
  echo "Lean emitted C output smaller than expected: ${C_SIZE} bytes" >&2
  exit 1
fi

if ! grep -q '#include <lean/lean.h>' "$OUT_C"; then
  echo "Lean-emitted C does not include <lean/lean.h>" >&2
  exit 1
fi

mkdir -p "$TMP_INCLUDE_LEAN_DIR"

cat > "$TMP_INCLUDE_LEAN_DIR/config.h" <<'EOF'
#pragma once
#include <lean/version.h>

#define LEAN_IS_STAGE0 0
EOF

cat > "$DRIVER_C" <<'EOF'
#include <lean/lean.h>

char ** lean_setup_args(int argc, char ** argv);
void lean_initialize(void);

lean_object * initialize_tests_lean_x2dsmoke_Hello(uint8_t builtin);
lean_object * l___private_tests_lean_x2dsmoke_Hello_0__main(void);

static lean_object * run_main(int argc, char ** argv) {
  (void)argc;
  (void)argv;
  return l___private_tests_lean_x2dsmoke_Hello_0__main();
}

int main(int argc, char ** argv) {
  lean_object * res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = initialize_tests_lean_x2dsmoke_Hello(1 /* builtin */);
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

cat > "$COMPAT_CPP" <<'EOF'
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <vector>

#include "runtime/alloc.h"
#include "runtime/utf8.h"

namespace lean {
namespace {
unsigned get_utf8_size_impl(unsigned char c) {
  if ((c & 0x80) == 0) {
    return 1;
  } else if ((c & 0xE0) == 0xC0) {
    return 2;
  } else if ((c & 0xF0) == 0xE0) {
    return 3;
  } else if ((c & 0xF8) == 0xF0) {
    return 4;
  } else if ((c & 0xFC) == 0xF8) {
    return 5;
  } else if ((c & 0xFE) == 0xFC) {
    return 6;
  } else {
    return 1;
  }
}

template <typename T>
class push_back_trait;

template <>
class push_back_trait<char *> {
public:
  static void push(char *& s, unsigned char c) {
    *s = static_cast<char>(c);
    ++s;
  }
};

template <>
class push_back_trait<std::string> {
public:
  static void push(std::string& s, unsigned char c) {
    s.push_back(static_cast<char>(c));
  }
};

template <typename T>
unsigned push_unicode_scalar_core(T& d, unsigned code) {
  constexpr unsigned char tag_cont = static_cast<unsigned char>(0b10000000);
  constexpr unsigned char tag_two_b = static_cast<unsigned char>(0b11000000);
  constexpr unsigned char tag_three_b = static_cast<unsigned char>(0b11100000);
  constexpr unsigned char tag_four_b = static_cast<unsigned char>(0b11110000);

  if (code < 0x80) {
    push_back_trait<T>::push(d, static_cast<unsigned char>(code));
    return 1;
  } else if (code < 0x800) {
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x1F) | tag_two_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 2;
  } else if (code < 0x10000) {
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 12) & 0x0F) | tag_three_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 3;
  } else {
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 18) & 0x07) | tag_four_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 12) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 4;
  }
}
} // namespace

size_t utf8_strlen(char const* str) {
  size_t result = 0;
  while (*str != 0) {
    ++result;
    str += get_utf8_size_impl(static_cast<unsigned char>(*str));
  }
  return result;
}

size_t utf8_strlen(char const* str, size_t size) {
  size_t result = 0;
  size_t i = 0;
  while (i < size) {
    ++result;
    i += get_utf8_size_impl(static_cast<unsigned char>(str[i]));
  }
  return result;
}

size_t utf8_strlen(std::string const& str) {
  return utf8_strlen(str.data(), str.size());
}

optional<unsigned> get_utf8_first_byte_opt(unsigned char c) {
  if ((c & 0x80) == 0) {
    return optional<unsigned>(1);
  } else if ((c & 0xE0) == 0xC0) {
    return optional<unsigned>(2);
  } else if ((c & 0xF0) == 0xE0) {
    return optional<unsigned>(3);
  } else if ((c & 0xF8) == 0xF0) {
    return optional<unsigned>(4);
  } else {
    return optional<unsigned>();
  }
}

unsigned next_utf8(char const* str, size_t size, size_t& i) {
  unsigned c = static_cast<unsigned char>(str[i]);
  if ((c & 0x80) == 0) {
    ++i;
    return c;
  }

  if ((c & 0xE0) == 0xC0 && i + 1 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned r = ((c & 0x1F) << 6) | (c1 & 0x3F);
    if (r >= 0x80) {
      i += 2;
      return r;
    }
  }

  if ((c & 0xF0) == 0xE0 && i + 2 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    unsigned r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
    if (r >= 0x800 && (r < 0xD800 || r > 0xDFFF)) {
      i += 3;
      return r;
    }
  }

  if ((c & 0xF8) == 0xF0 && i + 3 < size) {
    unsigned c1 = static_cast<unsigned char>(str[i + 1]);
    unsigned c2 = static_cast<unsigned char>(str[i + 2]);
    unsigned c3 = static_cast<unsigned char>(str[i + 3]);
    unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
    if (r >= 0x10000 && r <= 0x10FFFF) {
      i += 4;
      return r;
    }
  }

  ++i;
  return c;
}

unsigned next_utf8(std::string const& str, size_t& i) {
  return next_utf8(str.data(), str.size(), i);
}

void utf8_decode(std::string const& str, std::vector<unsigned>& out) {
  size_t i = 0;
  while (i < str.size()) {
    out.push_back(next_utf8(str, i));
  }
}

bool validate_utf8_one(uint8_t const* str, size_t size, size_t& pos) {
  unsigned c = str[pos];
  if ((c & 0x80) == 0) {
    ++pos;
  } else if ((c & 0xE0) == 0xC0) {
    if (pos + 1 >= size) return false;
    unsigned c1 = str[pos + 1];
    if ((c1 & 0xC0) != 0x80) return false;
    unsigned r = ((c & 0x1F) << 6) | (c1 & 0x3F);
    if (r < 0x80) return false;
    pos += 2;
  } else if ((c & 0xF0) == 0xE0) {
    if (pos + 2 >= size) return false;
    unsigned c1 = str[pos + 1];
    unsigned c2 = str[pos + 2];
    if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80) return false;
    unsigned r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
    if (r < 0x800 || (r >= 0xD800 && r <= 0xDFFF)) return false;
    pos += 3;
  } else if ((c & 0xF8) == 0xF0) {
    if (pos + 3 >= size) return false;
    unsigned c1 = str[pos + 1];
    unsigned c2 = str[pos + 2];
    unsigned c3 = str[pos + 3];
    if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80 || (c3 & 0xC0) != 0x80) return false;
    unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
    if (r < 0x10000 || r > 0x10FFFF) return false;
    pos += 4;
  } else {
    return false;
  }
  return true;
}

bool validate_utf8(uint8_t const* str, size_t size, size_t& pos, size_t& i) {
  while (pos < size) {
    if (!validate_utf8_one(str, size, pos)) {
      return false;
    }
    ++i;
  }
  return true;
}

unsigned push_unicode_scalar(char* d, unsigned code) {
  return push_unicode_scalar_core<char*>(d, code);
}

void push_unicode_scalar(std::string& s, unsigned code) {
  push_unicode_scalar_core(s, code);
}
} // namespace lean

extern "C" void* mi_malloc_small(size_t size) {
  unsigned aligned = lean_align(static_cast<unsigned>(size), LEAN_OBJECT_SIZE_DELTA);
  void* mem = std::malloc(sizeof(size_t) + aligned);
  if (mem == nullptr) {
    return nullptr;
  }
  *static_cast<size_t*>(mem) = aligned;
  return static_cast<size_t*>(mem) + 1;
}

extern "C" void mi_free(void* ptr) {
  if (ptr == nullptr) {
    return;
  }
  std::free(static_cast<size_t*>(ptr) - 1);
}
EOF

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$OUT_C" \
  -o "$HELLO_O"

cc -Wall -Wextra -pedantic -x c -std=c11 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  "$DRIVER_C" \
  -o "$DRIVER_O"

c++ -Wall -Wextra -pedantic -std=c++17 -c \
  -I "$TMP_INCLUDE_DIR" \
  -I "$LEAN4_DIR/src/include" \
  -I "$LEAN4_DIR/build/release/stage1/include" \
  -I "$LEAN4_DIR/src" \
  "$COMPAT_CPP" \
  -o "$COMPAT_O"

cc \
  "$HELLO_O" \
  "$DRIVER_O" \
  "$COMPAT_O" \
  "$ZB_DIR/zig-out/lib/libleanrt-zig.a" \
  "$ZB_DIR/zig-out/lib/libleanrt_cpp_partial.a" \
  -L "$LEAN4_DIR/build/release/stage1/lib/lean" \
  -lleancpp \
  -lInit \
  -lStd \
  -lLean \
  -lLake \
  -L "$GMP_PREFIX/lib" -lgmp \
  -L "$LIBUV_PREFIX/lib" -luv \
  -lc++ -lpthread -lm \
  -o "$OUT_BIN"

set +e
ACTUAL_STDOUT="$("$OUT_BIN")"
PROGRAM_STATUS=$?
set -e

if [ "$PROGRAM_STATUS" -ne 0 ]; then
  echo "Lean smoke binary exited with status $PROGRAM_STATUS" >&2
  exit 1
fi

if [ "$ACTUAL_STDOUT" != "$EXPECTED_STDOUT" ]; then
  echo "unexpected stdout: '$ACTUAL_STDOUT'" >&2
  exit 1
fi

if [ "$CHECK_LEAKS" = "1" ]; then
  if [ ! -f "$SUPPRESSIONS_FILE" ]; then
    echo "missing leak suppressions file: $SUPPRESSIONS_FILE" >&2
    exit 1
  fi

  if ! command -v leaks >/dev/null 2>&1; then
    echo "LEAN_SMOKE_CHECK_LEAKS=1 requires /usr/bin/leaks" >&2
    exit 1
  fi

  set +e
  env MallocStackLoggingNoCompact=1 /usr/bin/leaks -quiet -atExit -- "$OUT_BIN" \
    2>&1 | tee "$LEAK_LOG" | grep -vFf "$SUPPRESSIONS_FILE" > "$FILTERED_LEAK_LOG"
  PIPESTATUS_CAPTURE=("${PIPESTATUS[@]}")
  set -e

  LEAK_STATUS="${PIPESTATUS_CAPTURE[0]}"
  TEE_STATUS="${PIPESTATUS_CAPTURE[1]}"

  if [ "$TEE_STATUS" -ne 0 ]; then
    cat "$LEAK_LOG" >&2
    echo "failed to capture leaks output" >&2
    exit 1
  fi

  if [ "$LEAK_STATUS" -gt 1 ]; then
    cat "$LEAK_LOG" >&2
    echo "leaks check failed with status $LEAK_STATUS" >&2
    exit 1
  fi

  if grep -q 'ROOT LEAK:' "$FILTERED_LEAK_LOG"; then
    cat "$FILTERED_LEAK_LOG" >&2
    echo "leaks output reported unsuppressed leaks" >&2
    exit 1
  fi

  if [ "$LEAK_STATUS" -eq 0 ] && ! grep -Eq '0 leaks for 0 total leaked bytes\.?' "$LEAK_LOG"; then
    cat "$LEAK_LOG" >&2
    echo "leaks output did not report a clean exit" >&2
    exit 1
  fi

  echo "leaks: 0 unsuppressed leaks after applying known delegated-runtime suppressions" >&2
fi

printf '%s\n' "$ACTUAL_STDOUT"
