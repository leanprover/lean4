cat > "$TMP_DIR/test.c" <<'EOF'
#if defined(__SIZEOF_INT128__)
#define LEAN_TEST_HAS_UINT128
#undef __SIZEOF_INT128__
#endif
#include <lean/lean.h>

#include <stdint.h>

#if defined(LEAN_TEST_HAS_UINT128)
static int check(uint64_t a, uint64_t b, uint64_t modulus) {
    uint64_t expected = modulus == 0
        ? a * b
        : (uint64_t)((unsigned __int128)a * (unsigned __int128)b % modulus);
    return lean_uint64_mul_mod(a, b, modulus) == expected;
}
#endif

int main() {
#if defined(LEAN_TEST_HAS_UINT128)
    if (!check(UINT64_MAX, UINT64_MAX, 0)) return 1;
    if (!check(UINT64_MAX, UINT64_MAX, 1)) return 1;
    if (!check(UINT64_MAX, UINT64_MAX, UINT64_C(18446744073709551557))) return 1;

    uint64_t a = UINT64_C(0x243f6a8885a308d3);
    uint64_t b = UINT64_C(0x13198a2e03707344);
    uint64_t modulus = UINT64_C(0xa4093822299f31d0);
    for (unsigned i = 0; i < 1000000; ++i) {
        a ^= a << 13;
        a ^= a >> 7;
        a ^= a << 17;
        b ^= b << 7;
        b ^= b >> 9;
        b ^= b << 8;
        modulus ^= modulus << 11;
        modulus ^= modulus >> 13;
        modulus ^= modulus << 17;
        if (!check(a, b, modulus)) return 1;
    }
#endif
    return 0;
}
EOF

read -ra CC_ARGS <<< "${LEAN_CC:-${CC:-cc}}"
read -ra LEANC_ARGS <<< "$LEANC_OPTS"
run "${CC_ARGS[@]}" -I"$SRC_DIR/include" "${LEANC_ARGS[@]}" -std=c11 \
  "$TMP_DIR/test.c" -o "$TMP_DIR/test"
run "$TMP_DIR/test"
