cat > "$TMP_DIR/test.c" <<'EOF'
#if defined(__SIZEOF_INT128__)
#define LEAN_TEST_HAS_UINT128
#undef __SIZEOF_INT128__
#endif
#include <lean/lean.h>

#include <stdint.h>

#if defined(LEAN_TEST_HAS_UINT128)
static int check(uint64_t a, uint64_t b) {
    uint64_t expected = (uint64_t)(((unsigned __int128)a * (unsigned __int128)b) >> 64);
    return lean_uint64_mul_hi(a, b) == expected;
}
#endif

int main() {
#if defined(LEAN_TEST_HAS_UINT128)
    if (!check(UINT64_C(1) << 32, UINT64_C(1) << 32)) return 1;
    if (!check(UINT64_C(1) << 63, 2)) return 1;
    if (!check(UINT64_MAX, UINT64_MAX)) return 1;

    uint64_t a = UINT64_C(0x243f6a8885a308d3);
    uint64_t b = UINT64_C(0x13198a2e03707344);
    for (unsigned i = 0; i < 1000000; ++i) {
        a ^= a << 13;
        a ^= a >> 7;
        a ^= a << 17;
        b ^= b << 7;
        b ^= b >> 9;
        b ^= b << 8;
        if (!check(a, b)) return 1;
    }
#endif
    return 0;
}
EOF

read -ra CC_ARGS <<< "$LEAN_CC"
read -ra LEANC_ARGS <<< "$LEANC_OPTS"
run "${CC_ARGS[@]}" -I"$SRC_DIR/include" "${LEANC_ARGS[@]}" -std=c11 \
  "$TMP_DIR/test.c" -o "$TMP_DIR/test"
run "$TMP_DIR/test"
