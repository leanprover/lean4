cat > "$TMP_DIR/test.c" <<'EOF'
#if defined(__SIZEOF_INT128__)
#define LEAN_TEST_HAS_UINT128
#undef __SIZEOF_INT128__
#endif
#include LEAN_TEST_HEADER

#include <stdint.h>
#include <stdio.h>

static int check_expected(uint64_t a, uint64_t b, uint64_t expected) {
    uint64_t actual = lean_uint64_mul_hi(a, b);
    if (actual != expected) {
        fprintf(stderr, "mul_hi(%016llx, %016llx) = %016llx, expected %016llx\n",
            (unsigned long long)a, (unsigned long long)b,
            (unsigned long long)actual, (unsigned long long)expected);
        return 0;
    }
    return 1;
}

#if defined(LEAN_TEST_HAS_UINT128)
static int check(uint64_t a, uint64_t b) {
    uint64_t expected = (uint64_t)(((unsigned __int128)a * (unsigned __int128)b) >> 64);
    return check_expected(a, b, expected);
}
#endif

static const uint64_t vectors[][3] = {
    {UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000), UINT64_C(0x0000000000000000)},
    {UINT64_C(0x0000000000000001), UINT64_C(0x0000000000000001), UINT64_C(0x0000000000000000)},
    {UINT64_C(0xFFFFFFFFFFFFFFFF), UINT64_C(0x0000000000000001), UINT64_C(0x0000000000000000)},
    {UINT64_C(0x0000000000000001), UINT64_C(0xFFFFFFFFFFFFFFFF), UINT64_C(0x0000000000000000)},
    {UINT64_C(0xFFFFFFFFFFFFFFFF), UINT64_C(0xFFFFFFFFFFFFFFFF), UINT64_C(0xFFFFFFFFFFFFFFFE)},
    {UINT64_C(0x0000000100000000), UINT64_C(0x0000000100000000), UINT64_C(0x0000000000000001)},
    {UINT64_C(0x8000000000000000), UINT64_C(0x0000000000000002), UINT64_C(0x0000000000000001)},
    {UINT64_C(0x0000000000000002), UINT64_C(0x8000000000000000), UINT64_C(0x0000000000000001)},
    {UINT64_C(0x00000000FFFFFFFF), UINT64_C(0x00000000FFFFFFFF), UINT64_C(0x0000000000000000)},
    {UINT64_C(0xFFFFFFFF00000000), UINT64_C(0xFFFFFFFF00000000), UINT64_C(0xFFFFFFFE00000001)},
    {UINT64_C(0xFFFFFFFF00000000), UINT64_C(0x00000000FFFFFFFF), UINT64_C(0x00000000FFFFFFFE)},
    {UINT64_C(0x00000000FFFFFFFF), UINT64_C(0xFFFFFFFF00000000), UINT64_C(0x00000000FFFFFFFE)},
    {UINT64_C(0x123456789ABCDEF0), UINT64_C(0x0FEDCBA987654321), UINT64_C(0x0121FA00AD77D742)},
    {UINT64_C(0x0FEDCBA987654321), UINT64_C(0x123456789ABCDEF0), UINT64_C(0x0121FA00AD77D742)},
    {UINT64_C(0x243F6A8885A308D3), UINT64_C(0x13198A2E03707344), UINT64_C(0x02B452AA3C8F8D75)},
};

int main() {
    for (size_t i = 0; i < sizeof(vectors) / sizeof(vectors[0]); ++i) {
        if (!check_expected(vectors[i][0], vectors[i][1], vectors[i][2])) return 1;
    }
#if defined(LEAN_TEST_HAS_UINT128)
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

read -ra LEANC_ARGS <<< "$LEANC_OPTS"
run leanc "-DLEAN_TEST_HEADER=\"$SRC_DIR/include/lean/lean.h\"" \
  "${LEANC_ARGS[@]}" -std=c11 \
  "$TMP_DIR/test.c" -o "$TMP_DIR/test"
run "$TMP_DIR/test"
