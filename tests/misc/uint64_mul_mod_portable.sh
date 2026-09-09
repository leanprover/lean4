cat > "$TMP_DIR/test.cpp" <<'EOF'
#if defined(__SIZEOF_INT128__)
#define LEAN_TEST_HAS_UINT128
#undef __SIZEOF_INT128__
#endif
#include <lean/lean.h>

#include <cstdint>

int main() {
#if defined(LEAN_TEST_HAS_UINT128)
    auto check = [](uint64_t a, uint64_t b, uint64_t modulus) {
        uint64_t expected = modulus == 0
            ? a * b
            : static_cast<uint64_t>(static_cast<__uint128_t>(a) * b % modulus);
        return lean_uint64_mul_mod(a, b, modulus) == expected;
    };

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

read -ra CXX_ARGS <<< "$CXX"
run "${CXX_ARGS[0]}" -I"$SRC_DIR/include" "${CXX_ARGS[@]:1}" -std=c++17 \
  "$TMP_DIR/test.cpp" -o "$TMP_DIR/test"
run "$TMP_DIR/test"
