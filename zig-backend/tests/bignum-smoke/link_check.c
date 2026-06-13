#include <lean/lean.h>

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* The Zig allocator frees legacy small objects through mimalloc, which is
 * statically linked into Lean binaries but not shipped as a standalone
 * archive. Mirror the malloc-backed stubs used by tests/abi-smoke/bignum.c. */
void *mi_malloc(size_t size) {
    return malloc(size);
}

void mi_free(void *ptr) {
    free(ptr);
}

void mi_free_size(void *ptr, size_t size) {
    (void)size;
    free(ptr);
}

extern lean_object *lean_nat_big_succ(lean_object *a);
extern lean_object *lean_nat_big_add(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_sub(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_mul(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_div(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_div_exact(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_mod(lean_object *a1, lean_object *a2);
extern bool lean_nat_big_eq(lean_object *a1, lean_object *a2);
extern bool lean_nat_big_le(lean_object *a1, lean_object *a2);
extern bool lean_nat_big_lt(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_land(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_lor(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_xor(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_shiftl(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_big_shiftr(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_pow(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_gcd(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_log2(lean_object *a);

extern lean_object *lean_cstr_to_nat(char const *n);
extern lean_object *lean_big_usize_to_nat(size_t n);
extern lean_object *lean_big_uint64_to_nat(uint64_t n);

extern lean_object *lean_cstr_to_int(char const *n);
extern lean_object *lean_big_int_to_int(int n);
extern lean_object *lean_big_size_t_to_int(size_t n);
extern lean_object *lean_big_int64_to_int(int64_t n);
extern lean_object *lean_big_int_to_nat(lean_object *a);
extern lean_object *lean_int_big_neg(lean_object *a);
extern lean_object *lean_int_big_add(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_sub(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_mul(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_div(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_div_exact(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_mod(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_ediv(lean_object *a1, lean_object *a2);
extern lean_object *lean_int_big_emod(lean_object *a1, lean_object *a2);
extern bool lean_int_big_eq(lean_object *a1, lean_object *a2);
extern bool lean_int_big_le(lean_object *a1, lean_object *a2);
extern bool lean_int_big_lt(lean_object *a1, lean_object *a2);
extern bool lean_int_big_nonneg(lean_object *a);

extern uint8_t lean_uint8_of_big_nat(lean_object *a);
extern uint16_t lean_uint16_of_big_nat(lean_object *a);
extern uint32_t lean_uint32_of_big_nat(lean_object *a);
extern uint64_t lean_uint64_of_big_nat(lean_object *a);
extern size_t lean_usize_of_big_nat(lean_object *a);
extern int8_t lean_int8_of_big_int(lean_object *a);
extern int16_t lean_int16_of_big_int(lean_object *a);
extern int32_t lean_int32_of_big_int(lean_object *a);
extern int64_t lean_int64_of_big_int(lean_object *a);
extern ptrdiff_t lean_isize_of_big_int(lean_object *a);
extern uint64_t lean_uint64_mix_hash(uint64_t h, uint64_t k);

extern uint8_t leanrt_test_nat_eq_cstr(lean_object *o, char const *value);
extern uint8_t leanrt_test_cpp_int_eq_cstr(lean_object *o, char const *value);

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

static void free_nat(lean_object *o) {
    if (!lean_is_scalar(o)) lean_dec(o);
}

static void free_int(lean_object *o) {
    if (!lean_is_scalar(o)) lean_dec(o);
}

int main(void) {
    lean_object *nat_a;
    lean_object *nat_b;
    lean_object *nat_c;
    lean_object *int_a;
    lean_object *int_b;
    lean_object *int_c;
    lean_object *tmp;

    lean_initialize_runtime_module();
    lean_initialize_thread();

    nat_a = lean_cstr_to_nat("340282366920938463463374607431768211456");
    nat_b = lean_big_uint64_to_nat(UINT64_MAX);
    nat_c = lean_big_usize_to_nat((size_t)LEAN_MAX_SMALL_NAT + 1u);
    CHECK(leanrt_test_nat_eq_cstr(nat_a, "340282366920938463463374607431768211456"));
    CHECK(leanrt_test_nat_eq_cstr(nat_b, "18446744073709551615"));
    CHECK(leanrt_test_nat_eq_cstr(nat_c, "9223372036854775808"));

    tmp = lean_nat_big_succ(nat_a);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "340282366920938463463374607431768211457"));
    free_nat(tmp);
    tmp = lean_nat_big_add(nat_a, nat_b);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "340282366920938463481821351505477763071"));
    free_nat(tmp);
    tmp = lean_nat_big_sub(nat_a, nat_b);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "340282366920938463444927863358058659841"));
    free_nat(tmp);
    tmp = lean_nat_big_mul(nat_b, nat_c);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "170141183460469231722463931679029329920"));
    free_nat(tmp);
    tmp = lean_nat_big_div(nat_a, nat_c);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "36893488147419103232"));
    free_nat(tmp);
    tmp = lean_nat_big_div_exact(nat_a, nat_c);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "36893488147419103232"));
    free_nat(tmp);
    tmp = lean_nat_big_mod(nat_a, nat_b);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "1"));
    free_nat(tmp);
    CHECK(!lean_nat_big_eq(nat_a, nat_b));
    CHECK(lean_nat_big_le(nat_b, nat_a));
    CHECK(lean_nat_big_lt(nat_b, nat_a));
    tmp = lean_nat_big_land(nat_a, nat_b);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "0"));
    free_nat(tmp);
    tmp = lean_nat_big_lor(nat_a, nat_b);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "340282366920938463481821351505477763071"));
    free_nat(tmp);
    tmp = lean_nat_big_xor(nat_a, nat_b);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "340282366920938463481821351505477763071"));
    free_nat(tmp);
    tmp = lean_nat_shiftl(nat_c, lean_box(4));
    CHECK(leanrt_test_nat_eq_cstr(tmp, "147573952589676412928"));
    free_nat(tmp);
    tmp = lean_nat_big_shiftr(nat_a, lean_box(64));
    CHECK(leanrt_test_nat_eq_cstr(tmp, "18446744073709551616"));
    free_nat(tmp);
    tmp = lean_nat_pow(nat_c, lean_box(2));
    CHECK(leanrt_test_nat_eq_cstr(tmp, "85070591730234615865843651857942052864"));
    free_nat(tmp);
    tmp = lean_nat_gcd(nat_a, nat_c);
    CHECK(leanrt_test_nat_eq_cstr(tmp, "9223372036854775808"));
    free_nat(tmp);
    tmp = lean_nat_log2(nat_a);
    CHECK(lean_is_scalar(tmp) && lean_unbox(tmp) == 128u);
    free_nat(tmp);

    CHECK(lean_uint8_of_big_nat(nat_a) == 0);
    CHECK(lean_uint16_of_big_nat(nat_b) == 0xffffu);
    CHECK(lean_uint32_of_big_nat(nat_b) == 0xffffffffu);
    CHECK(lean_uint64_of_big_nat(nat_b) == UINT64_MAX);
    CHECK(lean_usize_of_big_nat(nat_b) == (size_t)UINT64_MAX);
    CHECK(lean_uint64_mix_hash(0x0123456789abcdefULL, 0xfedcba9876543210ULL) == 0xf625c5a4385e7d54ULL);

    int_a = lean_cstr_to_int("-340282366920938463463374607431768211456");
    int_b = lean_big_int64_to_int(INT64_MIN);
    int_c = lean_big_size_t_to_int(SIZE_MAX);
    CHECK(leanrt_test_cpp_int_eq_cstr(int_a, "-340282366920938463463374607431768211456"));
    CHECK(leanrt_test_cpp_int_eq_cstr(int_b, "-9223372036854775808"));
    CHECK(leanrt_test_cpp_int_eq_cstr(int_c, "18446744073709551615"));
    tmp = lean_big_int_to_int(-17);
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "-17"));
    free_int(tmp);
    tmp = lean_big_int_to_nat(lean_cstr_to_int("18446744073709551616"));
    CHECK(leanrt_test_nat_eq_cstr(tmp, "18446744073709551616"));
    free_nat(tmp);

    tmp = lean_int_big_neg(int_a);
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "340282366920938463463374607431768211456"));
    free_int(tmp);
    tmp = lean_int_big_add(int_a, int_c);
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "-340282366920938463444927863358058659841"));
    free_int(tmp);
    tmp = lean_int_big_sub(int_c, int_b);
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "27670116110564327423"));
    free_int(tmp);
    tmp = lean_int_big_mul(int_b, lean_cstr_to_int("-3"));
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "27670116110564327424"));
    free_int(tmp);
    tmp = lean_int_big_div(int_a, lean_cstr_to_int("3"));
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "-113427455640312821154458202477256070485"));
    free_int(tmp);
    tmp = lean_int_big_div_exact(lean_cstr_to_int("18446744073709551616"), lean_cstr_to_int("-4294967296"));
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "-4294967296"));
    free_int(tmp);
    tmp = lean_int_big_mod(int_a, lean_cstr_to_int("3"));
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "-1"));
    free_int(tmp);
    tmp = lean_int_big_ediv(int_a, lean_cstr_to_int("3"));
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "-113427455640312821154458202477256070486"));
    free_int(tmp);
    tmp = lean_int_big_emod(int_a, lean_cstr_to_int("3"));
    CHECK(leanrt_test_cpp_int_eq_cstr(tmp, "2"));
    free_int(tmp);
    CHECK(!lean_int_big_eq(int_a, int_b));
    CHECK(lean_int_big_le(int_a, int_b));
    CHECK(lean_int_big_lt(int_a, int_b));
    CHECK(!lean_int_big_nonneg(int_a));
    CHECK(lean_int_big_nonneg(int_c));

    CHECK(lean_int8_of_big_int(int_a) == 0);
    CHECK(lean_int16_of_big_int(int_a) == 0);
    CHECK(lean_int32_of_big_int(int_a) == 0);
    CHECK(lean_int64_of_big_int(int_b) == INT64_MIN);
    CHECK(lean_isize_of_big_int(int_b) == (ptrdiff_t)INT64_MIN);

    free_nat(nat_a);
    free_nat(nat_b);
    free_nat(nat_c);
    free_int(int_a);
    free_int(int_b);
    free_int(int_c);

    lean_finalize_thread();
    return 0;
}
