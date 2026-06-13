#include <lean/lean.h>

#include <gmp.h>

#include <stdbool.h>
#include <string.h>
#include <sys/wait.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

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
extern lean_object *leanrt_test_alloc_mpz_from_cstr(char const *value);
extern uint8_t leanrt_test_nat_eq_cstr(lean_object *o, char const *value);
extern uint8_t leanrt_test_cpp_int_eq_cstr(lean_object *o, char const *value);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_free_count(void);

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

_Static_assert(sizeof(size_t) == 8, "M4b-F12 requires 64-bit size_t");
_Static_assert(sizeof(ptrdiff_t) == 8, "M4b-F12 requires 64-bit ptrdiff_t");

#define UINT64_MIX_HASH_GOLDEN_PATH "tests/bignum-smoke/uint64_mix_hash.golden"

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

#define CHECK_OWNED_RESULT(result)                                                  \
    do {                                                                            \
        if (!lean_is_scalar(result)) {                                              \
            CHECK((result)->m_rc == 1);                                             \
        }                                                                           \
    } while (0)

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

static uint64_t next_u64(uint64_t *state) {
    uint64_t x = *state;
    x ^= x << 7;
    x ^= x >> 9;
    x ^= x << 8;
    *state = x;
    return x;
}

static void free_nat(lean_object *o) {
    if (!lean_is_scalar(o)) {
        lean_dec(o);
    }
}

static bool nat_equal(lean_object *lhs, lean_object *rhs) {
    if (lean_is_scalar(lhs) && lean_is_scalar(rhs)) {
        return lhs == rhs;
    }
    return lean_nat_big_eq(lhs, rhs);
}

static void free_int(lean_object *o) {
    if (!lean_is_scalar(o)) {
        lean_dec(o);
    }
}

static lean_object *make_nat_from_mpz(const mpz_t value) {
    if (mpz_fits_ulong_p(value)) {
        unsigned long small = mpz_get_ui(value);
        if ((size_t)small <= LEAN_MAX_SMALL_NAT) {
            return lean_box((size_t)small);
        }
    }

    char *text = mpz_get_str(NULL, 10, value);
    lean_object *result = lean_cstr_to_nat(text);
    free(text);
    return result;
}

static int expect_nat_matches_mpz(lean_object *actual, const mpz_t expected) {
    lean_object *expected_obj = make_nat_from_mpz(expected);
    CHECK(nat_equal(actual, expected_obj));
    free_nat(expected_obj);
    return 0;
}

typedef lean_object *(*binary_nat_fn)(lean_object *, lean_object *);

static int expect_binary_panic(binary_nat_fn fn, lean_object *lhs, lean_object *rhs, const char *needle) {
    int pipefd[2];
    pid_t pid;
    int status;
    char stderr_buf[1024];
    ssize_t used = 0;
    ssize_t nread;

    CHECK(pipe(pipefd) == 0);
    pid = fork();
    CHECK(pid >= 0);

    if (pid == 0) {
        close(pipefd[0]);
        CHECK(dup2(pipefd[1], STDERR_FILENO) >= 0);
        close(pipefd[1]);
        (void)fn(lhs, rhs);
        _exit(0);
    }

    close(pipefd[1]);
    while ((nread = read(pipefd[0], stderr_buf + used, (sizeof(stderr_buf) - 1) - (size_t)used)) > 0) {
        used += nread;
        if ((size_t)used == sizeof(stderr_buf) - 1) break;
    }
    close(pipefd[0]);
    stderr_buf[used] = '\0';

    CHECK(waitpid(pid, &status, 0) == pid);
    CHECK(!WIFEXITED(status) || WEXITSTATUS(status) != 0);
    CHECK(strstr(stderr_buf, needle) != NULL);
    return 0;
}

static int expect_kind(lean_object *o, bool expect_scalar) {
    CHECK(lean_is_scalar(o) == expect_scalar);
    if (!expect_scalar) {
        CHECK(lean_obj_tag(o) == LeanMPZ);
        CHECK(o->m_rc == 1);
    }
    return 0;
}

static int check_int_constructors(void) {
    lean_object *zero = lean_cstr_to_int("0");
    lean_object *pos = lean_cstr_to_int("42");
    lean_object *neg = lean_cstr_to_int("-42");
    lean_object *big_neg = lean_cstr_to_int("-1234567890123456789012");
    lean_object *int_from_int = lean_big_int_to_int(-17);
    lean_object *size_max = lean_big_size_t_to_int(SIZE_MAX);
    lean_object *int64_min = lean_big_int64_to_int(INT64_MIN);
    lean_object *zig_big = leanrt_test_alloc_mpz_from_cstr("18446744073709551616");
    lean_object *nat_from_big;
    size_t free_before;

    CHECK(lean_is_scalar(zero));
    CHECK((int64_t)lean_scalar_to_int64(zero) == 0);
    CHECK(leanrt_test_cpp_int_eq_cstr(zero, "0"));

    CHECK(lean_is_scalar(pos));
    CHECK((int64_t)lean_scalar_to_int64(pos) == 42);
    CHECK(leanrt_test_cpp_int_eq_cstr(pos, "42"));

    CHECK(lean_is_scalar(neg));
    CHECK((int64_t)lean_scalar_to_int64(neg) == -42);
    CHECK(leanrt_test_cpp_int_eq_cstr(neg, "-42"));

    CHECK(!lean_is_scalar(big_neg));
    CHECK(leanrt_test_cpp_int_eq_cstr(big_neg, "-1234567890123456789012"));
    CHECK(!lean_int_big_nonneg(big_neg));

    CHECK(!lean_is_scalar(int_from_int));
    CHECK(leanrt_test_cpp_int_eq_cstr(int_from_int, "-17"));

    CHECK(!lean_is_scalar(size_max));
    CHECK(leanrt_test_cpp_int_eq_cstr(size_max, "18446744073709551615"));
    CHECK(lean_int_big_nonneg(size_max));

    CHECK(!lean_is_scalar(int64_min));
    CHECK(leanrt_test_cpp_int_eq_cstr(int64_min, "-9223372036854775808"));
    CHECK(!lean_int_big_nonneg(int64_min));
    {
        lean_object *int64_min_copy = lean_big_int64_to_int(INT64_MIN);
        CHECK(lean_int_big_eq(int64_min, int64_min_copy));
        free_int(int64_min_copy);
    }

    leanrt_test_allocator_reset_counters();
    free_before = leanrt_test_allocator_free_count();
    nat_from_big = lean_big_int_to_nat(zig_big);
    CHECK(leanrt_test_allocator_free_count() == free_before + 1);
    CHECK(leanrt_test_nat_eq_cstr(nat_from_big, "18446744073709551616"));
    free_nat(nat_from_big);

    free_int(big_neg);
    free_int(int_from_int);
    free_int(size_max);
    free_int(int64_min);
    return 0;
}

static lean_object *make_int_from_mpz(const mpz_t value) {
    char *text = mpz_get_str(NULL, 10, value);
    lean_object *result = lean_cstr_to_int(text);
    free(text);
    return result;
}

static int expect_int_matches_mpz(lean_object *actual, const mpz_t expected) {
    char *text = mpz_get_str(NULL, 10, expected);
    CHECK(leanrt_test_cpp_int_eq_cstr(actual, text));
    free(text);
    return 0;
}

static lean_object *make_zig_mpz_from_mpz(const mpz_t value) {
    char *text = mpz_get_str(NULL, 10, value);
    lean_object *result = leanrt_test_alloc_mpz_from_cstr(text);
    free(text);
    return result;
}

static uint64_t unsigned_trunc_bits(const mpz_t value, unsigned bits) {
    mpz_t truncated;
    uint64_t result;

    mpz_init(truncated);
    mpz_fdiv_r_2exp(truncated, value, bits);
    result = mpz_get_ui(truncated);
    mpz_clear(truncated);
    return result;
}

static int64_t signed_trunc_bits(const mpz_t value, unsigned bits) {
    mpz_t truncated, threshold, modulus;
    int64_t result;

    mpz_inits(truncated, threshold, modulus, NULL);
    mpz_fdiv_r_2exp(truncated, value, bits);
    if (bits != 0) {
        mpz_set_ui(threshold, 1u);
        mpz_mul_2exp(threshold, threshold, bits - 1u);
        if (mpz_cmp(truncated, threshold) >= 0) {
            mpz_set_ui(modulus, 1u);
            mpz_mul_2exp(modulus, modulus, bits);
            mpz_sub(truncated, truncated, modulus);
        }
    }
    result = (int64_t)mpz_get_si(truncated);
    mpz_clears(truncated, threshold, modulus, NULL);
    return result;
}

static void random_nat_bits(mpz_t out, uint64_t *state, unsigned bits) {
    uint64_t limbs[5] = {0, 0, 0, 0, 0};
    size_t limb_count = (bits + 63u) / 64u;
    size_t i;

    mpz_set_ui(out, 0);
    if (bits == 0) {
        return;
    }

    for (i = 0; i < limb_count; ++i) {
        limbs[i] = next_u64(state);
    }
    if ((bits & 63u) != 0) {
        limbs[limb_count - 1] &= (((uint64_t)1) << (bits & 63u)) - 1u;
    }
    limbs[limb_count - 1] |= (uint64_t)1 << ((bits - 1u) & 63u);
    mpz_import(out, limb_count, -1, sizeof(uint64_t), 0, 0, limbs);
}

static void generate_pair(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index) {
    switch (index % 6u) {
    case 0:
        mpz_set_ui(lhs, next_u64(state) & 0xffffu);
        mpz_set_ui(rhs, next_u64(state) & 0xffffu);
        break;
    case 1:
        mpz_set_ui(lhs, LEAN_MAX_SMALL_NAT - (next_u64(state) & 0xffu));
        mpz_set_ui(rhs, next_u64(state) & 0x3ffu);
        break;
    case 2:
        mpz_set_ui(lhs, next_u64(state) & 0xffffu);
        random_nat_bits(rhs, state, 96u + (unsigned)(next_u64(state) % 64u));
        break;
    case 3:
        random_nat_bits(lhs, state, 96u + (unsigned)(next_u64(state) % 64u));
        mpz_set_ui(rhs, next_u64(state) & 0xffffu);
        break;
    case 4:
        random_nat_bits(lhs, state, 64u + (unsigned)(next_u64(state) % 8u));
        random_nat_bits(rhs, state, 64u + (unsigned)(next_u64(state) % 8u));
        break;
    default:
        random_nat_bits(lhs, state, 160u + (unsigned)(next_u64(state) % 97u));
        random_nat_bits(rhs, state, 160u + (unsigned)(next_u64(state) % 97u));
        break;
    }

    if (index < 50u && mpz_cmp(lhs, rhs) >= 0) {
        mpz_set(rhs, lhs);
        mpz_add_ui(rhs, rhs, 1u + (unsigned long)(next_u64(state) & 0x7fu));
    }
}

static int check_randomized_gmp_differential(void) {
    uint64_t seed = 0x5eedcafe1234abcdULL;
    size_t i;
    mpz_t lhs, rhs, expected;

    mpz_inits(lhs, rhs, expected, NULL);
    for (i = 0; i < 200u; ++i) {
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;

        generate_pair(lhs, rhs, &seed, i);
        lhs_obj = make_nat_from_mpz(lhs);
        rhs_obj = make_nat_from_mpz(rhs);

        mpz_add_ui(expected, lhs, 1u);
        actual = lean_nat_big_succ(lhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        mpz_add(expected, lhs, rhs);
        actual = lean_nat_big_add(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        if (mpz_cmp(lhs, rhs) < 0) {
            mpz_set_ui(expected, 0);
        } else {
            mpz_sub(expected, lhs, rhs);
        }
        actual = lean_nat_big_sub(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        if (i < 50u) {
            CHECK(lean_is_scalar(actual));
            CHECK(lean_unbox(actual) == 0u);
        }
        free_nat(actual);

        mpz_mul(expected, lhs, rhs);
        actual = lean_nat_big_mul(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        free_nat(lhs_obj);
        free_nat(rhs_obj);
    }

    mpz_clears(lhs, rhs, expected, NULL);
    return 0;
}

static int check_div_mod_randomized_gmp_differential(void) {
    uint64_t seed = 0x1234fedcba987654ULL;
    size_t i;
    mpz_t lhs, rhs, expected;

    mpz_inits(lhs, rhs, expected, NULL);
    for (i = 0; i < 200u; ++i) {
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;

        generate_pair(lhs, rhs, &seed, i);
        if (mpz_sgn(rhs) == 0) {
            mpz_set_ui(rhs, 1u + (unsigned long)(i % 17u));
        }

        lhs_obj = make_nat_from_mpz(lhs);
        rhs_obj = make_nat_from_mpz(rhs);

        mpz_fdiv_q(expected, lhs, rhs);
        actual = lean_nat_big_div(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        mpz_fdiv_r(expected, lhs, rhs);
        actual = lean_nat_big_mod(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        free_nat(lhs_obj);
        free_nat(rhs_obj);
    }

    mpz_clears(lhs, rhs, expected, NULL);
    return 0;
}

static int check_div_exact_randomized_gmp_differential(void) {
    uint64_t seed = 0x0ddc0ffeebadf00dULL;
    size_t i;
    mpz_t lhs, rhs, q, expected;

    mpz_inits(lhs, rhs, q, expected, NULL);
    for (i = 0; i < 100u; ++i) {
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;

        generate_pair(rhs, q, &seed, i + 31u);
        if (mpz_sgn(rhs) == 0) {
            mpz_set_ui(rhs, 1u + (unsigned long)(i % 29u));
        }
        mpz_mul(lhs, rhs, q);

        lhs_obj = make_nat_from_mpz(lhs);
        rhs_obj = make_nat_from_mpz(rhs);

        mpz_divexact(expected, lhs, rhs);
        actual = lean_nat_big_div_exact(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        free_nat(lhs_obj);
        free_nat(rhs_obj);
    }

    mpz_clears(lhs, rhs, q, expected, NULL);
    return 0;
}

static int check_compare_bitwise_randomized_gmp_differential(void) {
    uint64_t seed = 0x9f3779b97f4a7c15ULL;
    size_t i;
    mpz_t lhs, rhs, expected;

    mpz_inits(lhs, rhs, expected, NULL);
    for (i = 0; i < 200u; ++i) {
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;
        bool eq;
        bool le;
        bool lt;
        bool gt;
        int cmp;

        generate_pair(lhs, rhs, &seed, i + 73u);
        lhs_obj = make_nat_from_mpz(lhs);
        rhs_obj = make_nat_from_mpz(rhs);

        cmp = mpz_cmp(lhs, rhs);
        eq = lean_nat_big_eq(lhs_obj, rhs_obj);
        le = lean_nat_big_le(lhs_obj, rhs_obj);
        lt = lean_nat_big_lt(lhs_obj, rhs_obj);
        gt = lean_nat_big_lt(rhs_obj, lhs_obj);
        CHECK(eq == (cmp == 0));
        CHECK(le == (cmp <= 0));
        CHECK(lt == (cmp < 0));
        CHECK((eq ? 1 : 0) + (lt ? 1 : 0) + (gt ? 1 : 0) == 1);
        CHECK(le == (eq || lt));
        CHECK(!lt || !gt);

        mpz_and(expected, lhs, rhs);
        actual = lean_nat_big_land(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        mpz_ior(expected, lhs, rhs);
        actual = lean_nat_big_lor(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        mpz_xor(expected, lhs, rhs);
        actual = lean_nat_big_xor(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        free_nat(lhs_obj);
        free_nat(rhs_obj);
    }

    mpz_clears(lhs, rhs, expected, NULL);
    return 0;
}

static int check_small_path_result_kinds(void) {
    size_t i;
    for (i = 0; i < 10u; ++i) {
        lean_object *result = lean_nat_big_succ(lean_box(i));
        CHECK(expect_kind(result, true) == 0);
        free_nat(result);
    }

    for (i = 0; i < 10u; ++i) {
        lean_object *result = lean_nat_big_add(lean_box(i), lean_box(i + 1u));
        CHECK(expect_kind(result, true) == 0);
        free_nat(result);
    }

    for (i = 0; i < 10u; ++i) {
        lean_object *result = lean_nat_big_mul(lean_box(i + 2u), lean_box(i + 3u));
        CHECK(expect_kind(result, true) == 0);
        free_nat(result);
    }

    for (i = 0; i < 10u; ++i) {
        lean_object *lhs = lean_cstr_to_nat("340282366920938463463374607431768211456");
        lean_object *rhs = lean_box(i + 1u);
        lean_object *result = lean_nat_big_add(lhs, rhs);
        CHECK(expect_kind(result, false) == 0);
        free_nat(lhs);
        free_nat(result);
    }

    for (i = 0; i < 5u; ++i) {
        lean_object *lhs = lean_box(LEAN_MAX_SMALL_NAT - (i + 3u));
        lean_object *rhs = lean_box(1u);
        lean_object *result = lean_nat_big_add(lhs, rhs);
        CHECK(expect_kind(result, true) == 0);
        free_nat(result);
    }

    for (i = 0; i < 5u; ++i) {
        lean_object *lhs = lean_box(LEAN_MAX_SMALL_NAT - i);
        lean_object *rhs = lean_box(i + 2u);
        lean_object *result = lean_nat_big_add(lhs, rhs);
        CHECK(expect_kind(result, false) == 0);
        free_nat(result);
    }

    return 0;
}

static int check_rc_discipline(void) {
    lean_object *a = lean_cstr_to_nat("340282366920938463463374607431768211456");
    lean_object *b = lean_cstr_to_nat("18446744073709551616");
    int a_rc_before;
    int b_rc_before;
    lean_object *result;

    lean_inc(a);
    a_rc_before = a->m_rc;
    result = lean_nat_big_succ(a);
    CHECK(a->m_rc == a_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_big_add(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_big_sub(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_big_mul(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);
    lean_dec(b);

    free_nat(a);
    free_nat(b);
    return 0;
}

static int check_division_edge_cases(void) {
    uint64_t seed = 0xface1234567890abULL;
    size_t i;

    for (i = 0; i < 50u; ++i) {
        mpz_t value;
        lean_object *a;
        lean_object *div_zero;
        lean_object *mod_zero;

        mpz_init(value);
        generate_pair(value, value, &seed, i + 9u);
        a = make_nat_from_mpz(value);
        mpz_clear(value);

        div_zero = lean_nat_big_div(a, lean_box(0));
        CHECK(lean_is_scalar(div_zero));
        CHECK(lean_unbox(div_zero) == 0u);

        if (lean_is_scalar(a)) {
            mod_zero = lean_nat_big_mod(a, lean_box(0));
            CHECK(mod_zero == a);
        } else {
            int rc_before = a->m_rc;
            mod_zero = lean_nat_big_mod(a, lean_box(0));
            CHECK(mod_zero == a);
            CHECK(a->m_rc == rc_before + 1);
            lean_dec(mod_zero);
        }

        free_nat(a);
    }

    return 0;
}

static int check_division_rc_discipline(void) {
    lean_object *a = lean_cstr_to_nat("340282366920938463463374607431768211456");
    lean_object *b = lean_cstr_to_nat("18446744073709551616");
    lean_object *mod_lhs = lean_cstr_to_nat("46116860184273879040");
    int a_rc_before;
    int b_rc_before;
    lean_object *result;

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_big_div(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_big_div_exact(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(mod_lhs);
    lean_inc(b);
    a_rc_before = mod_lhs->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_big_mod(mod_lhs, b);
    CHECK(mod_lhs->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    {
        mpz_t expected;
        mpz_init_set_str(expected, "9223372036854775808", 10);
        CHECK(expect_nat_matches_mpz(result, expected) == 0);
        mpz_clear(expected);
    }
    free_nat(result);
    lean_dec(mod_lhs);
    lean_dec(b);

    lean_inc(a);
    a_rc_before = a->m_rc;
    result = lean_nat_big_mod(a, lean_box(0));
    CHECK(result == a);
    CHECK(a->m_rc == a_rc_before + 1);
    lean_dec(result);
    lean_dec(a);

    free_nat(a);
    free_nat(b);
    free_nat(mod_lhs);
    return 0;
}

static int check_compare_bitwise_identities(void) {
    uint64_t seed = 0x0123456789abcdefULL;
    size_t i;
    mpz_t lhs;

    mpz_init(lhs);
    for (i = 0; i < 50u; ++i) {
        lean_object *a;
        lean_object *actual;

        generate_pair(lhs, lhs, &seed, i + 11u);
        a = make_nat_from_mpz(lhs);

        actual = lean_nat_big_land(a, lean_box(0));
        CHECK(lean_is_scalar(actual));
        CHECK(lean_unbox(actual) == 0u);
        free_nat(actual);

        actual = lean_nat_big_lor(a, lean_box(0));
        CHECK(nat_equal(actual, a));
        free_nat(actual);

        actual = lean_nat_big_xor(a, lean_box(0));
        CHECK(nat_equal(actual, a));
        free_nat(actual);

        actual = lean_nat_big_xor(a, a);
        CHECK(lean_is_scalar(actual));
        CHECK(lean_unbox(actual) == 0u);
        free_nat(actual);

        free_nat(a);
    }

    mpz_clear(lhs);
    return 0;
}

static int check_compare_rc_discipline(void) {
    lean_object *a = lean_cstr_to_nat("340282366920938463463374607431768211456");
    lean_object *b = lean_cstr_to_nat("18446744073709551616");
    int a_rc_before;
    int b_rc_before;

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    CHECK(lean_nat_big_eq(a, b) == false);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    CHECK(lean_nat_big_le(a, b) == false);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    CHECK(lean_nat_big_lt(a, b) == false);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    lean_dec(a);
    lean_dec(b);

    free_nat(a);
    free_nat(b);
    return 0;
}

static int check_shift_randomized_gmp_differential(void) {
    uint64_t seed = 0x13579bdf2468ace0ULL;
    size_t i;
    mpz_t value;
    mpz_t expected;

    mpz_inits(value, expected, NULL);
    for (i = 0; i < 100u; ++i) {
        size_t shift = (size_t)(next_u64(&seed) % 4097u);
        lean_object *value_obj;
        lean_object *actual;

        random_nat_bits(value, &seed, (unsigned)(1u + (next_u64(&seed) % 256u)));
        if ((i % 9u) == 0) {
            mpz_set_ui(value, 0u);
        }

        value_obj = make_nat_from_mpz(value);

        mpz_mul_2exp(expected, value, shift);
        actual = lean_nat_shiftl(value_obj, lean_box(shift));
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        mpz_fdiv_q_2exp(expected, value, shift);
        actual = lean_nat_big_shiftr(value_obj, lean_box(shift));
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);

        free_nat(value_obj);
    }

    mpz_clears(value, expected, NULL);
    return 0;
}

static int check_pow_randomized_gmp_differential(void) {
    uint64_t seed = 0x2468ace013579bdfULL;
    size_t i;
    mpz_t value;
    mpz_t expected;

    mpz_inits(value, expected, NULL);
    for (i = 0; i < 50u; ++i) {
        unsigned long exponent = (unsigned long)(next_u64(&seed) % 65u);
        lean_object *value_obj;
        lean_object *actual;

        random_nat_bits(value, &seed, (unsigned)(1u + (next_u64(&seed) % 192u)));
        if ((i % 7u) == 0) {
            mpz_set_ui(value, 0u);
        }

        value_obj = make_nat_from_mpz(value);
        mpz_pow_ui(expected, value, exponent);
        actual = lean_nat_pow(value_obj, lean_box((size_t)exponent));
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);
        free_nat(value_obj);
    }

    mpz_set_ui(value, 0u);
    mpz_set_ui(expected, 1u);
    {
        lean_object *actual = lean_nat_pow(lean_box(0), lean_box(0));
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);
    }

    mpz_set_ui(expected, 0u);
    {
        lean_object *actual = lean_nat_pow(lean_box(0), lean_box(5));
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);
    }

    mpz_clears(value, expected, NULL);
    return 0;
}

static int check_gcd_randomized_gmp_differential(void) {
    uint64_t seed = 0x0f1e2d3c4b5a6978ULL;
    size_t i;
    mpz_t lhs;
    mpz_t rhs;
    mpz_t expected;

    mpz_inits(lhs, rhs, expected, NULL);
    for (i = 0; i < 100u; ++i) {
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;

        generate_pair(lhs, rhs, &seed, i + 101u);
        if ((i % 11u) == 0) mpz_set_ui(lhs, 0u);
        if ((i % 13u) == 0) mpz_set_ui(rhs, 0u);

        lhs_obj = make_nat_from_mpz(lhs);
        rhs_obj = make_nat_from_mpz(rhs);

        mpz_gcd(expected, lhs, rhs);
        actual = lean_nat_gcd(lhs_obj, rhs_obj);
        CHECK(expect_nat_matches_mpz(actual, expected) == 0);
        free_nat(actual);
        free_nat(lhs_obj);
        free_nat(rhs_obj);
    }

    mpz_clears(lhs, rhs, expected, NULL);
    return 0;
}

static int check_log2_matches_gmp(void) {
    uint64_t seed = 0xa1b2c3d4e5f60718ULL;
    size_t i;
    mpz_t value;

    mpz_init(value);
    CHECK(lean_unbox(lean_nat_log2(lean_box(0))) == 0u);
    for (i = 0; i < 100u; ++i) {
        lean_object *value_obj;
        lean_object *actual;
        size_t expected;

        random_nat_bits(value, &seed, (unsigned)(1u + (next_u64(&seed) % 256u)));
        if (mpz_sgn(value) == 0) {
            mpz_set_ui(value, 1u);
        }

        value_obj = make_nat_from_mpz(value);
        actual = lean_nat_log2(value_obj);
        expected = mpz_sizeinbase(value, 2) - 1u;
        CHECK(lean_is_scalar(actual));
        CHECK(lean_unbox(actual) == expected);
        free_nat(value_obj);
    }

    mpz_clear(value);
    return 0;
}

static int check_shift_pow_gcd_edge_cases(void) {
    lean_object *a = lean_cstr_to_nat("340282366920938463463374607431768211456");
    lean_object *b = lean_cstr_to_nat("36893488147419103232");
    lean_object *huge_exp = lean_cstr_to_nat("18446744073709551616");
    lean_object *large_scalar_shift = lean_big_uint64_to_nat((uint64_t)UINT32_MAX + 1u);
    lean_object *actual;

    actual = lean_nat_shiftl(lean_box(0), lean_box(123));
    CHECK(lean_is_scalar(actual));
    CHECK(lean_unbox(actual) == 0u);

    actual = lean_nat_big_shiftr(a, huge_exp);
    CHECK(lean_is_scalar(actual));
    CHECK(lean_unbox(actual) == 0u);
    free_nat(actual);

    actual = lean_nat_big_shiftr(lean_box(7), large_scalar_shift);
    CHECK(lean_is_scalar(actual));
    CHECK(lean_unbox(actual) == 0u);
    free_nat(actual);

    actual = lean_nat_gcd(a, lean_box(0));
    CHECK(nat_equal(actual, a));
    free_nat(actual);

    actual = lean_nat_gcd(lean_box(0), b);
    CHECK(nat_equal(actual, b));
    free_nat(actual);

    actual = lean_nat_gcd(lean_box(0), lean_box(0));
    CHECK(lean_is_scalar(actual));
    CHECK(lean_unbox(actual) == 0u);
    free_nat(actual);

    free_nat(a);
    free_nat(b);
    free_nat(huge_exp);
    free_nat(large_scalar_shift);
    return 0;
}

static int check_shift_pow_rc_discipline(void) {
    lean_object *a = lean_cstr_to_nat("340282366920938463463374607431768211456");
    lean_object *b = lean_cstr_to_nat("36893488147419103232");
    int a_rc_before;
    int b_rc_before;
    lean_object *result;

    lean_inc(a);
    a_rc_before = a->m_rc;
    result = lean_nat_shiftl(a, lean_box(1));
    CHECK(a->m_rc == a_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);

    lean_inc(a);
    a_rc_before = a->m_rc;
    result = lean_nat_big_shiftr(a, lean_box(64));
    CHECK(a->m_rc == a_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);

    lean_inc(b);
    b_rc_before = b->m_rc;
    result = lean_nat_pow(b, lean_box(2));
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_nat_gcd(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_nat(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    a_rc_before = a->m_rc;
    result = lean_nat_log2(a);
    CHECK(a->m_rc == a_rc_before);
    CHECK(lean_is_scalar(result));
    lean_dec(a);

    free_nat(a);
    free_nat(b);
    return 0;
}

static int check_shiftl_and_pow_panics(void) {
    lean_object *huge_shift = lean_cstr_to_nat("18446744073709551616");
    lean_object *huge_pow = lean_big_uint64_to_nat((uint64_t)UINT32_MAX + 1u);

    CHECK(expect_binary_panic(lean_nat_shiftl, lean_box(1), huge_shift, "Nat.shiftl exponent is too big") == 0);
    CHECK(expect_binary_panic(lean_nat_pow, lean_box(2), huge_pow, "Nat.pow exponent is too big") == 0);

    free_nat(huge_shift);
    free_nat(huge_pow);
    return 0;
}

static void generate_int_operand(mpz_t out, uint64_t *state, size_t index) {
    switch (index % 6u) {
    case 0:
        mpz_set_si(out, (int64_t)((int32_t)(next_u64(state) & 0x7fffffffU)) - 0x3fffffff);
        break;
    case 1:
        mpz_set_si(out, (next_u64(state) & 1u) ? INT32_MIN : INT32_MAX);
        mpz_add_ui(out, out, (unsigned long)(next_u64(state) & 0xffu));
        break;
    case 2:
        random_nat_bits(out, state, 96u + (unsigned)(next_u64(state) % 64u));
        break;
    case 3:
        random_nat_bits(out, state, 96u + (unsigned)(next_u64(state) % 64u));
        mpz_neg(out, out);
        break;
    case 4:
        random_nat_bits(out, state, 160u + (unsigned)(next_u64(state) % 97u));
        if ((next_u64(state) & 1u) != 0) mpz_neg(out, out);
        break;
    default:
        mpz_set_ui(out, 0u);
        break;
    }
}

static int check_int_arith_randomized_gmp_differential(void) {
    uint64_t seed = 0x6d5a56da1234abcdULL;
    size_t i;
    mpz_t lhs, rhs, expected;

    mpz_inits(lhs, rhs, expected, NULL);
    for (i = 0; i < 128u; ++i) {
        lean_object *a;
        lean_object *b;
        lean_object *neg_a;
        lean_object *negneg_a;
        lean_object *add_ab;
        lean_object *add_ba;
        lean_object *sub_back;
        lean_object *sub_ab;
        lean_object *mul_ab;
        lean_object *mul_ba;

        generate_int_operand(lhs, &seed, i);
        generate_int_operand(rhs, &seed, i + 17u);
        a = make_int_from_mpz(lhs);
        b = make_int_from_mpz(rhs);

        mpz_neg(expected, lhs);
        neg_a = lean_int_big_neg(a);
        CHECK(expect_int_matches_mpz(neg_a, expected) == 0);

        negneg_a = lean_int_big_neg(neg_a);
        CHECK(lean_int_big_eq(negneg_a, a));

        mpz_add(expected, lhs, rhs);
        add_ab = lean_int_big_add(a, b);
        CHECK(expect_int_matches_mpz(add_ab, expected) == 0);

        add_ba = lean_int_big_add(b, a);
        CHECK(lean_int_big_eq(add_ab, add_ba));

        sub_back = lean_int_big_sub(add_ab, b);
        CHECK(lean_int_big_eq(sub_back, a));

        mpz_sub(expected, lhs, rhs);
        sub_ab = lean_int_big_sub(a, b);
        CHECK(expect_int_matches_mpz(sub_ab, expected) == 0);

        mpz_mul(expected, lhs, rhs);
        mul_ab = lean_int_big_mul(a, b);
        CHECK(expect_int_matches_mpz(mul_ab, expected) == 0);
        CHECK(lean_int_big_nonneg(mul_ab) == (mpz_sgn(expected) >= 0));

        mul_ba = lean_int_big_mul(b, a);
        CHECK(lean_int_big_eq(mul_ab, mul_ba));

        free_int(neg_a);
        free_int(negneg_a);
        free_int(add_ab);
        free_int(add_ba);
        free_int(sub_back);
        free_int(sub_ab);
        free_int(mul_ab);
        free_int(mul_ba);
        free_int(a);
        free_int(b);
    }

    mpz_clears(lhs, rhs, expected, NULL);
    return 0;
}

static int check_int_mul_sign_quadrants(void) {
    static const char *values[4][2] = {
        {"340282366920938463463374607431768211456", "18446744073709551616"},
        {"340282366920938463463374607431768211456", "-18446744073709551616"},
        {"-340282366920938463463374607431768211456", "18446744073709551616"},
        {"-340282366920938463463374607431768211456", "-18446744073709551616"},
    };
    size_t i;

    for (i = 0; i < 4u; ++i) {
        mpz_t lhs, rhs, expected;
        lean_object *a = lean_cstr_to_int(values[i][0]);
        lean_object *b = lean_cstr_to_int(values[i][1]);
        lean_object *product;

        mpz_inits(lhs, rhs, expected, NULL);
        mpz_set_str(lhs, values[i][0], 10);
        mpz_set_str(rhs, values[i][1], 10);
        mpz_mul(expected, lhs, rhs);

        product = lean_int_big_mul(a, b);
        CHECK(expect_int_matches_mpz(product, expected) == 0);
        CHECK(lean_int_big_nonneg(product) == (mpz_sgn(expected) >= 0));

        free_int(product);
        free_int(a);
        free_int(b);
        mpz_clears(lhs, rhs, expected, NULL);
    }

    {
        lean_object *zero = lean_cstr_to_int("0");
        lean_object *neg_zero = lean_int_big_neg(zero);
        CHECK(lean_int_big_nonneg(neg_zero));
        free_int(neg_zero);
        free_int(zero);
    }

    return 0;
}

static int check_int_arith_rc_discipline(void) {
    lean_object *a = lean_cstr_to_int("340282366920938463463374607431768211456");
    lean_object *b = lean_cstr_to_int("-18446744073709551616");
    int a_rc_before;
    int b_rc_before;
    lean_object *result;

    lean_inc(a);
    a_rc_before = a->m_rc;
    result = lean_int_big_neg(a);
    CHECK(a->m_rc == a_rc_before);
    CHECK(!lean_is_scalar(result));
    CHECK(result->m_rc == 1);
    free_int(result);
    lean_dec(a);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_add(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(result->m_rc == 1);
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_sub(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(result->m_rc == 1);
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_mul(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK(result->m_rc == 1);
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    free_int(a);
    free_int(b);
    return 0;
}

static int check_int_division_case(
    const char *lhs_str,
    const char *rhs_str,
    const char *expected_div,
    const char *expected_mod,
    const char *expected_ediv,
    const char *expected_emod) {
    lean_object *lhs = lean_cstr_to_int(lhs_str);
    lean_object *rhs = lean_cstr_to_int(rhs_str);
    lean_object *div_result = lean_int_big_div(lhs, rhs);
    lean_object *mod_result = lean_int_big_mod(lhs, rhs);
    lean_object *ediv_result = lean_int_big_ediv(lhs, rhs);
    lean_object *emod_result = lean_int_big_emod(lhs, rhs);
    lean_object *product;
    lean_object *recomposed;

    CHECK(leanrt_test_cpp_int_eq_cstr(div_result, expected_div));
    CHECK(leanrt_test_cpp_int_eq_cstr(mod_result, expected_mod));
    CHECK(leanrt_test_cpp_int_eq_cstr(ediv_result, expected_ediv));
    CHECK(leanrt_test_cpp_int_eq_cstr(emod_result, expected_emod));
    CHECK(lean_int_big_nonneg(emod_result));

    product = lean_int_big_mul(ediv_result, rhs);
    recomposed = lean_int_big_add(product, emod_result);
    CHECK(lean_int_big_eq(recomposed, lhs));

    free_int(div_result);
    free_int(mod_result);
    free_int(ediv_result);
    free_int(emod_result);
    free_int(product);
    free_int(recomposed);
    free_int(lhs);
    free_int(rhs);
    return 0;
}

static int check_int_division_family_edge_cases(void) {
    lean_object *exact_lhs = lean_cstr_to_int("18446744073709551616");
    lean_object *exact_rhs = lean_cstr_to_int("-4294967296");
    lean_object *exact_result = lean_int_big_div_exact(exact_lhs, exact_rhs);

    CHECK(leanrt_test_cpp_int_eq_cstr(exact_result, "-4294967296"));
    free_int(exact_result);
    free_int(exact_lhs);
    free_int(exact_rhs);

    CHECK(check_int_division_case("-7", "3", "-2", "-1", "-3", "2") == 0);
    CHECK(check_int_division_case("-7", "-3", "2", "-1", "3", "2") == 0);
    CHECK(check_int_division_case("7", "-3", "-2", "1", "-2", "1") == 0);
    CHECK(check_int_division_case("-9223372036854775808", "-1",
                                  "9223372036854775808", "0",
                                  "9223372036854775808", "0") == 0);
    return 0;
}

static int check_int_division_zero_divisor_paths(void) {
    lean_object *zero = lean_cstr_to_int("0");
    lean_object *big = lean_cstr_to_int("340282366920938463463374607431768211456");
    int rc_before;
    lean_object *result;

    CHECK(lean_is_scalar(zero));

    result = lean_int_big_div(big, zero);
    CHECK(result == zero);

    result = lean_int_big_ediv(big, zero);
    CHECK(result == zero);

    rc_before = big->m_rc;
    result = lean_int_big_mod(big, zero);
    CHECK(result == big);
    CHECK(big->m_rc == rc_before + 1);
    lean_dec(result);

    rc_before = big->m_rc;
    result = lean_int_big_emod(big, zero);
    CHECK(result == big);
    CHECK(big->m_rc == rc_before + 1);
    lean_dec(result);

    free_int(big);
    free_int(zero);
    return 0;
}

static int check_int_division_rc_discipline(void) {
    lean_object *a = lean_cstr_to_int("340282366920938463463374607431768211457");
    lean_object *b = lean_cstr_to_int("-18446744073709551616");
    int a_rc_before;
    int b_rc_before;
    lean_object *result;

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_div(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK_OWNED_RESULT(result);
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_mod(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK_OWNED_RESULT(result);
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_ediv(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK_OWNED_RESULT(result);
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;
    result = lean_int_big_emod(a, b);
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);
    CHECK_OWNED_RESULT(result);
    CHECK(lean_int_big_nonneg(result));
    free_int(result);
    lean_dec(a);
    lean_dec(b);

    free_int(a);
    free_int(b);
    return 0;
}

static int check_int_compare_randomized_gmp_differential(void) {
    uint64_t seed = 0x1f2e3d4c5b6a7988ULL;
    size_t i;
    mpz_t lhs, rhs;

    mpz_inits(lhs, rhs, NULL);
    for (i = 0; i < 128u; ++i) {
        lean_object *a;
        lean_object *b;
        int cmp;
        bool eq;
        bool le;
        bool lt;

        generate_int_operand(lhs, &seed, i);
        generate_int_operand(rhs, &seed, i + 29u);
        a = make_int_from_mpz(lhs);
        b = make_int_from_mpz(rhs);
        cmp = mpz_cmp(lhs, rhs);

        eq = lean_int_big_eq(a, b);
        le = lean_int_big_le(a, b);
        lt = lean_int_big_lt(a, b);

        CHECK(lean_int_big_eq(a, a));
        CHECK(lean_int_big_le(a, a));
        CHECK(!lean_int_big_lt(a, a));
        CHECK(eq == (cmp == 0));
        CHECK(le == (cmp <= 0));
        CHECK(lt == (cmp < 0));
        CHECK(lt == (le && !eq));
        CHECK(lean_int_big_lt(b, a) == (cmp > 0));
        CHECK(lean_int_big_nonneg(a) == (mpz_sgn(lhs) >= 0));

        free_int(a);
        free_int(b);
    }

    mpz_clears(lhs, rhs, NULL);
    return 0;
}

static int check_int_compare_rc_discipline(void) {
    lean_object *a = lean_cstr_to_int("340282366920938463463374607431768211457");
    lean_object *b = lean_cstr_to_int("-18446744073709551616");
    int a_rc_before;
    int b_rc_before;

    lean_inc(a);
    lean_inc(b);
    a_rc_before = a->m_rc;
    b_rc_before = b->m_rc;

    CHECK(!lean_int_big_eq(a, b));
    CHECK(!lean_int_big_le(a, b));
    CHECK(!lean_int_big_lt(a, b));
    CHECK(lean_int_big_nonneg(a));
    CHECK(a->m_rc == a_rc_before);
    CHECK(b->m_rc == b_rc_before);

    lean_dec(a);
    lean_dec(b);
    free_int(a);
    free_int(b);
    return 0;
}

static int check_int_compare_mixed_zig_mpz_path(void) {
    lean_object *zig_big = leanrt_test_alloc_mpz_from_cstr("340282366920938463463374607431768211456");
    lean_object *same = lean_cstr_to_int("340282366920938463463374607431768211456");
    lean_object *neg = lean_cstr_to_int("-18446744073709551616");

    CHECK(lean_int_big_eq(zig_big, same));
    CHECK(lean_int_big_le(zig_big, same));
    CHECK(!lean_int_big_lt(zig_big, same));
    CHECK(lean_int_big_lt(neg, zig_big));
    CHECK(lean_int_big_le(neg, zig_big));
    CHECK(!lean_int_big_nonneg(neg));
    CHECK(lean_int_big_nonneg(zig_big));

    free_int(zig_big);
    free_int(same);
    free_int(neg);
    return 0;
}

static int check_width_conversions_randomized_gmp_differential(void) {
    uint64_t nat_seed = 0x4a6f79215f776364ULL;
    uint64_t int_seed = 0x6d34725f69366432ULL;
    size_t i;
    mpz_t nat_value, int_value;

    mpz_inits(nat_value, int_value, NULL);

    for (i = 0; i < 100u; ++i) {
        lean_object *legacy_nat;
        lean_object *zig_nat;
        uint64_t expected64;

        random_nat_bits(nat_value, &nat_seed, 192u + (unsigned)(next_u64(&nat_seed) % 129u));
        expected64 = unsigned_trunc_bits(nat_value, 64u);
        legacy_nat = make_nat_from_mpz(nat_value);
        zig_nat = make_zig_mpz_from_mpz(nat_value);

        CHECK(lean_uint8_of_big_nat(legacy_nat) == (uint8_t)unsigned_trunc_bits(nat_value, 8u));
        CHECK(lean_uint16_of_big_nat(legacy_nat) == (uint16_t)unsigned_trunc_bits(nat_value, 16u));
        CHECK(lean_uint32_of_big_nat(legacy_nat) == (uint32_t)unsigned_trunc_bits(nat_value, 32u));
        CHECK(lean_uint64_of_big_nat(legacy_nat) == expected64);
        CHECK(lean_usize_of_big_nat(legacy_nat) == (size_t)expected64);

        CHECK(lean_uint8_of_big_nat(zig_nat) == (uint8_t)unsigned_trunc_bits(nat_value, 8u));
        CHECK(lean_uint16_of_big_nat(zig_nat) == (uint16_t)unsigned_trunc_bits(nat_value, 16u));
        CHECK(lean_uint32_of_big_nat(zig_nat) == (uint32_t)unsigned_trunc_bits(nat_value, 32u));
        CHECK(lean_uint64_of_big_nat(zig_nat) == expected64);
        CHECK(lean_usize_of_big_nat(zig_nat) == (size_t)expected64);

        free_nat(legacy_nat);
        free_nat(zig_nat);
    }

    for (i = 0; i < 100u; ++i) {
        lean_object *legacy_int;
        lean_object *zig_int;
        int64_t expected64;

        generate_int_operand(int_value, &int_seed, i + 41u);
        expected64 = signed_trunc_bits(int_value, 64u);
        legacy_int = make_int_from_mpz(int_value);
        zig_int = make_zig_mpz_from_mpz(int_value);

        CHECK(lean_int8_of_big_int(legacy_int) == (int8_t)signed_trunc_bits(int_value, 8u));
        CHECK(lean_int16_of_big_int(legacy_int) == (int16_t)signed_trunc_bits(int_value, 16u));
        CHECK(lean_int32_of_big_int(legacy_int) == (int32_t)signed_trunc_bits(int_value, 32u));
        CHECK(lean_int64_of_big_int(legacy_int) == expected64);
        CHECK(lean_isize_of_big_int(legacy_int) == (ptrdiff_t)expected64);

        CHECK(lean_int8_of_big_int(zig_int) == (int8_t)signed_trunc_bits(int_value, 8u));
        CHECK(lean_int16_of_big_int(zig_int) == (int16_t)signed_trunc_bits(int_value, 16u));
        CHECK(lean_int32_of_big_int(zig_int) == (int32_t)signed_trunc_bits(int_value, 32u));
        CHECK(lean_int64_of_big_int(zig_int) == expected64);
        CHECK(lean_isize_of_big_int(zig_int) == (ptrdiff_t)expected64);

        free_int(legacy_int);
        free_int(zig_int);
    }

    mpz_clears(nat_value, int_value, NULL);
    return 0;
}

static int check_uint64_mix_hash_golden(void) {
    FILE *golden = fopen(UINT64_MIX_HASH_GOLDEN_PATH, "r");
    uint64_t lhs, rhs, expected;
    size_t count = 0;

    CHECK(golden != NULL);
    while (fscanf(golden, "%" SCNx64 " %" SCNx64 " %" SCNx64, &lhs, &rhs, &expected) == 3) {
        CHECK(lean_uint64_mix_hash(lhs, rhs) == expected);
        ++count;
    }
    CHECK(ferror(golden) == 0);
    CHECK(feof(golden));
    CHECK(count == 1000u);
    CHECK(fclose(golden) == 0);
    return 0;
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    CHECK(check_small_path_result_kinds() == 0);
    CHECK(check_randomized_gmp_differential() == 0);
    CHECK(check_div_mod_randomized_gmp_differential() == 0);
    CHECK(check_div_exact_randomized_gmp_differential() == 0);
    CHECK(check_compare_bitwise_randomized_gmp_differential() == 0);
    CHECK(check_shift_randomized_gmp_differential() == 0);
    CHECK(check_pow_randomized_gmp_differential() == 0);
    CHECK(check_gcd_randomized_gmp_differential() == 0);
    CHECK(check_log2_matches_gmp() == 0);
    CHECK(check_rc_discipline() == 0);
    CHECK(check_division_edge_cases() == 0);
    CHECK(check_division_rc_discipline() == 0);
    CHECK(check_compare_bitwise_identities() == 0);
    CHECK(check_compare_rc_discipline() == 0);
    CHECK(check_shift_pow_gcd_edge_cases() == 0);
    CHECK(check_shift_pow_rc_discipline() == 0);
    CHECK(check_int_constructors() == 0);
    CHECK(check_int_arith_randomized_gmp_differential() == 0);
    CHECK(check_int_mul_sign_quadrants() == 0);
    CHECK(check_int_arith_rc_discipline() == 0);
    CHECK(check_int_division_family_edge_cases() == 0);
    CHECK(check_int_division_zero_divisor_paths() == 0);
    CHECK(check_int_division_rc_discipline() == 0);
    CHECK(check_int_compare_randomized_gmp_differential() == 0);
    CHECK(check_int_compare_rc_discipline() == 0);
    CHECK(check_int_compare_mixed_zig_mpz_path() == 0);
    CHECK(check_width_conversions_randomized_gmp_differential() == 0);
    CHECK(check_uint64_mix_hash_golden() == 0);

    lean_finalize_thread();
    return 0;
}
