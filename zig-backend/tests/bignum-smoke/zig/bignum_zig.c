#include "../common.h"

#include <lean/lean.h>

#include <gmp.h>

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

extern lean_object *lean_cstr_to_nat(char const *n);
extern lean_object *lean_nat_big_mul(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_gcd(lean_object *a1, lean_object *a2);
extern lean_object *lean_nat_pow(lean_object *a1, lean_object *a2);

extern lean_object *lean_cstr_to_int(char const *n);
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
extern lean_object *lean_int_big_neg(lean_object *a);

extern uint8_t leanrt_test_nat_eq_cstr(lean_object *o, char const *value);
extern uint8_t leanrt_test_cpp_int_eq_cstr(lean_object *o, char const *value);
extern void leanrt_test_allocator_reset_counters(void);
extern size_t leanrt_test_allocator_alloc_count(void);
extern size_t leanrt_test_allocator_free_count(void);

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

static void free_nat(lean_object *o) {
    if (!lean_is_scalar(o)) {
        lean_dec(o);
    }
}

static void free_int(lean_object *o) {
    if (!lean_is_scalar(o)) {
        lean_dec(o);
    }
}

static lean_object *make_nat_from_mpz(const mpz_t value) {
    char *text = smoke_mpz_strdup(value);
    lean_object *result = lean_cstr_to_nat(text);
    smoke_free_string(text);
    return result;
}

static lean_object *make_int_from_mpz(const mpz_t value) {
    char *text = smoke_mpz_strdup(value);
    lean_object *result = lean_cstr_to_int(text);
    smoke_free_string(text);
    return result;
}

static int verify_nat(lean_object *actual, const mpz_t expected, const char *label) {
    char *text = smoke_mpz_strdup(expected);
    int ok = leanrt_test_nat_eq_cstr(actual, text) == 1 ? 0 : 1;
    if (ok != 0) {
        fprintf(stderr, "nat mismatch: %s expected %s\n", label, text);
    }
    smoke_free_string(text);
    return ok;
}

static int verify_int(lean_object *actual, const mpz_t expected, const char *label) {
    char *text = smoke_mpz_strdup(expected);
    int ok = leanrt_test_cpp_int_eq_cstr(actual, text) == 1 ? 0 : 1;
    if (ok != 0) {
        fprintf(stderr, "int mismatch: %s expected %s\n", label, text);
    }
    smoke_free_string(text);
    return ok;
}

static int verify_leak_free(void) {
    const size_t alloc_count = leanrt_test_allocator_alloc_count();
    const size_t free_count = leanrt_test_allocator_free_count();
    if (alloc_count != free_count) {
        fprintf(stderr, "allocator leak: alloc=%zu free=%zu\n", alloc_count, free_count);
        return 1;
    }
    return 0;
}

static int run_canonical(FILE *out) {
    uint64_t div_seed = UINT64_C(0x2468ace013579bdf);
    uint64_t roundtrip_seed = UINT64_C(0x0ddc0ffeebadf00d);
    mpz_t lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value;
    int bezout_ok = 0;
    size_t i;

    mpz_inits(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);

    mpz_ui_pow_ui(pow_value, 2u, 100u);
    {
        lean_object *actual = lean_nat_pow(lean_box(2u), lean_box(100u));
        char *text = smoke_mpz_strdup(pow_value);
        if (verify_nat(actual, pow_value, "pow_2_100") != 0) {
            free_nat(actual);
            smoke_free_string(text);
            mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
            return 1;
        }
        fprintf(out, "pow_2_100=%s\n", text);
        free_nat(actual);
        smoke_free_string(text);
    }

    mpz_set_ui(fact_value, 1u);
    {
        lean_object *current = lean_box(1u);
        for (i = 2u; i <= 1000u; ++i) {
            lean_object *next;
            mpz_mul_ui(fact_value, fact_value, (unsigned long)i);
            next = lean_nat_big_mul(current, lean_box(i));
            free_nat(current);
            current = next;
        }
        if (verify_nat(current, fact_value, "factorial_1000") != 0) {
            free_nat(current);
            mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
            return 1;
        }
        {
            char *text = smoke_mpz_strdup(fact_value);
            fprintf(out, "factorial_1000=%s\n", text);
            smoke_free_string(text);
        }
        free_nat(current);
    }

    smoke_generate_gcd_operands(lhs, rhs, gcd_value, &bezout_ok);
    {
        lean_object *lhs_obj = make_nat_from_mpz(lhs);
        lean_object *rhs_obj = make_nat_from_mpz(rhs);
        lean_object *actual = lean_nat_gcd(lhs_obj, rhs_obj);
        if (verify_nat(actual, gcd_value, "large_gcd") != 0) {
            free_nat(actual);
            free_nat(lhs_obj);
            free_nat(rhs_obj);
            mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
            return 1;
        }
        {
            char *text = smoke_mpz_strdup(gcd_value);
            fprintf(out, "large_gcd=%s\n", text);
            smoke_free_string(text);
        }
        fprintf(out, "bezout_check=%d\n", bezout_ok);
        free_nat(actual);
        free_nat(lhs_obj);
        free_nat(rhs_obj);
    }

    fprintf(out, "mixed_sign_int_div_begin\n");
    for (i = 0u; i < SMOKE_DIV_CASES; ++i) {
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *div_obj;
        lean_object *ediv_obj;
        lean_object *mod_obj;
        lean_object *emod_obj;
        char *lhs_text;
        char *rhs_text;
        char *div_text;
        char *ediv_text;
        char *mod_text;
        char *emod_text;

        smoke_generate_div_case(lhs, rhs, &div_seed, i);
        if (mpz_sgn(rhs) == 0) {
            mpz_set_ui(q, 0u);
            mpz_set(ediv, q);
            mpz_set(r, lhs);
            mpz_set(emod, lhs);
        } else {
            smoke_trunc_divmod(q, r, lhs, rhs);
            smoke_euclidean_divmod(ediv, emod, lhs, rhs);
        }

        lhs_obj = make_int_from_mpz(lhs);
        rhs_obj = make_int_from_mpz(rhs);
        div_obj = lean_int_big_div(lhs_obj, rhs_obj);
        ediv_obj = lean_int_big_ediv(lhs_obj, rhs_obj);
        mod_obj = lean_int_big_mod(lhs_obj, rhs_obj);
        emod_obj = lean_int_big_emod(lhs_obj, rhs_obj);

        if (verify_int(div_obj, q, "div_case.div") != 0 ||
            verify_int(ediv_obj, ediv, "div_case.ediv") != 0 ||
            verify_int(mod_obj, r, "div_case.mod") != 0 ||
            verify_int(emod_obj, emod, "div_case.emod") != 0) {
            free_int(div_obj);
            free_int(ediv_obj);
            free_int(mod_obj);
            free_int(emod_obj);
            free_int(lhs_obj);
            free_int(rhs_obj);
            mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
            return 1;
        }

        lhs_text = smoke_mpz_strdup(lhs);
        rhs_text = smoke_mpz_strdup(rhs);
        div_text = smoke_mpz_strdup(q);
        ediv_text = smoke_mpz_strdup(ediv);
        mod_text = smoke_mpz_strdup(r);
        emod_text = smoke_mpz_strdup(emod);
        fprintf(
            out,
            "div_case[%04zu]=%s|%s|%s|%s|%s|%s\n",
            i,
            lhs_text,
            rhs_text,
            div_text,
            ediv_text,
            mod_text,
            emod_text
        );

        smoke_free_string(lhs_text);
        smoke_free_string(rhs_text);
        smoke_free_string(div_text);
        smoke_free_string(ediv_text);
        smoke_free_string(mod_text);
        smoke_free_string(emod_text);
        free_int(div_obj);
        free_int(ediv_obj);
        free_int(mod_obj);
        free_int(emod_obj);
        free_int(lhs_obj);
        free_int(rhs_obj);
    }
    fprintf(out, "mixed_sign_int_div_end\n");

    fprintf(out, "string_roundtrip_begin\n");
    for (i = 0u; i < SMOKE_ROUNDTRIP_CASES; ++i) {
        lean_object *obj;
        char *text;
        smoke_generate_roundtrip_value(lhs, &roundtrip_seed, i);
        text = smoke_mpz_strdup(lhs);
        obj = lean_cstr_to_int(text);
        if (leanrt_test_cpp_int_eq_cstr(obj, text) != 1) {
            fprintf(stderr, "roundtrip mismatch[%zu]: %s\n", i, text);
            free_int(obj);
            smoke_free_string(text);
            mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
            return 1;
        }
        fprintf(out, "roundtrip[%03zu]=%s\n", i, text);
        free_int(obj);
        smoke_free_string(text);
    }
    fprintf(out, "string_roundtrip_end\n");

    mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
    return verify_leak_free();
}

static void count_mismatch(const char *op, size_t index) {
    fprintf(stderr, "randomized mismatch: %s[%zu]\n", op, index);
}

static int run_randomized(const char *results_path) {
    const uint64_t base_seed = UINT64_C(0x5eedcafe1234abcd);
    struct smoke_count counts[] = {
        {"add", 0u, SMOKE_RANDOM_CASES},
        {"sub", 0u, SMOKE_RANDOM_CASES},
        {"mul", 0u, SMOKE_RANDOM_CASES},
        {"div", 0u, SMOKE_RANDOM_CASES},
        {"div_exact", 0u, SMOKE_RANDOM_CASES},
        {"mod", 0u, SMOKE_RANDOM_CASES},
        {"ediv", 0u, SMOKE_RANDOM_CASES},
        {"emod", 0u, SMOKE_RANDOM_CASES},
        {"neg", 0u, SMOKE_RANDOM_CASES},
        {"eq", 0u, SMOKE_RANDOM_CASES},
        {"le", 0u, SMOKE_RANDOM_CASES},
        {"lt", 0u, SMOKE_RANDOM_CASES},
        {"nonneg", 0u, SMOKE_RANDOM_CASES},
    };
    mpz_t lhs, rhs, expected, aux;
    size_t i;
    int status = 0;

    mpz_inits(lhs, rhs, expected, aux, NULL);

    for (i = 0u; i < SMOKE_RANDOM_CASES; ++i) {
        uint64_t seed = base_seed ^ (UINT64_C(0x9e3779b97f4a7c15) * (i + 1u));
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;

        smoke_generate_general_pair(lhs, rhs, &seed, i);
        lhs_obj = make_int_from_mpz(lhs);
        rhs_obj = make_int_from_mpz(rhs);

        mpz_add(expected, lhs, rhs);
        actual = lean_int_big_add(lhs_obj, rhs_obj);
        if (verify_int(actual, expected, "random.add") == 0) counts[0].pass += 1u; else { count_mismatch("add", i); status = 1; }
        free_int(actual);

        mpz_sub(expected, lhs, rhs);
        actual = lean_int_big_sub(lhs_obj, rhs_obj);
        if (verify_int(actual, expected, "random.sub") == 0) counts[1].pass += 1u; else { count_mismatch("sub", i); status = 1; }
        free_int(actual);

        mpz_mul(expected, lhs, rhs);
        actual = lean_int_big_mul(lhs_obj, rhs_obj);
        if (verify_int(actual, expected, "random.mul") == 0) counts[2].pass += 1u; else { count_mismatch("mul", i); status = 1; }
        free_int(actual);

        mpz_neg(expected, lhs);
        actual = lean_int_big_neg(lhs_obj);
        if (verify_int(actual, expected, "random.neg") == 0) counts[8].pass += 1u; else { count_mismatch("neg", i); status = 1; }
        free_int(actual);

        if (lean_int_big_eq(lhs_obj, rhs_obj) == (mpz_cmp(lhs, rhs) == 0)) counts[9].pass += 1u; else { count_mismatch("eq", i); status = 1; }
        if (lean_int_big_le(lhs_obj, rhs_obj) == (mpz_cmp(lhs, rhs) <= 0)) counts[10].pass += 1u; else { count_mismatch("le", i); status = 1; }
        if (lean_int_big_lt(lhs_obj, rhs_obj) == (mpz_cmp(lhs, rhs) < 0)) counts[11].pass += 1u; else { count_mismatch("lt", i); status = 1; }
        if (lean_int_big_nonneg(lhs_obj) == (mpz_sgn(lhs) >= 0)) counts[12].pass += 1u; else { count_mismatch("nonneg", i); status = 1; }

        free_int(lhs_obj);
        free_int(rhs_obj);
    }

    for (i = 0u; i < SMOKE_RANDOM_CASES; ++i) {
        uint64_t seed = base_seed ^ (UINT64_C(0xc2b2ae3d27d4eb4f) * (i + 1u));
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *div_obj;
        lean_object *mod_obj;
        lean_object *ediv_obj;
        lean_object *emod_obj;

        smoke_generate_div_case(lhs, rhs, &seed, i);
        lhs_obj = make_int_from_mpz(lhs);
        rhs_obj = make_int_from_mpz(rhs);

        if (mpz_sgn(rhs) == 0) {
            mpz_set_ui(expected, 0u);
            mpz_set(aux, lhs);
            div_obj = lean_int_big_div(lhs_obj, rhs_obj);
            if (verify_int(div_obj, expected, "random.div") == 0) counts[3].pass += 1u; else { count_mismatch("div", i); status = 1; }
            free_int(div_obj);

            mod_obj = lean_int_big_mod(lhs_obj, rhs_obj);
            if (verify_int(mod_obj, aux, "random.mod") == 0) counts[5].pass += 1u; else { count_mismatch("mod", i); status = 1; }
            free_int(mod_obj);

            ediv_obj = lean_int_big_ediv(lhs_obj, rhs_obj);
            if (verify_int(ediv_obj, expected, "random.ediv") == 0) counts[6].pass += 1u; else { count_mismatch("ediv", i); status = 1; }
            free_int(ediv_obj);

            emod_obj = lean_int_big_emod(lhs_obj, rhs_obj);
            if (verify_int(emod_obj, aux, "random.emod") == 0) counts[7].pass += 1u; else { count_mismatch("emod", i); status = 1; }
            free_int(emod_obj);
        } else {
            smoke_trunc_divmod(expected, aux, lhs, rhs);
            div_obj = lean_int_big_div(lhs_obj, rhs_obj);
            if (verify_int(div_obj, expected, "random.div") == 0) counts[3].pass += 1u; else { count_mismatch("div", i); status = 1; }
            free_int(div_obj);

            mod_obj = lean_int_big_mod(lhs_obj, rhs_obj);
            if (verify_int(mod_obj, aux, "random.mod") == 0) counts[5].pass += 1u; else { count_mismatch("mod", i); status = 1; }
            free_int(mod_obj);

            smoke_euclidean_divmod(expected, aux, lhs, rhs);
            ediv_obj = lean_int_big_ediv(lhs_obj, rhs_obj);
            if (verify_int(ediv_obj, expected, "random.ediv") == 0) counts[6].pass += 1u; else { count_mismatch("ediv", i); status = 1; }
            free_int(ediv_obj);

            emod_obj = lean_int_big_emod(lhs_obj, rhs_obj);
            if (verify_int(emod_obj, aux, "random.emod") == 0) counts[7].pass += 1u; else { count_mismatch("emod", i); status = 1; }
            free_int(emod_obj);
        }

        free_int(lhs_obj);
        free_int(rhs_obj);
    }

    for (i = 0u; i < SMOKE_RANDOM_CASES; ++i) {
        uint64_t seed = base_seed ^ (UINT64_C(0x94d049bb133111eb) * (i + 1u));
        lean_object *lhs_obj;
        lean_object *rhs_obj;
        lean_object *actual;

        smoke_generate_exact_case(lhs, rhs, &seed, i);
        lhs_obj = make_int_from_mpz(lhs);
        rhs_obj = make_int_from_mpz(rhs);
        mpz_tdiv_q(expected, lhs, rhs);
        actual = lean_int_big_div_exact(lhs_obj, rhs_obj);
        if (verify_int(actual, expected, "random.div_exact") == 0) counts[4].pass += 1u; else { count_mismatch("div_exact", i); status = 1; }
        free_int(actual);
        free_int(lhs_obj);
        free_int(rhs_obj);
    }

    if (verify_leak_free() != 0) {
        status = 1;
    }

    if (smoke_write_results_json(
            results_path,
            base_seed,
            counts,
            sizeof(counts) / sizeof(counts[0]),
            leanrt_test_allocator_alloc_count(),
            leanrt_test_allocator_free_count()) != 0) {
        fprintf(stderr, "failed to write results: %s\n", results_path);
        status = 1;
    }

    mpz_clears(lhs, rhs, expected, aux, NULL);
    return status;
}

int main(int argc, char **argv) {
    int status;

    if (argc < 2) {
        fprintf(stderr, "usage: %s canonical | randomized <results.json>\n", argv[0]);
        return 1;
    }

    lean_initialize_runtime_module();
    lean_initialize_thread();
    leanrt_test_allocator_reset_counters();

    if (strcmp(argv[1], "canonical") == 0) {
        status = run_canonical(stdout);
    } else if (strcmp(argv[1], "randomized") == 0 && argc == 3) {
        status = run_randomized(argv[2]);
    } else {
        fprintf(stderr, "usage: %s canonical | randomized <results.json>\n", argv[0]);
        status = 1;
    }

    lean_finalize_thread();
    return status;
}
