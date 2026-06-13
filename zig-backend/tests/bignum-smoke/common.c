#include "common.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static void smoke_abort(void) {
    abort();
}

static void set_decimal(mpz_t out, const char *text) {
    if (mpz_set_str(out, text, 10) != 0) {
        smoke_abort();
    }
}

uint64_t smoke_next_u64(uint64_t *state) {
    uint64_t x = *state;
    x ^= x << 7;
    x ^= x >> 9;
    x ^= x << 8;
    *state = x;
    return x;
}

char *smoke_mpz_strdup(const mpz_t value) {
    char *text = mpz_get_str(NULL, 10, value);
    if (text == NULL) {
        smoke_abort();
    }
    return text;
}

void smoke_free_string(char *text) {
    free(text);
}

void smoke_random_positive_bits(mpz_t out, uint64_t *state, unsigned bits) {
    const size_t limb_count = bits == 0 ? 1u : (size_t)((bits + 63u) / 64u);
    uint64_t *limbs = (uint64_t *)calloc(limb_count, sizeof(uint64_t));
    size_t i;

    if (limbs == NULL) {
        smoke_abort();
    }

    mpz_set_ui(out, 0);
    if (bits == 0) {
        free(limbs);
        return;
    }

    for (i = 0; i < limb_count; ++i) {
        limbs[i] = smoke_next_u64(state);
    }
    if ((bits & 63u) != 0u) {
        limbs[limb_count - 1u] &= ((((uint64_t)1u) << (bits & 63u)) - 1u);
    }
    limbs[limb_count - 1u] |= ((uint64_t)1u) << ((bits - 1u) & 63u);
    mpz_import(out, limb_count, -1, sizeof(uint64_t), 0, 0, limbs);
    free(limbs);
}

static void generate_mixed_value(mpz_t out, uint64_t *state, size_t index, size_t salt) {
    const size_t mode = (index + salt) % 8u;

    switch (mode) {
    case 0:
        mpz_set_ui(out, smoke_next_u64(state) & 0xffffu);
        break;
    case 1:
        mpz_set_si(out, (long)((smoke_next_u64(state) & 0x7ffffu) - 0x3ffffu));
        break;
    case 2:
        smoke_random_positive_bits(out, state, 63u);
        if ((smoke_next_u64(state) & 1u) != 0u) mpz_neg(out, out);
        break;
    case 3:
        smoke_random_positive_bits(out, state, 64u + (unsigned)(smoke_next_u64(state) % 3u));
        if ((smoke_next_u64(state) & 1u) != 0u) mpz_neg(out, out);
        break;
    case 4:
        smoke_random_positive_bits(out, state, 96u + (unsigned)(smoke_next_u64(state) % 65u));
        if ((smoke_next_u64(state) & 1u) != 0u) mpz_neg(out, out);
        break;
    case 5:
        smoke_random_positive_bits(out, state, 160u + (unsigned)(smoke_next_u64(state) % 97u));
        if ((smoke_next_u64(state) & 1u) != 0u) mpz_neg(out, out);
        break;
    case 6:
        mpz_ui_pow_ui(out, 2u, 63u);
        mpz_add_ui(out, out, (unsigned long)(smoke_next_u64(state) & 0xffu));
        if ((smoke_next_u64(state) & 1u) != 0u) mpz_neg(out, out);
        break;
    default:
        if ((index % 11u) == 0u) {
            mpz_set_ui(out, 0u);
        } else {
            smoke_random_positive_bits(out, state, 256u + (unsigned)(smoke_next_u64(state) % 129u));
            if ((smoke_next_u64(state) & 1u) != 0u) mpz_neg(out, out);
        }
        break;
    }
}

void smoke_generate_general_pair(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index) {
    generate_mixed_value(lhs, state, index, 0u);
    generate_mixed_value(rhs, state, index, 3u);
}

void smoke_generate_div_case(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index) {
    static const char *const edge_cases[][2] = {
        {"-7", "3"},
        {"-7", "-3"},
        {"7", "-3"},
        {"-9223372036854775808", "-1"},
        {"0", "0"},
        {"340282366920938463463374607431768211456", "0"},
        {"-340282366920938463463374607431768211456", "0"},
        {"18446744073709551616", "4294967296"},
        {"-18446744073709551616", "4294967296"},
        {"18446744073709551616", "-4294967296"},
        {"-18446744073709551616", "-4294967296"},
        {"1", "1"},
        {"1", "-1"},
        {"-1", "1"},
        {"-1", "-1"},
        {"123456789012345678901234567890", "-97"},
    };

    if (index < (sizeof(edge_cases) / sizeof(edge_cases[0]))) {
        set_decimal(lhs, edge_cases[index][0]);
        set_decimal(rhs, edge_cases[index][1]);
        return;
    }

    smoke_generate_general_pair(lhs, rhs, state, index);
    switch (index % 19u) {
    case 0:
        mpz_set_ui(rhs, 0u);
        break;
    case 1:
        mpz_set_si(rhs, 1);
        break;
    case 2:
        mpz_set_si(rhs, -1);
        break;
    case 3:
        mpz_set_si(rhs, 3);
        break;
    case 4:
        mpz_set_si(rhs, -3);
        break;
    default:
        if (mpz_sgn(rhs) == 0) {
            mpz_set_si(rhs, (smoke_next_u64(state) & 1u) != 0u ? 5 : -5);
        }
        break;
    }
}

void smoke_generate_exact_case(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index) {
    mpz_t q;
    mpz_init(q);

    generate_mixed_value(rhs, state, index, 1u);
    if (mpz_sgn(rhs) == 0) {
        mpz_set_si(rhs, (smoke_next_u64(state) & 1u) != 0u ? 11 : -11);
    }

    generate_mixed_value(q, state, index, 5u);
    mpz_mul(lhs, rhs, q);

    mpz_clear(q);
}

void smoke_generate_roundtrip_value(mpz_t out, uint64_t *state, size_t index) {
    smoke_random_positive_bits(out, state, 96u + (unsigned)(smoke_next_u64(state) % 289u));
    if ((index & 1u) != 0u) {
        mpz_neg(out, out);
    }
}

static void random_prime(mpz_t out, uint64_t *state, unsigned bits) {
    smoke_random_positive_bits(out, state, bits);
    mpz_setbit(out, 0u);
    mpz_nextprime(out, out);
}

void smoke_generate_gcd_operands(mpz_t lhs, mpz_t rhs, mpz_t gcd, int *bezout_ok) {
    uint64_t seed = UINT64_C(0x13579bdf2468ace0);
    mpz_t shared, lhs_factor, rhs_factor, s, t, g;

    mpz_inits(shared, lhs_factor, rhs_factor, s, t, g, NULL);
    random_prime(shared, &seed, 4096u);
    random_prime(lhs_factor, &seed, 4096u);
    random_prime(rhs_factor, &seed, 4096u);

    mpz_mul(lhs, shared, lhs_factor);
    mpz_mul(rhs, shared, rhs_factor);
    mpz_gcd(gcd, lhs, rhs);
    mpz_gcdext(g, s, t, lhs, rhs);

    mpz_mul(s, s, lhs);
    mpz_mul(t, t, rhs);
    mpz_add(s, s, t);
    *bezout_ok = mpz_cmp(s, g) == 0 ? 1 : 0;

    mpz_clears(shared, lhs_factor, rhs_factor, s, t, g, NULL);
}

void smoke_trunc_divmod(mpz_t q, mpz_t r, const mpz_t lhs, const mpz_t rhs) {
    mpz_tdiv_qr(q, r, lhs, rhs);
}

void smoke_euclidean_divmod(mpz_t q, mpz_t r, const mpz_t lhs, const mpz_t rhs) {
    mpz_tdiv_qr(q, r, lhs, rhs);
    if (mpz_sgn(r) < 0) {
        if (mpz_sgn(rhs) > 0) {
            mpz_sub_ui(q, q, 1u);
            mpz_add(r, r, rhs);
        } else {
            mpz_add_ui(q, q, 1u);
            mpz_sub(r, r, rhs);
        }
    }
}

int smoke_write_results_json(
    const char *path,
    uint64_t seed,
    const struct smoke_count *counts,
    size_t count_len,
    size_t alloc_count,
    size_t free_count
) {
    FILE *out = fopen(path, "w");
    size_t i;

    if (out == NULL) {
        return 1;
    }

    fprintf(out, "{\n");
    fprintf(out, "  \"seed\": \"0x%016" PRIx64 "\",\n", seed);
    fprintf(out, "  \"allocator\": {\n");
    fprintf(out, "    \"alloc\": %zu,\n", alloc_count);
    fprintf(out, "    \"free\": %zu,\n", free_count);
    fprintf(out, "    \"net\": %zu\n", alloc_count >= free_count ? alloc_count - free_count : free_count - alloc_count);
    fprintf(out, "  },\n");
    fprintf(out, "  \"ops\": {\n");
    for (i = 0; i < count_len; ++i) {
        fprintf(
            out,
            "    \"%s\": {\"pass\": %zu, \"total\": %zu}%s\n",
            counts[i].name,
            counts[i].pass,
            counts[i].total,
            i + 1u == count_len ? "" : ","
        );
    }
    fprintf(out, "  }\n");
    fprintf(out, "}\n");

    return fclose(out) == 0 ? 0 : 1;
}
