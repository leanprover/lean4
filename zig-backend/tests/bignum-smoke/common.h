#ifndef ZIG_BACKEND_BIGNUM_SMOKE_COMMON_H
#define ZIG_BACKEND_BIGNUM_SMOKE_COMMON_H

#include <gmp.h>

#include <stddef.h>
#include <stdint.h>

#define SMOKE_DIV_CASES 1000u
#define SMOKE_ROUNDTRIP_CASES 256u
#define SMOKE_RANDOM_CASES 128u

struct smoke_count {
    const char *name;
    size_t pass;
    size_t total;
};

uint64_t smoke_next_u64(uint64_t *state);
char *smoke_mpz_strdup(const mpz_t value);
void smoke_free_string(char *text);

void smoke_random_positive_bits(mpz_t out, uint64_t *state, unsigned bits);
void smoke_generate_general_pair(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index);
void smoke_generate_div_case(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index);
void smoke_generate_exact_case(mpz_t lhs, mpz_t rhs, uint64_t *state, size_t index);
void smoke_generate_roundtrip_value(mpz_t out, uint64_t *state, size_t index);
void smoke_generate_gcd_operands(mpz_t lhs, mpz_t rhs, mpz_t gcd, int *bezout_ok);

void smoke_trunc_divmod(mpz_t q, mpz_t r, const mpz_t lhs, const mpz_t rhs);
void smoke_euclidean_divmod(mpz_t q, mpz_t r, const mpz_t lhs, const mpz_t rhs);

int smoke_write_results_json(
    const char *path,
    uint64_t seed,
    const struct smoke_count *counts,
    size_t count_len,
    size_t alloc_count,
    size_t free_count
);

#endif
