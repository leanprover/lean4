#include <gmp.h>

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static void init_decimal(mpz_t out, const char *text) {
    if (mpz_init_set_str(out, text, 10) != 0) {
        abort();
    }
}

static char *stringify_base(const mpz_t value, int base) {
    char *text = mpz_get_str(NULL, base, value);
    if (text == NULL) {
        abort();
    }
    return text;
}

static char *stringify_decimal(const mpz_t value) {
    return stringify_base(value, 10);
}

static int cmp_decimal_literal(const mpz_t value, const char *literal) {
    mpz_t other;
    init_decimal(other, literal);
    const int result = mpz_cmp(value, other);
    mpz_clear(other);
    return result;
}

static void euclidean_divmod(mpz_t q, mpz_t r, const mpz_t lhs, const mpz_t rhs) {
    mpz_tdiv_qr(q, r, lhs, rhs);
    if (mpz_sgn(r) < 0) {
        if (mpz_sgn(rhs) > 0) {
            mpz_sub_ui(q, q, 1);
            mpz_add(r, r, rhs);
        } else {
            mpz_add_ui(q, q, 1);
            mpz_sub(r, r, rhs);
        }
    }
}

void gmp_oracle_free_string(char *text) {
    free(text);
}

char *gmp_oracle_add(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_add(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_sub(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_sub(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_mul(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_mul(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

void gmp_oracle_div_trunc_qr(const char *lhs_text, const char *rhs_text, char **q_text, char **r_text) {
    mpz_t lhs, rhs, q, r;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_inits(q, r, NULL);
    mpz_tdiv_qr(q, r, lhs, rhs);
    *q_text = stringify_decimal(q);
    *r_text = stringify_decimal(r);
    mpz_clears(lhs, rhs, q, r, NULL);
}

void gmp_oracle_div_floor(const char *lhs_text, const char *rhs_text, char **q_text, char **r_text) {
    mpz_t lhs, rhs, q, r;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_inits(q, r, NULL);
    mpz_fdiv_qr(q, r, lhs, rhs);
    *q_text = stringify_decimal(q);
    *r_text = stringify_decimal(r);
    mpz_clears(lhs, rhs, q, r, NULL);
}

char *gmp_oracle_ediv(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, q, r;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_inits(q, r, NULL);
    euclidean_divmod(q, r, lhs, rhs);
    char *text = stringify_decimal(q);
    mpz_clears(lhs, rhs, q, r, NULL);
    return text;
}

char *gmp_oracle_emod(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, q, r;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_inits(q, r, NULL);
    euclidean_divmod(q, r, lhs, rhs);
    char *text = stringify_decimal(r);
    mpz_clears(lhs, rhs, q, r, NULL);
    return text;
}

char *gmp_oracle_div_exact(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_divexact(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_neg(const char *text) {
    mpz_t value;
    init_decimal(value, text);
    mpz_neg(value, value);
    char *out = stringify_decimal(value);
    mpz_clear(value);
    return out;
}

char *gmp_oracle_pow(const char *text, uint32_t exponent) {
    mpz_t value, out;
    init_decimal(value, text);
    mpz_init(out);
    mpz_pow_ui(out, value, exponent);
    char *result = stringify_decimal(out);
    mpz_clears(value, out, NULL);
    return result;
}

char *gmp_oracle_gcd(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_gcd(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_bit_and(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_and(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_bit_or(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_ior(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_bit_xor(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs, out;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    mpz_init(out);
    mpz_xor(out, lhs, rhs);
    char *text = stringify_decimal(out);
    mpz_clears(lhs, rhs, out, NULL);
    return text;
}

char *gmp_oracle_mul_2exp(const char *text, size_t shift) {
    mpz_t value, out;
    init_decimal(value, text);
    mpz_init(out);
    mpz_mul_2exp(out, value, shift);
    char *result = stringify_decimal(out);
    mpz_clears(value, out, NULL);
    return result;
}

char *gmp_oracle_fdiv_q_2exp(const char *text, size_t shift) {
    mpz_t value, out;
    init_decimal(value, text);
    mpz_init(out);
    mpz_fdiv_q_2exp(out, value, shift);
    char *result = stringify_decimal(out);
    mpz_clears(value, out, NULL);
    return result;
}

char *gmp_oracle_fdiv_r_2exp(const char *text, size_t shift) {
    mpz_t value, out;
    init_decimal(value, text);
    mpz_init(out);
    mpz_fdiv_r_2exp(out, value, shift);
    char *result = stringify_decimal(out);
    mpz_clears(value, out, NULL);
    return result;
}

char *gmp_oracle_smod_pow2(const char *text, size_t shift) {
    mpz_t value, out, threshold, modulus;
    init_decimal(value, text);
    mpz_inits(out, threshold, modulus, NULL);
    mpz_fdiv_r_2exp(out, value, shift);
    if (shift != 0) {
        mpz_set_ui(threshold, 1);
        mpz_mul_2exp(threshold, threshold, shift - 1);
        if (mpz_cmp(out, threshold) >= 0) {
            mpz_set_ui(modulus, 1);
            mpz_mul_2exp(modulus, modulus, shift);
            mpz_sub(out, out, modulus);
        }
    }
    char *result = stringify_decimal(out);
    mpz_clears(value, out, threshold, modulus, NULL);
    return result;
}

int gmp_oracle_cmp(const char *lhs_text, const char *rhs_text) {
    mpz_t lhs, rhs;
    init_decimal(lhs, lhs_text);
    init_decimal(rhs, rhs_text);
    const int result = mpz_cmp(lhs, rhs);
    mpz_clears(lhs, rhs, NULL);
    return result;
}

int gmp_oracle_cmp_i64(const char *lhs_text, int64_t rhs) {
    mpz_t lhs, rhs_value;
    char buffer[64];
    snprintf(buffer, sizeof(buffer), "%" PRId64, rhs);
    init_decimal(lhs, lhs_text);
    init_decimal(rhs_value, buffer);
    const int result = mpz_cmp(lhs, rhs_value);
    mpz_clears(lhs, rhs_value, NULL);
    return result;
}

int gmp_oracle_cmp_u64(const char *lhs_text, uint64_t rhs) {
    mpz_t lhs, rhs_value;
    char buffer[64];
    snprintf(buffer, sizeof(buffer), "%" PRIu64, rhs);
    init_decimal(lhs, lhs_text);
    init_decimal(rhs_value, buffer);
    const int result = mpz_cmp(lhs, rhs_value);
    mpz_clears(lhs, rhs_value, NULL);
    return result;
}

bool gmp_oracle_fits_i64(const char *text) {
    mpz_t value;
    init_decimal(value, text);
    const bool result =
        cmp_decimal_literal(value, "-9223372036854775808") >= 0 &&
        cmp_decimal_literal(value, "9223372036854775807") <= 0;
    mpz_clear(value);
    return result;
}

bool gmp_oracle_fits_u64(const char *text) {
    mpz_t value;
    init_decimal(value, text);
    const bool result =
        mpz_sgn(value) >= 0 &&
        cmp_decimal_literal(value, "18446744073709551615") <= 0;
    mpz_clear(value);
    return result;
}

bool gmp_oracle_fits_size_t(const char *text) {
    mpz_t value;
    init_decimal(value, text);
    const bool result =
        mpz_sgn(value) >= 0 &&
        cmp_decimal_literal(value, "18446744073709551615") <= 0;
    mpz_clear(value);
    return result;
}

int64_t gmp_oracle_get_i64(const char *text) {
    char *end = NULL;
    const int64_t value = strtoll(text, &end, 10);
    if (end == text || (end != NULL && *end != '\0')) {
        abort();
    }
    return value;
}

uint64_t gmp_oracle_get_u64(const char *text) {
    char *end = NULL;
    const uint64_t value = strtoull(text, &end, 10);
    if (end == text || (end != NULL && *end != '\0')) {
        abort();
    }
    return value;
}

size_t gmp_oracle_get_size_t(const char *text) {
    char *end = NULL;
    const uint64_t value = strtoull(text, &end, 10);
    if (end == text || (end != NULL && *end != '\0')) {
        abort();
    }
    return (size_t)value;
}

unsigned long long gmp_oracle_get_limb(const char *text, size_t index) {
    mpz_t value;
    init_decimal(value, text);
    const unsigned long long limb = (unsigned long long)mpz_getlimbn(value, index);
    mpz_clear(value);
    return limb;
}

char *gmp_oracle_to_string_base(const char *text, int base) {
    mpz_t value;
    init_decimal(value, text);
    char *result = stringify_base(value, base);
    mpz_clear(value);
    return result;
}

char *gmp_oracle_parse_base_to_base(const char *text, int input_base, int output_base) {
    mpz_t value;
    mpz_init(value);
    if (mpz_set_str(value, text, input_base) != 0) {
        abort();
    }
    char *result = stringify_base(value, output_base);
    mpz_clear(value);
    return result;
}

size_t gmp_oracle_log2_abs(const char *text) {
    mpz_t value;
    init_decimal(value, text);
    mpz_abs(value, value);
    const size_t result = mpz_sgn(value) == 0 ? 0 : mpz_sizeinbase(value, 2) - 1;
    mpz_clear(value);
    return result;
}

size_t gmp_oracle_bit_count_abs(const char *text) {
    mpz_t value;
    init_decimal(value, text);
    mpz_abs(value, value);
    const size_t result = mpz_sgn(value) == 0 ? 0 : mpz_sizeinbase(value, 2);
    mpz_clear(value);
    return result;
}
