#include "../common.h"

#include <gmp.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int run_canonical(FILE *out) {
    uint64_t div_seed = UINT64_C(0x2468ace013579bdf);
    uint64_t roundtrip_seed = UINT64_C(0x0ddc0ffeebadf00d);
    mpz_t lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value;
    int bezout_ok = 0;
    size_t i;

    mpz_inits(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);

    mpz_ui_pow_ui(pow_value, 2u, 100u);
    {
        char *text = smoke_mpz_strdup(pow_value);
        fprintf(out, "pow_2_100=%s\n", text);
        smoke_free_string(text);
    }

    mpz_set_ui(fact_value, 1u);
    for (i = 2u; i <= 1000u; ++i) {
        mpz_mul_ui(fact_value, fact_value, (unsigned long)i);
    }
    {
        char *text = smoke_mpz_strdup(fact_value);
        fprintf(out, "factorial_1000=%s\n", text);
        smoke_free_string(text);
    }

    smoke_generate_gcd_operands(lhs, rhs, gcd_value, &bezout_ok);
    {
        char *text = smoke_mpz_strdup(gcd_value);
        fprintf(out, "large_gcd=%s\n", text);
        smoke_free_string(text);
    }
    fprintf(out, "bezout_check=%d\n", bezout_ok);

    fprintf(out, "mixed_sign_int_div_begin\n");
    for (i = 0u; i < SMOKE_DIV_CASES; ++i) {
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
        {
            char *lhs_text = smoke_mpz_strdup(lhs);
            char *rhs_text = smoke_mpz_strdup(rhs);
            char *div_text = smoke_mpz_strdup(q);
            char *ediv_text = smoke_mpz_strdup(ediv);
            char *mod_text = smoke_mpz_strdup(r);
            char *emod_text = smoke_mpz_strdup(emod);
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
        }
    }
    fprintf(out, "mixed_sign_int_div_end\n");

    fprintf(out, "string_roundtrip_begin\n");
    for (i = 0u; i < SMOKE_ROUNDTRIP_CASES; ++i) {
        smoke_generate_roundtrip_value(lhs, &roundtrip_seed, i);
        {
            char *text = smoke_mpz_strdup(lhs);
            fprintf(out, "roundtrip[%03zu]=%s\n", i, text);
            smoke_free_string(text);
        }
    }
    fprintf(out, "string_roundtrip_end\n");

    mpz_clears(lhs, rhs, q, r, ediv, emod, pow_value, fact_value, gcd_value, NULL);
    return 0;
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "canonical";

    if (strcmp(mode, "canonical") != 0) {
        fprintf(stderr, "usage: %s [canonical]\n", argv[0]);
        return 1;
    }

    return run_canonical(stdout);
}
