#include <lean/lean.h>

#include <stdbool.h>
#include <stdio.h>

extern lean_object *lean_cstr_to_int(char const *n);
extern bool lean_int_big_eq(lean_object *a1, lean_object *a2);
extern int leanrt_test_mpz_compactor_roundtrip(lean_object *o, char const *expected);
extern size_t leanrt_test_mpz_object_size(void);
extern size_t leanrt_test_cpp_mpz_object_size(void);

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

int main(void) {
    static char const *const kValue = "340282366920938463463374607431768211457";
    lean_object *value;
    int roundtrip_result;

    lean_initialize_runtime_module();
    lean_initialize_thread();

    value = lean_cstr_to_int(kValue);
    CHECK(value != NULL);
    CHECK(lean_int_big_eq(value, value));

    roundtrip_result = leanrt_test_mpz_compactor_roundtrip(value, kValue);
    if (leanrt_test_mpz_object_size() == leanrt_test_cpp_mpz_object_size()) {
        CHECK(roundtrip_result == 1);
    } else {
        CHECK(roundtrip_result == 0);
    }

    if (!lean_is_scalar(value)) lean_dec(value);
    lean_finalize_thread();
    return 0;
}
