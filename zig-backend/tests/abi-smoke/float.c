#include <lean/lean.h>

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

/* Mimics mimalloc's layout: the returned pointer is the allocation itself
 * (no size prefix), so it pairs with the malloc-backed mi_free stubs. */
void *mi_malloc_small(size_t size) {
    return malloc(size);
}

static double double_from_bits(uint64_t bits) {
    double value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static uint64_t double_to_bits(double value) {
    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

static float float_from_bits(uint32_t bits) {
    float value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static uint32_t float_to_bits(float value) {
    uint32_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

int main(void) {
    const uint64_t nan64_bits = UINT64_C(0x7ff8000000001234);
    const uint32_t nan32_bits = UINT32_C(0x7fc01234);

    lean_initialize_runtime_module();
    lean_initialize_thread();

    {
        const double nan64 = double_from_bits(nan64_bits);
        lean_object *boxed = lean_box_float(nan64);
        CHECK(lean_float_isnan(nan64) == 1);
        CHECK(double_to_bits(lean_unbox_float(boxed)) == nan64_bits);
        lean_dec(boxed);
    }

    {
        const float nan32 = float_from_bits(nan32_bits);
        lean_object *boxed = lean_box_float32(nan32);
        CHECK(lean_float32_isnan(nan32) == 1);
        CHECK(float_to_bits(lean_unbox_float32(boxed)) == nan32_bits);
        lean_dec(boxed);
    }

    {
        lean_object *result = lean_float_frexp(0.0);
        CHECK(!lean_is_scalar(result));
        CHECK(double_to_bits(lean_unbox_float(lean_ctor_get(result, 0))) == 0);
        CHECK(lean_ctor_get(result, 1) == lean_box(0));
        lean_dec(result);
    }

    {
        lean_object *result = lean_float32_frexp(0.0f);
        CHECK(!lean_is_scalar(result));
        CHECK(float_to_bits(lean_unbox_float32(lean_ctor_get(result, 0))) == 0);
        CHECK(lean_ctor_get(result, 1) == lean_box(0));
        lean_dec(result);
    }

    CHECK(lean_float_isfinite(INFINITY) == 0);
    CHECK(lean_float_isinf(INFINITY) == 1);
    CHECK(lean_float32_isfinite(INFINITY) == 0);
    CHECK(lean_float32_isinf(INFINITY) == 1);

    {
        lean_object *str = lean_float_to_string(3.14);
        CHECK(strncmp(lean_string_cstr(str), "3.14", 4) == 0);
        lean_dec(str);
    }

    {
        lean_object *str = lean_float32_to_string(3.14f);
        CHECK(strncmp(lean_string_cstr(str), "3.14", 4) == 0);
        lean_dec(str);
    }

    lean_finalize_thread();
    return 0;
}
