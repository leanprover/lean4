#include <lean/lean.h>

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

lean_obj_res lean_box_uint8_zig(uint8_t v);
uint8_t lean_unbox_uint8_zig(b_lean_obj_arg o);
lean_obj_res lean_box_uint16_zig(uint16_t v);
uint16_t lean_unbox_uint16_zig(b_lean_obj_arg o);

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

void *mi_malloc_small(size_t size) {
    return malloc(size);
}

int main(void) {
    const uint8_t u8_values[] = {0, UINT8_MAX};
    const uint16_t u16_values[] = {0, UINT16_MAX};
    const uint32_t u32_values[] = {0, UINT32_MAX};
    const uint64_t u64_values[] = {0, UINT64_MAX};

    lean_initialize_runtime_module();
    lean_initialize_thread();

    for (size_t i = 0; i < sizeof(u8_values) / sizeof(u8_values[0]); ++i) {
        lean_object *boxed = lean_box_uint8_zig(u8_values[i]);
        CHECK(lean_unbox_uint8_zig(boxed) == u8_values[i]);
    }

    for (size_t i = 0; i < sizeof(u16_values) / sizeof(u16_values[0]); ++i) {
        lean_object *boxed = lean_box_uint16_zig(u16_values[i]);
        CHECK(lean_unbox_uint16_zig(boxed) == u16_values[i]);
    }

    for (size_t i = 0; i < sizeof(u32_values) / sizeof(u32_values[0]); ++i) {
        lean_object *boxed = lean_box_uint32(u32_values[i]);
        CHECK(lean_unbox_uint32(boxed) == u32_values[i]);
    }

    for (size_t i = 0; i < sizeof(u64_values) / sizeof(u64_values[0]); ++i) {
        lean_object *boxed = lean_box_uint64(u64_values[i]);
        CHECK(lean_unbox_uint64(boxed) == u64_values[i]);
    }

    printf("BX1.uint_variants OK\n");
    lean_finalize_thread();
    return 0;
}
