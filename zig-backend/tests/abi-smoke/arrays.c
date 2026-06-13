#include <lean/lean.h>

#include <stdint.h>
#include <stdio.h>

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
    lean_initialize_runtime_module();
    lean_initialize_thread();

    lean_object *array = lean_mk_empty_array();
    CHECK(array != NULL);
    CHECK(lean_array_size(array) == 0);

    array = lean_array_push(array, lean_box(10));
    array = lean_array_push(array, lean_box(20));
    array = lean_array_push(array, lean_box(30));
    CHECK(lean_array_size(array) == 3);
    CHECK(lean_unbox(lean_array_get(lean_box(0), array, lean_box(0))) == 10);
    CHECK(lean_unbox(lean_array_get(lean_box(0), array, lean_box(2))) == 30);

    array = lean_array_set(array, lean_box(1), lean_box(42));
    CHECK(lean_unbox(lean_array_get(lean_box(0), array, lean_box(1))) == 42);

    lean_object *bytes = lean_mk_empty_byte_array(lean_box(0));
    CHECK(bytes != NULL);
    CHECK(lean_sarray_size(bytes) == 0);

    bytes = lean_byte_array_push(bytes, 0x11);
    bytes = lean_byte_array_push(bytes, 0x22);
    bytes = lean_byte_array_push(bytes, 0x33);
    CHECK(lean_sarray_size(bytes) == 3);
    CHECK(lean_byte_array_get(bytes, lean_box(0)) == 0x11);
    CHECK(lean_byte_array_get(bytes, lean_box(2)) == 0x33);

    bytes = lean_byte_array_set(bytes, lean_box(1), 0x44);
    CHECK(lean_byte_array_get(bytes, lean_box(1)) == 0x44);

    lean_dec(array);
    lean_dec(bytes);
    lean_finalize_thread();
    return 0;
}
