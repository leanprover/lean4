#include <lean/lean.h>

#include <stdbool.h>
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

    lean_object *ascii = lean_mk_string("hello, world");
    lean_object *ascii_copy = lean_mk_string("hello, world");
    lean_object *utf8 = lean_mk_string("héllo");
    lean_object *utf8_copy = lean_mk_string("héllo");

    CHECK(ascii != NULL);
    CHECK(utf8 != NULL);
    CHECK(lean_obj_tag(ascii) == LeanString);
    CHECK(lean_obj_tag(utf8) == LeanString);

    CHECK(lean_to_string(ascii)->m_size == 13);
    CHECK(lean_to_string(ascii)->m_length == 12);
    CHECK(lean_unbox(lean_string_length(ascii)) == 12);
    CHECK(lean_unbox(lean_string_utf8_byte_size(ascii)) == 12);

    CHECK(lean_to_string(utf8)->m_size == 7);
    CHECK(lean_to_string(utf8)->m_length == 5);
    CHECK(lean_unbox(lean_string_length(utf8)) == 5);
    CHECK(lean_unbox(lean_string_utf8_byte_size(utf8)) == 6);
    CHECK(lean_string_utf8_get(utf8, lean_box(0)) == (uint32_t)'h');
    CHECK(lean_string_utf8_get(utf8, lean_box(1)) == 0xE9u);

    CHECK(lean_string_eq(ascii, ascii_copy));
    CHECK(lean_string_eq(utf8, utf8_copy));
    CHECK(!lean_string_eq(ascii, utf8));

    lean_dec(ascii);
    lean_dec(ascii_copy);
    lean_dec(utf8);
    lean_dec(utf8_copy);
    lean_finalize_thread();
    return 0;
}
