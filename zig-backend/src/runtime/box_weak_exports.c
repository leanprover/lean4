#include <stdint.h>

void *lean_box_uint8_zig_impl(uint8_t v);
uint8_t lean_unbox_uint8_zig_impl(void *o);
void *lean_box_uint16_zig_impl(uint16_t v);
uint16_t lean_unbox_uint16_zig_impl(void *o);

__attribute__((weak)) void *lean_box_uint8_zig(uint8_t v) {
    return lean_box_uint8_zig_impl(v);
}

__attribute__((weak)) uint8_t lean_unbox_uint8_zig(void *o) {
    return lean_unbox_uint8_zig_impl(o);
}

__attribute__((weak)) void *lean_box_uint16_zig(uint16_t v) {
    return lean_box_uint16_zig_impl(v);
}

__attribute__((weak)) uint16_t lean_unbox_uint16_zig(void *o) {
    return lean_unbox_uint16_zig_impl(o);
}
