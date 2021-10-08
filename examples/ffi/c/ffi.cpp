#include <lean/lean.h>

extern "C" uint32_t my_add(uint32_t a, uint32_t b) {
    return a + b;
}

extern "C" lean_obj_res my_lean_fun() {
    return lean_io_result_mk_ok(lean_box(0));
}
