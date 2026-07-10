/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
*/

#define lean_alloc_ctor lean_native_inline_alloc_ctor
#define lean_box_float lean_native_inline_box_float
#define lean_ctor_set lean_native_inline_ctor_set
#define lean_dec lean_native_inline_dec
#define lean_dec_ref lean_native_inline_dec_ref
#define lean_float_add lean_native_inline_float_add
#define lean_inc_ref lean_native_inline_inc_ref
#define lean_nat_add lean_native_inline_nat_add
#define lean_nat_dec_eq lean_native_inline_nat_dec_eq
#define lean_nat_mul lean_native_inline_nat_mul
#define lean_nat_sub lean_native_inline_nat_sub
#define lean_unbox_float lean_native_inline_unbox_float

#include <lean/lean.h>

#undef lean_alloc_ctor
#undef lean_box_float
#undef lean_ctor_set
#undef lean_dec
#undef lean_dec_ref
#undef lean_float_add
#undef lean_inc_ref
#undef lean_nat_add
#undef lean_nat_dec_eq
#undef lean_nat_mul
#undef lean_nat_sub
#undef lean_unbox_float

extern "C" {

LEAN_EXPORT lean_object * lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    return lean_native_inline_alloc_ctor(tag, num_objs, scalar_sz);
}

LEAN_EXPORT void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v) {
    lean_native_inline_ctor_set(o, i, v);
}

LEAN_EXPORT void lean_inc_ref(lean_object * o) {
    lean_native_inline_inc_ref(o);
}

LEAN_EXPORT void lean_dec_ref(lean_object * o) {
    lean_native_inline_dec_ref(o);
}

LEAN_EXPORT void lean_dec(lean_object * o) {
    lean_native_inline_dec(o);
}

LEAN_EXPORT lean_object * lean_nat_add(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_add(a, b);
}

LEAN_EXPORT lean_object * lean_nat_sub(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_sub(a, b);
}

LEAN_EXPORT lean_object * lean_nat_mul(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_mul(a, b);
}

LEAN_EXPORT uint8_t lean_nat_dec_eq(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_dec_eq(a, b);
}

LEAN_EXPORT lean_object * lean_box_float(double value) {
    return lean_native_inline_box_float(value);
}

LEAN_EXPORT double lean_unbox_float(b_lean_obj_arg value) {
    return lean_native_inline_unbox_float(value);
}

LEAN_EXPORT double lean_float_add(double a, double b) {
    return lean_native_inline_float_add(a, b);
}

}
