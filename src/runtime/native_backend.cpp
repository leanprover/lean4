/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
*/

#define lean_alloc_ctor lean_native_inline_alloc_ctor
#define lean_alloc_closure lean_native_inline_alloc_closure
#define lean_array_get lean_native_inline_array_get
#define lean_array_get_size lean_native_inline_array_get_size
#define lean_array_fget lean_native_inline_array_fget
#define lean_array_size lean_native_inline_array_size
#define lean_box_float lean_native_inline_box_float
#define lean_box_float32 lean_native_inline_box_float32
#define lean_box_uint32 lean_native_inline_box_uint32
#define lean_box_uint64 lean_native_inline_box_uint64
#define lean_box_usize lean_native_inline_box_usize
#define lean_ctor_set lean_native_inline_ctor_set
#define lean_closure_set lean_native_inline_closure_set
#define lean_ctor_release lean_native_inline_ctor_release
#define lean_dec lean_native_inline_dec
#define lean_dec_ref lean_native_inline_dec_ref
#define lean_del_object lean_native_inline_del_object
#define lean_float_add lean_native_inline_float_add
#define lean_inc_ref lean_native_inline_inc_ref
#define lean_inc_ref_n lean_native_inline_inc_ref_n
#define lean_inc_n lean_native_inline_inc_n
#define lean_nat_add lean_native_inline_nat_add
#define lean_nat_dec_eq lean_native_inline_nat_dec_eq
#define lean_nat_dec_lt lean_native_inline_nat_dec_lt
#define lean_nat_dec_le lean_native_inline_nat_dec_le
#define lean_nat_mul lean_native_inline_nat_mul
#define lean_nat_mod lean_native_inline_nat_mod
#define lean_nat_sub lean_native_inline_nat_sub
#define lean_mk_empty_array_with_capacity lean_native_inline_mk_empty_array_with_capacity
#define lean_uint32_of_nat lean_native_inline_uint32_of_nat
#define lean_uint32_to_nat lean_native_inline_uint32_to_nat
#define lean_unbox_float lean_native_inline_unbox_float
#define lean_unbox_float32 lean_native_inline_unbox_float32
#define lean_unbox_uint32 lean_native_inline_unbox_uint32
#define lean_unbox_uint64 lean_native_inline_unbox_uint64
#define lean_unbox_usize lean_native_inline_unbox_usize
#define lean_usize_of_nat lean_native_inline_usize_of_nat
#define lean_array_uget_borrowed lean_native_inline_array_uget_borrowed
#define lean_array_fget_borrowed lean_native_inline_array_fget_borrowed
#define lean_array_get_borrowed lean_native_inline_array_get_borrowed
#define lean_string_dec_eq lean_native_inline_string_dec_eq

#include <lean/lean.h>

#undef lean_alloc_ctor
#undef lean_alloc_closure
#undef lean_array_get
#undef lean_array_get_size
#undef lean_array_fget
#undef lean_array_size
#undef lean_box_float
#undef lean_box_float32
#undef lean_box_uint32
#undef lean_box_uint64
#undef lean_box_usize
#undef lean_ctor_set
#undef lean_closure_set
#undef lean_ctor_release
#undef lean_dec
#undef lean_dec_ref
#undef lean_del_object
#undef lean_float_add
#undef lean_inc_ref
#undef lean_inc_ref_n
#undef lean_inc_n
#undef lean_nat_add
#undef lean_nat_dec_eq
#undef lean_nat_dec_lt
#undef lean_nat_dec_le
#undef lean_nat_mul
#undef lean_nat_mod
#undef lean_nat_sub
#undef lean_mk_empty_array_with_capacity
#undef lean_uint32_of_nat
#undef lean_uint32_to_nat
#undef lean_unbox_float
#undef lean_unbox_float32
#undef lean_unbox_uint32
#undef lean_unbox_uint64
#undef lean_unbox_usize
#undef lean_usize_of_nat
#undef lean_array_uget_borrowed
#undef lean_array_fget_borrowed
#undef lean_array_get_borrowed
#undef lean_string_dec_eq

extern "C" {

LEAN_EXPORT lean_object * lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    return lean_native_inline_alloc_ctor(tag, num_objs, scalar_sz);
}

LEAN_EXPORT lean_object * lean_alloc_closure(void * fun, unsigned arity, unsigned num_fixed) {
    return lean_native_inline_alloc_closure(fun, arity, num_fixed);
}

LEAN_EXPORT lean_object * lean_mk_empty_array_with_capacity(b_lean_obj_arg capacity) {
    return lean_native_inline_mk_empty_array_with_capacity(capacity);
}

LEAN_EXPORT lean_object * lean_array_get(b_lean_obj_arg default_value, b_lean_obj_arg array,
                                         b_lean_obj_arg index) {
    return lean_native_inline_array_get(default_value, array, index);
}

LEAN_EXPORT lean_object * lean_array_get_size(b_lean_obj_arg array) {
    return lean_native_inline_array_get_size(array);
}

LEAN_EXPORT lean_object * lean_array_fget(b_lean_obj_arg array, b_lean_obj_arg index) {
    return lean_native_inline_array_fget(array, index);
}

LEAN_EXPORT lean_object * lean_array_size(b_lean_obj_arg array) {
    return lean_box(lean_native_inline_array_size(array));
}

LEAN_EXPORT void lean_closure_set(lean_object * o, unsigned i, lean_object * a) {
    lean_native_inline_closure_set(o, i, a);
}

LEAN_EXPORT lean_object * lean_wasm_reset(lean_object * o, uint32_t fields) {
    if (lean_is_exclusive(o)) {
        for (uint32_t i = 0; i < fields; ++i) lean_native_inline_ctor_release(o, i);
        return o;
    }
    lean_native_inline_dec_ref(o);
    return lean_box(0);
}

LEAN_EXPORT lean_object * lean_wasm_reuse_ctor(lean_object * token, uint32_t tag,
                                          uint32_t objects, uint32_t scalar_size,
                                          uint8_t update_header) {
    if (lean_is_scalar(token)) return lean_native_inline_alloc_ctor(tag, objects, scalar_size);
    if (update_header) lean_ctor_set_tag(token, tag);
    return token;
}

LEAN_EXPORT void lean_ctor_set(b_lean_obj_arg o, unsigned i, lean_obj_arg v) {
    lean_native_inline_ctor_set(o, i, v);
}

LEAN_EXPORT void lean_inc_ref(lean_object * o) {
    lean_native_inline_inc_ref(o);
}

LEAN_EXPORT void lean_inc_ref_n(lean_object * o, size_t n) {
    lean_native_inline_inc_ref_n(o, n);
}

LEAN_EXPORT void lean_inc_n(lean_object * o, size_t n) {
    lean_native_inline_inc_n(o, n);
}

LEAN_EXPORT void lean_dec_ref(lean_object * o) {
    lean_native_inline_dec_ref(o);
}

LEAN_EXPORT void lean_dec(lean_object * o) {
    lean_native_inline_dec(o);
}

LEAN_EXPORT uint8_t lean_wasm_is_shared(lean_object * o) {
    return !lean_is_exclusive(o);
}

LEAN_EXPORT void lean_wasm_del_object(lean_object * o) {
    lean_native_inline_del_object(o);
}

LEAN_EXPORT void lean_wasm_ctor_set_tag(lean_object * o, uint8_t tag) {
    lean_ctor_set_tag(o, tag);
}

LEAN_EXPORT uint32_t lean_wasm_string_byte_size(lean_object * o) {
    return lean_string_size(o) - 1;
}

LEAN_EXPORT lean_object * lean_wasm_unsigned_to_nat(uint32_t value) {
    return lean_unsigned_to_nat(value);
}

LEAN_EXPORT lean_object * lean_wasm_init_ok(void) {
    return lean_io_result_mk_ok(lean_box(0));
}

/* Staging buffer for high-arity closure application (arity > 16).
   Single-threaded WASI / browser demos only; not re-entrant through apply_m. */
enum { LEAN_WASM_APPLY_M_MAX = 64 };
static lean_object * lean_wasm_apply_m_buf[LEAN_WASM_APPLY_M_MAX];

LEAN_EXPORT void lean_wasm_apply_m_set(uint32_t i, lean_object * a) {
    if (i >= LEAN_WASM_APPLY_M_MAX) return;
    lean_wasm_apply_m_buf[i] = a;
}

LEAN_EXPORT lean_object * lean_wasm_apply_m(lean_object * f, uint32_t n) {
    if (n > LEAN_WASM_APPLY_M_MAX) n = LEAN_WASM_APPLY_M_MAX;
    return lean_apply_m(f, (unsigned)n, lean_wasm_apply_m_buf);
}

/* --- Minimal UI reconciler host bridge (fiber demo) -------------------------
   Flat effect buffer readable from JS; optional fiber object retained across frames.
   Strings are interned for the current effect batch; JS reads them via ptr/len
   into wasm linear memory (UTF-8, no trailing NUL required). */
/* Effect words: op, id, parent, a, b, c, d
   create: a=tag, b=classStrId, c=index, d=onClickStrId (0 = none)
   createText/updateText free string: a=255, b=strId
   setClass: a=classStrId */
enum { LEAN_UI_MAX_EFFECTS = 512, LEAN_UI_EFFECT_WORDS = 7, LEAN_UI_MAX_STRINGS = 256,
       LEAN_UI_SCRATCH = 8192 };
static uint32_t lean_ui_effects[LEAN_UI_MAX_EFFECTS * LEAN_UI_EFFECT_WORDS];
static uint32_t lean_ui_effect_count = 0;
static lean_object * lean_ui_fiber = nullptr; /* Option Fiber as a Lean object */
static lean_object * lean_ui_model = nullptr; /* Option Model as a Lean object */
static lean_object * lean_ui_strings[LEAN_UI_MAX_STRINGS];
static uint32_t lean_ui_string_count = 0;
static uint8_t lean_ui_scratch[LEAN_UI_SCRATCH];

static void lean_ui_clear_strings() {
    for (uint32_t i = 0; i < lean_ui_string_count; i++) {
        if (lean_ui_strings[i]) {
            lean_dec(lean_ui_strings[i]);
            lean_ui_strings[i] = nullptr;
        }
    }
    lean_ui_string_count = 0;
}

/* World-token ABI: each op takes/returns a UInt32 so Lean cannot DCE the call
   as an unused pure Unit computation. Token is passed through unchanged. */
LEAN_EXPORT uint32_t lean_ui_clear_effects(uint32_t world) {
    lean_ui_effect_count = 0;
    lean_ui_clear_strings();
    return world;
}

/* Intern a Lean String for this frame. Returns string id (index). Holds a ref
   until the next clear_effects. `s` is borrowed. */
LEAN_EXPORT uint32_t lean_ui_intern_string(b_lean_obj_arg s) {
    if (lean_ui_string_count >= LEAN_UI_MAX_STRINGS)
        return 0;
    lean_inc(s);
    uint32_t id = lean_ui_string_count++;
    lean_ui_strings[id] = s;
    return id;
}

/* Wasm32: pointer is a 32-bit offset into linear memory. */
LEAN_EXPORT uint32_t lean_ui_string_ptr(uint32_t id) {
    if (id >= lean_ui_string_count || !lean_ui_strings[id]) return 0;
    return (uint32_t)(uintptr_t)lean_string_cstr(lean_ui_strings[id]);
}

LEAN_EXPORT uint32_t lean_ui_string_len(uint32_t id) {
    if (id >= lean_ui_string_count || !lean_ui_strings[id]) return 0;
    size_t sz = lean_string_size(lean_ui_strings[id]);
    return sz == 0 ? 0 : (uint32_t)(sz - 1); /* drop NUL */
}

/* Scratch buffer so JS can pass UTF-8 event names into Lean without a full allocator. */
LEAN_EXPORT uint32_t lean_ui_scratch_ptr(void) {
    return (uint32_t)(uintptr_t)lean_ui_scratch;
}

LEAN_EXPORT uint32_t lean_ui_scratch_cap(void) {
    return LEAN_UI_SCRATCH;
}

/* Build a Lean String from bytes already in linear memory (copied). */
LEAN_EXPORT lean_object * lean_ui_string_from_utf8(uint32_t ptr, uint32_t len) {
    if (len == 0) return lean_mk_string("");
    char const * p = (char const *)(uintptr_t)ptr;
    return lean_mk_string_from_bytes(p, (size_t)len);
}

LEAN_EXPORT uint32_t lean_ui_push_effect(uint32_t world, uint32_t op, uint32_t id, uint32_t parent,
                                        uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
    if (lean_ui_effect_count < LEAN_UI_MAX_EFFECTS) {
        uint32_t * slot = &lean_ui_effects[lean_ui_effect_count * LEAN_UI_EFFECT_WORDS];
        slot[0] = op;
        slot[1] = id;
        slot[2] = parent;
        slot[3] = a;
        slot[4] = b;
        slot[5] = c;
        slot[6] = d;
        lean_ui_effect_count++;
    }
    return world;
}

LEAN_EXPORT uint32_t lean_ui_effect_count_get(uint32_t /* world */) {
    return lean_ui_effect_count;
}

LEAN_EXPORT uint32_t lean_ui_effect_word(uint32_t index) {
    if (index >= lean_ui_effect_count * LEAN_UI_EFFECT_WORDS) return 0;
    return lean_ui_effects[index];
}

LEAN_EXPORT lean_object * lean_ui_load_fiber(uint32_t /* world */) {
    if (!lean_ui_fiber) return lean_box(0); /* Option.none */
    lean_inc(lean_ui_fiber);
    return lean_ui_fiber;
}

/* Borrowed Option Fiber: we lean_inc so the retained root outlives the caller. */
LEAN_EXPORT uint32_t lean_ui_store_fiber(uint32_t world, b_lean_obj_arg fiber_opt) {
    if (lean_ui_fiber) lean_dec(lean_ui_fiber);
    lean_inc(fiber_opt);
    lean_ui_fiber = fiber_opt;
    return world;
}

LEAN_EXPORT lean_object * lean_ui_load_model(uint32_t /* world */) {
    if (!lean_ui_model) return lean_box(0);
    lean_inc(lean_ui_model);
    return lean_ui_model;
}

/* Borrowed Option Model (same ownership model as store_fiber). */
LEAN_EXPORT uint32_t lean_ui_store_model(uint32_t world, b_lean_obj_arg model_opt) {
    if (lean_ui_model) lean_dec(lean_ui_model);
    lean_inc(model_opt);
    lean_ui_model = model_opt;
    return world;
}

LEAN_EXPORT __attribute__((weak)) lean_object * initialize_Init(uint8_t) {
    return lean_io_result_mk_ok(lean_box(0));
}

/* Core RT has no IO streams; object.cpp references this for panic paths. */
LEAN_EXPORT lean_object * lean_io_eprintln(lean_object * s) {
    lean_dec(s);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Closed-nullary Inhabited Array instance used by some compiled defaults. */
LEAN_EXPORT lean_object * l_Array_instInhabited(void) {
    return lean_alloc_array(0, 0);
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

LEAN_EXPORT lean_object * lean_nat_mod(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_mod(a, b);
}

LEAN_EXPORT lean_object * lean_uint32_to_nat(uint32_t value) {
    return lean_native_inline_uint32_to_nat(value);
}

LEAN_EXPORT uint32_t lean_uint32_of_nat(b_lean_obj_arg value) {
    return lean_native_inline_uint32_of_nat(value);
}

LEAN_EXPORT uint8_t lean_nat_dec_eq(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_dec_eq(a, b);
}

LEAN_EXPORT uint8_t lean_nat_dec_lt(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_dec_lt(a, b);
}

/* Header-only inlines that the wasm backend calls as symbols. */
LEAN_EXPORT uint8_t lean_nat_dec_le(b_lean_obj_arg a, b_lean_obj_arg b) {
    return lean_native_inline_nat_dec_le(a, b);
}

LEAN_EXPORT size_t lean_usize_of_nat(b_lean_obj_arg a) {
    return lean_native_inline_usize_of_nat(a);
}

LEAN_EXPORT lean_object * lean_array_uget_borrowed(b_lean_obj_arg a, size_t i) {
    return lean_native_inline_array_uget_borrowed(a, i);
}

LEAN_EXPORT lean_object * lean_array_fget_borrowed(b_lean_obj_arg a, b_lean_obj_arg i) {
    return lean_native_inline_array_fget_borrowed(a, i);
}

LEAN_EXPORT lean_object * lean_array_get_borrowed(b_lean_obj_arg def_val, b_lean_obj_arg a,
                                                 b_lean_obj_arg i) {
    return lean_native_inline_array_get_borrowed(def_val, a, i);
}

LEAN_EXPORT uint8_t lean_string_dec_eq(b_lean_obj_arg s1, b_lean_obj_arg s2) {
    return lean_native_inline_string_dec_eq(s1, s2);
}

LEAN_EXPORT lean_object * lean_box_float(double value) {
    return lean_native_inline_box_float(value);
}

LEAN_EXPORT double lean_unbox_float(b_lean_obj_arg value) {
    return lean_native_inline_unbox_float(value);
}

LEAN_EXPORT lean_object * lean_box_float32(float value) {
    return lean_native_inline_box_float32(value);
}

LEAN_EXPORT float lean_unbox_float32(b_lean_obj_arg value) {
    return lean_native_inline_unbox_float32(value);
}

LEAN_EXPORT lean_object * lean_box_uint32(uint32_t value) {
    return lean_native_inline_box_uint32(value);
}

LEAN_EXPORT uint32_t lean_unbox_uint32(b_lean_obj_arg value) {
    return lean_native_inline_unbox_uint32(value);
}

LEAN_EXPORT lean_object * lean_box_uint64(uint64_t value) {
    return lean_native_inline_box_uint64(value);
}

LEAN_EXPORT uint64_t lean_unbox_uint64(b_lean_obj_arg value) {
    return lean_native_inline_unbox_uint64(value);
}

LEAN_EXPORT lean_object * lean_box_usize(size_t value) {
    return lean_native_inline_box_usize(value);
}

LEAN_EXPORT size_t lean_unbox_usize(b_lean_obj_arg value) {
    return lean_native_inline_unbox_usize(value);
}

LEAN_EXPORT double lean_float_add(double a, double b) {
    return lean_native_inline_float_add(a, b);
}

}
