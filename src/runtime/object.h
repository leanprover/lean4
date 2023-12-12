/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <lean/lean.h>
#include "runtime/mpz.h"

namespace lean {
typedef uint8_t  uint8;
typedef uint16_t uint16;
typedef uint32_t uint32;
typedef uint64_t uint64;
typedef size_t   usize;

typedef lean_object object;
typedef object * obj_arg;
typedef object * b_obj_arg;
typedef object * u_obj_arg;
typedef object * obj_res;
typedef object * b_obj_res;

struct mpz_object {
    lean_object m_header;
    mpz         m_value;
    mpz_object() {}
    explicit mpz_object(mpz const & m):m_value(m) {}
};

typedef lean_external_class         external_object_class;
typedef lean_external_finalize_proc external_object_finalize_proc;
typedef lean_external_foreach_proc  external_object_foreach_proc;

inline external_object_class * register_external_object_class(external_object_finalize_proc p1, external_object_foreach_proc p2) {
    return lean_register_external_class(p1, p2);
}

inline bool is_scalar(object * o) { return lean_is_scalar(o); }
inline object * box(size_t n) { return lean_box(n); }
inline size_t unbox(object * o) { return lean_unbox(o); }

inline bool is_mt_heap_obj(object * o) { return lean_is_mt(o); }
inline bool is_st_heap_obj(object * o) { return lean_is_st(o); }
inline bool is_heap_obj(object * o) { return is_st_heap_obj(o) || is_mt_heap_obj(o); }
inline void mark_mt(object * o) { lean_mark_mt(o); }
inline bool is_shared(object * o) { return lean_is_shared(o); }
inline bool is_exclusive(object * o) { return lean_is_exclusive(o); }
inline void inc_ref(object * o) { lean_inc_ref(o); }
inline void inc_ref(object * o, size_t n) { lean_inc_ref_n(o, n); }
inline void dec_ref(object * o) { lean_dec_ref(o); }
inline void inc(object * o) { lean_inc(o); }
inline void inc(object * o, size_t n) { lean_inc_n(o, n); }
inline void dec(object * o) { lean_dec(o); }
inline void free_heap_obj(object * o) { lean_free_object(o); }

inline bool is_cnstr(object * o) { return lean_is_ctor(o); }
inline bool is_closure(object * o) { return lean_is_closure(o); }
inline bool is_array(object * o) { return lean_is_array(o); }
inline bool is_sarray(object * o) { return lean_is_sarray(o); }
inline bool is_string(object * o) { return lean_is_string(o); }
inline bool is_mpz(object * o) { return lean_is_mpz(o); }
inline bool is_thunk(object * o) { return lean_is_thunk(o); }
inline bool is_task(object * o) { return lean_is_task(o); }
inline bool is_external(object * o) { return lean_is_external(o); }
inline bool is_ref(object * o) { return lean_is_ref(o); }

inline void mark_persistent(object * o) { return lean_mark_persistent(o); }

inline unsigned obj_tag(b_obj_arg o) { return lean_obj_tag(o); }

// =======================================
// Constructors

inline unsigned cnstr_num_objs(object * o) { return lean_ctor_num_objs(o); }
inline object ** cnstr_obj_cptr(object * o) { return lean_ctor_obj_cptr(o); }
inline uint8 * cnstr_scalar_cptr(object * o) { return lean_ctor_scalar_cptr(o); }
inline obj_res alloc_cnstr(unsigned tag, unsigned num_objs, unsigned scalar_sz) { return lean_alloc_ctor(tag, num_objs, scalar_sz); }
inline unsigned cnstr_tag(b_obj_arg o) { lean_assert(is_cnstr(o)); return lean_ptr_tag(o); }
inline void cnstr_set_tag(b_obj_arg o, unsigned tag) { lean_ctor_set_tag(o, tag); }
inline b_obj_res cnstr_get(b_obj_arg o, unsigned i) { return lean_ctor_get(o, i); }
inline void cnstr_set(u_obj_arg o, unsigned i, obj_arg v) { lean_ctor_set(o, i, v); }
inline void cnstr_release(u_obj_arg o, unsigned i) { lean_ctor_release(o, i); }
inline usize cnstr_get_usize(b_obj_arg o, unsigned i) { return lean_ctor_get_usize(o, i); }
inline void cnstr_set_usize(b_obj_arg o, unsigned i, usize v) { lean_ctor_set_usize(o, i, v); }
inline uint8 cnstr_get_uint8(b_obj_arg o, unsigned offset) { return lean_ctor_get_uint8(o, offset); }
inline uint16 cnstr_get_uint16(b_obj_arg o, unsigned offset) { return lean_ctor_get_uint16(o, offset); }
inline uint32 cnstr_get_uint32(b_obj_arg o, unsigned offset) { return lean_ctor_get_uint32(o, offset); }
inline uint64 cnstr_get_uint64(b_obj_arg o, unsigned offset) { return lean_ctor_get_uint64(o, offset); }
inline double cnstr_get_float(b_obj_arg o, unsigned offset) { return lean_ctor_get_float(o, offset); }
inline void cnstr_set_uint8(b_obj_arg o, unsigned offset, uint8 v) { lean_ctor_set_uint8(o, offset, v); }
inline void cnstr_set_uint16(b_obj_arg o, unsigned offset, uint16 v) { lean_ctor_set_uint16(o, offset, v); }
inline void cnstr_set_uint32(b_obj_arg o, unsigned offset, uint32 v) { lean_ctor_set_uint32(o, offset, v); }
inline void cnstr_set_uint64(b_obj_arg o, unsigned offset, uint64 v) { lean_ctor_set_uint64(o, offset, v); }
inline void cnstr_set_float(b_obj_arg o, unsigned offset, double v) { lean_ctor_set_float(o, offset, v); }

// =======================================
// Closures

void free_closure_obj(object * o);
inline void * closure_fun(object * o) { return lean_closure_fun(o); }
inline unsigned closure_arity(object * o) { return lean_closure_arity(o); }
inline unsigned closure_num_fixed(object * o) { return lean_closure_num_fixed(o); }
inline object ** closure_arg_cptr(object * o) { return lean_closure_arg_cptr(o); }
inline obj_res alloc_closure(void * fun, unsigned arity, unsigned num_fixed) { return lean_alloc_closure(fun, arity, num_fixed); }
inline b_obj_res closure_get(b_obj_arg o, unsigned i) { return lean_closure_get(o, i); }
inline void closure_set(u_obj_arg o, unsigned i, obj_arg a) { lean_closure_set(o, i, a); }
inline obj_res alloc_closure(object*(*fun)(object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 1, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 2, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 3, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 4, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 5, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 6, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 7, num_fixed);
}
inline obj_res alloc_closure(object*(*fun)(object *, object *, object *, object *, object *, object *, object *, object *), unsigned num_fixed) {
    return alloc_closure(reinterpret_cast<void*>(fun), 8, num_fixed);
}
inline object* apply_1(object* f, object* a1) { return lean_apply_1(f, a1); }
inline object* apply_2(object* f, object* a1, object* a2) { return lean_apply_2(f, a1, a2); }
inline object* apply_3(object* f, object* a1, object* a2, object* a3) { return lean_apply_3(f, a1, a2, a3); }
inline object* apply_4(object* f, object* a1, object* a2, object* a3, object* a4) { return lean_apply_4(f, a1, a2, a3, a4); }
inline object* apply_5(object* f, object* a1, object* a2, object* a3, object* a4, object* a5) {
    return lean_apply_5(f, a1, a2, a3, a4, a5);
}
inline object* apply_6(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6) {
    return lean_apply_6(f, a1, a2, a3, a4, a5, a6);
}
inline object* apply_7(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7) {
    return lean_apply_7(f, a1, a2, a3, a4, a5, a6, a7);
}
inline object* apply_8(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8) {
    return lean_apply_8(f, a1, a2, a3, a4, a5, a6, a7, a8);
}
inline object* apply_9(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9) {
    return lean_apply_9(f, a1, a2, a3, a4, a5, a6, a7, a8, a9);
}
inline object* apply_10(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10) {
    return lean_apply_10(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
}
inline object* apply_11(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10, object* a11) {
    return lean_apply_11(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
}
inline object* apply_12(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10, object* a11, object* a12) {
    return lean_apply_12(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
}
inline object* apply_13(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10, object* a11, object* a12, object* a13) {
    return lean_apply_13(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13);
}
inline object* apply_14(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10, object* a11, object* a12, object* a13, object* a14) {
    return lean_apply_14(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14);
}
inline object* apply_15(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10, object* a11, object* a12, object* a13, object* a14, object* a15) {
    return lean_apply_15(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15);
}
inline object* apply_16(object* f, object* a1, object* a2, object* a3, object* a4, object* a5, object* a6, object* a7, object* a8, object* a9, object* a10, object* a11, object* a12, object* a13, object* a14, object* a15, object* a16) {
    return lean_apply_16(f, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16);
}
inline object* apply_n(object* f, unsigned n, object** args) { return lean_apply_n(f, n, args); }
// pre: n > 16
inline object* apply_m(object* f, unsigned n, object** args) { return lean_apply_m(f, n, args); }

// =======================================
// MPZ

object * alloc_mpz(mpz const &);
inline mpz_object * to_mpz(object * o) { lean_assert(is_mpz(o)); return (mpz_object*)o; }

// =======================================
// Array of objects

inline size_t array_capacity(object * o) { return lean_array_capacity(o); }
inline object ** array_cptr(object * o) { return lean_array_cptr(o); }
inline obj_res alloc_array(size_t size, size_t capacity) { return lean_alloc_array(size, capacity); }
object * array_mk_empty();
inline size_t array_size(b_obj_arg o) { return lean_array_size(o); }
inline void array_set_size(u_obj_arg o, size_t sz) { lean_array_set_size(o, sz); }
inline b_obj_res array_get(b_obj_arg o, size_t i) { return lean_array_get_core(o, i); }
inline void array_set(u_obj_arg o, size_t i, obj_arg v) { lean_array_set_core(o, i, v); }
inline object * array_sz(obj_arg a) { return lean_array_sz(a); }
inline object * array_get_size(b_obj_arg a) { return lean_array_get_size(a); }
inline object * mk_empty_array() { return lean_mk_empty_array(); }
inline object * mk_empty_array(b_obj_arg capacity) { return lean_mk_empty_array_with_capacity(capacity); }
inline object * array_uget(b_obj_arg a, usize i) { return lean_array_uget(a, i); }
inline obj_res array_fget(b_obj_arg a, b_obj_arg i) { return lean_array_fget(a, i); }
inline object * array_get(obj_arg def_val, b_obj_arg a, b_obj_arg i) { return lean_array_get(def_val, a, i); }
inline obj_res copy_array(obj_arg a, bool expand = false) { return lean_copy_expand_array(a, expand); }
inline object * array_uset(obj_arg a, usize i, obj_arg v) { return lean_array_uset(a, i, v); }
inline object * array_fset(obj_arg a, b_obj_arg i, obj_arg v) { return lean_array_fset(a, i, v); }
inline object * array_set(obj_arg a, b_obj_arg i, obj_arg v) { return lean_array_set(a, i, v); }
inline object * array_pop(obj_arg a) { return lean_array_pop(a); }
inline object * array_uswap(obj_arg a, usize i, usize j) { return lean_array_uswap(a, i, j); }
inline object * array_fswap(obj_arg a, b_obj_arg i, b_obj_arg j) { return lean_array_fswap(a, i, j); }
inline object * array_swap(obj_arg a, b_obj_arg i, b_obj_arg j) { return lean_array_swap(a, i, j); }
inline object * array_push(obj_arg a, obj_arg v) { return lean_array_push(a, v); }
inline object * mk_array(obj_arg n, obj_arg v) { return lean_mk_array(n, v); }

// =======================================
// Array of scalars

inline obj_res alloc_sarray(unsigned elem_size, size_t size, size_t capacity) { return lean_alloc_sarray(elem_size, size, capacity); }
inline size_t sarray_size(b_obj_arg o) { return lean_sarray_size(o); }
inline void sarray_set_size(u_obj_arg o, size_t sz) { lean_sarray_set_size(o, sz); }
inline unsigned sarray_elem_size(object * o) { return lean_sarray_elem_size(o); }
inline size_t sarray_capacity(object * o) { return lean_sarray_capacity(o); }
inline uint8 * sarray_cptr(object * o) { return lean_sarray_cptr(o); }

// =======================================
// ByteArray

inline obj_res byte_array_mk(obj_arg a) { return lean_byte_array_mk(a); }
inline obj_res byte_array_data(obj_arg a) { return lean_byte_array_data(a); }
inline obj_res copy_byte_array(obj_arg a) { return lean_copy_byte_array(a); }
inline obj_res mk_empty_byte_array(b_obj_arg capacity) { return lean_mk_empty_byte_array(capacity); }
inline obj_res byte_array_size(b_obj_arg a) { return lean_byte_array_size(a); }
inline uint8 byte_array_get(b_obj_arg a, b_obj_arg i) { return lean_byte_array_get(a, i); }
inline obj_res byte_array_push(obj_arg a, uint8 b) { return lean_byte_array_push(a, b); }
inline obj_res byte_array_set(obj_arg a, b_obj_arg i, uint8 b) { return lean_byte_array_set(a, i, b); }

// =======================================
// String

inline size_t string_capacity(object * o) { return lean_string_capacity(o); }
inline uint32 char_default_value() { return lean_char_default_value(); }
inline obj_res alloc_string(size_t size, size_t capacity, size_t len) { return lean_alloc_string(size, capacity, len); }
inline obj_res mk_string(char const * s) { return lean_mk_string(s); }
obj_res mk_string(std::string const & s);
std::string string_to_std(b_obj_arg o);
inline char const * string_cstr(b_obj_arg o) { return lean_string_cstr(o); }
inline size_t string_size(b_obj_arg o) { return lean_string_size(o); }
inline size_t string_len(b_obj_arg o) { return lean_string_len(o); }
inline obj_res string_push(obj_arg s, uint32 c) { return lean_string_push(s, c); }
inline obj_res string_append(obj_arg s1, b_obj_arg s2) { return lean_string_append(s1, s2); }
inline obj_res string_length(b_obj_arg s) { return lean_string_length(s); }
inline obj_res string_mk(obj_arg cs) { return lean_string_mk(cs); }
inline obj_res string_data(obj_arg s) { return lean_string_data(s); }
inline uint32  string_utf8_get(b_obj_arg s, b_obj_arg i) { return lean_string_utf8_get(s, i); }
inline obj_res string_utf8_next(b_obj_arg s, b_obj_arg i) { return lean_string_utf8_next(s, i); }
inline obj_res string_utf8_prev(b_obj_arg s, b_obj_arg i) { return lean_string_utf8_prev(s, i); }
inline obj_res string_utf8_set(obj_arg s, b_obj_arg i, uint32 c) { return lean_string_utf8_set(s, i, c); }
inline uint8 string_utf8_at_end(b_obj_arg s, b_obj_arg i) { return lean_string_utf8_at_end(s, i); }
inline obj_res string_utf8_extract(b_obj_arg s, b_obj_arg b, b_obj_arg e) { return lean_string_utf8_extract(s, b, e); }
inline obj_res string_utf8_byte_size(b_lean_obj_arg s) { return lean_string_utf8_byte_size(s); }
inline bool string_eq(b_obj_arg s1, b_obj_arg s2) { return lean_string_eq(s1, s2); }
bool string_eq(b_obj_arg s1, char const * s2);
inline bool string_ne(b_obj_arg s1, b_obj_arg s2) { return lean_string_ne(s1, s2); }
inline bool string_lt(b_obj_arg s1, b_obj_arg s2) { return lean_string_lt(s1, s2); }
inline uint8 string_dec_eq(b_obj_arg s1, b_obj_arg s2) { return string_eq(s1, s2); }
inline uint8 string_dec_lt(b_obj_arg s1, b_obj_arg s2) { return string_lt(s1, s2); }
inline uint64 string_hash(b_obj_arg s) { return lean_string_hash(s); }

// =======================================
// Thunks

inline obj_res mk_thunk(obj_arg c) { return lean_mk_thunk(c); }
inline obj_res thunk_pure(obj_arg v) { return lean_thunk_pure(v); }
inline b_obj_res thunk_get(b_obj_arg t) { return lean_thunk_get(t); }
inline obj_res thunk_get_own(b_obj_arg t) { return lean_thunk_get_own(t); }

// =======================================
// Tasks

class scoped_task_manager {
public:
    scoped_task_manager(unsigned num_workers);
    ~scoped_task_manager();
};

inline obj_res task_spawn(obj_arg c, unsigned prio = 0, bool keep_alive = false) { return lean_task_spawn_core(c, prio, keep_alive); }
inline obj_res task_pure(obj_arg a) { return lean_task_pure(a); }
inline obj_res task_bind(obj_arg x, obj_arg f, unsigned prio = 0, bool keep_alive = false) { return lean_task_bind_core(x, f, prio, keep_alive); }
inline obj_res task_map(obj_arg f, obj_arg t, unsigned prio = 0, bool keep_alive = false) { return lean_task_map_core(f, t, prio, keep_alive); }
inline b_obj_res task_get(b_obj_arg t) { return lean_task_get(t); }

inline bool io_check_canceled_core() { return lean_io_check_canceled_core(); }
inline void io_cancel_core(b_obj_arg t) { return lean_io_cancel_core(t); }
inline bool io_has_finished_core(b_obj_arg t) { return lean_io_has_finished_core(t); }
inline b_obj_res io_wait_any_core(b_obj_arg task_list) { return lean_io_wait_any_core(task_list); }

// =======================================
// External

inline object * alloc_external(external_object_class * cls, void * data) { return lean_alloc_external(cls, data); }
inline external_object_class * external_class(object * o) { return lean_get_external_class(o); }
inline void * external_data(object * o) { return lean_get_external_data(o); }

// =======================================
// Option

inline obj_res mk_option_none() { return box(0); }
inline obj_res mk_option_some(obj_arg v) { obj_res r = alloc_cnstr(1, 1, 0); cnstr_set(r, 0, v); return r; }

// =======================================
// Natural numbers

inline mpz const & mpz_value(b_obj_arg o) { return to_mpz(o)->m_value; }
object * mpz_to_nat_core(mpz const & m);
inline object * mk_nat_obj_core(mpz const & m) { return mpz_to_nat_core(m); }
inline obj_res mk_nat_obj(mpz const & m) {
    if (m.is_size_t() && m.get_size_t() <= LEAN_MAX_SMALL_NAT)
        return box(m.get_size_t());
    else
        return mk_nat_obj_core(m);
}
inline obj_res usize_to_nat(usize n) { return lean_usize_to_nat(n); }
inline obj_res mk_nat_obj(unsigned n) { return lean_unsigned_to_nat(n); }
inline obj_res uint64_to_nat(uint64 n) { return lean_uint64_to_nat(n); }
inline obj_res nat_succ(b_obj_arg a) { return lean_nat_succ(a); }
inline obj_res nat_add(b_obj_arg a1, b_obj_arg a2) { return lean_nat_add(a1, a2); }
inline obj_res nat_sub(b_obj_arg a1, b_obj_arg a2) { return lean_nat_sub(a1, a2); }
inline obj_res nat_mul(b_obj_arg a1, b_obj_arg a2) { return lean_nat_mul(a1, a2); }
inline obj_res nat_pow(b_obj_arg a1, b_obj_arg a2) { return lean_nat_pow(a1, a2); }
inline obj_res nat_gcd(b_obj_arg a1, b_obj_arg a2) { return lean_nat_gcd(a1, a2); }
inline obj_res nat_div(b_obj_arg a1, b_obj_arg a2) { return lean_nat_div(a1, a2); }
inline obj_res nat_mod(b_obj_arg a1, b_obj_arg a2) { return lean_nat_mod(a1, a2); }
inline bool nat_eq(b_obj_arg a1, b_obj_arg a2) { return lean_nat_eq(a1, a2); }
inline uint8 nat_dec_eq(b_obj_arg a1, b_obj_arg a2) { return lean_nat_dec_eq(a1, a2); }
inline bool nat_ne(b_obj_arg a1, b_obj_arg a2) { return lean_nat_ne(a1, a2); }
inline bool nat_le(b_obj_arg a1, b_obj_arg a2) { return lean_nat_le(a1, a2); }
inline uint8 nat_dec_le(b_obj_arg a1, b_obj_arg a2) { return lean_nat_dec_le(a1, a2); }
inline bool nat_lt(b_obj_arg a1, b_obj_arg a2) { return lean_nat_lt(a1, a2); }
inline uint8 nat_dec_lt(b_obj_arg a1, b_obj_arg a2) { return lean_nat_dec_lt(a1, a2); }
inline obj_res nat_land(b_obj_arg a1, b_obj_arg a2) { return lean_nat_land(a1, a2); }
inline obj_res nat_lor(b_obj_arg a1, b_obj_arg a2) { return lean_nat_lor(a1, a2); }
inline obj_res nat_lxor(b_obj_arg a1, b_obj_arg a2) { return lean_nat_lxor(a1, a2); }

// =======================================
// Integers
object * mk_int_obj_core(mpz const & m);
inline obj_res mk_int_obj(mpz const & m) {
    if (m < LEAN_MIN_SMALL_INT || m > LEAN_MAX_SMALL_INT)
        return mk_int_obj_core(m);
    else
        return box(static_cast<unsigned>(m.get_int()));
}
inline obj_res mk_int_obj(int n) { return lean_int_to_int(n); }
inline obj_res mk_int_obj(int64 n) { return lean_int64_to_int(n); }
inline obj_res nat2int(obj_arg a) { return lean_nat_to_int(a); }
inline obj_res int_neg(b_obj_arg a) { return lean_int_neg(a); }
inline obj_res int_neg_succ_of_nat(obj_arg a) { return lean_int_neg_succ_of_nat(a); }
inline obj_res int_add(b_obj_arg a1, b_obj_arg a2) { return lean_int_add(a1, a2); }
inline obj_res int_sub(b_obj_arg a1, b_obj_arg a2) { return lean_int_sub(a1, a2); }
inline obj_res int_mul(b_obj_arg a1, b_obj_arg a2) { return lean_int_mul(a1, a2); }
inline obj_res int_div(b_obj_arg a1, b_obj_arg a2) { return lean_int_div(a1, a2); }
inline obj_res int_mod(b_obj_arg a1, b_obj_arg a2) { return lean_int_mod(a1, a2); }
inline bool int_eq(b_obj_arg a1, b_obj_arg a2) { return lean_int_eq(a1, a2); }
inline bool int_ne(b_obj_arg a1, b_obj_arg a2) { return lean_int_ne(a1, a2); }
inline bool int_le(b_obj_arg a1, b_obj_arg a2) { return lean_int_le(a1, a2); }
inline bool int_lt(b_obj_arg a1, b_obj_arg a2) { return lean_int_lt(a1, a2); }
inline obj_res nat_abs(b_obj_arg i) { return lean_nat_abs(i); }
inline uint8 int_dec_eq(b_obj_arg a1, b_obj_arg a2) { return lean_int_dec_eq(a1, a2); }
inline uint8 int_dec_le(b_obj_arg a1, b_obj_arg a2) { return lean_int_dec_le(a1, a2); }
inline uint8 int_dec_lt(b_obj_arg a1, b_obj_arg a2) { return lean_int_dec_lt(a1, a2); }
inline uint8 int_dec_nonneg(b_obj_arg a) { return lean_int_dec_nonneg(a); }

// =======================================
// Boxing

inline obj_res box_uint32(unsigned v) { return lean_box_uint32(v); }
inline unsigned unbox_uint32(b_obj_arg o) { return lean_unbox_uint32(o); }
inline obj_res box_uint64(unsigned long long v) { return lean_box_uint64(v); }
inline unsigned long long unbox_uint64(b_obj_arg o) { return lean_unbox_uint64(o); }
inline obj_res box_float(double v) { return lean_box_float(v); }
inline double unbox_float(b_obj_arg o) { return lean_unbox_float(o); }
inline obj_res box_size_t(size_t v) { return lean_box_usize(v); }
inline size_t unbox_size_t(b_obj_arg o) { return lean_unbox_usize(o); }

// =======================================
// uint8
inline uint8 uint8_of_nat(b_obj_arg a) { return lean_uint8_of_nat(a); }
inline obj_res uint8_to_nat(uint8 a) { return lean_uint8_to_nat(a); }
inline uint8 uint8_add(uint8 a1, uint8 a2) { return lean_uint8_add(a1, a2); }
inline uint8 uint8_sub(uint8 a1, uint8 a2) { return lean_uint8_sub(a1, a2); }
inline uint8 uint8_mul(uint8 a1, uint8 a2) { return lean_uint8_mul(a1, a2); }
inline uint8 uint8_div(uint8 a1, uint8 a2) { return lean_uint8_div(a1, a2); }
inline uint8 uint8_mod(uint8 a1, uint8 a2) { return lean_uint8_mod(a1, a2); }
inline uint8 uint8_modn(uint8 a1, b_obj_arg a2) { return lean_uint8_modn(a1, a2); }
inline uint8 uint8_dec_eq(uint8 a1, uint8 a2) { return lean_uint8_dec_eq(a1, a2); }
inline uint8 uint8_dec_lt(uint8 a1, uint8 a2) { return lean_uint8_dec_lt(a1, a2); }
inline uint8 uint8_dec_le(uint8 a1, uint8 a2) { return lean_uint8_dec_le(a1, a2); }

// =======================================
// uint16
inline uint16 uint16_of_nat(b_obj_arg a) { return lean_uint16_of_nat(a); }
inline obj_res uint16_to_nat(uint16 a) { return lean_uint16_to_nat(a); }
inline uint16 uint16_add(uint16 a1, uint16 a2) { return lean_uint16_add(a1, a2); }
inline uint16 uint16_sub(uint16 a1, uint16 a2) { return lean_uint16_sub(a1, a2); }
inline uint16 uint16_mul(uint16 a1, uint16 a2) { return lean_uint16_mul(a1, a2); }
inline uint16 uint16_div(uint16 a1, uint16 a2) { return lean_uint16_div(a1, a2); }
inline uint16 uint16_mod(uint16 a1, uint16 a2) { return lean_uint16_mod(a1, a2); }
inline uint16 uint16_modn(uint16 a1, b_obj_arg a2) { return lean_uint16_modn(a1, a2); }
inline uint16 uint16_dec_eq(uint16 a1, uint16 a2) { return lean_uint16_dec_eq(a1, a2); }
inline uint16 uint16_dec_lt(uint16 a1, uint16 a2) { return lean_uint16_dec_lt(a1, a2); }
inline uint16 uint16_dec_le(uint16 a1, uint16 a2) { return lean_uint16_dec_le(a1, a2); }

// =======================================
// uint32
inline uint32 uint32_of_nat(b_obj_arg a) { return lean_uint32_of_nat(a); }
inline obj_res uint32_to_nat(uint32 a) { return lean_uint32_to_nat(a); }
inline uint32 uint32_add(uint32 a1, uint32 a2) { return lean_uint32_add(a1, a2); }
inline uint32 uint32_sub(uint32 a1, uint32 a2) { return lean_uint32_sub(a1, a2); }
inline uint32 uint32_mul(uint32 a1, uint32 a2) { return lean_uint32_mul(a1, a2); }
inline uint32 uint32_div(uint32 a1, uint32 a2) { return lean_uint32_div(a1, a2); }
inline uint32 uint32_mod(uint32 a1, uint32 a2) { return lean_uint32_mod(a1, a2); }
inline uint32 uint32_modn(uint32 a1, b_obj_arg a2) { return lean_uint32_modn(a1, a2); }
inline uint32 uint32_dec_eq(uint32 a1, uint32 a2) { return lean_uint32_dec_eq(a1, a2); }
inline uint32 uint32_dec_lt(uint32 a1, uint32 a2) { return lean_uint32_dec_lt(a1, a2); }
inline uint32 uint32_dec_le(uint32 a1, uint32 a2) { return lean_uint32_dec_le(a1, a2); }

// =======================================
// uint64
inline uint64 uint64_of_nat(b_obj_arg a) { return lean_uint64_of_nat(a); }
inline uint64 uint64_add(uint64 a1, uint64 a2) { return lean_uint64_add(a1, a2); }
inline uint64 uint64_sub(uint64 a1, uint64 a2) { return lean_uint64_sub(a1, a2); }
inline uint64 uint64_mul(uint64 a1, uint64 a2) { return lean_uint64_mul(a1, a2); }
inline uint64 uint64_div(uint64 a1, uint64 a2) { return lean_uint64_div(a1, a2); }
inline uint64 uint64_mod(uint64 a1, uint64 a2) { return lean_uint64_mod(a1, a2); }
inline uint64 uint64_modn(uint64 a1, b_obj_arg a2) { return lean_uint64_modn(a1, a2); }
inline uint64 uint64_dec_eq(uint64 a1, uint64 a2) { return lean_uint64_dec_eq(a1, a2); }
inline uint64 uint64_dec_lt(uint64 a1, uint64 a2) { return lean_uint64_dec_lt(a1, a2); }
inline uint64 uint64_dec_le(uint64 a1, uint64 a2) { return lean_uint64_dec_le(a1, a2); }

// =======================================
// usize
inline usize usize_of_nat(b_obj_arg a) { return lean_usize_of_nat(a); }
inline usize usize_add(usize a1, usize a2) { return lean_usize_add(a1, a2); }
inline usize usize_sub(usize a1, usize a2) { return lean_usize_sub(a1, a2); }
inline usize usize_mul(usize a1, usize a2) { return lean_usize_mul(a1, a2); }
inline usize usize_div(usize a1, usize a2) { return lean_usize_div(a1, a2); }
inline usize usize_mod(usize a1, usize a2) { return lean_usize_mod(a1, a2); }
inline usize usize_modn(usize a1, b_obj_arg a2) { return lean_usize_modn(a1, a2); }
inline usize usize_dec_eq(usize a1, usize a2) { return lean_usize_dec_eq(a1, a2); }
inline usize usize_dec_lt(usize a1, usize a2) { return lean_usize_dec_lt(a1, a2); }
inline usize usize_dec_le(usize a1, usize a2) { return lean_usize_dec_le(a1, a2); }

// =======================================
// debugging helper functions
inline object * dbg_trace(obj_arg s, obj_arg fn) { return lean_dbg_trace(s, fn); }
inline object * dbg_sleep(uint32 ms, obj_arg fn) { return lean_dbg_sleep(ms, fn); }
inline object * dbg_trace_if_shared(obj_arg s, obj_arg a) { return lean_dbg_trace_if_shared(s, a); }

// =======================================
// IO helper functions
inline obj_res io_mk_world() { return lean_io_mk_world(); }
inline bool io_result_is_ok(b_obj_arg r) { return lean_io_result_is_ok(r); }
inline bool io_result_is_error(b_obj_arg r) { return lean_io_result_is_error(r); }
inline b_obj_res io_result_get_value(b_obj_arg r) { return lean_io_result_get_value(r); }
inline b_obj_res io_result_get_error(b_obj_arg r) { return lean_io_result_get_error(r); }
inline void io_result_show_error(b_obj_arg r) { return lean_io_result_show_error(r); }
inline void io_mark_end_initialization() { return lean_io_mark_end_initialization(); }
void io_eprintln(obj_arg s);

// =======================================
// ST ref primitives
inline obj_res st_mk_ref(obj_arg v, obj_arg w) { return lean_st_mk_ref(v, w); }
inline obj_res st_ref_get(b_obj_arg r, obj_arg w) { return lean_st_ref_get(r, w); }
inline obj_res st_ref_set(b_obj_arg r, obj_arg v, obj_arg w) { return lean_st_ref_set(r, v, w); }
inline obj_res st_ref_reset(b_obj_arg r, obj_arg w) { return lean_st_ref_reset(r, w); }
inline obj_res st_ref_swap(b_obj_arg r, obj_arg v, obj_arg w) { return lean_st_ref_swap(r, v, w); }

// =======================================
// Module initialization/finalization
void initialize_object();
void finalize_object();
}
