/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <chrono>
#include <iomanip>
#include "runtime/object.h"
#include "runtime/allocprof.h"
namespace lean {
static obj_res const REAL_WORLD = box(0);

void io_result_show_error(b_obj_arg r) {
    std::cerr << "uncaught exception: " << string_cstr(io_result_get_error(r)) << std::endl;
}

obj_res set_io_result(obj_arg r, obj_arg a) {
    if (is_exclusive(r)) {
        cnstr_set(r, 0, a);
        return r;
    } else {
        dec_ref(r);
        object * new_r = alloc_cnstr(0, 2, 0);
        cnstr_set(new_r, 0, a);
        cnstr_set(new_r, 1, REAL_WORLD);
        return new_r;
    }
}

obj_res set_io_error(obj_arg r, obj_arg e) {
    if (is_exclusive(r)) {
        cnstr_set_tag(r, 1);
        cnstr_set(r, 0, e);
        return r;
    } else {
        dec_ref(r);
        object * new_r = alloc_cnstr(1, 2, 0);
        cnstr_set(new_r, 0, e);
        cnstr_set(new_r, 1, REAL_WORLD);
        return new_r;
    }
}

object * mk_io_user_error(object * str) {
    // TODO(Leo): fix after we expand IO.Error
    return str;
}

obj_res set_io_error(obj_arg r, char const * msg) {
    return set_io_error(r, mk_io_user_error(mk_string(msg)));
}

obj_res set_io_error(obj_arg r, std::string const & msg) {
    return set_io_error(r, mk_io_user_error(mk_string(msg)));
}

static obj_res option_of_io_result(obj_arg r) {
    if (io_result_is_ok(r)) {
        object * o = alloc_cnstr(1, 1, 0);
        cnstr_set(o, 0, io_result_get_value(r));
        dec(r);
        return o;
    } else {
        dec(r);
        return box(0);
    }
}

static bool g_initializing = true;
void io_mark_end_initialization() {
    g_initializing = false;
}

extern "C" obj_res lean_io_initializing(obj_arg r) {
    return set_io_result(r, box(g_initializing));
}

extern "C" obj_res lean_io_prim_put_str(b_obj_arg s, obj_arg r) {
    std::cout << string_to_std(s); // TODO(Leo): use out handle
    return set_io_result(r, box(0));
}

extern "C" obj_res lean_io_prim_get_line(obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.mk (s : string) (m : mode) (bin : bool := ff) : eio handle */
extern "C" obj_res lean_io_prim_handle_mk(b_obj_arg /* s */, uint8 /* mode */, uint8 /* bin */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.is_eof : handle → eio bool */
extern "C" obj_res lean_io_prim_handle_is_eof(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.flush : handle → eio bool */
extern "C" obj_res lean_io_prim_handle_flush(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.close : handle → eio unit */
extern "C" obj_res lean_io_prim_handle_close(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.get_line : handle → eio unit */
extern "C" obj_res lean_io_prim_handle_get_line(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* timeit {α : Type} (msg : @& string) (fn : io α) : io α */
extern "C" obj_res lean_io_timeit(obj_arg, b_obj_arg msg, obj_arg fn, obj_arg r) {
    auto start = std::chrono::steady_clock::now();
    r = apply_1(fn, r);
    auto end   = std::chrono::steady_clock::now();
    auto diff  = std::chrono::duration<double>(end - start);
    std::ostream & out = std::cerr; // TODO(Leo): replace?
    out << std::setprecision(3);
    if (diff < std::chrono::duration<double>(1)) {
        out << string_cstr(msg) << " " << std::chrono::duration<double, std::milli>(diff).count() << "ms\n";
    } else {
        out << string_cstr(msg) << " " << diff.count() << "s\n";
    }
    return r;
}

/* allocprof {α : Type} (msg : string) (fn : io α) : io α */
extern "C" obj_res lean_io_allocprof(obj_arg, b_obj_arg msg, obj_arg fn, obj_arg r) {
    std::ostream & out = std::cerr; // TODO(Leo): replace?
    allocprof prof(out, string_cstr(msg));
    return apply_1(fn, r);
}

// =======================================
// IO ref primitives
obj_res io_mk_ref(obj_arg a, obj_arg r) {
    object * ref = new (alloc_heap_object(sizeof(ref_object))) ref_object(a);
    return set_io_result(r, ref);
}

static object * g_io_error_nullptr_read = nullptr;

static inline atomic<object*> * mt_ref_val_addr(object * o) {
    return reinterpret_cast<atomic<object*> *>(&(to_ref(o)->m_value));
}

/*
  Important: we have added support for initializing global constants
  at program startup. This feature is particularly useful for
  initializing `IO.Ref` values. Any `IO.Ref` value created during
  initialization will be marked as persistent. Thus, to make `IO.Ref`
  API thread-safe, we must treat persistent `IO.Ref` objects created
  during initialization as a multi-threaded object. Then, whenever we store
  a value `val` into a global `IO.Ref`, we have to mark `va`l as a multi-threaded
  object as we do for multi-threaded `IO.Ref`s. It makes sense since
  the global `IO.Ref` may be used to communicate data between threads.
*/
static inline bool ref_maybe_mt(b_obj_arg ref) {
    return
        ref->m_mem_kind == static_cast<unsigned>(object_memory_kind::MTHeap) ||
        ref->m_mem_kind == static_cast<unsigned>(object_memory_kind::Persistent);
}

obj_res io_ref_get(b_obj_arg ref, obj_arg r) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * val = val_addr->exchange(nullptr);
        if (val == nullptr)
            return set_io_error(r, g_io_error_nullptr_read);
        inc(val);
        object * tmp = val_addr->exchange(val);
        if (tmp != nullptr) {
            /* this may happen if another thread wrote `ref` */
            dec(tmp);
        }
        return set_io_result(r, val);
    } else {
        object * val = to_ref(ref)->m_value;
        if (val == nullptr)
            return set_io_error(r, g_io_error_nullptr_read);
        inc(val);
        return set_io_result(r, val);
    }
}

static_assert(sizeof(atomic<unsigned short>) == sizeof(unsigned short), "`atomic<unsigned short>` and `unsigned short` must have the same size"); // NOLINT

obj_res io_ref_reset(b_obj_arg ref, obj_arg r) {
    if (ref_maybe_mt(ref)) {
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(nullptr);
        if (old_a != nullptr)
            dec(old_a);
        return r;
    } else {
        if (to_ref(ref)->m_value != nullptr)
            dec(to_ref(ref)->m_value);
        to_ref(ref)->m_value = nullptr;
        return r;
    }
}

obj_res io_ref_set(b_obj_arg ref, obj_arg a, obj_arg r) {
    if (ref_maybe_mt(ref)) {
        /* We must mark `a` as multi-threaded if `ref` is marked as multi-threaded.
           Reason: our runtime relies on the fact that a single-threaded object
           cannot be reached from a multi-thread object. */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(a);
        if (old_a != nullptr)
            dec(old_a);
        return r;
    } else {
        if (to_ref(ref)->m_value != nullptr)
            dec(to_ref(ref)->m_value);
        to_ref(ref)->m_value = a;
        return r;
    }
}

obj_res io_ref_swap(b_obj_arg ref, obj_arg a, obj_arg r) {
    if (ref_maybe_mt(ref)) {
        /* See io_ref_write */
        mark_mt(a);
        atomic<object *> * val_addr = mt_ref_val_addr(ref);
        object * old_a = val_addr->exchange(a);
        if (old_a == nullptr)
            return set_io_error(r, g_io_error_nullptr_read);
        return set_io_result(r, old_a);
    } else {
        object * old_a = to_ref(ref)->m_value;
        if (old_a == nullptr)
            return set_io_error(r, g_io_error_nullptr_read);
        to_ref(ref)->m_value = a;
        return set_io_result(r, old_a);
    }
}

void initialize_io() {
    g_io_error_nullptr_read = mk_string("null reference read");
    mark_persistent(g_io_error_nullptr_read);
}

void finalize_io() {
}
}
