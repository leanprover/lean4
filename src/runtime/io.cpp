/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <chrono>
#include <iomanip>
#include "runtime/io.h"
#include "runtime/allocprof.h"
namespace lean {
static obj_res const REAL_WORLD = box(0);

obj_res mk_io_result(obj_arg r) {
    object * res = alloc_cnstr(0, 2, 0);
    cnstr_set(res, 0, r);
    cnstr_set(res, 1, REAL_WORLD);
    return res;
}

/* `(r : α) → (except ε α × real_world)` */
obj_res mk_ioe_result(obj_arg r) {
    object * res = alloc_cnstr(1, 1, 0);
    cnstr_set(res, 0, r);
    return mk_io_result(res);
}

extern "C" obj_res lean_io_prim_put_str(b_obj_arg s, obj_arg /* w */) {
    // TODO(Leo): this is a temporary hack for testing
    std::cout << string_to_std(s);
    return mk_ioe_result(box(0));
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

/* constant unsafe_io {α : Type} [inhabited α] (fn : io α) : α */
extern "C" obj_res lean_io_unsafe(obj_arg, obj_arg, obj_arg fn) {
    object * r = apply_1(fn, REAL_WORLD);
    object * a = cnstr_get(r, 0);
    inc(a); dec(r);
    return a;
}

/* timeit {α : Type} (msg : @& string) (fn : io α) : io α */
extern "C" obj_res lean_io_timeit(obj_arg, b_obj_arg msg, obj_arg fn, obj_arg w) {
    auto start = std::chrono::steady_clock::now();
    object * r = apply_1(fn, w);
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
extern "C" obj_res lean_io_allocprof(obj_arg, b_obj_arg msg, obj_arg fn, obj_arg w) {
    std::ostream & out = std::cerr; // TODO(Leo): replace?
    allocprof prof(out, string_cstr(msg));
    return apply_1(fn, w);
}
}
