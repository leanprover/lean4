/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "runtime/io.h"
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

obj_res io_prim_put_str(b_obj_arg s, obj_arg /* w */) {
    // TODO(Leo): this is a temporary hack for testing
    std::cout << string_to_std(s);
    return mk_ioe_result(box(0));
}

obj_res io_prim_get_line(obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.mk (s : string) (m : mode) (bin : bool := ff) : eio handle */
obj_res io_prim_handle_mk(b_obj_arg /* s */, uint8 /* mode */, uint8 /* bin */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.is_eof : handle → eio bool */
obj_res io_prim_handle_is_eof(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.flush : handle → eio bool */
obj_res io_prim_handle_flush(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.close : handle → eio unit */
obj_res io_prim_handle_close(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

/* handle.get_line : handle → eio unit */
obj_res io_prim_handle_get_line(b_obj_arg /* h */, obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}
}
