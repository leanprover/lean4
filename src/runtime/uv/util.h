/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/object.h"

namespace lean {

// The loop thread resolves and releases the promise, so its refcount has to be atomic.
inline lean_obj_res mk_mt_promise() {
    lean_object * promise = lean_promise_new();
    mark_mt(promise);
    return promise;
}

// Resolves `promise` with `.ok ()` if `status` is zero, and with the decoded libuv error otherwise.
inline void resolve_with_code(int status, b_obj_arg promise) {
    obj_arg res = status == 0
        ? mk_except_ok(lean_box(0))
        : mk_except_err(lean_decode_uv_error(status, nullptr));

    lean_promise_resolve(res, promise);
}

}
