/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/debug.h"
#include "runtime/object.h"
#include <utility>

namespace lean {

// An owned reference to a Lean object, or `nullptr`. Move-only, so every transfer is explicit.
class owned_ref {
    lean_object * m_obj = nullptr;
public:
    owned_ref() = default;

    explicit owned_ref(obj_arg o) : m_obj(o) {}

    owned_ref(owned_ref && o) noexcept : m_obj(std::exchange(o.m_obj, nullptr)) {}

    owned_ref & operator=(owned_ref && o) noexcept {
        lean_assert(m_obj == nullptr);
        m_obj = std::exchange(o.m_obj, nullptr);
        return *this;
    }

    owned_ref(owned_ref const &) = delete;

    owned_ref & operator=(owned_ref const &) = delete;

    ~owned_ref() {
        if (m_obj != nullptr) lean_dec(m_obj);
    }

    static owned_ref retain(b_obj_arg o) {
        lean_inc(o);
        return owned_ref(o);
    }

    lean_object * get() const {
        return m_obj;
    }

    lean_object * release() {
        return std::exchange(m_obj, nullptr);
    }
};

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
