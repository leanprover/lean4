/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/debug.h"
#include "runtime/object.h"
#include <array>
#include <utility>
#include <vector>
#include <uv.h>

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

// An operation in flight on a handle: its promise and an optional payload. The event loop holds a
// reference to the handle exactly while `m_promise` is set.
struct uv_pending_op {
    owned_ref m_promise;
    owned_ref m_payload;

    bool pending() const { return m_promise.get() != nullptr; }
};

// The `foreach` of a handle's external class: applies `f` to every Lean object `T::lean_refs()` lists.
template<class T>
void uv_foreach_refs(void * obj, b_obj_arg f) {
    for (owned_ref * ref : static_cast<T*>(obj)->lean_refs()) {
        if (lean_object * o = ref->get()) {
            lean_inc(f);
            lean_inc(o);
            lean_dec(lean_apply_1(f, o));
        }
    }
}

// The loop thread resolves and releases the promise, so its refcount has to be atomic.
inline lean_obj_res mk_mt_promise() {
    lean_object * promise = lean_promise_new();
    mark_mt(promise);
    return promise;
}

// Resolves `promise` with `.ok ()` if `status` is zero, and with the decoded libuv error otherwise.
// A null `promise` was taken by finalization, which settled it already.
inline void resolve_with_code(int status, b_obj_arg promise) {
    if (promise == nullptr) {
        return;
    }
    obj_arg res = status == 0
        ? mk_except_ok(lean_box(0))
        : mk_except_err(lean_decode_uv_error(status, nullptr));

    lean_promise_resolve(res, promise);
}

// A request whose callback settles `promise`. While libuv owns it, it is linked into `g_uv_requests`
// under the loop lock, so that finalization can take and settle the promise without its callback,
// which then finds `promise` empty. Finalization leaves it linked, since libuv still owns it: the
// list keeps it reachable, and a restarted loop runs the callback, which unlinks and frees it.
struct uv_tracked_req {
    uv_tracked_req * m_prev = nullptr;
    uv_tracked_req * m_next = nullptr;
    uv_req_t *       m_uv = nullptr;
    owned_ref        promise;

    void link(uv_req_t * uv);
    // Does nothing if the request is not linked.
    void unlink();
};

// Every request libuv owns. Guarded by the loop lock.
inline uv_tracked_req * g_uv_requests = nullptr;

inline void uv_tracked_req::link(uv_req_t * uv) {
    m_uv = uv;
    m_prev = nullptr;
    m_next = g_uv_requests;
    if (g_uv_requests != nullptr) {
        g_uv_requests->m_prev = this;
    }
    g_uv_requests = this;
}

inline void uv_tracked_req::unlink() {
    if (m_prev != nullptr) {
        m_prev->m_next = m_next;
    } else if (g_uv_requests == this) {
        g_uv_requests = m_next;
    }
    if (m_next != nullptr) {
        m_next->m_prev = m_prev;
    }
    m_prev = nullptr;
    m_next = nullptr;
}

// What finalization takes from pending operations under the loop lock: their promises, settled with
// `UV_ECANCELED` once the lock is released, and the loop's references to their handles, released
// after that.
struct uv_finalize_batch {
    std::vector<owned_ref> m_promises;
    std::vector<owned_ref> m_refs;
    // Before the flush: leave operations that send data, such as a TCP shutdown, to finish.
    bool m_keep_flushable = false;
    // After the flush: sockets whose writes, connects or shutdowns are cancelled. Closing them makes
    // libuv cancel those requests itself, so that their callbacks free them.
    std::vector<uv_handle_t *> m_close;
};

// An array libuv allocated together with its length, released with `Free(data, count)`.
template<class T, void (*Free)(T*, int)>
class uv_owned_array {
    T * m_data;
    int m_count;
public:
    uv_owned_array(T * data, int count) : m_data(data), m_count(count) {}
    ~uv_owned_array() { Free(m_data, m_count); }
    uv_owned_array(uv_owned_array const &) = delete;
    uv_owned_array & operator=(uv_owned_array const &) = delete;
    T * begin() const { return m_data; }
    T * end() const { return m_data + m_count; }
};

}
