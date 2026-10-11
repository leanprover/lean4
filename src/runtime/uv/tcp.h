/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/net_addr.h"
#include "runtime/uv/util.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

inline lean_external_class * g_uv_tcp_socket_external_class = nullptr;
void initialize_libuv_tcp_socket();

#ifndef LEAN_EMSCRIPTEN

// A TCP socket. Allocated with `new`; the close callback deletes it.
struct lean_uv_tcp_socket_object {
    uv_tcp_t      m_uv_tcp;                     // LibUV TCP handle.
    uv_pending_op m_read;                       // `recv?` (payload: the receive buffer) or `waitReadable` (none).
    uv_pending_op m_accept;                     // `accept` (payload: the client socket) or `waitAcceptable` (none).
    owned_ref     m_promise_shutdown;           // The pending `shutdown`.
    bool          m_shutdown_requested = false; // Whether `uv_shutdown` was already requested for this socket.
    bool          m_listening = false;          // Whether `uv_listen` succeeded on this socket.
    unsigned      m_pending_connections = 0;    // Connections the listen callback reported that nobody accepted yet.
};

// =======================================
// Tcp socket object manipulation functions.
static inline lean_object* lean_uv_tcp_socket_new(lean_uv_tcp_socket_object* s) { return lean_alloc_external(g_uv_tcp_socket_external_class, s); }
static inline lean_uv_tcp_socket_object* lean_to_uv_tcp_socket(lean_object* o) { return (lean_uv_tcp_socket_object*)(lean_get_external_data(o)); }
#endif

// =======================================
// TCP Socket Operations

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, obj_arg data_array);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket, uint64_t buffer_size);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_wait_readable(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_recv(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_bind(b_obj_arg socket, b_obj_arg addr);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_listen(b_obj_arg socket, int32_t backlog);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_accept(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_try_accept(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_wait_acceptable(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket);

// =======================================
// TCP Socket Utility Functions

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, uint8_t enable, uint32_t delay);

}
