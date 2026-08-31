/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"
#include "runtime/uv/net_addr.h"
#include "runtime/object_ref.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

static lean_external_class* g_uv_tcp_socket_external_class = NULL;
void initialize_libuv_tcp_socket();

#ifndef LEAN_EMSCRIPTEN

// Structure for managing a single TCP socket object, including promise handling,
// connection state, and read/write buffers.
typedef struct {
    uv_tcp_t*      m_uv_tcp;           // LibUV TCP handle.
    lean_object*   m_promise_accept;   // The associated promise for asynchronous results for accepting new sockets.
    lean_object*   m_promise_read;     // The associated promise for asynchronous results for reading from the socket.
    lean_object*   m_promise_shutdown; // The associated promise for asynchronous results to shutdown the socket.
    lean_object*   m_client;           // Cached client that is going to be used in the next accept.
    lean_object*   m_byte_array;       //  Buffer for storing data received via `recv_start`.
} lean_uv_tcp_socket_object;

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
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket);

// =======================================
// TCP Socket Utility Functions

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay);

}
