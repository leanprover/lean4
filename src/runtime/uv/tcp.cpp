/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/tcp.h"
#include <cstring>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

void lean_uv_tcp_socket_finalizer(void* ptr) {

} 

void initialize_libuv_tcp_socket() {
    g_uv_tcp_socket_external_class = lean_register_external_class(lean_uv_tcp_socket_finalizer, [](void* obj, lean_object* f) {
        // TODO.
    });
}

// TCP Socket Operations
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new() {
    lean_uv_tcp_socket_object * tcp_socket = (lean_uv_tcp_socket_object*)malloc(sizeof(lean_uv_tcp_socket_object));
    tcp_socket->m_promise_accept = NULL;
    tcp_socket->m_promise_read = NULL;

    uv_tcp_t * uv_tcp = (uv_tcp_t*)malloc(sizeof(uv_tcp_t));

    event_loop_lock(&global_ev);
    int result = uv_tcp_init(global_ev.loop, uv_tcp);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(uv_tcp);
        free(tcp_socket);
        std::string err = std::string("failed to initialize tcp_socket: ") + uv_strerror(result);
        return io_result_mk_error(err.c_str());
    }

    tcp_socket->m_uv_tcp = uv_tcp;

    lean_object * obj = lean_uv_tcp_socket_new(tcp_socket);
    lean_mark_mt(obj);
    tcp_socket->m_uv_tcp->data = obj;

    return lean_io_result_mk_ok(obj);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, b_obj_arg data) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_bind(b_obj_arg socket, b_obj_arg addr) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_listen(b_obj_arg socket, int32_t backlog) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket) {
   
}

// TCP Socket Utility Functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket) {
   
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay) {
   
}

#else

// TCP Socket Operations
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, b_obj_arg data) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_bind(b_obj_arg socket, b_obj_arg addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_listen(b_obj_arg socket, int32_t backlog) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// TCP Socket Utility Functions
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
