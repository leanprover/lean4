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
    lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)ptr;

    if(tcp_socket->m_promise_accept != NULL) {
        lean_dec_ref(tcp_socket->m_promise_accept);
    }

    if(tcp_socket->m_promise_read != NULL) {
        lean_dec_ref(tcp_socket->m_promise_read);
    }

    if(tcp_socket->m_byte_array != NULL) {
        lean_dec_ref(tcp_socket->m_byte_array);
    }

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*)tcp_socket->m_uv_tcp, [](uv_handle_t* handle) {
        free(handle);
    });

    event_loop_unlock(&global_ev);

    free(tcp_socket);
}

void initialize_libuv_tcp_socket() {
    g_uv_tcp_socket_external_class = lean_register_external_class(lean_uv_tcp_socket_finalizer, [](void* obj, lean_object* f) {
        lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)obj;

        if (tcp_socket->m_promise_accept != NULL) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_promise_accept);
        }

        if (tcp_socket->m_promise_read != NULL) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_promise_read);
        }

        if (tcp_socket->m_byte_array != NULL) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_byte_array);
        }
    });
}

// TCP Socket Operations
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new() {
    lean_uv_tcp_socket_object * tcp_socket = (lean_uv_tcp_socket_object*)malloc(sizeof(lean_uv_tcp_socket_object));

    tcp_socket->m_promise_accept = NULL;
    tcp_socket->m_promise_read = NULL;
    tcp_socket->m_byte_array = NULL;

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

    // Stores the higher level struct in the data field of `uv_tcp_t` like with timers.
    tcp_socket->m_uv_tcp->data = obj;

    return lean_io_result_mk_ok(obj);
}

lean_object* create_promise() {
    lean_object * prom_res = lean_io_promise_new(lean_io_mk_world());
    lean_object * promise = lean_ctor_get(prom_res, 0);
    lean_inc(promise);
    lean_dec(prom_res);
    return promise;
}

void resolve_promise(lean_object* promise, int status) {
    lean_object * res;

    if (status == 0) {
        res = alloc_cnstr(1, 1, 0);
        cnstr_set(res, 0, lean_box(0));
    } else {
        res = mk_except_error_string(uv_strerror(status));
    }

    lean_object * result = lean_io_promise_resolve(res, promise, lean_io_mk_world());
    lean_dec(result);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr_in addr_ptr;
    lean_socket_addr_to_sockaddr(addr, &addr_ptr);

    lean_object * promise = create_promise();

    uv_connect_t * uv_connect = (uv_connect_t*)malloc(sizeof(uv_connect_t));
    uv_connect->data = promise;

    event_loop_lock(&global_ev);

    int result = uv_tcp_connect(uv_connect, tcp_socket->m_uv_tcp, (const struct sockaddr *)&addr_ptr, [](uv_connect_t* req, int status) {
        lean_object * promise = (lean_object *) req->data;
        resolve_promise(promise, status);
        free(req);
    });

    if (result < 0) {
        free(uv_connect);
        return lean_io_result_mk_error(mk_except_error_string("Connection failed"));
    }

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(promise);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, b_obj_arg data) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    size_t data_len = lean_sarray_size(data);
    char * data_str = (char *)lean_sarray_cptr(data);
    uv_buf_t buf = uv_buf_init(data_str, data_len);

    lean_object * promise = create_promise();

    event_loop_lock(&global_ev);

    uv_write_t * write_uv = (uv_write_t*)malloc(sizeof(uv_write_t));
    write_uv->data = promise;

    int result = uv_write(write_uv, (uv_stream_t*)tcp_socket->m_uv_tcp, &buf, 1, [](uv_write_t * req, int status) {
        lean_object * promise = (lean_object *) req->data;
        resolve_promise(promise, status);
        free(req);
    });

    if (result < 0) {
        free(write_uv);
        return lean_io_result_mk_error(mk_except_error_string("Write failed"));
    }

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(promise);
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
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    int result = uv_tcp_nodelay(tcp_socket->m_uv_tcp, 1);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("Failed to set TCP_NODELAY")));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    int result = uv_tcp_keepalive(tcp_socket->m_uv_tcp, enable, delay);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, mk_string("Failed to set TCP_KEEPALIVE")));
    }

    return lean_io_result_mk_ok(lean_box(0));
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
