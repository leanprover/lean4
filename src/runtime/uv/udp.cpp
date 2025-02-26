/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/udp.h"
#include <cstring>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// =======================================
// Utility functions

// Stores all the things needed to send data to a UDP socket.
typedef struct {
    lean_object *promise;
    lean_object *data;
    lean_object *socket;
} udp_send_data;

void lean_uv_udp_socket_finalizer(void* ptr) {
    lean_uv_udp_socket_object* udp_socket = (lean_uv_udp_socket_object*)ptr;

    lean_always_assert(udp_socket->m_promise_read == nullptr);
    lean_always_assert(udp_socket->m_byte_array == nullptr);

    udp_socket->m_uv_udp->data = ptr;

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*)udp_socket->m_uv_udp, [](uv_handle_t* handle) {
        lean_uv_udp_socket_object* udp_socket = (lean_uv_udp_socket_object*)handle->data;
        free(udp_socket->m_uv_udp);
        free(udp_socket);
    });

    event_loop_unlock(&global_ev);
}

void initialize_libuv_udp_socket() {
    g_uv_udp_socket_external_class = lean_register_external_class(lean_uv_udp_socket_finalizer, [](void* obj, lean_object* f) {
        lean_uv_udp_socket_object* udp_socket = (lean_uv_udp_socket_object*)obj;

        if (udp_socket->m_promise_read != nullptr) {
            lean_inc(f);
            lean_apply_1(f, udp_socket->m_promise_read);
        }

        if (udp_socket->m_byte_array != nullptr) {
            lean_inc(f);
            lean_apply_1(f, udp_socket->m_byte_array);
        }
    });
}

// =======================================
// UDP Socket Operations

/* Std.Internal.UV.UDP.Socket.new : IO Socket */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_new() {
    lean_uv_udp_socket_object * udp_socket = (lean_uv_udp_socket_object*)malloc(sizeof(lean_uv_udp_socket_object));
    udp_socket->m_promise_read = nullptr;
    udp_socket->m_byte_array = nullptr;
    udp_socket->m_buffer_size = 0;

    uv_udp_t * uv_udp = (uv_udp_t*)malloc(sizeof(uv_udp_t));

    event_loop_lock(&global_ev);
    int result = uv_udp_init(global_ev.loop, uv_udp);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(uv_udp);
        free(udp_socket);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    udp_socket->m_uv_udp = uv_udp;

    lean_object * obj = lean_uv_udp_socket_new(udp_socket);
    lean_mark_mt(obj);

    udp_socket->m_uv_udp->data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.UDP.Socket.bind (socket : @& Socket) (addr : SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_bind(b_obj_arg socket, obj_arg addr) {
    lean_uv_udp_socket_object * udp_socket = lean_to_uv_udp_socket(socket);

    sockaddr addr_ptr;
    lean_socket_address_to_sockaddr(addr, &addr_ptr);

    event_loop_lock(&global_ev);
    int result = uv_udp_bind(udp_socket->m_uv_udp, (sockaddr *)&addr_ptr, 0);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.connect (socket : @& Socket) (addr : SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_connect(b_obj_arg socket, obj_arg addr) {
    lean_uv_udp_socket_object * udp_socket = lean_to_uv_udp_socket(socket);

    sockaddr addr_ptr;
    lean_socket_address_to_sockaddr(addr, &addr_ptr);

    event_loop_lock(&global_ev);
    int result = uv_udp_connect(udp_socket->m_uv_udp, (sockaddr *)&addr_ptr);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.send (socket : @& Socket) (data : ByteArray) (addr : Option SocketAddress) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_send(b_obj_arg socket, obj_arg data, obj_arg opt_addr) {
    lean_uv_udp_socket_object * udp_socket = lean_to_uv_udp_socket(socket);

    size_t data_len = lean_sarray_size(data);
    char * data_str = (char *)lean_sarray_cptr(data);

    uv_buf_t buf = uv_buf_init(data_str, data_len);

    lean_object * promise = lean_promise_new();
    mark_mt(promise);

    uv_udp_send_t * send_uv = (uv_udp_send_t*)malloc(sizeof(uv_udp_send_t));
    udp_send_data * send_data = (udp_send_data*)malloc(sizeof(udp_send_data));

    send_data->promise = promise;
    send_data->data = data;
    send_data->socket = socket;
    send_uv->data = send_data;

    lean_inc(promise);
    lean_inc(socket);

    sockaddr* addr_ptr = nullptr;

    if (lean_obj_tag(opt_addr) == 1) {
        lean_object* addr = lean_ctor_get(opt_addr, 0);
        addr_ptr = (sockaddr*)malloc(sizeof(sockaddr));
        lean_socket_address_to_sockaddr(addr, addr_ptr);
    }

    event_loop_lock(&global_ev);

    int result = uv_udp_send(send_uv, udp_socket->m_uv_udp, &buf, 1, (sockaddr *)addr_ptr, [](uv_udp_send_t* req, int status) {
        udp_send_data * tup = (udp_send_data*) req->data;
        lean_promise_resolve_with_code(status, tup->promise);

        lean_dec(tup->socket);
        lean_dec(tup->data);

        free(req->data);
        free(req);
    });

    event_loop_unlock(&global_ev);

    if (addr_ptr != nullptr) {
        free(addr_ptr);
    }

    if (result < 0) {
        free(send_uv);
        free(send_uv->data);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.UDP.Socket.recv (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (ByteArray × SocketAddress))) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_recv(b_obj_arg socket, uint64_t buffer_size) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    if (udp_socket->m_promise_read != nullptr) {
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, nullptr));
    }

    lean_object * promise = lean_promise_new();
    mark_mt(promise);

    udp_socket->m_promise_read = promise;
    udp_socket->m_buffer_size = buffer_size;
    lean_inc(promise);

    event_loop_lock(&global_ev);

    lean_inc(socket);

    uv_udp_recv_start(udp_socket->m_uv_udp, [](uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf) {
        lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket((lean_object*)handle->data);

        udp_socket->m_byte_array = lean_alloc_sarray(1, 0, udp_socket->m_buffer_size);

        buf->base = (char*)lean_sarray_cptr(udp_socket->m_byte_array);
        buf->len = udp_socket->m_buffer_size;

    }, [](uv_udp_t *handle, ssize_t nread, const uv_buf_t *buf, const struct sockaddr *addr, unsigned flags) {
        uv_udp_recv_stop(handle);

        lean_object * addr_obj = lean_sockaddr_to_socketaddress(addr);

        lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket((lean_object*)handle->data);
        lean_object * promise = udp_socket->m_promise_read;
        lean_object * byte_array = udp_socket->m_byte_array;

        udp_socket->m_promise_read = nullptr;
        udp_socket->m_byte_array = nullptr;

        if (nread >= 0) {
            lean_sarray_set_size(byte_array, nread);

            lean_object * prod = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(prod, 0, byte_array);
            lean_ctor_set(prod, 1, addr_obj);

            lean_promise_resolve(mk_except_ok(prod), promise);
        } else if (nread < 0) {
            lean_dec(byte_array);
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(nread, nullptr)), promise);
        }

        lean_dec(promise);

        // The event loop does not own the object anymore.
        lean_dec((lean_object*)handle->data);
    });

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(promise);
}


// =======================================
// UDP Socket Utility Functions

/* Std.Internal.UV.UDP.Socket.getPeerName (socket : Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getpeername(b_obj_arg socket) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    sockaddr addr_storage;
    int addr_len = sizeof(addr_storage);

    event_loop_lock(&global_ev);
    int result = uv_udp_getpeername(udp_socket->m_uv_udp, (sockaddr*)&addr_storage, &addr_len);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object *lean_addr = lean_sockaddr_to_socketaddress(&addr_storage);

    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.UDP.Socket.getSockName (socket : Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getsockname(b_obj_arg socket) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    sockaddr addr_storage;
    int addr_len = sizeof(addr_storage);

    event_loop_lock(&global_ev);
    int result = uv_udp_getsockname(udp_socket->m_uv_udp, &addr_storage, &addr_len);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object *lean_addr = lean_sockaddr_to_socketaddress(&addr_storage);
    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.UDP.Socket.setBroadcast (socket : Socket) (on : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_broadcast(b_obj_arg socket, int32_t enable) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    event_loop_lock(&global_ev);
    int result = uv_udp_set_broadcast(udp_socket->m_uv_udp, enable);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMulticastLoop (socket : Socket) (on : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_loop(b_obj_arg socket, int32_t enable) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    event_loop_lock(&global_ev);
    int result = uv_udp_set_multicast_loop(udp_socket->m_uv_udp, enable);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMulticastTTL (socket : Socket) (ttl : UInt32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    event_loop_lock(&global_ev);
    int result = uv_udp_set_multicast_ttl(udp_socket->m_uv_udp, ttl);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMembership (socket : @& Socket) (multicast_addr interface_addr : String) (membership : Membership) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_membership(b_obj_arg socket, obj_arg multicast_addr, obj_arg interface_addr, int32_t membership) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    const char *multicast_addr_str = lean_string_cstr(multicast_addr);
    const char *interface_addr_str = lean_string_cstr(interface_addr);

    event_loop_lock(&global_ev);
    int result = uv_udp_set_membership(udp_socket->m_uv_udp, multicast_addr_str, interface_addr_str, (uv_membership)membership);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMulticastInterface (socket : @& Socket) (interface_addr : String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_interface(b_obj_arg socket, obj_arg interface_addr) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    const char *interface_addr_str = lean_string_cstr(interface_addr);

    event_loop_lock(&global_ev);
    int result = uv_udp_set_multicast_interface(udp_socket->m_uv_udp, interface_addr_str);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setTTL (socket : @& Socket) (ttl : UInt32) : IO Unit  */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);
    event_loop_lock(&global_ev);
    int result = uv_udp_set_ttl(udp_socket->m_uv_udp, ttl);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

}

#else

// =======================================
// UDP Socket Operations
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_new() {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_bind(b_obj_arg socket, b_obj_arg addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_send(b_obj_arg socket, b_obj_arg data, b_obj_arg addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_recv(b_obj_arg socket, uint64_t buffer_size) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

// =======================================
// UDP Socket Utility Functions

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getpeername(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getsockname(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_broadcast(b_obj_arg socket, int32_t enable) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_loop(b_obj_arg socket, int32_t enable) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_membership(b_obj_arg socket, b_obj_arg multicast_addr, b_obj_arg interface_addr, int32_t membership) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_interface(b_obj_arg socket, b_obj_arg interface_addr) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
