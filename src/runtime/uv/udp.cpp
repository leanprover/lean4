/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/udp.h"
#include "runtime/uv/buffer.h"
#include "runtime/uv/util.h"
#include <cstring>
#include <memory>
#include <new>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// A send request. The callback deletes it, and so does a failed submit. It keeps `data` alive
// because libuv sends from its bytes.
struct udp_send_req_t {
    uv_udp_send_t uv;
    owned_ref     data;
    owned_ref     socket;
    owned_ref     promise;
};

static void udp_socket_finalizer(void* ptr) {
    lean_uv_udp_socket_object* udp_socket = (lean_uv_udp_socket_object*)ptr;

    lean_always_assert(udp_socket->m_promise_read == nullptr);
    lean_always_assert(udp_socket->m_byte_array == nullptr);

    event_loop_guard guard;

    // The Lean object is being freed, so the close callback gets the struct instead. No callback
    // reads `data` as the Lean object after `uv_close`.
    udp_socket->m_uv_udp.data = udp_socket;

    uv_close((uv_handle_t*)&udp_socket->m_uv_udp, [](uv_handle_t* handle) {
        free(handle->data);
    });
}

void initialize_libuv_udp_socket() {
    g_uv_udp_socket_external_class = lean_register_external_class(udp_socket_finalizer, [](void* obj, lean_object* f) {
        lean_uv_udp_socket_object* udp_socket = (lean_uv_udp_socket_object*)obj;

        if (udp_socket->m_promise_read != nullptr) {
            lean_inc(f);
            lean_inc(udp_socket->m_promise_read);
            lean_dec(lean_apply_1(f, udp_socket->m_promise_read));
        }

        if (udp_socket->m_byte_array != nullptr) {
            lean_inc(f);
            lean_inc(udp_socket->m_byte_array);
            lean_dec(lean_apply_1(f, udp_socket->m_byte_array));
        }
    });
}

// =======================================
// UDP Socket Operations

/* Std.Internal.UV.UDP.Socket.new : IO Socket */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_new() {
    lean_uv_udp_socket_object* udp_socket = (lean_uv_udp_socket_object*)malloc(sizeof(lean_uv_udp_socket_object));
    if (udp_socket == nullptr) {
        return io_result_mk_enomem();
    }

    udp_socket->m_promise_read = nullptr;
    udp_socket->m_byte_array = nullptr;

    int result;

    {
        event_loop_guard guard;
        result = uv_udp_init(global_ev.m_loop, &udp_socket->m_uv_udp);
    }

    if (result != 0) {
        free(udp_socket);

        return io_result_mk_uv_error(result);
    }

    lean_object* obj = lean_uv_udp_socket_new(udp_socket);
    lean_mark_mt(obj);

    udp_socket->m_uv_udp.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.UDP.Socket.bind (socket : @& Socket) (addr : @& SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_bind(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_udp_socket_object* udp_socket = lean_to_uv_udp_socket(socket);

    sockaddr_storage addr_ptr;
    lean_socket_address_to_sockaddr_storage(addr, &addr_ptr);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_bind(&udp_socket->m_uv_udp, (sockaddr*)&addr_ptr, UV_UDP_REUSEADDR);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.connect (socket : @& Socket) (addr : @& SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_udp_socket_object* udp_socket = lean_to_uv_udp_socket(socket);

    sockaddr_storage addr_ptr;
    lean_socket_address_to_sockaddr_storage(addr, &addr_ptr);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_connect(&udp_socket->m_uv_udp, (sockaddr*)&addr_ptr);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.send (socket : @& Socket) (data : Array ByteArray) (addr : @& Option SocketAddress) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_send(b_obj_arg socket, obj_arg data_array, b_obj_arg opt_addr) {
    lean_uv_udp_socket_object* udp_socket = lean_to_uv_udp_socket(socket);
    owned_ref data(data_array);

    if (lean_array_size(data_array) == 0) {
        lean_object * promise = mk_mt_promise();
        resolve_with_code(0, promise);

        return lean_io_result_mk_ok(promise);
    }

    uv_send_bufs bufs;
    if (lean_object * error = bufs.init(data_array)) {
        return error;
    }

    udp_send_req_t * req = new (std::nothrow) udp_send_req_t;
    if (req == nullptr) {
        return io_result_mk_enomem();
    }

    // The loop thread releases `data_array`, which recursively releases the `ByteArray`s the caller
    // may still hold references to, so their refcounts have to be atomic.
    mark_mt(data_array);

    req->uv.data = req;
    req->data = std::move(data);
    req->socket = owned_ref::retain(socket);
    req->promise = owned_ref(mk_mt_promise());
    owned_ref promise = owned_ref::retain(req->promise.get());

    // libuv copies the destination address too.
    sockaddr_storage addr_storage;
    sockaddr* addr_ptr = nullptr;

    if (lean_obj_tag(opt_addr) == 1) {
        lean_socket_address_to_sockaddr_storage(lean_ctor_get(opt_addr, 0), &addr_storage);
        addr_ptr = (sockaddr*)&addr_storage;
    }

    auto on_send = [](uv_udp_send_t * uv, int status) {
        std::unique_ptr<udp_send_req_t> req(static_cast<udp_send_req_t*>(uv->data));
        resolve_with_code(status, req->promise.get());
    };

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_send(&req->uv, &udp_socket->m_uv_udp, bufs.data(), bufs.count(), addr_ptr, on_send);
    }

    if (result < 0) {
        delete req;
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise.release());
}

/* Std.Internal.UV.UDP.Socket.recv (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (ByteArray × SocketAddress))) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_recv(b_obj_arg socket, uint64_t buffer_size) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    auto alloc_cb = [](uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf) {
        lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket((lean_object*)handle->data);

        buf->base = (char*)lean_sarray_cptr(udp_socket->m_byte_array);
        buf->len = lean_sarray_capacity(udp_socket->m_byte_array);
    };

    auto recv_cb = [](uv_udp_t *handle, ssize_t nread, const uv_buf_t *buf, const struct sockaddr *addr, unsigned flags) {
        if (nread == 0 && addr == NULL) return;

        uv_udp_recv_stop(handle);

        lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket((lean_object*)handle->data);
        lean_object* promise = udp_socket->m_promise_read;
        lean_object* byte_array = udp_socket->m_byte_array;

        udp_socket->m_promise_read = nullptr;
        udp_socket->m_byte_array = nullptr;

        if (nread >= 0 && (flags & UV_UDP_PARTIAL) != 0) {
            lean_dec(byte_array);
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(UV_EMSGSIZE, nullptr)), promise);
        } else if (nread >= 0) {
            byte_array = fit_read_buffer(byte_array, nread);

            lean_object* addr_obj;

            if (addr != NULL) {
                addr_obj = lean::mk_option_some(lean_sockaddr_to_socketaddress(addr));
            } else {
                addr_obj = lean::mk_option_none();
            }

            lean_object* prod = lean_alloc_ctor(1, 2, 0);
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
    };

    lean_object* byte_array;
    lean_object* promise;
    int result;
    {
        // Locking earlier to avoid parallelism issues with m_promise_read.
        event_loop_guard guard;

        if (udp_socket->m_promise_read != nullptr) {
            return io_result_mk_uv_error(UV_EALREADY);
        }

        if (lean_object * size_error = recv_size_error(buffer_size)) {
            return size_error;
        }

        byte_array = lean_alloc_sarray(1, 0, buffer_size);
        promise = mk_mt_promise();

        udp_socket->m_byte_array = byte_array;
        udp_socket->m_promise_read = promise;

        // The event loop owns the socket.
        lean_inc(promise);
        lean_inc(socket);

        result = uv_udp_recv_start(&udp_socket->m_uv_udp, alloc_cb, recv_cb);

        if (result < 0) {
            udp_socket->m_byte_array = nullptr;
            udp_socket->m_promise_read = nullptr;
        }
    }

    if (result < 0) {
        lean_dec(byte_array);
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.UDP.Socket.waitReadable (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_wait_readable(b_obj_arg socket) {
    lean_uv_udp_socket_object* udp_socket = lean_to_uv_udp_socket(socket);

    auto alloc_cb = [](uv_handle_t* handle, size_t suggested_size, uv_buf_t *buf) {
        // According to libuv documentation if we do this we do not lose data and a UV_ENOBUFS will
        // be triggered in the read cb.
        buf->base = NULL;
        buf->len = 0;
    };

    auto recv_cb = [](uv_udp_t* handle, ssize_t nread, const uv_buf_t *buf, const struct sockaddr *addr, unsigned flags) {
        // `nread == 0` without an address is libuv's equivalent of `EAGAIN`: the socket is not
        // actually readable, so keep waiting rather than resolving the promise.
        if (nread == 0 && addr == NULL) return;

        uv_udp_recv_stop(handle);

        lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket((lean_object*)handle->data);
        lean_object* promise = udp_socket->m_promise_read;

        udp_socket->m_promise_read = nullptr;

        if (nread < 0 && nread != UV_ENOBUFS) {
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(nread, nullptr)), promise);
        } else {
            // `UV_ENOBUFS` is the documented answer to the zero-length `alloc_cb` above. A
            // non-negative `nread` is an empty datagram, which equally means the socket woke up
            // readable, so report that rather than aborting the process.
            lean_promise_resolve(mk_except_ok(lean_box(0)), promise);
        }

        lean_dec(promise);

        // The event loop does not own the object anymore.
        lean_dec((lean_object*)handle->data);
    };

    lean_object* promise;
    int result;
    {
        // Locking earlier to avoid parallelism issues with m_promise_read.
        event_loop_guard guard;

        if (udp_socket->m_promise_read != nullptr) {
            return io_result_mk_uv_error(UV_EALREADY);
        }

        promise = mk_mt_promise();

        udp_socket->m_promise_read = promise;

        // The event loop owns the socket.
        lean_inc(promise);
        lean_inc(socket);

        result = uv_udp_recv_start(&udp_socket->m_uv_udp, alloc_cb, recv_cb);

        if (result < 0) {
            udp_socket->m_promise_read = nullptr;
        }
    }

    if (result < 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.UDP.Socket.cancelRecv (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_cancel_recv(b_obj_arg socket) {
    lean_uv_udp_socket_object* udp_socket = lean_to_uv_udp_socket(socket);

    lean_object* promise = nullptr;
    lean_object* byte_array = nullptr;
    {
        event_loop_guard guard;

        if (udp_socket->m_promise_read != nullptr) {
            uv_udp_recv_stop(&udp_socket->m_uv_udp);

            promise = udp_socket->m_promise_read;
            byte_array = udp_socket->m_byte_array;

            udp_socket->m_promise_read = nullptr;
            udp_socket->m_byte_array = nullptr;
        }
    }

    if (promise != nullptr) {
        lean_dec(promise);

        if (byte_array != nullptr) {
            lean_dec(byte_array);
        }

        lean_dec(socket);
    }

    return lean_io_result_mk_ok(lean_box(0));
}


// =======================================
// UDP Socket Utility Functions

/* Std.Internal.UV.UDP.Socket.getPeerName (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getpeername(b_obj_arg socket) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    struct sockaddr_storage addr_storage;
    int addr_len = sizeof(addr_storage);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_getpeername(&udp_socket->m_uv_udp, (struct sockaddr*)&addr_storage, &addr_len);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    lean_object *lean_addr = lean_sockaddr_to_socketaddress((struct sockaddr*)&addr_storage);

    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.UDP.Socket.getSockName (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_getsockname(b_obj_arg socket) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    struct sockaddr_storage addr_storage;
    int addr_len = sizeof(addr_storage);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_getsockname(&udp_socket->m_uv_udp, (struct sockaddr*)&addr_storage, &addr_len);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    lean_object *lean_addr = lean_sockaddr_to_socketaddress((struct sockaddr*)&addr_storage);
    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.UDP.Socket.setBroadcast (socket : @& Socket) (on : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_broadcast(b_obj_arg socket, uint8_t enable) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_set_broadcast(&udp_socket->m_uv_udp, enable);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMulticastLoop (socket : @& Socket) (on : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_loop(b_obj_arg socket, uint8_t enable) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_set_multicast_loop(&udp_socket->m_uv_udp, enable);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMulticastTTL (socket : @& Socket) (ttl : UInt32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_set_multicast_ttl(&udp_socket->m_uv_udp, ttl);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMembership (socket : @& Socket) (multicastAddr : @& IpAddr) (interfaceAddr : @& Option IpAddr) (membership : UInt8) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_membership(b_obj_arg socket, b_obj_arg multicast_addr, b_obj_arg interface_addr, uint8_t membership) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    char multicast_addr_str[INET6_ADDRSTRLEN];
    lean_ip_addr_ntop(multicast_addr, multicast_addr_str, sizeof(multicast_addr_str));

    bool is_interface_null = is_scalar(interface_addr);
    char interface_addr_str[INET6_ADDRSTRLEN];

    if (!is_interface_null) {
        lean_object* interface_addr_obj = lean_ctor_get(interface_addr, 0);
        lean_ip_addr_ntop(interface_addr_obj, interface_addr_str, sizeof(interface_addr_str));
    }

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_set_membership(&udp_socket->m_uv_udp, multicast_addr_str, is_interface_null ? nullptr : interface_addr_str, (uv_membership)membership);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setMulticastInterface (socket : @& Socket) (interfaceAddr : @& IPAddr) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_interface(b_obj_arg socket, b_obj_arg interface_addr) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    char interface_addr_str[INET6_ADDRSTRLEN];
    lean_ip_addr_ntop(interface_addr, interface_addr_str, sizeof(interface_addr_str));

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_set_multicast_interface(&udp_socket->m_uv_udp, interface_addr_str);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.UDP.Socket.setTTL (socket : @& Socket) (ttl : UInt32) : IO Unit  */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_uv_udp_socket_object *udp_socket = lean_to_uv_udp_socket(socket);

    int result;
    {
        event_loop_guard guard;
        result = uv_udp_set_ttl(&udp_socket->m_uv_udp, ttl);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

#else

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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_send(b_obj_arg socket, obj_arg data, b_obj_arg opt_addr) {
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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_broadcast(b_obj_arg socket, uint8_t enable) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_loop(b_obj_arg socket, uint8_t enable) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_multicast_ttl(b_obj_arg socket, uint32_t ttl) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_udp_set_membership(b_obj_arg socket, b_obj_arg multicast_addr, b_obj_arg interface_addr, uint8_t membership) {
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
}
