/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/tcp.h"
#include <cstring>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

#define UV_OK 1
#define UV_ERROR 0

// Stores all the things needed to connect to a TCP socket.
typedef struct {
    lean_object *promise;
    lean_object *socket;
} tcp_connect_data;

// Stores all the things needed to send data to a TCP socket.
typedef struct {
    lean_object *promise;
    lean_object *data;
    lean_object *socket;
} tcp_send_data;

// =======================================
// Utility functions

lean_object* unpack_io(lean_object* io) {
    lean_object* io_res = lean_ctor_get(io, 0);
    lean_inc(io_res);
    lean_dec(io);
    return io_res;
}

lean_object* create_promise() {
    lean_object * prom_res = lean_io_promise_new(lean_io_mk_world());
    return unpack_io(prom_res);
}

lean_object * mk_ok_except(lean_object * value) {
    lean_object * ok = alloc_cnstr(1, 1, 0);
    cnstr_set(ok, 0, value);
    return ok;
}

lean_object * mk_err_except(lean_object * value) {
    lean_object * err = alloc_cnstr(0, 1, 0);
    cnstr_set(err, 0, value);
    return err;
}

void resolve_promise(lean_object* promise, lean_object* res) {
    lean_object * result = lean_io_promise_resolve(res, promise, lean_io_mk_world());
    lean_dec(result);
}

void resolve_promise_with_status(lean_object* promise, int status) {
    lean_object * res;

    if (status == 0) {
        res = mk_ok_except(lean_box(0));
    } else {
        res = mk_err_except(lean_decode_uv_error(status, mk_string(uv_strerror(status))));
    }

    resolve_promise(promise, res);
}

// =======================================
// TCP socket object manipulation functions.

void lean_uv_tcp_socket_finalizer(void* ptr) {
    lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)ptr;

    lean_always_assert(tcp_socket->m_promise_shutdown == NULL);
    lean_always_assert(tcp_socket->m_promise_accept == NULL);
    lean_always_assert(tcp_socket->m_promise_read == NULL);
    lean_always_assert(tcp_socket->m_byte_array == NULL);

    /// It's changing here because the object is being freed in the finalizer, and we need the data
    /// inside of it.
    tcp_socket->m_uv_tcp->data = ptr;

    event_loop_lock(&global_ev);

    uv_close((uv_handle_t*)tcp_socket->m_uv_tcp, [](uv_handle_t* handle) {
        lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)handle->data;
        free(tcp_socket->m_uv_tcp);
        free(tcp_socket);
    });

    event_loop_unlock(&global_ev);
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

// =======================================
// TCP Socket Operations

/* Std.Internal.UV.TCP.Socket.new : IO Socket */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new() {
    lean_uv_tcp_socket_object * tcp_socket = (lean_uv_tcp_socket_object*)malloc(sizeof(lean_uv_tcp_socket_object));
    tcp_socket->m_promise_accept = NULL;
    tcp_socket->m_promise_shutdown = NULL;
    tcp_socket->m_promise_read = NULL;
    tcp_socket->m_byte_array = NULL;
    tcp_socket->m_client = NULL;
    tcp_socket->m_buffer_size = 0;

    uv_tcp_t * uv_tcp = (uv_tcp_t*)malloc(sizeof(uv_tcp_t));

    event_loop_lock(&global_ev);
    int result = uv_tcp_init(global_ev.loop, uv_tcp);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(uv_tcp);
        free(tcp_socket);

        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string("failed to initialize")));
    }

    tcp_socket->m_uv_tcp = uv_tcp;

    lean_object * obj = lean_uv_tcp_socket_new(tcp_socket);
    lean_mark_mt(obj);

    tcp_socket->m_uv_tcp->data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.TCP.Socket.connect (socket : @& Socket) (addr : SocketAddress) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr addr_ptr;
    lean_socket_addr_to_sockaddr(addr, &addr_ptr);

    lean_object * promise = create_promise();

    uv_connect_t * uv_connect = (uv_connect_t*)malloc(sizeof(uv_connect_t));

    uv_connect->data = (tcp_connect_data*)malloc(sizeof(tcp_connect_data));

    tcp_connect_data* connect_data = (tcp_connect_data*)uv_connect->data;
    connect_data->promise = promise;
    connect_data->socket = socket;

    lean_inc(promise);

    // The event loop owns the socket.
    lean_inc(socket);

    event_loop_lock(&global_ev);

    int result = uv_tcp_connect(uv_connect, tcp_socket->m_uv_tcp, (const struct sockaddr *)&addr_ptr, [](uv_connect_t* req, int status) {
        tcp_connect_data* tup = (tcp_connect_data*) req->data;
        resolve_promise_with_status(tup->promise, status);

        // The event loop does not own the object anymore.
        lean_dec(tup->socket);

        free(req->data);
        free(req);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        free(uv_connect);
        free(uv_connect->data);

        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string("failed to connect")));
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.send (socket : @& Socket) (data : ByteArray) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, obj_arg data) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    size_t data_len = lean_sarray_size(data);
    char * data_str = (char *)lean_sarray_cptr(data);

    uv_buf_t buf = uv_buf_init(data_str, data_len);

    lean_object * promise = create_promise();

    uv_write_t * write_uv = (uv_write_t*)malloc(sizeof(uv_write_t));

    write_uv->data = (tcp_send_data*)malloc(sizeof(tcp_send_data));

    tcp_send_data* send_data = (tcp_send_data*)write_uv->data;
    send_data->promise = promise;
    send_data->data = data;
    send_data->socket = socket;

    lean_inc(promise);

    // The event loop owns the socket.
    lean_inc(socket);

    event_loop_lock(&global_ev);

    int result = uv_write(write_uv, (uv_stream_t*)tcp_socket->m_uv_tcp, &buf, 1, [](uv_write_t * req, int status) {
        tcp_send_data * tup = (tcp_send_data*) req->data;

        resolve_promise_with_status(tup->promise, status);

        // The event loop does not own the object anymore.
        lean_dec(tup->socket);
        lean_dec(tup->data);

        free(req->data);
        free(req);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        free(write_uv);
        free(write_uv->data);

        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string("failed to write")));
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.recv (socket : @& Socket) : IO (IO.Promise (Except IO.Error ByteArray)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket, uint64_t buffer_size) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    if (tcp_socket->m_byte_array != NULL) {
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, mk_string("parallel recv is not allowed.")));
    }

    lean_object * promise = create_promise();
    tcp_socket->m_promise_read = promise;
    tcp_socket->m_buffer_size = buffer_size;
    lean_inc(promise);

    event_loop_lock(&global_ev);

    // The event loop owns the socket.
    lean_inc(socket);

    uv_read_start((uv_stream_t*)tcp_socket->m_uv_tcp, [](uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf) {
        lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket((lean_object*)handle->data);

        tcp_socket->m_byte_array = lean_alloc_sarray(1, 0, tcp_socket->m_buffer_size);

        buf->base = (char*)lean_sarray_cptr(tcp_socket->m_byte_array);
        buf->len = tcp_socket->m_buffer_size;

    }, [](uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
        uv_read_stop(stream);

        lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);
        lean_object * promise = tcp_socket->m_promise_read;
        lean_object * byte_array = tcp_socket->m_byte_array;

        tcp_socket->m_promise_read = NULL;
        tcp_socket->m_byte_array = NULL;

        if (nread >= 0) {
            lean_sarray_set_size(byte_array, nread);
            resolve_promise(promise, mk_ok_except(byte_array));
        } else if (nread < 0) {
            lean_dec(byte_array);
            resolve_promise(promise, mk_err_except(lean_decode_uv_error(nread, mk_string(uv_strerror(nread)))));
        }

        lean_dec(promise);

        // The event loop does not own the object anymore.
        lean_dec((lean_object*)stream->data);
    });

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.bind (socket : @& Socket) (addr : SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_bind(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr addr_ptr;
    lean_socket_addr_to_sockaddr(addr, &addr_ptr);

    event_loop_lock(&global_ev);

    int result = uv_tcp_bind(tcp_socket->m_uv_tcp, (const struct sockaddr *)&addr_ptr, 0);

    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string("failed to bind")));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.listen (socket : @& Socket) (backlog : Int32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_listen(b_obj_arg socket, int32_t backlog) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);

    int result = uv_listen((uv_stream_t*)tcp_socket->m_uv_tcp, backlog, [](uv_stream_t* stream, int status) {
        lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);

        if (tcp_socket->m_promise_accept == NULL) {
            return;
        }

        lean_object * promise = tcp_socket->m_promise_accept;

        if (status < 0) {
            resolve_promise_with_status(promise, status);
            lean_dec(promise);
            return;
        }

        lean_object * client = tcp_socket->m_client;
        lean_uv_tcp_socket_object * client_socket = lean_to_uv_tcp_socket(client);

        int result = uv_accept((uv_stream_t*)tcp_socket->m_uv_tcp, (uv_stream_t*)client_socket->m_uv_tcp);

        tcp_socket->m_promise_accept = NULL;
        tcp_socket->m_client = NULL;

        if (result < 0) {
            lean_dec(client);
            resolve_promise_with_status(promise, result);
            lean_dec(promise);
            return;
        }

        resolve_promise(promise, mk_ok_except(client));
        lean_dec(promise);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string(uv_strerror(result))));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.accept (socket : @& Socket) : IO (IO.Promise (Except IO.Error Socket)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    if (tcp_socket->m_promise_accept != NULL) {
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, mk_string("parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead")));
    }

    lean_object * promise = create_promise();
    lean_object * client = unpack_io(lean_uv_tcp_new());

    lean_uv_tcp_socket_object * client_socket = lean_to_uv_tcp_socket(client);

    event_loop_lock(&global_ev);
    int result = uv_accept((uv_stream_t*)tcp_socket->m_uv_tcp, (uv_stream_t*)client_socket->m_uv_tcp);
    event_loop_unlock(&global_ev);

    if (result < 0 && result != UV_EAGAIN) {
        lean_dec(client);
        resolve_promise_with_status(promise, result);
    } else if (result >= 0) {
        resolve_promise(promise, mk_ok_except(client));
    } else {
        tcp_socket->m_promise_accept = promise;
        tcp_socket->m_client = client;
        lean_inc(promise);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.shutdown (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    if (tcp_socket->m_promise_shutdown != NULL) {
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, mk_string("shutdown already in progress")));
    }

    lean_object * promise = create_promise();
    tcp_socket->m_promise_shutdown = promise;
    lean_inc(promise);

    event_loop_lock(&global_ev);

    uv_shutdown_t* shutdown_req = (uv_shutdown_t*)malloc(sizeof(uv_shutdown_t));
    shutdown_req->data = (void*)socket;

    lean_inc(socket);

    int result = uv_shutdown(shutdown_req, (uv_stream_t*)tcp_socket->m_uv_tcp, [](uv_shutdown_t* req, int status) {
        lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket((lean_object*)req->data);

        if (status < 0) {
            resolve_promise_with_status(tcp_socket->m_promise_shutdown, status);
        } else {
            resolve_promise(tcp_socket->m_promise_shutdown, mk_ok_except(lean_box(0)));
        }

        lean_dec(tcp_socket->m_promise_shutdown);

        tcp_socket->m_promise_shutdown = NULL;

        lean_dec((lean_object*)req->data);
        free(req);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        free(shutdown_req);
        tcp_socket->m_promise_shutdown = NULL;
        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string("failed to initiate shutdown")));
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.getpeername (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket) {
    lean_uv_tcp_socket_object *tcp_socket = lean_to_uv_tcp_socket(socket);

    struct sockaddr addr_storage;
    int addr_len = sizeof(addr_storage);

    int result = uv_tcp_getpeername(tcp_socket->m_uv_tcp, (struct sockaddr*)&addr_storage, &addr_len);

    if (result < 0) {
        return io_result_mk_error(uv_strerror(result));
    }

    lean_object *lean_addr = lean_sockaddr_to_socketaddress(&addr_storage);

    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.TCP.Socket.getsockname (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket) {
    lean_uv_tcp_socket_object *tcp_socket = lean_to_uv_tcp_socket(socket);

    struct sockaddr addr_storage;
    int addr_len = sizeof(addr_storage);

    int result = uv_tcp_getsockname(tcp_socket->m_uv_tcp, &addr_storage, &addr_len);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    lean_object *lean_addr = lean_sockaddr_to_socketaddress(&addr_storage);
    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.TCP.Socket.nodelay (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    int result = uv_tcp_nodelay(tcp_socket->m_uv_tcp, 1);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.keepalive (socket : @& Socket) (enable : Int32) (delay : UInt32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay) {
    lean_uv_tcp_socket_object * tcp_socket = lean_to_uv_tcp_socket(socket);

    int result = uv_tcp_keepalive(tcp_socket->m_uv_tcp, enable, delay);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, mk_string("failed to set TCP_KEEPALIVE")));
    }

    return lean_io_result_mk_ok(lean_box(0));
}
}

#else

// =======================================
// TCP Socket Operations

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

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

// =======================================
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
