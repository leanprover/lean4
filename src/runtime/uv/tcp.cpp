/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/tcp.h"
#include <cstring>

namespace lean {

#ifndef LEAN_EMSCRIPTEN

// Stores all the things needed to connect to a TCP socket.
typedef struct {
    lean_object* promise;
    lean_object* socket;
} tcp_connect_data;

// Stores all the things needed to send data to a TCP socket.
typedef struct {
    lean_object* promise;
    lean_object* data;
    lean_object* socket;
    uv_buf_t* bufs;
} tcp_send_data;

// =======================================
// TCP socket object manipulation functions.

void lean_uv_tcp_socket_finalizer(void* ptr) {
    lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)ptr;

    lean_always_assert(tcp_socket->m_promise_shutdown == nullptr);
    lean_always_assert(tcp_socket->m_promise_accept == nullptr);
    lean_always_assert(tcp_socket->m_promise_read == nullptr);
    lean_always_assert(tcp_socket->m_byte_array == nullptr);

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

        if (tcp_socket->m_promise_accept != nullptr) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_promise_accept);
        }

        if (tcp_socket->m_promise_shutdown != nullptr) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_promise_shutdown);
        }

        if (tcp_socket->m_promise_read != nullptr) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_promise_read);
        }

        if (tcp_socket->m_byte_array != nullptr) {
            lean_inc(f);
            lean_apply_1(f, tcp_socket->m_byte_array);
        }
    });
}

// =======================================
// TCP Socket Operations

/* Std.Internal.UV.TCP.Socket.new : IO Socket */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new() {
    lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)malloc(sizeof(lean_uv_tcp_socket_object));

    tcp_socket->m_promise_accept = nullptr;
    tcp_socket->m_promise_shutdown = nullptr;
    tcp_socket->m_promise_read = nullptr;
    tcp_socket->m_byte_array = nullptr;
    tcp_socket->m_client = nullptr;

    uv_tcp_t* uv_tcp = (uv_tcp_t*)malloc(sizeof(uv_tcp_t));

    event_loop_lock(&global_ev);
    int result = uv_tcp_init(global_ev.loop, uv_tcp);
    event_loop_unlock(&global_ev);

    if (result != 0) {
        free(uv_tcp);
        free(tcp_socket);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    tcp_socket->m_uv_tcp = uv_tcp;

    lean_object* obj = lean_uv_tcp_socket_new(tcp_socket);
    lean_mark_mt(obj);

    tcp_socket->m_uv_tcp->data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.TCP.Socket.connect (socket : @& Socket) (addr : @& SocketAddress) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    sockaddr_storage addr_struct;
    lean_socket_address_to_sockaddr_storage(addr, &addr_struct);

    uv_connect_t* uv_connect = (uv_connect_t*)malloc(sizeof(uv_connect_t));
    tcp_connect_data* connect_data = (tcp_connect_data*)malloc(sizeof(tcp_connect_data));

    connect_data->promise = promise;
    connect_data->socket = socket;

    uv_connect->data = connect_data;

    // The event loop owns the socket.
    lean_inc(socket);
    lean_inc(promise);

    event_loop_lock(&global_ev);

    int result = uv_tcp_connect(uv_connect, tcp_socket->m_uv_tcp, (sockaddr*)&addr_struct, [](uv_connect_t* req, int status) {
        tcp_connect_data* tup = (tcp_connect_data*) req->data;
        lean_promise_resolve_with_code(status, tup->promise);

        // The event loop does not own the object anymore.
        lean_dec(tup->socket);
        lean_dec(tup->promise);

        free(req->data);
        free(req);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        free(uv_connect->data);
        free(uv_connect);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.send (socket : @& Socket) (data : Array ByteArray) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, obj_arg data_array) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    size_t array_len = lean_array_size(data_array);

    if (array_len == 0) {
        lean_dec(data_array);

        lean_object* promise = lean_promise_new();
        mark_mt(promise);
        lean_promise_resolve_with_code(0, promise);

        return lean_io_result_mk_ok(promise);
    }

    // Allocate buffer array for uv_write
    uv_buf_t* bufs = (uv_buf_t*)malloc(array_len * sizeof(uv_buf_t));

    for (size_t i = 0; i < array_len; i++) {
        lean_object* byte_array = lean_array_get_core(data_array, i);
        size_t data_len = lean_sarray_size(byte_array);
        char* data_str = (char*)lean_sarray_cptr(byte_array);
        bufs[i] = uv_buf_init(data_str, data_len);
    }

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    uv_write_t* write_uv = (uv_write_t*)malloc(sizeof(uv_write_t));
    write_uv->data = (tcp_send_data*)malloc(sizeof(tcp_send_data));

    tcp_send_data* send_data = (tcp_send_data*)write_uv->data;
    send_data->promise = promise;
    send_data->data = data_array;
    send_data->socket = socket;
    send_data->bufs = bufs;

    // These objects are going to enter the loop and be owned by it
    lean_inc(promise);
    lean_inc(socket);

    event_loop_lock(&global_ev);

    int result = uv_write(write_uv, (uv_stream_t*)tcp_socket->m_uv_tcp, bufs, array_len, [](uv_write_t* req, int status) {
        tcp_send_data* tup = (tcp_send_data*) req->data;

        lean_promise_resolve_with_code(status, tup->promise);

        lean_dec(tup->promise);
        lean_dec(tup->data);
        lean_dec(tup->socket);

        free(tup->bufs);
        free(req->data);
        free(req);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);
        lean_dec(data_array);
        free(bufs);

        free(write_uv->data);
        free(write_uv);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.recv? (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (Option ByteArray))) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket, uint64_t buffer_size) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    // Locking early prevents potential parallelism issues setting the byte_array.
    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_read != nullptr) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, nullptr));
    }

    lean_object* byte_array = lean_alloc_sarray(1, 0, buffer_size);
    tcp_socket->m_byte_array = byte_array;

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    tcp_socket->m_promise_read = promise;

    // The event loop owns the socket.
    lean_inc(socket);
    lean_inc(promise);

    int result = uv_read_start((uv_stream_t*)tcp_socket->m_uv_tcp, [](uv_handle_t* handle, size_t suggested_size, uv_buf_t* buf) {
        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)handle->data);

        buf->base = (char*)lean_sarray_cptr(tcp_socket->m_byte_array);
        buf->len = lean_sarray_capacity(tcp_socket->m_byte_array);
    }, [](uv_stream_t* stream, ssize_t nread, const uv_buf_t* buf) {
        uv_read_stop(stream);

        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);
        lean_object* promise = tcp_socket->m_promise_read;
        lean_object* byte_array = tcp_socket->m_byte_array;

        tcp_socket->m_promise_read = nullptr;
        tcp_socket->m_byte_array = nullptr;

        if (nread >= 0) {
            lean_sarray_set_size(byte_array, nread);
            lean_promise_resolve(mk_except_ok(lean::mk_option_some(byte_array)), promise);
        } else if (nread == UV_EOF) {
            lean_dec(byte_array);
            lean_promise_resolve(mk_except_ok(lean::mk_option_none()), promise);
        } else if (nread < 0) {
            lean_dec(byte_array);
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(nread, nullptr)), promise);
        }

        lean_dec(promise);

        // The event loop does not own the object anymore.
        lean_dec((lean_object*)stream->data);
    });

    if (result < 0) {
        tcp_socket->m_byte_array = nullptr;
        tcp_socket->m_promise_read = nullptr;

        event_loop_unlock(&global_ev);

        lean_dec(byte_array);
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.waitReadable (socket : @& Socket) : IO (IO.Promise (Except IO.Error Bool)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_wait_readable(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_read != nullptr) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, nullptr));
    }

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    tcp_socket->m_promise_read = promise;

    // The event loop owns the socket.
    lean_inc(socket);
    lean_inc(promise);

    int result = uv_read_start((uv_stream_t*)tcp_socket->m_uv_tcp, [](uv_handle_t* handle, size_t suggested_size, uv_buf_t* buf) {
        // According to libuv documentation if we do this we do not lose data and a UV_ENOBUFS will
        // be triggered in the read cb.
        buf->base = NULL;
        buf->len = 0;
    }, [](uv_stream_t* stream, ssize_t nread, const uv_buf_t* buf) {
        uv_read_stop(stream);

        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);
        lean_object* promise = tcp_socket->m_promise_read;

        tcp_socket->m_promise_read = nullptr;

        if (nread == UV_ENOBUFS) {
            lean_promise_resolve(mk_except_ok(lean_box(1)), promise);
        } else if (nread == UV_EOF) {
            lean_promise_resolve(mk_except_ok(lean_box(0)), promise);
        } else if (nread < 0) {
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(nread, nullptr)), promise);
        } else {
            // This branch should be dead, we cannot receive a value >= 0 according to docs.
            lean_always_assert(false);
        }

        lean_dec(promise);

        // The event loop does not own the object anymore.
        lean_dec((lean_object*)stream->data);
    });

    if (result < 0) {
        tcp_socket->m_promise_read = nullptr;

        event_loop_unlock(&global_ev);

        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.cancelRecv (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_recv(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_read == nullptr) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(lean_box(0));
    }

    uv_read_stop((uv_stream_t*)tcp_socket->m_uv_tcp);

    lean_object* promise = tcp_socket->m_promise_read;
    lean_dec(promise);
    tcp_socket->m_promise_read = nullptr;

    lean_object* byte_array = tcp_socket->m_byte_array;
    if (byte_array != nullptr) {
        lean_dec(byte_array);
        tcp_socket->m_byte_array = nullptr;
    }

    lean_dec(socket);

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.bind (socket : @& Socket) (addr : @& SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_bind(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr_storage addr_ptr;
    lean_socket_address_to_sockaddr_storage(addr, &addr_ptr);

    event_loop_lock(&global_ev);
    int result = uv_tcp_bind(tcp_socket->m_uv_tcp, (sockaddr*)&addr_ptr, 0);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.listen (socket : @& Socket) (backlog : Int32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_listen(b_obj_arg socket, int32_t backlog) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);

    int result = uv_listen((uv_stream_t*)tcp_socket->m_uv_tcp, backlog, [](uv_stream_t* stream, int status) {
        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);

        if (tcp_socket->m_promise_accept == nullptr) {
            return;
        }

        lean_object* promise = tcp_socket->m_promise_accept;

        if (status < 0) {
            lean_promise_resolve_with_code(status, promise);
            lean_dec(promise);
            tcp_socket->m_promise_accept = nullptr;
            return;
        }

        lean_object* client = tcp_socket->m_client;
        lean_uv_tcp_socket_object* client_socket = lean_to_uv_tcp_socket(client);

        int result = uv_accept((uv_stream_t*)tcp_socket->m_uv_tcp, (uv_stream_t*)client_socket->m_uv_tcp);

        tcp_socket->m_promise_accept = nullptr;
        tcp_socket->m_client = nullptr;

        if (result < 0) {
            lean_dec(client);
            lean_promise_resolve_with_code(result, promise);
            lean_dec(promise);
            return;
        }

        lean_promise_resolve(mk_except_ok(client), promise);
        lean_dec(promise);

        // The accept increases the count and then the listen decreases
        lean_dec((lean_object*)stream->data);
    });

    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.accept (socket : @& Socket) : IO (IO.Promise (Except IO.Error Socket)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    // Locking early prevents potential parallelism issues setting m_promise_accept.
    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_accept != nullptr) {
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, mk_string("parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead")));
    }

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    lean_object* client = lean_io_result_take_value(lean_uv_tcp_new());

    lean_uv_tcp_socket_object* client_socket = lean_to_uv_tcp_socket(client);

    int result = uv_accept((uv_stream_t*)tcp_socket->m_uv_tcp, (uv_stream_t*)client_socket->m_uv_tcp);

    if (result < 0 && result != UV_EAGAIN) {
        event_loop_unlock(&global_ev);
        lean_dec(client);
        lean_promise_resolve_with_code(result, promise);
    } else if (result >= 0) {
        event_loop_unlock(&global_ev);
        lean_promise_resolve(mk_except_ok(client), promise);
    } else {
        // The event loop owns the object. It will be released in the listen
        lean_inc(socket);
        lean_inc(promise);

        tcp_socket->m_promise_accept = promise;
        tcp_socket->m_client = client;

        event_loop_unlock(&global_ev);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.tryAccept (socket : @& Socket) : IO (Except IO.Error (Option Socket)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_try_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    // Locking early prevents potential parallelism issues setting m_promise_accept.
    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_accept != nullptr) {
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, mk_string("parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead")));
    }

    lean_object* client = lean_io_result_take_value(lean_uv_tcp_new());
    lean_uv_tcp_socket_object* client_socket = lean_to_uv_tcp_socket(client);

    int result = uv_accept((uv_stream_t*)tcp_socket->m_uv_tcp, (uv_stream_t*)client_socket->m_uv_tcp);

    if (result < 0 && result != UV_EAGAIN) {
        event_loop_unlock(&global_ev);
        lean_dec(client);
        return lean_io_result_mk_error(lean_decode_uv_error(result, NULL));
    } else if (result >= 0) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(mk_except_ok(lean::mk_option_some(client)));
    } else {
        event_loop_unlock(&global_ev);
        lean_dec(client);
        return lean_io_result_mk_ok(mk_except_ok(lean::mk_option_none()));
    }
}



/* Std.Internal.UV.TCP.Socket.cancelAccept (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_accept == nullptr) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_ok(lean_box(0));
    }

    lean_object* promise = tcp_socket->m_promise_accept;
    lean_dec(promise);
    tcp_socket->m_promise_accept = nullptr;

    lean_object* client = tcp_socket->m_client;

    if (client != nullptr) {
        lean_dec(client);
        tcp_socket->m_client = nullptr;
    }

    lean_dec(socket);

    event_loop_unlock(&global_ev);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.shutdown (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    // Locking early prevents potential parallelism issues setting the m_promise_shutdown.
    event_loop_lock(&global_ev);

    if (tcp_socket->m_promise_shutdown != nullptr) {
        event_loop_unlock(&global_ev);
        return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, mk_string("shutdown already in progress")));
    }

    lean_object* promise = lean_promise_new();
    mark_mt(promise);

    tcp_socket->m_promise_shutdown = promise;
    lean_inc(promise);


    uv_shutdown_t* shutdown_req = (uv_shutdown_t*)malloc(sizeof(uv_shutdown_t));
    shutdown_req->data = (void*)socket;

    lean_inc(socket);

    int result = uv_shutdown(shutdown_req, (uv_stream_t*)tcp_socket->m_uv_tcp, [](uv_shutdown_t* req, int status) {
        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)req->data);

        if (status < 0) {
            lean_promise_resolve_with_code(status, tcp_socket->m_promise_shutdown);
        } else {
            lean_promise_resolve(mk_except_ok(lean_box(0)), tcp_socket->m_promise_shutdown);
        }

        lean_dec(tcp_socket->m_promise_shutdown);

        tcp_socket->m_promise_shutdown = nullptr;

        lean_dec((lean_object*)req->data);
        free(req);
    });


    if (result < 0) {
        free(shutdown_req);
        lean_dec(tcp_socket->m_promise_shutdown);
        tcp_socket->m_promise_shutdown = nullptr;
        event_loop_unlock(&global_ev);

        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    event_loop_unlock(&global_ev);

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.getPeerName (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr_storage addr_storage;
    int addr_len = sizeof(addr_storage);

    event_loop_lock(&global_ev);
    int result = uv_tcp_getpeername(tcp_socket->m_uv_tcp, (struct sockaddr*)&addr_storage, &addr_len);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_addr = lean_sockaddr_to_socketaddress((struct sockaddr*)&addr_storage);

    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.TCP.Socket.getSockName (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    struct sockaddr_storage addr_storage;
    int addr_len = sizeof(addr_storage);

    event_loop_lock(&global_ev);
    int result = uv_tcp_getsockname(tcp_socket->m_uv_tcp, (struct sockaddr*)&addr_storage, &addr_len);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    lean_object* lean_addr = lean_sockaddr_to_socketaddress((struct sockaddr*)&addr_storage);
    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.TCP.Socket.noDelay (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);
    int result = uv_tcp_nodelay(tcp_socket->m_uv_tcp, 1);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.keepAlive (socket : @& Socket) (enable : Int8) (delay : UInt32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    event_loop_lock(&global_ev);
    int result = uv_tcp_keepalive(tcp_socket->m_uv_tcp, enable, delay);
    event_loop_unlock(&global_ev);

    if (result < 0) {
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }

    return lean_io_result_mk_ok(lean_box(0));
}
#else

// =======================================
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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, obj_arg data) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket, uint64_t buffer_size) {
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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_accept(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket) {
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
}
