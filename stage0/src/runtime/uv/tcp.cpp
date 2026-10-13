/*
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/uv/tcp.h"
#include "runtime/uv/util.h"
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

static void tcp_socket_finalizer(void* ptr) {
    lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)ptr;

    lean_always_assert(tcp_socket->m_promise_shutdown == nullptr);
    lean_always_assert(tcp_socket->m_promise_accept == nullptr);
    lean_always_assert(tcp_socket->m_promise_read == nullptr);
    lean_always_assert(tcp_socket->m_byte_array == nullptr);

    event_loop_guard guard;

    // The Lean object is being freed, so the close callback gets the struct instead. No callback
    // reads `data` as the Lean object after `uv_close`.
    tcp_socket->m_uv_tcp.data = tcp_socket;

    uv_close((uv_handle_t*)&tcp_socket->m_uv_tcp, [](uv_handle_t* handle) {
        free(handle->data);
    });
}

void initialize_libuv_tcp_socket() {
    g_uv_tcp_socket_external_class = lean_register_external_class(tcp_socket_finalizer, [](void* obj, lean_object* f) {
        lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)obj;

        if (tcp_socket->m_promise_accept != nullptr) {
            lean_inc(f);
            lean_inc(tcp_socket->m_promise_accept);
            lean_dec(lean_apply_1(f, tcp_socket->m_promise_accept));
        }

        if (tcp_socket->m_promise_shutdown != nullptr) {
            lean_inc(f);
            lean_inc(tcp_socket->m_promise_shutdown);
            lean_dec(lean_apply_1(f, tcp_socket->m_promise_shutdown));
        }

        if (tcp_socket->m_promise_read != nullptr) {
            lean_inc(f);
            lean_inc(tcp_socket->m_promise_read);
            lean_dec(lean_apply_1(f, tcp_socket->m_promise_read));
        }

        if (tcp_socket->m_byte_array != nullptr) {
            lean_inc(f);
            lean_inc(tcp_socket->m_byte_array);
            lean_dec(lean_apply_1(f, tcp_socket->m_byte_array));
        }

        if (tcp_socket->m_client != nullptr) {
            lean_inc(f);
            lean_inc(tcp_socket->m_client);
            lean_dec(lean_apply_1(f, tcp_socket->m_client));
        }
    });
}

// =======================================
// TCP Socket Operations

/* Std.Internal.UV.TCP.Socket.new : IO Socket */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_new() {
    lean_uv_tcp_socket_object* tcp_socket = (lean_uv_tcp_socket_object*)malloc(sizeof(lean_uv_tcp_socket_object));
    if (tcp_socket == nullptr) {
        return io_result_mk_enomem();
    }

    tcp_socket->m_promise_accept = nullptr;
    tcp_socket->m_promise_shutdown = nullptr;
    tcp_socket->m_promise_read = nullptr;
    tcp_socket->m_byte_array = nullptr;
    tcp_socket->m_client = nullptr;
    tcp_socket->m_shutdown_requested = false;
    tcp_socket->m_listening = false;
    tcp_socket->m_pending_connections = 0;

    int result;

    {
        event_loop_guard guard;
        result = uv_tcp_init(global_ev.m_loop, &tcp_socket->m_uv_tcp);
    }

    if (result != 0) {
        free(tcp_socket);

        return io_result_mk_uv_error(result);
    }

    lean_object* obj = lean_uv_tcp_socket_new(tcp_socket);
    lean_mark_mt(obj);

    tcp_socket->m_uv_tcp.data = obj;

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.UV.TCP.Socket.connect (socket : @& Socket) (addr : @& SocketAddress) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_connect(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr_storage addr_struct;
    lean_socket_address_to_sockaddr_storage(addr, &addr_struct);

    uv_connect_t* uv_connect = (uv_connect_t*)malloc(sizeof(uv_connect_t));
    if (uv_connect == nullptr) {
        return io_result_mk_enomem();
    }
    tcp_connect_data* connect_data = (tcp_connect_data*)malloc(sizeof(tcp_connect_data));
    if (connect_data == nullptr) {
        free(uv_connect);
        return io_result_mk_enomem();
    }

    lean_object * promise = mk_mt_promise();

    connect_data->promise = promise;
    connect_data->socket = socket;

    uv_connect->data = connect_data;

    // The event loop owns the socket.
    lean_inc(socket);
    lean_inc(promise);

    auto on_connect = [](uv_connect_t* req, int status) {
        tcp_connect_data* tup = (tcp_connect_data*) req->data;
        resolve_with_code(status, tup->promise);

        // The event loop does not own the object anymore.
        lean_dec(tup->socket);
        lean_dec(tup->promise);

        free(req->data);
        free(req);
    };

    int result;
    {
        event_loop_guard guard;
        result = uv_tcp_connect(uv_connect, &tcp_socket->m_uv_tcp, (sockaddr*)&addr_struct, on_connect);
    }

    if (result < 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        free(uv_connect->data);
        free(uv_connect);

        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.send (socket : @& Socket) (data : Array ByteArray) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_send(b_obj_arg socket, obj_arg data_array) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    size_t array_len = lean_array_size(data_array);

    if (array_len == 0) {
        lean_dec(data_array);

        lean_object * promise = mk_mt_promise();
        resolve_with_code(0, promise);

        return lean_io_result_mk_ok(promise);
    }

    // Allocate buffer array for uv_write
    if (lean_usize_mul_would_overflow(array_len, sizeof(uv_buf_t))) {
        lean_dec(data_array);
        return io_result_mk_enomem();
    }
    uv_buf_t* bufs = (uv_buf_t*)malloc(array_len * sizeof(uv_buf_t));
    if (bufs == nullptr) {
        lean_dec(data_array);
        return io_result_mk_enomem();
    }

    for (size_t i = 0; i < array_len; i++) {
        lean_object* byte_array = lean_array_get_core(data_array, i);
        size_t data_len = lean_sarray_size(byte_array);
        char* data_str = (char*)lean_sarray_cptr(byte_array);
        bufs[i] = uv_buf_init(data_str, data_len);
    }

    uv_write_t* write_uv = (uv_write_t*)malloc(sizeof(uv_write_t));
    if (write_uv == nullptr) {
        lean_dec(data_array);
        free(bufs);
        return io_result_mk_enomem();
    }
    write_uv->data = (tcp_send_data*)malloc(sizeof(tcp_send_data));
    if (write_uv->data == nullptr) {
        lean_dec(data_array);
        free(bufs);
        free(write_uv);
        return io_result_mk_enomem();
    }

    lean_object * promise = mk_mt_promise();
    mark_mt(data_array);

    tcp_send_data* send_data = (tcp_send_data*)write_uv->data;
    send_data->promise = promise;
    send_data->data = data_array;
    send_data->socket = socket;
    send_data->bufs = bufs;

    // These objects are going to enter the loop and be owned by it
    lean_inc(promise);
    lean_inc(socket);

    auto on_write = [](uv_write_t* req, int status) {
        tcp_send_data* tup = (tcp_send_data*) req->data;

        resolve_with_code(status, tup->promise);

        lean_dec(tup->promise);
        lean_dec(tup->data);
        lean_dec(tup->socket);

        free(tup->bufs);
        free(req->data);
        free(req);
    };

    int result;
    {
        event_loop_guard guard;
        result = uv_write(write_uv, (uv_stream_t*)&tcp_socket->m_uv_tcp, bufs, array_len, on_write);
    }

    if (result < 0) {
        lean_dec(promise); // The structure does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);
        lean_dec(data_array);
        free(bufs);

        free(write_uv->data);
        free(write_uv);

        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.recv? (socket : @& Socket) (size : UInt64) : IO (IO.Promise (Except IO.Error (Option ByteArray))) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_recv(b_obj_arg socket, uint64_t buffer_size) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    auto alloc_cb = [](uv_handle_t* handle, size_t suggested_size, uv_buf_t* buf) {
        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)handle->data);

        buf->base = (char*)lean_sarray_cptr(tcp_socket->m_byte_array);
        buf->len = lean_sarray_capacity(tcp_socket->m_byte_array);
    };

    auto read_cb = [](uv_stream_t* stream, ssize_t nread, const uv_buf_t* buf) {
        if (nread == 0) return;

        uv_read_stop(stream);

        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);
        lean_object* promise = tcp_socket->m_promise_read;
        lean_object* byte_array = tcp_socket->m_byte_array;

        tcp_socket->m_promise_read = nullptr;
        tcp_socket->m_byte_array = nullptr;

        if (nread >= 0) {
            byte_array = fit_read_buffer(byte_array, nread);
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
    };

    lean_object* byte_array;
    lean_object* promise;
    int result;
    {
        // Locking early prevents potential parallelism issues setting the byte_array.
        event_loop_guard guard;

        if (tcp_socket->m_promise_read != nullptr) {
            return io_result_mk_uv_error(UV_EALREADY);
        }

        if (lean_object * size_error = recv_size_error(buffer_size)) {
            return size_error;
        }

        byte_array = lean_alloc_sarray(1, 0, buffer_size);
        tcp_socket->m_byte_array = byte_array;

        promise = mk_mt_promise();

        tcp_socket->m_promise_read = promise;

        // The event loop owns the socket.
        lean_inc(socket);
        lean_inc(promise);

        result = uv_read_start((uv_stream_t*)&tcp_socket->m_uv_tcp, alloc_cb, read_cb);

        if (result < 0) {
            tcp_socket->m_byte_array = nullptr;
            tcp_socket->m_promise_read = nullptr;
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

/* Std.Internal.UV.TCP.Socket.waitReadable (socket : @& Socket) : IO (IO.Promise (Except IO.Error Bool)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_wait_readable(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    auto alloc_cb = [](uv_handle_t* handle, size_t suggested_size, uv_buf_t* buf) {
        // According to libuv documentation if we do this we do not lose data and a UV_ENOBUFS will
        // be triggered in the read cb.
        buf->base = NULL;
        buf->len = 0;
    };

    auto read_cb = [](uv_stream_t* stream, ssize_t nread, const uv_buf_t* buf) {
        // `nread == 0` is libuv's equivalent of `EAGAIN`: the socket is not actually readable, so
        // keep waiting rather than resolving the promise.
        if (nread == 0) return;

        uv_read_stop(stream);

        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)stream->data);
        lean_object* promise = tcp_socket->m_promise_read;

        tcp_socket->m_promise_read = nullptr;

        if (nread == UV_EOF) {
            lean_promise_resolve(mk_except_ok(lean_box(0)), promise);
        } else if (nread < 0 && nread != UV_ENOBUFS) {
            lean_promise_resolve(mk_except_err(lean_decode_uv_error(nread, nullptr)), promise);
        } else {
            lean_promise_resolve(mk_except_ok(lean_box(1)), promise);
        }

        lean_dec(promise);

        // The event loop does not own the object anymore.
        lean_dec((lean_object*)stream->data);
    };

    lean_object* promise;
    int result;
    {
        event_loop_guard guard;

        if (tcp_socket->m_promise_read != nullptr) {
            return io_result_mk_uv_error(UV_EALREADY);
        }

        promise = mk_mt_promise();

        tcp_socket->m_promise_read = promise;

        // The event loop owns the socket.
        lean_inc(socket);
        lean_inc(promise);

        result = uv_read_start((uv_stream_t*)&tcp_socket->m_uv_tcp, alloc_cb, read_cb);

        if (result < 0) {
            tcp_socket->m_promise_read = nullptr;
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

/* Std.Internal.UV.TCP.Socket.cancelRecv (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_recv(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    lean_object* promise = nullptr;
    lean_object* byte_array = nullptr;
    {
        event_loop_guard guard;

        if (tcp_socket->m_promise_read != nullptr) {
            uv_read_stop((uv_stream_t*)&tcp_socket->m_uv_tcp);

            promise = tcp_socket->m_promise_read;
            byte_array = tcp_socket->m_byte_array;

            tcp_socket->m_promise_read = nullptr;
            tcp_socket->m_byte_array = nullptr;
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

/* Std.Internal.UV.TCP.Socket.bind (socket : @& Socket) (addr : @& SocketAddress) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_bind(b_obj_arg socket, b_obj_arg addr) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr_storage addr_ptr;
    lean_socket_address_to_sockaddr_storage(addr, &addr_ptr);

    int result;
    {
        event_loop_guard guard;
        result = uv_tcp_bind(&tcp_socket->m_uv_tcp, (sockaddr*)&addr_ptr, 0);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.listen (socket : @& Socket) (backlog : Int32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_listen(b_obj_arg socket, int32_t backlog) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    auto on_connection = [](uv_stream_t* stream, int status) {
        lean_object* socket = (lean_object*)stream->data;
        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

        lean_object* promise = tcp_socket->m_promise_accept;
        lean_object* client = tcp_socket->m_client;

        // libuv reports a connection once and keeps it queued until `uv_accept` takes it.
        if (status >= 0 && client == nullptr) {
            tcp_socket->m_pending_connections++;
        }

        if (promise == nullptr) {
            return;
        }

        int result = status;

        if (status >= 0 && client != nullptr) {
            lean_uv_tcp_socket_object* client_socket = lean_to_uv_tcp_socket(client);
            result = uv_accept((uv_stream_t*)&tcp_socket->m_uv_tcp, (uv_stream_t*)&client_socket->m_uv_tcp);
        }

        tcp_socket->m_promise_accept = nullptr;
        tcp_socket->m_client = nullptr;

        // The accept increases the count and then the listen decreases
        lean_dec(socket);

        if (result < 0) {
            if (client != nullptr) {
                lean_dec(client);
            }
            resolve_with_code(result, promise);
        } else {
            lean_promise_resolve(mk_except_ok(client != nullptr ? client : lean_box(0)), promise);
        }

        lean_dec(promise);
    };

    int result;
    {
        event_loop_guard guard;

        result = uv_listen((uv_stream_t*)&tcp_socket->m_uv_tcp, backlog, on_connection);

        if (result == 0) {
            tcp_socket->m_listening = true;
        }
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

// An accept on a socket that is not listening would wait for a connection that never arrives.
static lean_obj_res tcp_not_listening_error() {
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string("socket is not listening")));
}

/* Std.Internal.UV.TCP.Socket.accept (socket : @& Socket) : IO (IO.Promise (Except IO.Error Socket)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    lean_object* client;
    lean_object* promise;
    int result;
    {
        // Locking early prevents potential parallelism issues setting m_promise_accept.
        event_loop_guard guard;

        if (tcp_socket->m_promise_accept != nullptr) {
            return lean_io_result_mk_error(lean_mk_io_error_other_error(-UV_EALREADY, mk_string("parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead")));
        }

        if (!tcp_socket->m_listening) {
            return tcp_not_listening_error();
        }

        lean_object* client_res = lean_uv_tcp_new();

        if (lean_io_result_is_error(client_res)) {
            return client_res;
        }

        client = lean_io_result_take_value(client_res);

        promise = mk_mt_promise();

        lean_uv_tcp_socket_object* client_socket = lean_to_uv_tcp_socket(client);

        result = uv_accept((uv_stream_t*)&tcp_socket->m_uv_tcp, (uv_stream_t*)&client_socket->m_uv_tcp);

        // `uv_accept` takes the queued connection unless there is none, even when it fails.
        if (result != UV_EAGAIN && tcp_socket->m_pending_connections > 0) {
            tcp_socket->m_pending_connections--;
        }

        if (result == UV_EAGAIN) {
            // The event loop owns the object. It will be released in the listen
            lean_inc(socket);
            lean_inc(promise);

            tcp_socket->m_promise_accept = promise;
            tcp_socket->m_client = client;
        }
    }

    if (result < 0 && result != UV_EAGAIN) {
        lean_dec(client);
        resolve_with_code(result, promise);
    } else if (result >= 0) {
        lean_promise_resolve(mk_except_ok(client), promise);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.tryAccept (socket : @& Socket) : IO (Except IO.Error (Option Socket)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_try_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    lean_object* client;
    int result;
    {
        // Locking early prevents potential parallelism issues setting m_promise_accept.
        event_loop_guard guard;

        if (tcp_socket->m_promise_accept != nullptr) {
            return lean_io_result_mk_error(lean_mk_io_error_other_error(-UV_EALREADY, mk_string("parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead")));
        }

        if (!tcp_socket->m_listening) {
            return tcp_not_listening_error();
        }

        lean_object* client_res = lean_uv_tcp_new();

        if (lean_io_result_is_error(client_res)) {
            return client_res;
        }

        client = lean_io_result_take_value(client_res);
        lean_uv_tcp_socket_object* client_socket = lean_to_uv_tcp_socket(client);

        result = uv_accept((uv_stream_t*)&tcp_socket->m_uv_tcp, (uv_stream_t*)&client_socket->m_uv_tcp);

        // `uv_accept` takes the queued connection unless there is none, even when it fails.
        if (result != UV_EAGAIN && tcp_socket->m_pending_connections > 0) {
            tcp_socket->m_pending_connections--;
        }
    }

    if (result < 0 && result != UV_EAGAIN) {
        lean_dec(client);
        return io_result_mk_uv_error(result);
    } else if (result >= 0) {
        return lean_io_result_mk_ok(mk_except_ok(lean::mk_option_some(client)));
    } else {
        lean_dec(client);
        return lean_io_result_mk_ok(mk_except_ok(lean::mk_option_none()));
    }
}



/* Std.Internal.UV.TCP.Socket.waitAcceptable (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_wait_acceptable(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    lean_object* promise;
    bool ready;
    {
        event_loop_guard guard;

        if (tcp_socket->m_promise_accept != nullptr) {
            return io_result_mk_uv_error(UV_EALREADY);
        }

        if (!tcp_socket->m_listening) {
            return tcp_not_listening_error();
        }

        promise = mk_mt_promise();

        ready = tcp_socket->m_pending_connections > 0;

        if (!ready) {
            // The event loop owns the object. It will be released in the listen
            lean_inc(socket);
            lean_inc(promise);
            tcp_socket->m_promise_accept = promise;
        }
    }

    if (ready) {
        lean_promise_resolve(mk_except_ok(lean_box(0)), promise);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.cancelAccept (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_cancel_accept(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    lean_object* promise = nullptr;
    lean_object* client = nullptr;
    {
        event_loop_guard guard;

        if (tcp_socket->m_promise_accept != nullptr) {
            promise = tcp_socket->m_promise_accept;
            client = tcp_socket->m_client;

            tcp_socket->m_promise_accept = nullptr;
            tcp_socket->m_client = nullptr;
        }
    }

    if (promise != nullptr) {
        lean_dec(promise);

        if (client != nullptr) {
            lean_dec(client);
        }

        lean_dec(socket);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.shutdown (socket : @& Socket) : IO (IO.Promise (Except IO.Error Unit)) */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_shutdown(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    auto on_shutdown = [](uv_shutdown_t* req, int status) {
        lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket((lean_object*)req->data);

        if (status < 0) {
            resolve_with_code(status, tcp_socket->m_promise_shutdown);
        } else {
            lean_promise_resolve(mk_except_ok(lean_box(0)), tcp_socket->m_promise_shutdown);
        }

        lean_dec(tcp_socket->m_promise_shutdown);

        tcp_socket->m_promise_shutdown = nullptr;

        lean_dec((lean_object*)req->data);
        free(req);
    };

    uv_shutdown_t* shutdown_req;
    lean_object* promise;
    int result;
    {
        // Locking early prevents potential parallelism issues setting the m_promise_shutdown.
        event_loop_guard guard;

        // `uv_shutdown` clears the writable flag right away, so a second request fails with `ENOTCONN`
        // no matter whether the first one is still pending; reject it here to report a meaningful error.
        if (tcp_socket->m_shutdown_requested) {
            return lean_io_result_mk_error(lean_mk_io_error_other_error(-UV_EALREADY, mk_string("shutdown already requested")));
        }

        shutdown_req = (uv_shutdown_t*)malloc(sizeof(uv_shutdown_t));
        if (shutdown_req == nullptr) {
            return io_result_mk_enomem();
        }
        shutdown_req->data = (void*)socket;

        promise = mk_mt_promise();
        tcp_socket->m_promise_shutdown = promise;
        lean_inc(promise);

        lean_inc(socket);

        result = uv_shutdown(shutdown_req, (uv_stream_t*)&tcp_socket->m_uv_tcp, on_shutdown);

        if (result < 0) {
            tcp_socket->m_promise_shutdown = nullptr;
        } else {
            tcp_socket->m_shutdown_requested = true;
        }
    }

    if (result < 0) {
        free(shutdown_req);

        lean_dec(promise); // The socket does not own it.
        lean_dec(promise); // We are not going to return it.
        lean_dec(socket);

        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(promise);
}

/* Std.Internal.UV.TCP.Socket.getPeerName (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getpeername(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    sockaddr_storage addr_storage;
    int addr_len = sizeof(addr_storage);

    int result;
    {
        event_loop_guard guard;
        result = uv_tcp_getpeername(&tcp_socket->m_uv_tcp, (struct sockaddr*)&addr_storage, &addr_len);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    lean_object* lean_addr = lean_sockaddr_to_socketaddress((struct sockaddr*)&addr_storage);

    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.TCP.Socket.getSockName (socket : @& Socket) : IO SocketAddress */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_getsockname(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    struct sockaddr_storage addr_storage;
    int addr_len = sizeof(addr_storage);

    int result;
    {
        event_loop_guard guard;
        result = uv_tcp_getsockname(&tcp_socket->m_uv_tcp, (struct sockaddr*)&addr_storage, &addr_len);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    lean_object* lean_addr = lean_sockaddr_to_socketaddress((struct sockaddr*)&addr_storage);
    return lean_io_result_mk_ok(lean_addr);
}

/* Std.Internal.UV.TCP.Socket.noDelay (socket : @& Socket) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_nodelay(b_obj_arg socket) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    int result;
    {
        event_loop_guard guard;
        result = uv_tcp_nodelay(&tcp_socket->m_uv_tcp, 1);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.UV.TCP.Socket.keepAlive (socket : @& Socket) (enable : Int8) (delay : UInt32) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, uint8_t enable, uint32_t delay) {
    lean_uv_tcp_socket_object* tcp_socket = lean_to_uv_tcp_socket(socket);

    int result;
    {
        event_loop_guard guard;
        // Lean passes `Int8` as `uint8_t`.
        result = uv_tcp_keepalive(&tcp_socket->m_uv_tcp, (int8_t)enable, delay);
    }

    if (result < 0) {
        return io_result_mk_uv_error(result);
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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_wait_acceptable(b_obj_arg socket) {
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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_tcp_keepalive(b_obj_arg socket, uint8_t enable, uint32_t delay) {
    lean_always_assert(
        false && ("Please build a version of Lean4 with libuv to invoke this.")
    );
}

#endif
}
