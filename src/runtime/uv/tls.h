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
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#endif

namespace lean {

static lean_external_class* g_uv_tls_socket_external_class = NULL;
void initialize_libuv_tls_socket();

#ifndef LEAN_EMSCRIPTEN

// Forward declarations
typedef struct lean_tls_uv_connection_state lean_tls_uv_connection_state_t;

// Protocol callback interface for handling connection events and data
typedef struct {
    lean_tls_uv_connection_state_t* (*create_connection)(uv_tcp_t* connection);
    int (*connection_established)(lean_tls_uv_connection_state_t* connection);
    void (*connection_closed)(lean_tls_uv_connection_state_t* connection, int status);
    int (*read)(lean_tls_uv_connection_state_t* connection, void* buf, ssize_t nread);
} lean_connection_handler_t;

// Shared state structure for TLS operations
typedef struct {
    SSL_CTX*                        ctx;                 // OpenSSL context for TLS
    uv_loop_t*                      loop;                // LibUV event loop
    lean_connection_handler_t.      protocol;            // Protocol callback handlers
    lean_tls_uv_connection_state_t* pending_writes;      // Queue of connections with pending writes
    int                             is_server;           // Flag: 1 for server mode, 0 for client mode
} lean_tls_uv_state_t;

// Per-connection state for TLS socket
typedef struct lean_tls_uv_connection_state {
    lean_tls_uv_state_t* state;           // Reference to shared state
    uv_tcp_t*            handle;          // LibUV TCP handle
    SSL*                 ssl;             // OpenSSL connection context
    BIO*                 read;            // BIO for reading encrypted data
    BIO*                 write;           // BIO for writing encrypted data

    // Lean-specific promise and buffer management
    lean_object* m_promise_connect;  // Promise for connection establishment
    lean_object* m_promise_read;     // Promise for read operations
    lean_object* m_promise_write;    // Promise for write operations
    lean_object* m_promise_shutdown; // Promise for shutdown operations
    lean_object* m_byte_array;       // Buffer for storing received data

    // Pending writes queue state
    struct {
        lean_tls_uv_connection_state_t** prev_holder;            // Pointer to previous connection's next pointer
        lean_tls_uv_connection_state_t*  next;                   // Next connection in queue
        int                               in_queue;              // Flag: is this connection queued?
        size_t                            pending_writes_count;  // Number of pending write buffers
        uv_buf_t*                         pending_writes_buffer; // Array of pending write buffers
    } pending;
} lean_tls_uv_connection_state_t;

// Structure for managing a single TLS socket object at the Lean level
typedef struct {
    lean_tls_uv_connection_state_t* connection; // TLS connection state
    lean_tls_uv_state_t*            state;      // Shared TLS state
} lean_uv_tls_socket_object;

// =======================================
// TLS socket object manipulation functions
static inline lean_object* lean_uv_tls_socket_new(lean_uv_tls_socket_object* s) {
    return lean_alloc_external(g_uv_tls_socket_external_class, s);
}

static inline lean_uv_tls_socket_object* lean_to_uv_tls_socket(lean_object* o) {
    return (lean_uv_tls_socket_object*)(lean_get_external_data(o));
}

#endif

// =======================================
// TLS Socket Operations (Lean API)

// Create a new TLS socket (client mode)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_new();

// Create a new TLS socket with custom SSL context
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_new_with_context(b_obj_arg ssl_ctx);

// Connect to a remote TLS server
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_connect(b_obj_arg socket, b_obj_arg addr, b_obj_arg hostname);

// Send data over TLS connection
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_send(b_obj_arg socket, obj_arg data_array);

// Receive data from TLS connection
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_recv(b_obj_arg socket, uint64_t buffer_size);

// Wait for socket to become readable
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_wait_readable(b_obj_arg socket);

// Cancel pending recv operation
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_cancel_recv(b_obj_arg socket);

// Bind TLS socket to local address (server mode)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_bind(b_obj_arg socket, b_obj_arg addr);

// Start listening for TLS connections (server mode)
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_listen(b_obj_arg socket, int32_t backlog, b_obj_arg cert_file, b_obj_arg key_file);

// Accept incoming TLS connection
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_accept(b_obj_arg socket);

// Cancel pending accept operation
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_cancel_accept(b_obj_arg socket);

// Try to accept connection without blocking
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_try_accept(b_obj_arg socket);

// Shutdown TLS connection gracefully
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_shutdown(b_obj_arg socket);

// =======================================
// TLS Socket Utility Functions

// Get remote peer address
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_getpeername(b_obj_arg socket);

// Get local socket address
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_getsockname(b_obj_arg socket);

// Enable/disable Nagle's algorithm on underlying TCP socket
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_nodelay(b_obj_arg socket);

// Configure TCP keepalive on underlying socket
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_keepalive(b_obj_arg socket, int32_t enable, uint32_t delay);

// Get peer certificate information
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_get_peer_certificate(b_obj_arg socket);

// Get cipher information for current connection
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_get_cipher_info(b_obj_arg socket);

// Verify peer certificate
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_verify_peer_certificate(b_obj_arg socket);

// =======================================
// SSL Context Configuration Functions

// Create a new SSL context for client
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_ctx_new_client();

// Create a new SSL context for server
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_ctx_new_server(b_obj_arg cert_file, b_obj_arg key_file);

// Load CA certificates for verification
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_ctx_load_verify_locations(b_obj_arg ctx, b_obj_arg ca_file, b_obj_arg ca_path);

// Set verification mode
extern "C" LEAN_EXPORT lean_obj_res lean_uv_tls_ctx_set_verify_mode(b_obj_arg ctx, int32_t mode, int32_t depth);

}
