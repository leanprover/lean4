/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>
#include "runtime/object.h"
#include "runtime/openssl/ssl_error.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#include <deque>
#include <vector>
#endif

namespace lean {

extern lean_external_class* g_ssl_session_external_class;
void initialize_openssl_session();

#ifndef LEAN_EMSCRIPTEN

// This object is not thread safe. Concurrent operations on the same session require external
// synchronization (e.g. a mutex).
struct lean_ssl_session_object {
    SSL* ssl = nullptr;

    // Plaintext OpenSSL would not take yet, replayed once the socket I/O it is waiting on completes.
    std::deque<std::vector<uint8_t>> pending_writes;

    // Total bytes `pending_writes` was given, so `lean_ssl_write` can bound the queue without
    // walking the deque. It tracks the queue only while the session is alive: `release_pending_writes`
    // frees the buffers of a finished session and deliberately leaves this standing, which is what
    // lets the teardown still report the plaintext that was accepted but never delivered.
    size_t pending_bytes = 0;

    // Set once `lean_ssl_feed_eof` has reported that no further encrypted input will arrive.
    bool input_eof = false;

    // Latched by `ssl_session_info_callback` once the handshake has completed. Sampling
    // `SSL_is_init_finished` instead would miss it: one `SSL_read` can both finish the handshake and
    // land back in init on a post-handshake message split across records, reading false either side.
    bool negotiated = false;

    // The verdict recorded once the session is finished; see `ssl_error_state`. Every later
    // `handshake`, `write`, `read`, `peek`, `feedEncrypted`, `setServerName` and `peerName` then
    // raises instead of driving a session that can no longer make progress. A zero-length
    // `feedEncrypted` is the one exemption: it asks the session to take nothing, so no state it
    // could be in makes that an error.
    ssl_error_state err{};
};

inline lean_object* lean_ssl_session_object_new(lean_ssl_session_object* s) { return lean_alloc_external(g_ssl_session_external_class, s); }
inline lean_ssl_session_object* lean_to_ssl_session_object(lean_object* o) { return (lean_ssl_session_object*)(lean_get_external_data(o)); }
#endif

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg ctx);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg ctx);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_peer_name(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg ssl, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg ssl, uint64_t max_bytes);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_peek(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_eof(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted_input(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg ssl);

}
