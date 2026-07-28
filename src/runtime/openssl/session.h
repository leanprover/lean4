/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/openssl/context.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#endif

#include <deque>
#include <vector>

namespace lean {

extern lean_external_class * g_ssl_session_external_class;
void initialize_openssl_session();

#ifndef LEAN_EMSCRIPTEN

// This object is not thread safe. Concurrent operations on the same session require external
// synchronization (e.g. a mutex).
struct lean_ssl_session_object {
    SSL * ssl;
    std::deque<std::vector<char>> * pending_writes;
};

static inline lean_object * lean_ssl_session_object_new(lean_ssl_session_object * s) { return lean_alloc_external(g_ssl_session_external_class, s); }
static inline lean_ssl_session_object * lean_to_ssl_session_object(lean_object * o) { return (lean_ssl_session_object*)(lean_get_external_data(o)); }
#endif

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_server(b_obj_arg ctx);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_mk_client(b_obj_arg ctx);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_verify_result_string(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_handshake(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_write(b_obj_arg ssl, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_read(b_obj_arg ssl, uint64_t max_bytes);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_drain_encrypted(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_encrypted(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_pending_plaintext(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_close_notify(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_negotiated_version(b_obj_arg ssl);

}
