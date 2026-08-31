/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once

#include <lean/lean.h>
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/openssl.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/ssl.h>
#endif

namespace lean {

extern lean_external_class * g_ssl_context_external_class;
void initialize_openssl_context();

#ifndef LEAN_EMSCRIPTEN

// Drains the OpenSSL error queue and returns a single error message combining up to 10 entries.
lean_object * mk_openssl_error(char const * where, int ssl_err = 0);
inline lean_obj_res mk_openssl_io_error(char const * where, int ssl_err = 0) { return lean_io_result_mk_error(mk_openssl_error(where, ssl_err)); }
inline lean_object * lean_ssl_context_new(SSL_CTX * ctx) { return lean_alloc_external(g_ssl_context_external_class, ctx); }
inline SSL_CTX * lean_to_ssl_context(lean_object * o) { return (SSL_CTX*)lean_get_external_data(o); }
#endif

// =======================================
// Context Operations

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert, uint8_t cert_is_file,
    b_obj_arg key, uint8_t key_is_file);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg ca, uint8_t ca_is_file,
    uint8_t has_ca, uint8_t verify_peer, uint8_t trust_system_roots);

}
