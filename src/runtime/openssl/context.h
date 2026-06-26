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
#include <openssl/err.h>
#include <string>
#endif

namespace lean {

extern lean_external_class * g_ssl_context_external_class;
void initialize_openssl_context();

#ifndef LEAN_EMSCRIPTEN

// Structure for managing a single Context object.
typedef struct {
    SSL_CTX * ctx;
} lean_ssl_context_object;

// Drains the OpenSSL error queue and returns a single error message combining up to 10 entries.
lean_object * mk_openssl_error(char const * where, int ssl_err = 0);
static inline lean_obj_res mk_openssl_io_error(char const * where, int ssl_err = 0) { return lean_io_result_mk_error(mk_openssl_error(where, ssl_err)); }
static inline lean_object * lean_ssl_context_object_new(lean_ssl_context_object * c) { return lean_alloc_external(g_ssl_context_external_class, c); }
static inline lean_ssl_context_object * lean_to_ssl_context_object(lean_object * o) { return (lean_ssl_context_object*)(lean_get_external_data(o)); }
#endif

// =======================================
// Context Operations

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server();
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(uint8_t default_verify);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_server(b_obj_arg ctx, b_obj_arg cert_file, b_obj_arg key_file);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_client(b_obj_arg ctx, b_obj_arg ca_file, uint8_t verify_peer);
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_client_from_pem(b_obj_arg ctx, b_obj_arg ca_pem, uint8_t verify_peer);

}
