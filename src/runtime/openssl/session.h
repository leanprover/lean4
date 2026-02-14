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
#include <openssl/bio.h>
#endif

namespace lean {

static lean_external_class * g_ssl_session_external_class = nullptr;
void initialize_openssl_session();

#ifndef LEAN_EMSCRIPTEN
typedef struct {
    char * data;
    size_t size;
} lean_ssl_pending_write;

typedef struct {
    SSL * ssl;
    BIO * read_bio;
    BIO * write_bio;
    size_t pending_writes_count;
    lean_ssl_pending_write * pending_writes;
} lean_ssl_session_object;

static inline lean_object * lean_ssl_session_object_new(lean_ssl_session_object * s) { return lean_alloc_external(g_ssl_session_external_class, s); }
static inline lean_ssl_session_object * lean_to_ssl_session_object(lean_object * o) { return (lean_ssl_session_object*)(lean_get_external_data(o)); }
#endif

extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk(uint8_t is_server);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk_server();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_mk_client();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_configure_server_ctx(b_obj_arg cert_file, b_obj_arg key_file);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_configure_client_ctx(b_obj_arg ca_file, uint8_t verify_peer);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_set_server_name(b_obj_arg ssl, b_obj_arg host);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_verify_result(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_handshake(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_write(b_obj_arg ssl, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_read(b_obj_arg ssl, uint64_t max_bytes);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_feed_encrypted(b_obj_arg ssl, b_obj_arg data);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_drain_encrypted(b_obj_arg ssl);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_ssl_pending_encrypted(b_obj_arg ssl);

}
