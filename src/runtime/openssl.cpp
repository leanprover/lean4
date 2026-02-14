/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/openssl.h"
#include "runtime/io.h"

#include <mutex>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/opensslv.h>
#include <openssl/err.h>

namespace lean {

static std::once_flag g_openssl_init_once;
static SSL_CTX * g_ssl_server_ctx = nullptr;
static SSL_CTX * g_ssl_client_ctx = nullptr;

static void configure_ctx_common(SSL_CTX * ctx) {
    SSL_CTX_set_mode(ctx, SSL_MODE_AUTO_RETRY);

    #ifdef SSL_OP_NO_RENEGOTIATION
    SSL_CTX_clear_options(ctx, SSL_OP_NO_RENEGOTIATION);
    #endif
    #ifdef SSL_OP_ALLOW_CLIENT_RENEGOTIATION
    SSL_CTX_set_options(ctx, SSL_OP_ALLOW_CLIENT_RENEGOTIATION);
    #endif
}

static void initialize_openssl_once() {
    if (OPENSSL_init_ssl(0, nullptr) != 1) {
        lean_internal_panic("failed to initialize OpenSSL");
    }

    g_ssl_server_ctx = SSL_CTX_new(TLS_server_method());
    g_ssl_client_ctx = SSL_CTX_new(TLS_client_method());

    if (g_ssl_server_ctx == nullptr || g_ssl_client_ctx == nullptr) {
        if (g_ssl_server_ctx != nullptr) SSL_CTX_free(g_ssl_server_ctx);
        if (g_ssl_client_ctx != nullptr) SSL_CTX_free(g_ssl_client_ctx);
        g_ssl_server_ctx = nullptr;
        g_ssl_client_ctx = nullptr;
        lean_internal_panic("failed to create OpenSSL SSL_CTX pair");
    }

    configure_ctx_common(g_ssl_server_ctx);
    configure_ctx_common(g_ssl_client_ctx);
}

void initialize_openssl() {
    std::call_once(g_openssl_init_once, initialize_openssl_once);
}

void finalize_openssl() {
    if (g_ssl_server_ctx != nullptr) {
        SSL_CTX_free(g_ssl_server_ctx);
        g_ssl_server_ctx = nullptr;
    }
    if (g_ssl_client_ctx != nullptr) {
        SSL_CTX_free(g_ssl_client_ctx);
        g_ssl_client_ctx = nullptr;
    }
}

SSL_CTX * get_openssl_server_ctx() {
    initialize_openssl();
    return g_ssl_server_ctx;
}

SSL_CTX * get_openssl_client_ctx() {
    initialize_openssl();
    return g_ssl_client_ctx;
}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(OPENSSL_VERSION_NUMBER);
}

#else

namespace lean {

void initialize_openssl() {}
void finalize_openssl() {}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_box(0);
}

#endif
