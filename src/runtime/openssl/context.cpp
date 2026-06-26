/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/context.h"
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <limits.h>

namespace lean {

lean_external_class * g_ssl_context_external_class = NULL;

#ifndef LEAN_EMSCRIPTEN

// This function drains at maximum 10 error messages from the Error queue.
lean_object * mk_openssl_error(char const * where, int ssl_err = 0) {
    std::string msg(where);

    if (ssl_err != 0) msg += " (ssl_error=" + std::to_string(ssl_err) + ")";

    // Drain up to 10 entries from the OpenSSL error queue; mark with "(truncated)" if more remain.
    unsigned long err;
    bool first = true;
    int cap = 10;

    while (cap-- > 0 && (err = ERR_get_error()) != 0) {
        char err_buf[256];
        ERR_error_string_n(err, err_buf, sizeof(err_buf));
        msg += first ? ": " : "; ";
        msg += err_buf;
        first = false;
    }

    if (!first && ERR_peek_error() != 0) {
        msg += "; ... (truncated)";
        ERR_clear_error();
    }

    return lean_mk_io_user_error(mk_string(msg.c_str()));
}

static void lean_ssl_context_finalizer(void * ptr) {
    lean_ssl_context_object * obj = (lean_ssl_context_object*)ptr;
    SSL_CTX_free(obj->ctx);
    free(obj);
}

void initialize_openssl_context() {
    g_ssl_context_external_class = lean_register_external_class(lean_ssl_context_finalizer, [](void * obj, lean_object * f) {
        (void)obj;
        (void)f;
    });
}

static bool configure_ctx_options(SSL_CTX * ctx) {
    SSL_CTX_set_options(ctx,
        // Disables TLS 1.2 renegotiation (SSL_OP_NO_RENEGOTIATION has no effect on
        // TLS 1.3, which replaced renegotiation with key updates).
        SSL_OP_NO_RENEGOTIATION |

        // Disables TLS compression. Mitigates the CRIME attack (compression leaks
        // secret bytes via ciphertext length). Already off by default in OpenSSL 1.1+
        // but set explicitly so the intent is clear.
        SSL_OP_NO_COMPRESSION |

        // Disables session tickets (TLS 1.2 RFC 5077 and TLS 1.3 PSK resumption).
        // This prevents 0-RTT session resumption but avoids stateful ticket
        // management complexity and removes one tracking vector in server deployments.
        // If session resumption performance matters, remove this flag and implement
        // a ticket key rotation strategy.
        SSL_OP_NO_TICKET
    );

    // Reject TLS 1.0 and 1.1. Both are deprecated (RFC 8996) and have known
    // protocol-level weaknesses (BEAST, POODLE). TLS 1.2 is the minimum acceptable
    // version; TLS 1.3 is preferred and used automatically when both peers support it.
    if (SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION) != 1) return false;

    // Allow SSL_write to be retried with a different pointer when the same
    // payload is copied into pending_writes and replayed after WANT_READ/WANT_WRITE.
    SSL_CTX_set_mode(ctx, SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER);
    return true;
}

static lean_obj_res mk_ssl_context(const SSL_METHOD * method, bool default_verify) {
    ERR_clear_error();

    SSL_CTX * ctx = SSL_CTX_new(method);

    if (ctx == nullptr) {
        return mk_openssl_io_error("SSL_CTX_new failed");
    }

    if (!configure_ctx_options(ctx)) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("SSL_CTX_set_min_proto_version failed");
    }

    if (default_verify) {

        // Secure default: verify the peer certificate against system trust anchors.
        // Callers that need to skip verification must call configure() with verifyPeer=false,
        // which calls SSL_CTX_set_verify(SSL_VERIFY_NONE) and overrides this setting.
        if (SSL_CTX_set_default_verify_paths(ctx) != 1) {
            SSL_CTX_free(ctx);
            return mk_openssl_io_error("SSL_CTX_set_default_verify_paths failed");
        }

        SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, nullptr);
    }

    lean_ssl_context_object * obj = (lean_ssl_context_object*)malloc(sizeof(lean_ssl_context_object));

    if (obj == nullptr) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("failed to allocate SSL context object");
    }

    obj->ctx = ctx;
    lean_object * lean_obj = lean_ssl_context_object_new(obj);
    lean_mark_mt(lean_obj);

    return lean_io_result_mk_ok(lean_obj);
}

/* Std.Internal.SSL.Context.Server.mk (defaultVerify : Bool) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(uint8_t default_verify) {
    return mk_ssl_context(TLS_server_method(), default_verify != 0);
}

/* Std.Internal.SSL.Context.Client.mk (defaultVerify : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(uint8_t default_verify) {
    // With default_verify set, the client verifies the peer against system trust anchors.
    return mk_ssl_context(TLS_client_method(), default_verify != 0);
}

/* Std.Internal.SSL.Context.Server.configure (ctx : @& Context.Server) (certFile keyFile : @& String) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_server(b_obj_arg ctx_obj, b_obj_arg cert_file, b_obj_arg key_file) {
    ERR_clear_error();

    lean_ssl_context_object * obj = lean_to_ssl_context_object(ctx_obj);
    const char * cert = lean_string_cstr(cert_file);
    const char * key = lean_string_cstr(key_file);

    // use_certificate_chain_file loads the leaf + any intermediates from the PEM file,
    // so clients receive the full chain and can build OCSP cert IDs without a separate CA fetch.
    if (SSL_CTX_use_certificate_chain_file(obj->ctx, cert) <= 0) {
        return mk_openssl_io_error("SSL_CTX_use_certificate_chain_file failed");
    }

    if (SSL_CTX_use_PrivateKey_file(obj->ctx, key, SSL_FILETYPE_PEM) <= 0) {
        return mk_openssl_io_error("SSL_CTX_use_PrivateKey_file failed");
    }

    if (SSL_CTX_check_private_key(obj->ctx) != 1) {
        return mk_openssl_io_error("SSL_CTX_check_private_key failed");
    }

    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Context.Client.configure (ctx : @& Context.Client) (caFile : @& String) (verifyPeer : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_client(b_obj_arg ctx_obj, b_obj_arg ca_file, uint8_t verify_peer) {
    ERR_clear_error();

    lean_ssl_context_object * obj = lean_to_ssl_context_object(ctx_obj);
    const char * ca = lean_string_cstr(ca_file);

    if (ca != nullptr && ca[0] != '\0') {
        if (SSL_CTX_load_verify_locations(obj->ctx, ca, nullptr) != 1) {
            return mk_openssl_io_error("SSL_CTX_load_verify_locations failed");
        }
    } else if (verify_peer) {
        if (SSL_CTX_set_default_verify_paths(obj->ctx) != 1) {
            return mk_openssl_io_error("SSL_CTX_set_default_verify_paths failed");
        }
    }

    SSL_CTX_set_verify(obj->ctx, verify_peer ? SSL_VERIFY_PEER : SSL_VERIFY_NONE, nullptr);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Std.Internal.SSL.Context.Client.configureFromPEM (ctx : @& Context.Client) (caPEM : @& String) (verifyPeer : Bool) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_client_from_pem(b_obj_arg ctx_obj, b_obj_arg ca_pem, uint8_t verify_peer) {
    ERR_clear_error();

    lean_ssl_context_object * obj = lean_to_ssl_context_object(ctx_obj);
    const char * pem = lean_string_cstr(ca_pem);
    size_t pem_size = lean_string_size(ca_pem) - 1;

    if (pem_size == 0) {
        if (!verify_peer) {
            SSL_CTX_set_verify(obj->ctx, SSL_VERIFY_NONE, nullptr);
            return lean_io_result_mk_ok(lean_box(0));
        }

        X509_STORE * store = X509_STORE_new();
        if (store == nullptr) {
            return mk_openssl_io_error("X509_STORE_new failed");
        }

        if (X509_STORE_set_default_paths(store) != 1) {
            X509_STORE_free(store);
            return mk_openssl_io_error("X509_STORE_set_default_paths failed");
        }

        SSL_CTX_set_cert_store(obj->ctx, store);
        SSL_CTX_set_verify(obj->ctx, SSL_VERIFY_PEER, nullptr);
        return lean_io_result_mk_ok(lean_box(0));
    }

    if (pem_size > INT_MAX) {
        return mk_openssl_io_error("CA PEM string is too large");
    }

    // Without peer verification the supplied CA certificates would never be consulted, so skip
    // parsing them and just disable verification (mirrors the empty-PEM and file-based paths).
    if (!verify_peer) {
        SSL_CTX_set_verify(obj->ctx, SSL_VERIFY_NONE, nullptr);
        return lean_io_result_mk_ok(lean_box(0));
    }

    BIO * bio = BIO_new_mem_buf(pem, (int)pem_size);

    if (bio == nullptr) {
        return mk_openssl_io_error("BIO_new_mem_buf failed");
    }

    STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, nullptr, nullptr);

    BIO_free(bio);

    if (infos == nullptr) {
        return mk_openssl_io_error("PEM_X509_INFO_read_bio failed");
    }

    // Store so we can rollback in case something fails!
    X509_STORE * store = X509_STORE_new();

    if (store == nullptr) {
        sk_X509_INFO_pop_free(infos, X509_INFO_free);
        return mk_openssl_io_error("X509_STORE_new failed");
    }

    // A non-empty CA bundle pins trust to exactly these certificates; system trust anchors are
    // intentionally not added, matching the file-based `configure` ("only this CA") behavior.
    int cert_count = 0;

    for (int i = 0; i < sk_X509_INFO_num(infos); i++) {
        X509_INFO * info = sk_X509_INFO_value(infos, i);
        if (info->x509 == nullptr) continue;
        cert_count++;

        if (X509_STORE_add_cert(store, info->x509) != 1) {
            unsigned long err = ERR_peek_last_error();
            if (ERR_GET_LIB(err) == ERR_LIB_X509 && ERR_GET_REASON(err) == X509_R_CERT_ALREADY_IN_HASH_TABLE) {
                ERR_clear_error();
                continue;
            }

            sk_X509_INFO_pop_free(infos, X509_INFO_free);
            X509_STORE_free(store);
            return mk_openssl_io_error("X509_STORE_add_cert failed");
        }
    }

    sk_X509_INFO_pop_free(infos, X509_INFO_free);

    if (cert_count == 0) {
        X509_STORE_free(store);
        return mk_openssl_io_error("no certificates found in CA PEM");
    }

    SSL_CTX_set_cert_store(obj->ctx, store);
    SSL_CTX_set_verify(obj->ctx, SSL_VERIFY_PEER, nullptr);
    return lean_io_result_mk_ok(lean_box(0));
}

#else

void initialize_openssl_context() {}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(uint8_t /*default_verify*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(uint8_t /*default_verify*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_server(b_obj_arg /*ctx_obj*/, b_obj_arg /*cert_file*/, b_obj_arg /*key_file*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_client(b_obj_arg /*ctx_obj*/, b_obj_arg /*ca_file*/, uint8_t /*verify_peer*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_configure_client_from_pem(b_obj_arg /*ctx_obj*/, b_obj_arg /*ca_pem*/, uint8_t /*verify_peer*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

#endif

}
