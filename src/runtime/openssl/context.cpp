/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/context.h"
#include "runtime/openssl/trust_store.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <climits>
#include <cstring>
#include <memory>
#include <string>

#endif

namespace lean {

lean_external_class * g_ssl_context_external_class = nullptr;

#ifndef LEAN_EMSCRIPTEN

static lean_obj_res reject_embedded_nul(b_obj_arg path) {
    return strlen(lean_string_cstr(path)) == lean_string_size(path) - 1
        ? nullptr
        : mk_embedded_nul_error(path);
}

static int reject_encrypted_pem(char *, int, int, void *) { return -1; }

struct ssl_ctx_deleter { void operator()(SSL_CTX * ctx) const { SSL_CTX_free(ctx); } };

// Owns a context while it is still being built, so no error path has to remember to free it.
using ssl_ctx_ptr = std::unique_ptr<SSL_CTX, ssl_ctx_deleter>;

void initialize_openssl_context() {
    g_ssl_context_external_class = lean_register_external_class(
        [](void * ptr) { SSL_CTX_free((SSL_CTX*)ptr); }, [](void *, lean_object *) {});
}

// Applies the hardened options every context shares. The minimum protocol version is left to the
// caller, since it is the only one whose failure is worth reporting.
static void configure_ctx_options(SSL_CTX * ctx) {
    SSL_CTX_set_options(ctx,
        // No effect on TLS 1.3, which replaced renegotiation with key updates.
        SSL_OP_NO_RENEGOTIATION |

        // Mitigates CRIME, where compression leaks secret bytes via ciphertext length. Already the
        // default since OpenSSL 1.1, but set explicitly so the intent is clear.
        SSL_OP_NO_COMPRESSION |

        // Disables RFC 5077 session tickets in TLS 1.2. In TLS 1.3 it only downgrades them to the
        // stateful form; the call below is what stops those being sent.
        SSL_OP_NO_TICKET
    );

    // Without this a TLS 1.3 server still puts two NewSessionTickets on the wire per connection.
    // Read only by the server state machine.
    SSL_CTX_set_num_tickets(ctx, 0);

    // Covers the certificate chain and the private key. A CA bundle is read through a bare BIO
    // rather than the context, so `load_ca_bundle` has to pass the same callback itself.
    SSL_CTX_set_default_passwd_cb(ctx, reject_encrypted_pem);

    // Backs the flags above: a TLS 1.2 server still offers session-ID resumption through this cache,
    // which defaults to SSL_SESS_CACHE_SERVER. The client half of the mask is already off there.
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);

    // Lets a session layer relocate a buffered write between SSL_write() retries, as long as its
    // contents stay identical, without tripping OpenSSL's buffer-stability check.
    SSL_CTX_set_mode(ctx, SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER);

    // Inherited by every session, and inert until the session layer binds a peer hostname with
    // SSL_set1_host; that check then rejects partial wildcards like `f*.example.com` (RFC 9525
    // §6.3, which obsoletes RFC 6125 — the latter still permitted them).
    X509_VERIFY_PARAM_set_hostflags(SSL_CTX_get0_param(ctx), X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS);
}

// Creates a configured SSL_CTX, or returns nullptr with an IO error stored in `*err`.
static ssl_ctx_ptr mk_ssl_ctx_base(const SSL_METHOD * method, lean_obj_res * err) {
    ERR_clear_error();

    if (!ensure_openssl_initialized()) {
        *err = mk_openssl_io_error("OPENSSL_init_ssl failed");
        return nullptr;
    }

    ssl_ctx_ptr ctx(SSL_CTX_new(method));

    if (ctx == nullptr) {
        *err = mk_openssl_io_error("SSL_CTX_new failed");
        return nullptr;
    }

    configure_ctx_options(ctx.get());

    if (SSL_CTX_set_min_proto_version(ctx.get(), TLS1_2_VERSION) != 1) {
        *err = mk_openssl_io_error("SSL_CTX_set_min_proto_version failed");
        return nullptr;
    }

    return ctx;
}

// Wraps a fully configured SSL_CTX into a Lean external object, taking ownership of it.
static lean_obj_res wrap_ssl_context(ssl_ctx_ptr ctx) {
    lean_object * obj = lean_ssl_context_new(ctx.release());
    lean_mark_mt(obj);

    return lean_io_result_mk_ok(obj);
}

// Loads the certificate chain the server presents and the key it signs with, from paths the caller
// has passed through `reject_embedded_nul`.
static lean_obj_res load_server_credentials(SSL_CTX * ctx, b_obj_arg cert_file, b_obj_arg key_file) {
    ERR_clear_error();

    if (SSL_CTX_use_certificate_chain_file(ctx, lean_string_cstr(cert_file)) <= 0) {
        return mk_ssl_file_error(cert_file, rejected_by_security_level()
            ? "the certificate is rejected by the TLS security level (key too small or signature "
              "digest too weak)"
            : "could not read a PEM certificate chain");
    }

    ERR_clear_error();

    char const * mismatch = "the private key does not match the certificate";

    if (SSL_CTX_use_PrivateKey_file(ctx, lean_string_cstr(key_file), SSL_FILETYPE_PEM) <= 0) {
        return mk_ssl_file_error(key_file, ERR_GET_LIB(ERR_peek_last_error()) == ERR_LIB_X509
            ? mismatch
            : "could not read an unencrypted PEM private key");
    }

    ERR_clear_error();

    if (SSL_CTX_check_private_key(ctx) != 1) return mk_ssl_file_error(key_file, mismatch);

    return nullptr;
}

/* Std.Internal.SSL.Context.Server.mk (certFile keyFile : @& String) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert_file, b_obj_arg key_file) {
    if (lean_obj_res err = reject_embedded_nul(cert_file)) return err;
    if (lean_obj_res err = reject_embedded_nul(key_file)) return err;

    lean_obj_res base_err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_server_method(), &base_err);
    if (ctx == nullptr) return base_err;

    // The server presents its certificate but never authenticates the client (no mutual TLS).
    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);

    if (lean_obj_res err = load_server_credentials(ctx.get(), cert_file, key_file)) return err;

    return wrap_ssl_context(std::move(ctx));
}

// Shared skeleton of the client constructors; `load_ca` returns nullptr or an IO error to propagate.
template<typename LoadCA>
static lean_obj_res mk_client_ctx(uint8_t verify_peer, LoadCA load_ca) {
    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_client_method(), &err);
    if (ctx == nullptr) return err;

    // With verification off the CA material is never consulted.
    if (!verify_peer) {
        SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(std::move(ctx));
    }

    std::string detail;

    if (!load_system_trust_store(ctx.get(), &detail)) {
        std::string msg("failed to load system trust store");
        if (!detail.empty()) msg += ": " + detail;

        return lean_io_result_mk_error(mk_openssl_error(msg.c_str()));
    }

    // The caller's own CAs are added on top of the platform anchors, not in place of them.
    if (lean_obj_res ca_err = load_ca(ctx.get())) return ca_err;

    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(std::move(ctx));
}

// Adds every certificate `bio` yields to the trust store, on top of the system anchors already there,
// and frees `bio`.
template<typename MkErr>
static lean_obj_res load_ca_bundle(SSL_CTX * ctx, BIO * bio, char const * unreadable, char const * no_certs, MkErr mk_err) {
    if (bio == nullptr) return mk_err(unreadable);

    STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, reject_encrypted_pem, nullptr);
    BIO_free(bio);

    if (infos == nullptr) return mk_err(unreadable);

    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    lean_obj_res err = nullptr;
    int cert_count = 0;

    for (int i = 0, n = sk_X509_INFO_num(infos); i < n; i++) {
        X509 * cert = sk_X509_INFO_value(infos, i)->x509;

        if (cert == nullptr) continue;
        cert_count++;

        if (X509_STORE_add_cert(store, cert) != 1) {
            err = mk_openssl_io_error("X509_STORE_add_cert failed");
            break;
        }
    }

    sk_X509_INFO_pop_free(infos, X509_INFO_free);

    if (err != nullptr) return err;
    if (cert_count == 0) return mk_err(no_certs);

    return nullptr;
}

/* Std.Internal.SSL.Context.Client.mkImpl (caFile : @& String) (verifyPeer : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg ca_file, uint8_t verify_peer) {
    if (lean_obj_res err = reject_embedded_nul(ca_file)) return err;

    return mk_client_ctx(verify_peer, [&](SSL_CTX * ctx) -> lean_obj_res {
        const char * ca = lean_string_cstr(ca_file);

        // An empty CA path leaves the client with just the system trust anchors.
        if (ca[0] == '\0') return nullptr;

        return load_ca_bundle(ctx, BIO_new_file(ca, "r"),
            "could not read PEM CA certificates", "the CA file contains no certificates",
            [&](char const * msg) { return mk_ssl_file_error(ca_file, msg); });
    });
}

/* Std.Internal.SSL.Context.Client.mkFromPEM (caPEM : @& String) (verifyPeer : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client_from_pem(b_obj_arg ca_pem, uint8_t verify_peer) {
    return mk_client_ctx(verify_peer, [&](SSL_CTX * ctx) -> lean_obj_res {
        const char * pem = lean_string_cstr(ca_pem);
        size_t pem_size = lean_string_size(ca_pem) - 1;

        if (pem_size == 0) return nullptr;
        if (pem_size > INT_MAX) return mk_ssl_invalid_argument("the CA PEM string is too large");

        return load_ca_bundle(ctx, BIO_new_mem_buf(pem, (int)pem_size),
            "could not read PEM CA certificates from the given string",
            "the given CA PEM string contains no certificates",
            mk_ssl_invalid_argument);
    });
}

#else

void initialize_openssl_context() {}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg /*cert_file*/, b_obj_arg /*key_file*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg /*ca_file*/, uint8_t /*verify_peer*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client_from_pem(b_obj_arg /*ca_pem*/, uint8_t /*verify_peer*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

#endif

}
