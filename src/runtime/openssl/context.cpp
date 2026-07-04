/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/context.h"
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <limits.h>

#if defined(__APPLE__)
#include <Security/Security.h>
#include <CoreFoundation/CoreFoundation.h>
#elif defined(_WIN32)
#include <windows.h>
#include <wincrypt.h>
// wincrypt.h defines these as object-like macros that collide with OpenSSL's identically named
// types (e.g. X509_NAME). We only need the certificate-store API from it, so drop the macros; the
// OpenSSL types were already declared by the headers above and remain intact.
#undef X509_NAME
#undef X509_EXTENSIONS
#undef X509_CERT_PAIR
#undef PKCS7_ISSUER_AND_SERIAL
#undef PKCS7_SIGNER_INFO
#undef OCSP_REQUEST
#undef OCSP_RESPONSE
#endif

namespace lean {

lean_external_class * g_ssl_context_external_class = NULL;

#ifndef LEAN_EMSCRIPTEN

lean_object * mk_openssl_error(char const * where, int ssl_err) {
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

    // Disable the internal session cache as well. SSL_OP_NO_TICKET only suppresses ticket-based
    // resumption (RFC 5077 and TLS 1.3 PSK); a TLS 1.2 server still offers session-ID resumption
    // through the cache, which defaults to SSL_SESS_CACHE_SERVER. Turning the cache off makes the
    // "no session resumption" guarantee hold for both client and server contexts.
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);

    // Reject TLS 1.0 and 1.1. Both are deprecated (RFC 8996) and have known
    // protocol-level weaknesses (BEAST, POODLE). TLS 1.2 is the minimum acceptable
    // version; TLS 1.3 is preferred and used automatically when both peers support it.
    if (SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION) != 1) return false;

    // Permit retrying SSL_write() after WANT_READ/WANT_WRITE with the payload at a moved buffer
    // address (its contents must stay identical). This lets a session layer relocate a buffered
    // write between retries without tripping OpenSSL's buffer-stability check.
    SSL_CTX_set_mode(ctx, SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER);

    // Secure hostname-matching default, inherited by every session (SSL) created from this context.
    // It is inert until a peer hostname is bound per-connection via SSL_set1_host in the session
    // layer; recording it here ensures that check, once wired, rejects partial wildcards such as
    // `f*.example.com` (disallowed by RFC 6125 §6.4.3).
    X509_VERIFY_PARAM_set_hostflags(SSL_CTX_get0_param(ctx), X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS);
    return true;
}

// Loads the platform's system root certificates into the context's trust store so clients verify
// public servers out of the box (like a browser), independent of where OpenSSL was built to look
// for its default certificate bundle.
static bool load_system_trust_store(SSL_CTX * ctx) {
#if defined(_WIN32)
    if (ctx == nullptr) return false;

    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    if (store == nullptr) return false;

    HCERTSTORE win_store = CertOpenSystemStoreA(0, "ROOT");
    if (win_store == nullptr) {
        return false;
    }

    PCCERT_CONTEXT cert = nullptr;
    while ((cert = CertEnumCertificatesInStore(win_store, cert)) != nullptr) {
        const unsigned char * data = cert->pbCertEncoded;

        X509 * x509 = d2i_X509(
            nullptr,
            &data,
            static_cast<long>(cert->cbCertEncoded)
        );

        if (x509 == nullptr) {
            continue;
        }

        X509_STORE_add_cert(store, x509);
        X509_free(x509);
    }

    CertCloseStore(win_store, 0);

    // Ignore duplicate-cert errors left in OpenSSL's error queue.
    ERR_clear_error();
    return true;
#elif defined(__APPLE__)
    // On macOS OpenSSL's compiled-in default paths usually don't point at the Keychain, so pull the
    // trusted anchor certificates directly from the Security framework instead.
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    if (store == nullptr) return false;

    CFArrayRef anchors = nullptr;
    if (SecTrustCopyAnchorCertificates(&anchors) != errSecSuccess || anchors == nullptr) {
        return false;
    }

    for (CFIndex i = 0, n = CFArrayGetCount(anchors); i < n; i++) {
        SecCertificateRef cert = (SecCertificateRef)CFArrayGetValueAtIndex(anchors, i);
        if (cert == nullptr) continue;

        CFDataRef der = SecCertificateCopyData(cert);
        if (der == nullptr) continue;

        const unsigned char * data = CFDataGetBytePtr(der);
        X509 * x509 = d2i_X509(nullptr, &data, CFDataGetLength(der));
        CFRelease(der);
        if (x509 == nullptr) continue;

        // X509_STORE_add_cert bumps the certificate's refcount, so drop our own reference after.
        // Duplicate anchors are harmless and ignored.
        X509_STORE_add_cert(store, x509);
        X509_free(x509);
    }

    CFRelease(anchors);
    // Drop any "already in hash table" errors left by duplicate anchors so they don't leak into a
    // later error message.
    ERR_clear_error();
    return true;
#else
    // Linux/BSD (and any other platform): OpenSSL's default verify paths already resolve to the
    // system certificate bundle.
    return SSL_CTX_set_default_verify_paths(ctx) == 1;
#endif
}

// Creates an SSL_CTX with the hardened options shared by all contexts. Returns nullptr and stores
// an IO error in *err on failure.
static SSL_CTX * mk_ssl_ctx_base(const SSL_METHOD * method, lean_obj_res * err) {
    ERR_clear_error();

    SSL_CTX * ctx = SSL_CTX_new(method);

    if (ctx == nullptr) {
        *err = mk_openssl_io_error("SSL_CTX_new failed");
        return nullptr;
    }

    if (!configure_ctx_options(ctx)) {
        SSL_CTX_free(ctx);
        *err = mk_openssl_io_error("SSL_CTX_set_min_proto_version failed");
        return nullptr;
    }

    return ctx;
}

// Wraps a fully configured SSL_CTX into a Lean external object, taking ownership of ctx.
static lean_obj_res wrap_ssl_context(SSL_CTX * ctx) {
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

/* Std.Internal.SSL.Context.Server.mk (certFile keyFile : @& String) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert_file, b_obj_arg key_file) {
    lean_obj_res err = nullptr;
    // The server presents its certificate but never authenticates the client (no mutual TLS).
    SSL_CTX * ctx = mk_ssl_ctx_base(TLS_server_method(), &err);
    if (ctx == nullptr) return err;

    const char * cert = lean_string_cstr(cert_file);
    const char * key = lean_string_cstr(key_file);

    // Load the leaf certificate plus any intermediates from the PEM file (unlike
    // SSL_CTX_use_certificate_file, which loads only the leaf), so the server presents the full
    // chain and clients can build a path to a trusted root.
    if (SSL_CTX_use_certificate_chain_file(ctx, cert) <= 0) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("SSL_CTX_use_certificate_chain_file failed");
    }

    if (SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) <= 0) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("SSL_CTX_use_PrivateKey_file failed");
    }

    if (SSL_CTX_check_private_key(ctx) != 1) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("SSL_CTX_check_private_key failed");
    }

    return wrap_ssl_context(ctx);
}

/* Std.Internal.SSL.Context.Client.mk (caFile : @& String) (verifyPeer : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg ca_file, uint8_t verify_peer) {
    lean_obj_res err = nullptr;
    SSL_CTX * ctx = mk_ssl_ctx_base(TLS_client_method(), &err);
    if (ctx == nullptr) return err;

    if (!verify_peer) {
        SSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(ctx);
    }

    // Trust the platform's system roots (so public servers verify out of the box, like a browser),
    // then add the caller's CA file on top if one was supplied. The supplied CA is additive: it
    // never replaces the system trust anchors.
    if (!load_system_trust_store(ctx)) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("failed to load system trust store");
    }

    const char * ca = lean_string_cstr(ca_file);

    if (ca[0] != '\0') {
        if (SSL_CTX_load_verify_locations(ctx, ca, nullptr) != 1) {
            SSL_CTX_free(ctx);
            return mk_openssl_io_error("SSL_CTX_load_verify_locations failed");
        }
    }

    SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(ctx);
}

/* Std.Internal.SSL.Context.Client.mkFromPEM (caPEM : @& String) (verifyPeer : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client_from_pem(b_obj_arg ca_pem, uint8_t verify_peer) {
    lean_obj_res err = nullptr;
    SSL_CTX * ctx = mk_ssl_ctx_base(TLS_client_method(), &err);
    if (ctx == nullptr) return err;

    // Without peer verification the supplied CA certificates would never be consulted, so skip
    // parsing them and just disable verification (mirrors the file-based `mk`).
    if (!verify_peer) {
        SSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(ctx);
    }

    // Trust the platform's system roots; any PEM certificates below are added on top of them.
    if (!load_system_trust_store(ctx)) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("failed to load system trust store");
    }

    const char * pem = lean_string_cstr(ca_pem);
    size_t pem_size = lean_string_size(ca_pem) - 1;

    // An empty PEM leaves the client with just the system trust anchors.
    if (pem_size == 0) {
        SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, nullptr);
        return wrap_ssl_context(ctx);
    }

    if (pem_size > INT_MAX) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("CA PEM string is too large");
    }

    BIO * bio = BIO_new_mem_buf(pem, (int)pem_size);

    if (bio == nullptr) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("BIO_new_mem_buf failed");
    }

    STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, nullptr, nullptr);

    BIO_free(bio);

    if (infos == nullptr) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("PEM_X509_INFO_read_bio failed");
    }

    // Add the parsed certificates to the context's verification store, which already holds the
    // system roots; the store is owned by the context, so it must not be freed here.
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    int cert_count = 0;

    for (int i = 0; i < sk_X509_INFO_num(infos); i++) {
        X509_INFO * info = sk_X509_INFO_value(infos, i);
        if (info->x509 == nullptr) continue;
        cert_count++;

        if (X509_STORE_add_cert(store, info->x509) != 1) {
            unsigned long err_code = ERR_peek_last_error();
            if (ERR_GET_LIB(err_code) == ERR_LIB_X509 && ERR_GET_REASON(err_code) == X509_R_CERT_ALREADY_IN_HASH_TABLE) {
                ERR_clear_error();
                continue;
            }

            sk_X509_INFO_pop_free(infos, X509_INFO_free);
            SSL_CTX_free(ctx);
            return mk_openssl_io_error("X509_STORE_add_cert failed");
        }
    }

    sk_X509_INFO_pop_free(infos, X509_INFO_free);

    if (cert_count == 0) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("no certificates found in CA PEM");
    }

    SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(ctx);
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
