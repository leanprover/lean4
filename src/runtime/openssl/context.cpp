/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/context.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <cerrno>
#include <climits>
#include <cstring>
#include <string>

#if defined(__APPLE__)
#include <Security/Security.h>
#include <CoreFoundation/CoreFoundation.h>
#endif

#endif

namespace lean {

lean_external_class * g_ssl_context_external_class = nullptr;

#ifndef LEAN_EMSCRIPTEN


static lean_obj_res mk_ssl_file_error(b_obj_arg file, char const * msg) {
    int errnum = 0;
    unsigned long err;

    while ((err = ERR_get_error()) != 0) {
        if (errnum == 0 && ERR_GET_LIB(err) == ERR_LIB_SYS) errnum = ERR_GET_REASON(err);
    }

    if (errnum != 0) return lean_io_result_mk_error(decode_io_error(errnum, file));

    lean_inc(file);
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(file, EINVAL, mk_string(msg)));
}

// Reports a failure that has no errno behind it. The OpenSSL error queue is discarded rather than
// appended, so its entries cannot leak into a later, unrelated diagnosis.
static lean_obj_res mk_ssl_invalid_argument(char const * msg) {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string(msg)));
}

lean_object * mk_openssl_error(char const * where, int ssl_err) {
    std::string msg(where);

    if (ssl_err != 0) msg += " (ssl_error=" + std::to_string(ssl_err) + ")";

    // Drains up to 10 entries from the OpenSSL error queue; marks with "(truncated)" if more remain.
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

    if (ERR_peek_error() != 0) {
        msg += "; ... (truncated)";
        ERR_clear_error();
    }

    return lean_mk_io_user_error(mk_string(msg));
}

static void lean_ssl_context_finalizer(void * ptr) {
    SSL_CTX_free((SSL_CTX*)ptr);
}

void initialize_openssl_context() {
    g_ssl_context_external_class = lean_register_external_class(lean_ssl_context_finalizer, [](void *, lean_object *) {});
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

        // Disables RFC 5077 session tickets in TLS 1.2. TLS 1.3 tickets cannot be switched off this
        // way: there the flag only downgrades them to the stateful form, which the disabled session
        // cache below then suppresses. If resumption performance matters, remove this flag and
        // implement a ticket key rotation strategy.
        SSL_OP_NO_TICKET
    );

    // Backs the flag above. A TLS 1.2 server still offers session-ID resumption through this cache
    // (which defaults to SSL_SESS_CACHE_SERVER), and the TLS 1.3 stateful tickets left by
    // SSL_OP_NO_TICKET are stored in it too, so turning it off is what makes "no session
    // resumption" hold for both protocol versions.
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
// public servers out of the box (like a browser). Success does not promise a non-empty trust store:
// only the Apple branch loads anchors eagerly and can count them.
static bool load_system_trust_store(SSL_CTX * ctx) {
#if defined(__APPLE__)
    // OpenSSL's default paths don't reach the Keychain, so the anchors are pulled from the Security
    // framework instead. This yields the built-in system roots only: certificates a user or an
    // administrator added to a keychain are not included, and per-certificate trust settings are
    // not consulted, so a root the user explicitly distrusted is still added here.
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);

    CFArrayRef anchors = nullptr;
    OSStatus status = SecTrustCopyAnchorCertificates(&anchors);

    if (status != errSecSuccess || anchors == nullptr) {
        if (anchors != nullptr) CFRelease(anchors);
        return false;
    }

    int added = 0;

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
        // An anchor already in the store is reported as success and counted like any other.
        if (X509_STORE_add_cert(store, x509) == 1) added++;
        X509_free(x509);
    }

    CFRelease(anchors);
    ERR_clear_error();

    return added > 0;
#elif defined(LEAN_WINDOWS)
    // The Windows ROOT store is reachable only through OpenSSL's winstore provider, which
    // `SSL_CTX_set_default_verify_paths` does not consult, so it has to be named explicitly. The
    // default paths are still added on top, and a build configured with `no-winstore` falls back to
    // them alone.
    int winstore = SSL_CTX_load_verify_store(ctx, "org.openssl.winstore://");
    int paths = SSL_CTX_set_default_verify_paths(ctx);

    if (winstore != 1 && paths != 1) return false;

    // Entries a failed load left behind would otherwise be picked up by a later diagnosis in this
    // call as its own.
    ERR_clear_error();
    return true;
#else
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
        // SSL_CTX_set_min_proto_version is the only way to get here, and it reports failure without
        // pushing anything onto the OpenSSL error queue, so this message has to stand on its own.
        *err = mk_openssl_io_error("SSL_CTX_set_min_proto_version failed");
        return nullptr;
    }

    return ctx;
}

// Wraps a fully configured SSL_CTX into a Lean external object, taking ownership of ctx.
static lean_obj_res wrap_ssl_context(SSL_CTX * ctx) {
    lean_object * obj = lean_ssl_context_new(ctx);
    lean_mark_mt(obj);

    return lean_io_result_mk_ok(obj);
}

/* Std.Internal.SSL.Context.Server.mk (certFile keyFile : @& String) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert_file, b_obj_arg key_file) {
    const char * cert = lean_string_cstr(cert_file);
    if (strlen(cert) != lean_string_size(cert_file) - 1) return mk_embedded_nul_error(cert_file);

    const char * key = lean_string_cstr(key_file);
    if (strlen(key) != lean_string_size(key_file) - 1) return mk_embedded_nul_error(key_file);

    lean_obj_res err = nullptr;
    // The server presents its certificate but never authenticates the client (no mutual TLS).
    SSL_CTX * ctx = mk_ssl_ctx_base(TLS_server_method(), &err);
    if (ctx == nullptr) return err;

    // Load the leaf certificate plus any intermediates from the PEM file (unlike
    // SSL_CTX_use_certificate_file, which loads only the leaf), so the server presents the full
    // chain and clients can build a path to a trusted root.
    if (SSL_CTX_use_certificate_chain_file(ctx, cert) <= 0) {
        SSL_CTX_free(ctx);
        return mk_ssl_file_error(cert_file, "could not read a PEM certificate chain");
    }

    // Encrypted private keys are not supported. Without a callback here OpenSSL falls back to
    // PEM_def_callback, which prompts for a passphrase on the terminal and blocks. The return value
    // is the passphrase length, so it has to be -1 (the documented failure code) and not 0: 0 is an
    // empty passphrase, which loads a key encrypted under one instead of rejecting it.
    SSL_CTX_set_default_passwd_cb(ctx, [](char *, int, int, void *) { return -1; });

    // Both key calls below are diagnosed from the error queue, so each must see only its own
    // entries.
    ERR_clear_error();

    // A key of the same algorithm as the certificate is compared against it here. The only errors
    // this raises from ERR_LIB_X509 come from that comparison, so they distinguish a key that does
    // not belong to the certificate from one that could not be read at all.
    if (SSL_CTX_use_PrivateKey_file(ctx, key, SSL_FILETYPE_PEM) <= 0) {
        bool mismatch = ERR_GET_LIB(ERR_peek_last_error()) == ERR_LIB_X509;

        SSL_CTX_free(ctx);
        return mk_ssl_file_error(key_file, mismatch
            ? "the private key does not match the certificate"
            : "could not read an unencrypted PEM private key");
    }

    ERR_clear_error();

    // A key whose algorithm differs from the certificate's occupies a different slot in the context
    // and is never compared above, so it is accepted there and only caught here. Without this the
    // context would be built with no usable certificate and fail at handshake time instead.
    if (SSL_CTX_check_private_key(ctx) != 1) {
        SSL_CTX_free(ctx);
        return mk_ssl_file_error(key_file, "the private key does not match the certificate");
    }

    return wrap_ssl_context(ctx);
}

// Shared skeleton of the client constructors. With verification off the CA material is never
// consulted, so `load_ca` is skipped entirely; otherwise the platform's trust anchors are loaded
// first and `load_ca` adds the caller's own CAs on top of them, additively. `load_ca` returns
// nullptr on success, or an IO error to propagate.
template<typename LoadCA>
static lean_obj_res mk_client_ctx(uint8_t verify_peer, LoadCA load_ca) {
    lean_obj_res err = nullptr;
    SSL_CTX * ctx = mk_ssl_ctx_base(TLS_client_method(), &err);
    if (ctx == nullptr) return err;

    if (!verify_peer) {
        SSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(ctx);
    }

    if (!load_system_trust_store(ctx)) {
        SSL_CTX_free(ctx);
        return mk_openssl_io_error("failed to load system trust store");
    }

    if (lean_obj_res ca_err = load_ca(ctx)) {
        SSL_CTX_free(ctx);
        return ca_err;
    }

    SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(ctx);
}

/* Std.Internal.SSL.Context.Client.mk (caFile : @& String) (verifyPeer : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg ca_file, uint8_t verify_peer) {
    const char * ca = lean_string_cstr(ca_file);
    if (strlen(ca) != lean_string_size(ca_file) - 1) return mk_embedded_nul_error(ca_file);

    return mk_client_ctx(verify_peer, [&](SSL_CTX * ctx) -> lean_obj_res {
        // An empty CA path leaves the client with just the system trust anchors.
        if (ca[0] == '\0') return nullptr;

        if (SSL_CTX_load_verify_locations(ctx, ca, nullptr) != 1) {
            return mk_ssl_file_error(ca_file, "could not read PEM CA certificates");
        }

        return nullptr;
    });
}

/* Std.Internal.SSL.Context.Client.mkFromPEM (caPEM : @& String) (verifyPeer : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client_from_pem(b_obj_arg ca_pem, uint8_t verify_peer) {
    return mk_client_ctx(verify_peer, [&](SSL_CTX * ctx) -> lean_obj_res {
        const char * pem = lean_string_cstr(ca_pem);
        size_t pem_size = lean_string_size(ca_pem) - 1;

        // An empty PEM leaves the client with just the system trust anchors.
        if (pem_size == 0) return nullptr;

        if (pem_size > INT_MAX) return mk_ssl_invalid_argument("the CA PEM string is too large");

        BIO * bio = BIO_new_mem_buf(pem, (int)pem_size);
        if (bio == nullptr) return mk_openssl_io_error("BIO_new_mem_buf failed");

        STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, nullptr, nullptr);

        BIO_free(bio);

        if (infos == nullptr) return mk_ssl_invalid_argument("could not read PEM CA certificates from the given string");

        // The store already holds the system roots and is owned by the context, so it is not freed
        // here.
        X509_STORE * store = SSL_CTX_get_cert_store(ctx);
        int cert_count = 0;

        for (int i = 0; i < sk_X509_INFO_num(infos); i++) {
            X509_INFO * info = sk_X509_INFO_value(infos, i);
            if (info->x509 == nullptr) continue;
            cert_count++;

            // A certificate that is already an anchor (e.g. a system root repeated in the bundle)
            // is reported as success, so duplicates need no special handling here.
            if (X509_STORE_add_cert(store, info->x509) != 1) {
                sk_X509_INFO_pop_free(infos, X509_INFO_free);
                return mk_openssl_io_error("X509_STORE_add_cert failed");
            }
        }

        sk_X509_INFO_pop_free(infos, X509_INFO_free);

        if (cert_count == 0) return mk_ssl_invalid_argument("the given CA PEM string contains no certificates");

        return nullptr;
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
