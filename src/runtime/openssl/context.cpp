/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/context.h"
#include "runtime/openssl/trust_store.h"

#include <cerrno>

#ifndef LEAN_EMSCRIPTEN

#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <algorithm>
#include <cstring>
#include <limits>
#include <memory>
#include <string>
#include <unordered_set>

#endif

namespace lean {

// For a TLS library that cannot meet Lean's policy, or a build without one.
static lean_obj_res mk_tls_unsupported(char const * msg) {
    return lean_io_result_mk_error(lean_mk_io_error_unsupported_operation(ENOTSUP, mk_string(msg)));
}

lean_external_class * g_ssl_context_external_class = nullptr;

#ifndef LEAN_EMSCRIPTEN

static int reject_encrypted_pem(char *, int, int, void *) { return -1; }

// `src` is a `LoadedPEM`: the PEM bytes and the `Option FilePath` they were read from. Reports a
// failure to use it, naming that file when there is one.
static lean_obj_res mk_pem_error(b_obj_arg src, char const * msg) {
    b_obj_arg path_opt = lean_ctor_get(src, 1);
    if (lean_is_scalar(path_opt)) return mk_ssl_invalid_argument(msg);

    ERR_clear_error();

    b_obj_arg path = lean_ctor_get(path_opt, 0);
    lean_inc(path);

    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(path, EINVAL, mk_string(msg)));
}

// Whether a certificate was turned away on policy grounds rather than being unreadable as PEM.
static bool rejected_by_security_level() {
    unsigned long err = ERR_peek_last_error();

    if (ERR_GET_LIB(err) != ERR_LIB_SSL) return false;

    int reason = ERR_GET_REASON(err);
    return reason == SSL_R_EE_KEY_TOO_SMALL || reason == SSL_R_CA_KEY_TOO_SMALL ||
           reason == SSL_R_CA_MD_TOO_WEAK;
}

// Opens `src` for reading. On failure returns nullptr and stores an IO error in `*err`.
static BIO * open_pem_bio(b_obj_arg src, char const * unreadable, lean_obj_res * err) {
    b_obj_arg bytes = lean_ctor_get(src, 0);
    size_t size = lean_sarray_size(bytes);

    if (size > static_cast<size_t>(std::numeric_limits<int>::max())) {
        *err = mk_pem_error(src, "the PEM material is too large");
        return nullptr;
    }

    BIO * bio = BIO_new_mem_buf(lean_sarray_cptr(bytes), (int)size);
    if (bio == nullptr) *err = mk_openssl_io_error(unreadable);
    return bio;
}

// Owns a context while it is still being built, so no error path has to remember to free it.
struct ssl_ctx_deleter { void operator()(SSL_CTX * ctx) const { SSL_CTX_free(ctx); } };
using ssl_ctx_ptr = std::unique_ptr<SSL_CTX, ssl_ctx_deleter>;

void initialize_openssl_context() {
    g_ssl_context_external_class = lean_register_external_class([](void * ptr) {
        SSL_CTX_free((SSL_CTX*)ptr);
    }, [](void *, lean_object *) {});
}

// Options every context shares. The caller sets the version floor and cipher list, whose failures it
// reports.
static void configure_ctx_options(SSL_CTX * ctx) {
    SSL_CTX_set_options(ctx,
        SSL_OP_NO_RENEGOTIATION |
        // TLS 1.2 tickets; `SSL_CTX_set_num_tickets` below covers TLS 1.3.
        SSL_OP_NO_TICKET |
        // The default, but a system `openssl.cnf` can re-enable compression (CRIME).
        SSL_OP_NO_COMPRESSION
    );

    // Off by default, but a system `openssl.cnf` can switch them on. The first makes a truncated
    // stream read as a clean close.
    SSL_CTX_clear_options(ctx,
        SSL_OP_IGNORE_UNEXPECTED_EOF |
        SSL_OP_NO_EXTENDED_MASTER_SECRET |
        SSL_OP_ALLOW_UNSAFE_LEGACY_RENEGOTIATION |
        SSL_OP_LEGACY_SERVER_CONNECT |
        SSL_OP_ALLOW_NO_DHE_KEX
    );

    // Level 2 (RSA and DH keys of at least 2048 bits) is the default only from OpenSSL 3.2. A stricter
    // system policy is kept.
    SSL_CTX_set_security_level(ctx, std::max(2, SSL_CTX_get_security_level(ctx)));

    // A TLS 1.3 server otherwise sends two NewSessionTickets per connection.
    SSL_CTX_set_num_tickets(ctx, 0);

    // Backstop: the reads below pass their own callback, but no OpenSSL path may prompt on a terminal.
    SSL_CTX_set_default_passwd_cb(ctx, reject_encrypted_pem);

    // A TLS 1.2 server would otherwise still offer session-ID resumption.
    SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);

    // The session layer may move a pending write's buffer between `SSL_write` retries.
    SSL_CTX_set_mode(ctx, SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER);

    // Applies once the session layer calls `SSL_set1_host`: no partial wildcards (RFC 9525 §6.3) and
    // no fallback to the subject CN (RFC 9525 Appendix A).
    X509_VERIFY_PARAM_set_hostflags(SSL_CTX_get0_param(ctx),
        X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS | X509_CHECK_FLAG_NEVER_CHECK_SUBJECT);
}

// OpenSSL's default TLS 1.3 suites (`TLS_DEFAULT_CIPHERSUITES`).
static char const * const g_tls13_suites[] = {
    "TLS_AES_256_GCM_SHA384",
    "TLS_CHACHA20_POLY1305_SHA256",
    "TLS_AES_128_GCM_SHA256",
};

// Narrows TLS 1.2 to ECDHE with an AEAD and TLS 1.3 to `g_tls13_suites`, keeping only suites the
// context already allowed, so a system policy can tighten the list but not widen it. Returns nullptr
// on success, an IO error otherwise.
static lean_obj_res restrict_ciphers(SSL_CTX * ctx) {
    char const * failed = "could not configure the TLS cipher suites";

    std::unordered_set<std::string> allowed;
    STACK_OF(SSL_CIPHER) * before = SSL_CTX_get_ciphers(ctx);

    for (int i = 0, n = sk_SSL_CIPHER_num(before); i < n; i++) {
        allowed.insert(SSL_CIPHER_get_name(sk_SSL_CIPHER_value(before, i)));
    }

    if (SSL_CTX_set_cipher_list(ctx, "ECDHE+AESGCM:ECDHE+CHACHA20") != 1)
        return mk_openssl_io_error(failed);

    std::string kept;
    bool narrowed = false;
    STACK_OF(SSL_CIPHER) * after = SSL_CTX_get_ciphers(ctx);

    for (int i = 0, n = sk_SSL_CIPHER_num(after); i < n; i++) {
        SSL_CIPHER const * cipher = sk_SSL_CIPHER_value(after, i);

        // The list also carries the TLS 1.3 suites, which `SSL_CTX_set_cipher_list` leaves alone.
        if (strcmp(SSL_CIPHER_get_version(cipher), "TLSv1.3") == 0) continue;

        char const * name = SSL_CIPHER_get_name(cipher);

        if (allowed.count(name) == 0) {
            narrowed = true;
            continue;
        }

        if (!kept.empty()) kept += ':';
        kept += name;
    }

    // A policy leaving no suite for a version it still permits is refused. The minimum is already at
    // least TLS 1.2, and a maximum of 0 means none.
    int max_version = SSL_CTX_get_max_proto_version(ctx);
    uint64_t options = SSL_CTX_get_options(ctx);

    bool tls12_permitted = SSL_CTX_get_min_proto_version(ctx) <= TLS1_2_VERSION &&
                           (max_version == 0 || max_version >= TLS1_2_VERSION) &&
                           (options & SSL_OP_NO_TLSv1_2) == 0;

    bool tls13_permitted = (max_version == 0 || max_version >= TLS1_3_VERSION) &&
                           (options & SSL_OP_NO_TLSv1_3) == 0;

    auto refused_by_policy = [](char const * version) {
        ERR_clear_error();
        std::string msg = std::string("could not configure the TLS cipher suites: the system OpenSSL "
                                      "configuration permits ") + version + " but leaves none of its "
                                      "suites that Lean allows";
        return mk_tls_unsupported(msg.c_str());
    };

    if (narrowed && kept.empty() && tls12_permitted) return refused_by_policy("TLS 1.2");
    if (narrowed && !kept.empty() && SSL_CTX_set_cipher_list(ctx, kept.c_str()) != 1)
        return mk_openssl_io_error(failed);

    std::string kept13;

    for (char const * name : g_tls13_suites) {
        if (allowed.count(name) == 0) continue;

        if (!kept13.empty()) kept13 += ':';
        kept13 += name;
    }

    // Without a TLS 1.3 suite OpenSSL would still offer TLS 1.3 and then fail every handshake.
    if (kept13.empty() && tls13_permitted) return refused_by_policy("TLS 1.3");
    if (SSL_CTX_set_ciphersuites(ctx, kept13.c_str()) != 1) return mk_openssl_io_error(failed);

    return nullptr;
}

// Creates a configured SSL_CTX, or returns nullptr with an IO error stored in `*err`.
static ssl_ctx_ptr mk_ssl_ctx_base(const SSL_METHOD * method, lean_obj_res * err) {
    ERR_clear_error();

    ssl_ctx_ptr ctx(SSL_CTX_new(method));

    if (ctx == nullptr) {
        *err = mk_openssl_io_error("could not create the TLS context");
        return nullptr;
    }

    configure_ctx_options(ctx.get());

    // A system crypto policy already requiring TLS 1.3 keeps that.
    if (SSL_CTX_get_min_proto_version(ctx.get()) < TLS1_2_VERSION &&
        SSL_CTX_set_min_proto_version(ctx.get(), TLS1_2_VERSION) != 1) {
        *err = mk_openssl_io_error("could not set the minimum TLS version");
        return nullptr;
    }

    if (lean_obj_res cipher_err = restrict_ciphers(ctx.get())) {
        *err = cipher_err;
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

// `SSL_CTX_use_certificate_chain_file` for a BIO, which OpenSSL has no public function for.
static bool use_certificate_chain_bio(SSL_CTX * ctx, BIO * bio) {
    // `_AUX`, as the file variant reads the leaf.
    X509 * leaf = PEM_read_bio_X509_AUX(bio, nullptr, reject_encrypted_pem, nullptr);
    if (leaf == nullptr) return false;

    bool used = SSL_CTX_use_certificate(ctx, leaf) == 1;
    X509_free(leaf);

    if (!used || SSL_CTX_clear_chain_certs(ctx) != 1) return false;

    while (X509 * ca = PEM_read_bio_X509(bio, nullptr, reject_encrypted_pem, nullptr)) {
        if (SSL_CTX_add0_chain_cert(ctx, ca) != 1) {
            X509_free(ca);
            return false;
        }
    }

    unsigned long err = ERR_peek_last_error();

    if (ERR_GET_LIB(err) != ERR_LIB_PEM || ERR_GET_REASON(err) != PEM_R_NO_START_LINE) return false;

    ERR_clear_error();
    return true;
}

// Loads the certificate chain the server presents and the key it signs with.
static lean_obj_res load_server_credentials(SSL_CTX * ctx, b_obj_arg cert, b_obj_arg key) {
    ERR_clear_error();

    lean_obj_res err = nullptr;

    BIO * cert_bio = open_pem_bio(cert, "could not read a PEM certificate chain", &err);

    if (cert_bio == nullptr) return err;

    bool cert_ok = use_certificate_chain_bio(ctx, cert_bio);
    BIO_free(cert_bio);

    if (!cert_ok) {
        return mk_pem_error(cert, rejected_by_security_level()
            ? "the certificate is rejected by the TLS security level (key too small or signature "
              "digest too weak)"
            : "could not read a PEM certificate chain");
    }

    char const * unreadable_key = "could not read an unencrypted PEM private key";
    char const * mismatch = "the private key does not match the certificate";
    BIO * key_bio = open_pem_bio(key, unreadable_key, &err);

    if (key_bio == nullptr) return err;

    EVP_PKEY * pkey = PEM_read_bio_PrivateKey(key_bio, nullptr, reject_encrypted_pem, nullptr);
    BIO_free(key_bio);

    if (pkey == nullptr) return mk_pem_error(key, unreadable_key);

    bool used = SSL_CTX_use_PrivateKey(ctx, pkey) == 1;
    EVP_PKEY_free(pkey);

    // A key of the leaf's algorithm is compared here. One of another algorithm lands in an unused
    // slot, which only `SSL_CTX_check_private_key` catches; one that cannot sign (X25519) has no slot.
    if (!used) {
        unsigned long reason = ERR_peek_last_error();
        bool unusable = ERR_GET_LIB(reason) == ERR_LIB_SSL &&
                        ERR_GET_REASON(reason) == SSL_R_UNKNOWN_CERTIFICATE_TYPE;

        return mk_pem_error(key, ERR_GET_LIB(reason) == ERR_LIB_X509 ? mismatch
            : unusable ? "the private key's algorithm cannot be used for TLS"
            : unreadable_key);
    }

    ERR_clear_error();

    if (SSL_CTX_check_private_key(ctx) != 1) return mk_pem_error(key, mismatch);

    return nullptr;
}

static lean_obj_res mk_server_ctx(b_obj_arg cert, b_obj_arg key) {
    lean_obj_res base_err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_server_method(), &base_err);
    if (ctx == nullptr) return base_err;

    // The server presents its certificate but never authenticates the client (no mutual TLS).
    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);

    if (lean_obj_res err = load_server_credentials(ctx.get(), cert, key)) return err;

    return wrap_ssl_context(std::move(ctx));
}

// Whether the store holds a chain anchor: a self-signed certificate, or one a `TRUSTED CERTIFICATE`
// block trusts for TLS servers. The store keeps only the first copy of a repeated certificate, so its
// copies are the ones checked.
static bool store_has_anchor(X509_STORE * store) {
    STACK_OF(X509) * certs = X509_STORE_get1_all_certs(store);
    if (certs == nullptr) return false;

    bool any = false;
    for (int i = 0; !any && i < sk_X509_num(certs); i++) {
        any = X509_check_trust(sk_X509_value(certs, i), X509_TRUST_SSL_SERVER, 0) == X509_TRUST_TRUSTED;
    }

    sk_X509_pop_free(certs, X509_free);
    return any;
}

// Adds every certificate in `src` to the trust store.
static lean_obj_res load_ca_bundle(SSL_CTX * ctx, b_obj_arg src) {
    ERR_clear_error();

    lean_obj_res err = nullptr;
    BIO * bio = open_pem_bio(src, "could not read PEM CA certificates", &err);

    if (bio == nullptr) return err;

    STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, reject_encrypted_pem, nullptr);
    BIO_free(bio);

    if (infos == nullptr) return mk_pem_error(src, "could not read PEM CA certificates");

    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    int cert_count = 0;

    for (int i = 0, n = sk_X509_INFO_num(infos); i < n; i++) {
        // A bundle may hold private keys and CRLs; only certificates are anchors.
        X509 * cert = sk_X509_INFO_value(infos, i)->x509;

        if (cert == nullptr) continue;
        cert_count++;

        if (X509_STORE_add_cert(store, cert) != 1) {
            err = mk_openssl_io_error("could not add a CA certificate to the trust store");
            break;
        }
    }

    sk_X509_INFO_pop_free(infos, X509_INFO_free);

    if (err != nullptr)
        return err;

    if (cert_count == 0)
        return mk_pem_error(src, "the CA material contains no certificates");

    return nullptr;
}

static lean_obj_res mk_client_ctx(b_obj_arg cas, uint8_t verify_peer, uint8_t trust_system_roots, uint8_t allow_partial_chain) {
    size_t ca_count = lean_array_size(cas);

    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_client_method(), &err);
    if (ctx == nullptr) return err;

    if (!verify_peer) {
        SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(std::move(ctx));
    }

    if (allow_partial_chain) {
        // Chain building may stop at any certificate in the store, as pinning an intermediate needs.
        X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()), X509_V_FLAG_PARTIAL_CHAIN);
    }

    bool system_roots = false;

    if (trust_system_roots) {
        std::string detail;
        system_roots = use_system_trust_store(ctx.get(), &detail);

        // With `ca` the context still has anchors when the platform supplies none.
        if (!system_roots && ca_count == 0) {
            std::string msg("failed to load system trust store");
            if (!detail.empty()) msg += ": " + detail;

            return lean_io_result_mk_error(lean_mk_io_error_no_such_thing(ENOENT, mk_string(msg)));
        }
    }

    for (size_t i = 0; i < ca_count; i++) {
        if (lean_obj_res ca_err = load_ca_bundle(ctx.get(), lean_array_get_core(cas, i))) return ca_err;
    }

    // CA material without an anchor only makes a dead context when it is the sole source.
    if (ca_count > 0 && !allow_partial_chain && !system_roots &&
        !store_has_anchor(SSL_CTX_get_cert_store(ctx.get()))) {
        char const * msg = "the CA material holds no root certificate for a chain to end at; include "
                           "the root, or set `allowPartialChain := true` to trust an intermediate";

        // With several bundles no single file is to blame.
        return ca_count == 1 ? mk_pem_error(lean_array_get_core(cas, 0), msg)
                             : mk_ssl_invalid_argument(msg);
    }

    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(std::move(ctx));
}

// Initializes OpenSSL before any other call can register `atexit(OPENSSL_cleanup)`, and keeps C++
// exceptions out of Lean code.
template<typename F>
static lean_obj_res ssl_entry_point(F && build) {
    try {
        if (!ensure_openssl_initialized()) return mk_tls_unsupported("could not initialize the TLS library");

        return build();
    } catch (std::exception & ex) {
        return lean_io_result_mk_error(lean_mk_io_user_error(mk_string(ex.what())));
    }
}

/* Std.Internal.SSL.Context.Server.mkImpl (cert key : @& LoadedPEM) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert, b_obj_arg key) {
    return ssl_entry_point([&] { return mk_server_ctx(cert, key); });
}

/* Std.Internal.SSL.Context.Client.mkImpl (ca : @& Array LoadedPEM) (verifyPeer trustSystemRoots allowPartialChain : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg ca, uint8_t verify_peer, uint8_t trust_system_roots, uint8_t allow_partial_chain) {
    return ssl_entry_point([&] {
        return mk_client_ctx(ca, verify_peer, trust_system_roots, allow_partial_chain);
    });
}

#else

void initialize_openssl_context() {}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg /*cert*/, b_obj_arg /*key*/) {
    return mk_tls_unsupported("this build of Lean has no TLS support");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg /*ca*/, uint8_t /*verify_peer*/, uint8_t /*trust_system_roots*/, uint8_t /*allow_partial_chain*/) {
    return mk_tls_unsupported("this build of Lean has no TLS support");
}

#endif

}
