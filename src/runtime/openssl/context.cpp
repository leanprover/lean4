/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/context.h"
#include "runtime/openssl/trust_store.h"

#include <cerrno>

#ifndef LEAN_EMSCRIPTEN

#include <openssl/crypto.h>
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
#include <string_view>
#include <unordered_set>

#endif

namespace lean {

// For a TLS library that cannot meet Lean's policy, or a build without one.
static lean_obj_res mk_tls_unsupported(char const * msg) {
    return lean_io_result_mk_error(lean_mk_io_error_unsupported_operation(ENOTSUP, mk_string(msg)));
}

#ifndef LEAN_EMSCRIPTEN

// Registered on first use rather than at runtime start-up, so that a program that does not import the
// TLS module links none of OpenSSL.
lean_external_class * ssl_context_class() {
    static lean_external_class * const cls = lean_register_external_class([](void * ptr) {
        SSL_CTX_free((SSL_CTX*)ptr);
    }, [](void *, lean_object *) {});
    return cls;
}

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

// Whether the last PEM read failed because no block was left.
static bool at_pem_end() {
    unsigned long err = ERR_peek_last_error();
    return ERR_GET_LIB(err) == ERR_LIB_PEM && ERR_GET_REASON(err) == PEM_R_NO_START_LINE;
}

using bio_ptr = std::unique_ptr<BIO, released_by<BIO_free>>;
using ssl_ctx_ptr = std::unique_ptr<SSL_CTX, released_by<SSL_CTX_free>>;

// Opens `src` for reading. On failure returns nullptr and stores an IO error in `*err`.
static bio_ptr open_pem_bio(b_obj_arg src, char const * unreadable, lean_obj_res * err) {
    b_obj_arg bytes = lean_ctor_get(src, 0);
    size_t size = lean_sarray_size(bytes);

    if (size > static_cast<size_t>(std::numeric_limits<int>::max())) {
        *err = mk_pem_error(src, "the PEM material is too large");
        return nullptr;
    }

    bio_ptr bio(BIO_new_mem_buf(lean_sarray_cptr(bytes), (int)size));
    if (bio == nullptr) *err = mk_openssl_io_error(unreadable);
    return bio;
}

// Options every context shares. The caller sets the version range and cipher list, whose failures it
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
        SSL_OP_ALLOW_CLIENT_RENEGOTIATION |
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

    // The session layer may move a pending write's buffer between `SSL_write` retries. A peer is sent
    // exactly the configured chain, never one completed from the trust store.
    SSL_CTX_set_mode(ctx, SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER | SSL_MODE_NO_AUTO_CHAIN);

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

// `Std.Internal.SSL.Version`'s constructors, in declaration order.
enum version_kind : uint8_t { tls12, tls13 };

static int openssl_version(uint8_t version) { return version == tls12 ? TLS1_2_VERSION : TLS1_3_VERSION; }

// Whether the context's version range and options still permit `version`.
static bool version_permitted(SSL_CTX * ctx, int version, uint64_t disabled_by) {
    int min = (int)SSL_CTX_get_min_proto_version(ctx);
    int max = (int)SSL_CTX_get_max_proto_version(ctx);

    return min <= version && version <= max && (SSL_CTX_get_options(ctx) & disabled_by) == 0;
}

static lean_obj_res refused_by_policy(char const * what, std::string const & why) {
    ERR_clear_error();
    std::string msg = std::string("could not configure the TLS ") + what + ": the system OpenSSL configuration " + why;
    return mk_tls_unsupported(msg.c_str());
}

static lean_obj_res no_suite_left(char const * version) {
    return refused_by_policy("cipher suites", std::string("permits ") + version +
                             " but leaves none of its suites that Lean allows");
}

// Narrows TLS 1.2 to ECDHE with an AEAD and TLS 1.3 to `g_tls13_suites`, keeping only suites the
// context already allowed, so a system policy can tighten the list but not widen it. Returns nullptr
// on success, an IO error otherwise.
static lean_obj_res restrict_ciphers(SSL_CTX * ctx) {
    char const * failed = "could not configure the TLS cipher suites";

    // `SSL_CIPHER_get_name` returns static strings.
    std::unordered_set<std::string_view> allowed;
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

    // An empty list cannot be set, and leaving the unnarrowed one would widen the policy.
    if (narrowed && kept.empty() && version_permitted(ctx, TLS1_2_VERSION, SSL_OP_NO_TLSv1_2))
        return no_suite_left("TLS 1.2");
    if (narrowed && !kept.empty() && SSL_CTX_set_cipher_list(ctx, kept.c_str()) != 1)
        return mk_openssl_io_error(failed);

    std::string kept13;

    for (char const * name : g_tls13_suites) {
        if (allowed.count(name) == 0) continue;

        if (!kept13.empty()) kept13 += ':';
        kept13 += name;
    }

    if (SSL_CTX_set_ciphersuites(ctx, kept13.c_str()) != 1) return mk_openssl_io_error(failed);

    return nullptr;
}

// Refuses a context no handshake could succeed with: one whose version range is empty, or that has no
// suite for a version it permits once the security level has filtered the lists. OpenSSL would
// otherwise still offer that version and then fail every handshake. Key exchange groups go unchecked:
// OpenSSL has no getter for a context's own list, so a policy leaving TLS 1.2 no elliptic curve for its
// ECDHE suites only shows in its handshakes.
static lean_obj_res check_usable(SSL_CTX * ctx) {
    bool permits12 = version_permitted(ctx, TLS1_2_VERSION, SSL_OP_NO_TLSv1_2);
    bool permits13 = version_permitted(ctx, TLS1_3_VERSION, SSL_OP_NO_TLSv1_3);

    if (!permits12 && !permits13) return refused_by_policy("versions", "permits none of the requested TLS versions");

    std::unique_ptr<SSL, released_by<SSL_free>> ssl(SSL_new(ctx));
    if (ssl == nullptr) return mk_openssl_io_error("could not create the TLS context");

    // Null when nothing is left.
    STACK_OF(SSL_CIPHER) * usable = SSL_get1_supported_ciphers(ssl.get());
    int n12 = 0, n13 = 0;

    for (int i = 0; i < sk_SSL_CIPHER_num(usable); i++) {
        bool is13 = strcmp(SSL_CIPHER_get_version(sk_SSL_CIPHER_value(usable, i)), "TLSv1.3") == 0;
        (is13 ? n13 : n12)++;
    }

    sk_SSL_CIPHER_free(usable);

    if (permits12 && n12 == 0) return no_suite_left("TLS 1.2");
    if (permits13 && n13 == 0) return no_suite_left("TLS 1.3");

    return nullptr;
}

// Creates a configured SSL_CTX accepting versions `min` to `max` (as `Std.Internal.SSL.Version`), or
// returns nullptr with an IO error stored in `*err`.
static ssl_ctx_ptr mk_ssl_ctx_base(const SSL_METHOD * method, uint8_t min, uint8_t max, lean_obj_res * err) {
    if (min > max) {
        *err = mk_ssl_invalid_argument("`minVersion` is above `maxVersion`");
        return nullptr;
    }

    ERR_clear_error();

    ssl_ctx_ptr ctx(SSL_CTX_new(method));

    if (ctx == nullptr) {
        *err = mk_openssl_io_error("could not create the TLS context");
        return nullptr;
    }

    configure_ctx_options(ctx.get());

    // A system policy can only narrow the range. OpenSSL takes a minimum above the maximum, which
    // `check_usable` then reports.
    int system_max = (int)SSL_CTX_get_max_proto_version(ctx.get());
    int lowest = std::max((int)SSL_CTX_get_min_proto_version(ctx.get()), openssl_version(min));
    int highest = system_max == 0 ? openssl_version(max) : std::min(system_max, openssl_version(max));

    if (SSL_CTX_set_min_proto_version(ctx.get(), lowest) != 1 ||
        SSL_CTX_set_max_proto_version(ctx.get(), highest) != 1) {
        *err = mk_openssl_io_error("could not set the TLS version range");
        return nullptr;
    }

    if (lean_obj_res e = restrict_ciphers(ctx.get())) {
        *err = e;
        return nullptr;
    }

    if (lean_obj_res e = check_usable(ctx.get())) {
        *err = e;
        return nullptr;
    }

    return ctx;
}

static lean_obj_res wrap_ssl_context(ssl_ctx_ptr ctx) {
    // A successful build can still leave errors queued, e.g. from `X509_check_trust`.
    ERR_clear_error();

    lean_object * obj = lean_ssl_context_new(ctx.release());
    lean_mark_mt(obj);

    return lean_io_result_mk_ok(obj);
}

// `SSL_CTX_use_certificate_chain_file` for a BIO, which OpenSSL has no public function for. Every
// certificate is read with `_AUX`, which also takes `TRUSTED CERTIFICATE` blocks; the plain reader the
// file variant uses for the chain skips them, silently leaving the peer an incomplete chain.
static bool use_certificate_chain_bio(SSL_CTX * ctx, BIO * bio) {
    X509 * leaf = PEM_read_bio_X509_AUX(bio, nullptr, reject_encrypted_pem, nullptr);
    if (leaf == nullptr) return false;

    bool used = SSL_CTX_use_certificate(ctx, leaf) == 1;
    X509_free(leaf);

    if (!used || SSL_CTX_clear_chain_certs(ctx) != 1) return false;

    while (X509 * ca = PEM_read_bio_X509_AUX(bio, nullptr, reject_encrypted_pem, nullptr)) {
        if (SSL_CTX_add0_chain_cert(ctx, ca) != 1) {
            X509_free(ca);
            return false;
        }
    }

    if (!at_pem_end()) return false;

    ERR_clear_error();
    return true;
}

// Loads the certificate chain presented to the peer and the key it signs with.
static lean_obj_res load_credentials(SSL_CTX * ctx, b_obj_arg cert, b_obj_arg key) {
    ERR_clear_error();

    lean_obj_res err = nullptr;

    bio_ptr cert_bio = open_pem_bio(cert, "could not read a PEM certificate chain", &err);

    if (cert_bio == nullptr) return err;

    if (!use_certificate_chain_bio(ctx, cert_bio.get())) {
        return mk_pem_error(cert, rejected_by_security_level()
            ? "the certificate is rejected by the TLS security level (key too small or signature "
              "digest too weak)"
            : "could not read a PEM certificate chain");
    }

    char const * unreadable_key = "could not read an unencrypted PEM private key";
    char const * mismatch = "the private key does not match the certificate";
    bio_ptr key_bio = open_pem_bio(key, unreadable_key, &err);

    if (key_bio == nullptr) return err;

    EVP_PKEY * pkey = PEM_read_bio_PrivateKey(key_bio.get(), nullptr, reject_encrypted_pem, nullptr);

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

// Whether `cert` can end a chain for `trust_id`: a `TRUSTED CERTIFICATE` block rejects neither it nor,
// in `distrusted`, a certificate with its key. Every context verifies with partial chains, so no more is
// needed.
static bool can_anchor(X509 * cert, int trust_id, STACK_OF(X509) * distrusted) {
    return X509_check_trust(cert, trust_id, 0) != X509_TRUST_REJECTED && !has_distrusted_key(distrusted, cert);
}

// Whether the store holds a certificate a chain can end at.
static bool store_has_anchor(X509_STORE * store, int trust_id, STACK_OF(X509) * distrusted) {
    x509_stack_ptr certs(X509_STORE_get1_all_certs(store));

    for (int i = 0; certs != nullptr && i < sk_X509_num(certs.get()); i++) {
        if (can_anchor(sk_X509_value(certs.get(), i), trust_id, distrusted)) return true;
    }

    return false;
}

// Records `cert` in `distrusted` if a `TRUSTED CERTIFICATE` block rejects it for `trust_id`. The store
// keeps only the first copy of a repeated certificate, so a distrusting copy is collected as it is read.
static bool note_distrust(X509 * cert, int trust_id, STACK_OF(X509) * distrusted) {
    return X509_check_trust(cert, trust_id, 0) != X509_TRUST_REJECTED || push_ref(distrusted, cert);
}

static void free_x509_info_stack(STACK_OF(X509_INFO) * sk) { sk_X509_INFO_pop_free(sk, X509_INFO_free); }

// Adds every certificate in `src` to `store`, collecting those distrusted for `trust_id` in `distrusted`.
// Material that does not parse or holds no certificate is an error.
static lean_obj_res load_ca_bundle(X509_STORE * store, b_obj_arg src, int trust_id, STACK_OF(X509) * distrusted) {
    ERR_clear_error();

    char const * unreadable = "could not read PEM CA certificates";
    lean_obj_res err = nullptr;
    bio_ptr bio = open_pem_bio(src, unreadable, &err);

    if (bio == nullptr) return err;

    std::unique_ptr<STACK_OF(X509_INFO), released_by<free_x509_info_stack>> infos(
        PEM_X509_INFO_read_bio(bio.get(), nullptr, reject_encrypted_pem, nullptr));

    if (infos == nullptr) return mk_pem_error(src, unreadable);

    int cert_count = 0;

    for (int i = 0, n = sk_X509_INFO_num(infos.get()); i < n; i++) {
        // A bundle may hold private keys and CRLs; only certificates are anchors.
        X509 * cert = sk_X509_INFO_value(infos.get(), i)->x509;

        if (cert == nullptr) continue;
        cert_count++;

        if (X509_STORE_add_cert(store, cert) != 1 || !note_distrust(cert, trust_id, distrusted))
            return mk_openssl_io_error("could not add a CA certificate to the trust store");
    }

    if (cert_count == 0) return mk_pem_error(src, "the CA material contains no certificates");

    return nullptr;
}

// Adds the certificates in `src` to `store`, skipping any block that does not parse, counts them in
// `*added`, and collects those distrusted for TLS server authentication in `distrusted`.
static lean_obj_res load_env_bundle(X509_STORE * store, b_obj_arg src, int * added, STACK_OF(X509) * distrusted) {
    ERR_clear_error();

    lean_obj_res err = nullptr;
    bio_ptr bio = open_pem_bio(src, "could not read PEM CA certificates", &err);
    if (bio == nullptr) return err;

    // A read consumes the input up to the next END line, so a block missing its own swallows the block
    // after it, which is lost; the first still loads if its data is whole. The pending count guards
    // against a read that consumes nothing.
    for (long pending = BIO_pending(bio.get()); pending > 0; ) {
        X509 * cert = PEM_read_bio_X509_AUX(bio.get(), nullptr, reject_encrypted_pem, nullptr);

        if (cert != nullptr) {
            bool stored = X509_STORE_add_cert(store, cert) == 1 &&
                          note_distrust(cert, X509_TRUST_SSL_SERVER, distrusted);
            X509_free(cert);

            if (!stored) return mk_openssl_io_error("could not add a CA certificate to the trust store");

            (*added)++;
        } else if (at_pem_end()) {
            break;
        } else {
            ERR_clear_error();
        }

        long left = BIO_pending(bio.get());
        if (left >= pending) break;
        pending = left;
    }

    ERR_clear_error();
    return nullptr;
}

static lean_obj_res load_ca_bundles(X509_STORE * store, b_obj_arg cas, int trust_id, STACK_OF(X509) * distrusted) {
    for (size_t i = 0; i < lean_array_size(cas); i++) {
        if (lean_obj_res err = load_ca_bundle(store, lean_array_get_core(cas, i), trust_id, distrusted)) return err;
    }

    return nullptr;
}

// The store holds no anchor for `trust_id`. `cas` is to blame when it was the only material loaded, and a
// single bundle is named.
static lean_obj_res no_anchor_error(b_obj_arg cas, bool cas_alone, int trust_id) {
    char const * msg = trust_id == X509_TRUST_SSL_CLIENT
        ? "the CA material holds no certificate trusted for TLS client authentication (each is "
          "distrusted, or trusted only for other uses)"
        : "the CA material holds no certificate trusted for TLS server authentication (each is "
          "distrusted, or trusted only for other uses)";

    return cas_alone && lean_array_size(cas) == 1 ? mk_pem_error(lean_array_get_core(cas, 0), msg)
                                                  : mk_ssl_invalid_argument(msg);
}

// The names fill one field of at most 2^16 - 1 bytes, each with a 2-byte length (RFC 5246 §7.4.4). TLS
// 1.3 carries them in an extension, and a CertificateRequest's extensions share a field of that size
// (RFC 8446 §4.3.2); the others take well under the 4 KiB left over.
static size_t const g_client_ca_names_limit = 60 * 1024;

static void free_x509_name_stack(STACK_OF(X509_NAME) * sk) { sk_X509_NAME_pop_free(sk, X509_NAME_free); }

// Sends clients the names of the CAs in `store` that can end a client's chain, to help them pick a
// certificate. Names that a CertificateRequest could not carry would fail every handshake, so then none
// are sent, which both TLS versions allow.
static lean_obj_res advertise_client_cas(SSL_CTX * ctx, X509_STORE * store, STACK_OF(X509) * distrusted) {
    char const * failed = "could not configure the client CA names";
    x509_stack_ptr certs(X509_STORE_get1_all_certs(store));
    std::unique_ptr<STACK_OF(X509_NAME), released_by<free_x509_name_stack>> names(sk_X509_NAME_new_null());
    if (certs == nullptr || names == nullptr) return mk_openssl_io_error(failed);

    size_t size = 0;

    for (int i = 0; i < sk_X509_num(certs.get()); i++) {
        X509 * cert = sk_X509_value(certs.get(), i);
        if (!can_anchor(cert, X509_TRUST_SSL_CLIENT, distrusted)) continue;

        X509_NAME * name = X509_NAME_dup(X509_get_subject_name(cert));
        int len = name == nullptr ? -1 : i2d_X509_NAME(name, nullptr);

        if (len < 0 || sk_X509_NAME_push(names.get(), name) <= 0) {
            X509_NAME_free(name);
            return mk_openssl_io_error(failed);
        }

        size += 2 + (size_t)len;
    }

    if (size <= g_client_ca_names_limit) SSL_CTX_set_client_CA_list(ctx, names.release());

    return nullptr;
}

// A client trusting the system has nothing to trust. The checks that led here can leave errors queued.
static lean_obj_res no_trust_store(std::string const & detail) {
    ERR_clear_error();
    std::string msg = "could not load the system trust store";
    if (!detail.empty()) msg += ": " + detail;

    return lean_io_result_mk_error(lean_mk_io_error_no_such_thing(ENOENT, mk_string(msg)));
}

// `Context.Server.ClientAuth`'s constructors, in declaration order.
enum client_auth_kind : unsigned { auth_none, auth_request, auth_require_any, auth_verify_if_given,
                                   auth_require_and_verify };

// `Context.Client.Trust`'s constructors, in declaration order.
enum trust_kind : unsigned { trust_system, trust_only, trust_insecure_skip_verify };

// For the client-authentication modes that take whatever certificate is sent. Nothing could anchor the
// chain, so it is not checked (which would only spend the peer's choice of CPU): the verdict is recorded
// as untrusted and the certificate accepted.
static int accept_unverified(X509_STORE_CTX * ctx, void *) {
    X509_STORE_CTX_set_error(ctx, X509_V_ERR_CERT_UNTRUSTED);
    return 1;
}

// `Std.Internal.SSL.Context.Server.mkImpl`. `client_ca` holds the CAs of `client_auth`, loaded.
static lean_obj_res mk_server_ctx(b_obj_arg cert, b_obj_arg key, b_obj_arg client_auth, b_obj_arg client_ca,
                                  uint8_t min, uint8_t max) {
    unsigned auth = lean_obj_tag(client_auth);
    if (auth > auth_require_and_verify) return mk_ssl_invalid_argument("unknown client authentication mode");

    bool verifies = auth == auth_verify_if_given || auth == auth_require_and_verify;

    if (verifies && lean_array_size(client_ca) == 0)
        return mk_ssl_invalid_argument("verifying client certificates needs at least one CA certificate");

    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_server_method(), min, max, &err);
    if (ctx == nullptr) return err;

    if (lean_obj_res e = load_credentials(ctx.get(), cert, key)) return e;

    // A DSA server could complete no handshake: the TLS 1.2 suites `restrict_ciphers` keeps need RSA or
    // ECDSA (which covers EdDSA), and TLS 1.3 has no DSA signature scheme. A client may still sign with
    // DSA in TLS 1.2.
    EVP_PKEY * leaf_key = X509_get0_pubkey(SSL_CTX_get0_certificate(ctx.get()));
    if (leaf_key != nullptr && EVP_PKEY_is_a(leaf_key, "DSA"))
        return mk_pem_error(cert, "the certificate's DSA key cannot be used with the cipher suites Lean allows");

    int mode = SSL_VERIFY_NONE;
    bool unverified = false;

    switch (auth) {
    case auth_request: mode = SSL_VERIFY_PEER; unverified = true; break;
    case auth_require_any: mode = SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT; unverified = true; break;
    case auth_verify_if_given: mode = SSL_VERIFY_PEER; break;
    case auth_require_and_verify: mode = SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT; break;
    }

    if (lean_array_size(client_ca) > 0) {
        // Kept apart from the context's own store, which a server never needs for its chain.
        std::unique_ptr<X509_STORE, released_by<X509_STORE_free>> store(X509_STORE_new());
        x509_stack_ptr distrusted(sk_X509_new_null());
        if (store == nullptr || distrusted == nullptr) return mk_openssl_io_error("could not create the TLS context");

        if (lean_obj_res e = load_ca_bundles(store.get(), client_ca, X509_TRUST_SSL_CLIENT, distrusted.get())) return e;
        if (!store_has_anchor(store.get(), X509_TRUST_SSL_CLIENT, distrusted.get()))
            return no_anchor_error(client_ca, true, X509_TRUST_SSL_CLIENT);
        if (lean_obj_res e = advertise_client_cas(ctx.get(), store.get(), distrusted.get())) return e;

        if (!install_chain_verifier(ctx.get(), store.get(), X509_TRUST_SSL_CLIENT, false, distrusted.get()))
            return mk_openssl_io_error("could not configure certificate verification");

        SSL_CTX_set0_verify_cert_store(ctx.get(), store.release());
        X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()), X509_V_FLAG_PARTIAL_CHAIN);
    }

    SSL_CTX_set_verify(ctx.get(), mode, nullptr);
    if (unverified) SSL_CTX_set_cert_verify_callback(ctx.get(), accept_unverified, nullptr);

    return wrap_ssl_context(std::move(ctx));
}

// `Std.Internal.SSL.Context.Client.mkImpl`. `cas` holds the CAs of `trust`, loaded, and `env_opt` the
// files `SSL_CERT_FILE` and `SSL_CERT_DIR` name for `Trust.system` if either is set, which then replace
// the platform's anchors.
static lean_obj_res mk_client_ctx(b_obj_arg trust, b_obj_arg cas, b_obj_arg env_opt, b_obj_arg cert_opt,
                                  b_obj_arg key_opt, uint8_t min, uint8_t max) {
    unsigned kind = lean_obj_tag(trust);
    bool use_env = !lean_is_scalar(env_opt);
    bool platform = kind == trust_system && !use_env;

    if (kind > trust_insecure_skip_verify) return mk_ssl_invalid_argument("unknown trust mode");
    if (lean_is_scalar(cert_opt) != lean_is_scalar(key_opt))
        return mk_ssl_invalid_argument("a certificate and its key must be given together");
    if (kind == trust_only && lean_array_size(cas) == 0)
        return mk_ssl_invalid_argument("`Trust.only` needs at least one CA certificate");

    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_client_method(), min, max, &err);
    if (ctx == nullptr) return err;

    if (!lean_is_scalar(cert_opt)) {
        if (lean_obj_res e = load_credentials(ctx.get(), lean_ctor_get(cert_opt, 0), lean_ctor_get(key_opt, 0)))
            return e;
    }

    if (kind == trust_insecure_skip_verify) {
        SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(std::move(ctx));
    }

    X509_STORE * store = SSL_CTX_get_cert_store(ctx.get());

    // Any certificate in the store may end a chain, so an intermediate can be trusted on its own.
    X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()), X509_V_FLAG_PARTIAL_CHAIN);

    x509_stack_ptr distrusted(sk_X509_new_null());
    if (distrusted == nullptr) return mk_openssl_io_error("could not create the TLS context");

    if (lean_obj_res e = load_ca_bundles(store, cas, X509_TRUST_SSL_SERVER, distrusted.get())) return e;

    bool has_ca = lean_array_size(cas) > 0;
    bool platform_roots = false;
    int env_added = 0;

    if (platform) {
        std::string detail;
        platform_roots = use_system_trust_store(ctx.get(), &detail);

        if (!platform_roots && !has_ca) return no_trust_store(detail);
    }

    if (use_env) {
        b_obj_arg env = lean_ctor_get(env_opt, 0);

        // A directory may hold anything, so what is not a certificate is skipped.
        for (size_t i = 0; i < lean_array_size(env); i++) {
            if (lean_obj_res e = load_env_bundle(store, lean_array_get_core(env, i), &env_added, distrusted.get()))
                return e;
        }

        if (!has_ca && (env_added == 0 || !store_has_anchor(store, X509_TRUST_SSL_SERVER, distrusted.get()))) {
            return no_trust_store(env_added == 0
                ? "SSL_CERT_FILE and SSL_CERT_DIR name no certificate (files that are missing, unreadable, "
                  "not regular or too large are skipped)"
                : "SSL_CERT_FILE and SSL_CERT_DIR name no certificate trusted for TLS server authentication");
        }
    }

    // The platform's anchors give every chain somewhere to end, so the check only applies without them.
    if (has_ca && !platform_roots && !store_has_anchor(store, X509_TRUST_SSL_SERVER, distrusted.get()))
        return no_anchor_error(cas, env_added == 0, X509_TRUST_SSL_SERVER);

    if (!install_chain_verifier(ctx.get(), store, X509_TRUST_SSL_SERVER, platform_roots, distrusted.get()))
        return mk_openssl_io_error("could not configure certificate verification");

    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(std::move(ctx));
}

// Initializes OpenSSL with Lean's flags before any other call can initialize it with the defaults, and
// keeps C++ exceptions out of Lean code.
template<typename F>
static lean_obj_res ssl_entry_point(F && build) {
    try {
        if (!ensure_openssl_initialized()) {
            ERR_clear_error();
            return mk_tls_unsupported("could not initialize the TLS library");
        }

        return build();
    } catch (std::exception & ex) {
        ERR_clear_error();
        return lean_io_result_mk_error(lean_mk_io_user_error(mk_string(ex.what())));
    }
}

/* Std.Internal.SSL.Context.Server.mkImpl (cert key : @& LoadedPEM) (clientAuth : @& ClientAuth)
     (clientCA : @& Array LoadedPEM) (minVersion maxVersion : Version) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert, b_obj_arg key, b_obj_arg client_auth,
                                                           b_obj_arg client_ca, uint8_t min, uint8_t max) {
    return ssl_entry_point([&] { return mk_server_ctx(cert, key, client_auth, client_ca, min, max); });
}

/* Std.Internal.SSL.Context.Client.mkImpl (trust : @& Trust) (ca : @& Array LoadedPEM)
     (env : @& Option (Array LoadedPEM)) (cert key : @& Option LoadedPEM) (minVersion maxVersion : Version) :
     IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg trust, b_obj_arg ca, b_obj_arg env,
                                                           b_obj_arg cert, b_obj_arg key, uint8_t min, uint8_t max) {
    return ssl_entry_point([&] { return mk_client_ctx(trust, ca, env, cert, key, min, max); });
}

/* Std.Internal.SSL.Context.Client.envIgnored : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_ssl_env_ignored() {
    // Set-user-ID and set-group-ID programs must not take trust from their caller's environment.
    return OPENSSL_issetugid() != 0;
}

#else

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg, uint8_t,
                                                           uint8_t) {
    return mk_tls_unsupported("this build of Lean has no TLS support");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg,
                                                           uint8_t, uint8_t) {
    return mk_tls_unsupported("this build of Lean has no TLS support");
}

extern "C" LEAN_EXPORT uint8_t lean_ssl_env_ignored() {
    return 0;
}

#endif

}
