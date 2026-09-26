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

struct ssl_deleter { void operator()(SSL * ssl) const { SSL_free(ssl); } };
struct x509_store_deleter { void operator()(X509_STORE * store) const { X509_STORE_free(store); } };
using x509_store_ptr = std::unique_ptr<X509_STORE, x509_store_deleter>;

void initialize_openssl_context() {
    g_ssl_context_external_class = lean_register_external_class([](void * ptr) {
        SSL_CTX_free((SSL_CTX*)ptr);
    }, [](void *, lean_object *) {});
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
    // exactly the chain it was given, never one completed from the trust store.
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

    // 0 leaves that end of the range open.
    return (min == 0 || min <= version) && (max == 0 || max >= version) &&
           (SSL_CTX_get_options(ctx) & disabled_by) == 0;
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
// otherwise still offer that version and then fail every handshake.
static lean_obj_res check_usable(SSL_CTX * ctx) {
    bool tls12 = version_permitted(ctx, TLS1_2_VERSION, SSL_OP_NO_TLSv1_2);
    bool tls13 = version_permitted(ctx, TLS1_3_VERSION, SSL_OP_NO_TLSv1_3);

    if (!tls12 && !tls13) return refused_by_policy("versions", "permits none of the TLS versions allowed here");

    std::unique_ptr<SSL, ssl_deleter> ssl(SSL_new(ctx));
    if (ssl == nullptr) return mk_openssl_io_error("could not create the TLS context");

    // Null when nothing is left.
    STACK_OF(SSL_CIPHER) * usable = SSL_get1_supported_ciphers(ssl.get());
    int n12 = 0, n13 = 0;

    for (int i = 0; i < sk_SSL_CIPHER_num(usable); i++) {
        bool is13 = strcmp(SSL_CIPHER_get_version(sk_SSL_CIPHER_value(usable, i)), "TLSv1.3") == 0;
        (is13 ? n13 : n12)++;
    }

    sk_SSL_CIPHER_free(usable);

    if (tls12 && n12 == 0) return no_suite_left("TLS 1.2");
    if (tls13 && n13 == 0) return no_suite_left("TLS 1.3");

    return nullptr;
}

// Creates a configured SSL_CTX accepting versions `min` to `max` (as `Std.Internal.SSL.Version`), or
// returns nullptr with an IO error stored in `*err`.
static ssl_ctx_ptr mk_ssl_ctx_base(const SSL_METHOD * method, uint8_t min, uint8_t max, lean_obj_res * err) {
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

// Wraps a fully configured SSL_CTX into a Lean external object, taking ownership of it.
static lean_obj_res wrap_ssl_context(ssl_ctx_ptr ctx) {
    // A successful build can still leave errors queued, e.g. from `X509_check_trust`.
    ERR_clear_error();

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

// Loads the certificate chain presented to the peer and the key it signs with.
static lean_obj_res load_credentials(SSL_CTX * ctx, b_obj_arg cert, b_obj_arg key) {
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

// Whether the store holds a certificate a chain can end at. Every context verifies with partial chains,
// so that is any certificate a `TRUSTED CERTIFICATE` block does not reject for `trust_id`. The store
// keeps only the first copy of a repeated certificate, so its copies are the ones checked.
static bool store_has_anchor(X509_STORE * store, int trust_id) {
    STACK_OF(X509) * certs = X509_STORE_get1_all_certs(store);
    if (certs == nullptr) return false;

    bool any = false;
    for (int i = 0; !any && i < sk_X509_num(certs); i++) {
        any = X509_check_trust(sk_X509_value(certs, i), trust_id, 0) != X509_TRUST_REJECTED;
    }

    sk_X509_pop_free(certs, X509_free);
    return any;
}

// Adds every certificate in `src` to `store`, and its subject to the names a server sends when asking
// for a client certificate if `names_for` is given. `*added` counts the certificates. Material holding
// no certificate is an error unless `lenient`, which also skips material that does not parse.
static lean_obj_res load_ca_bundle(X509_STORE * store, SSL_CTX * names_for, b_obj_arg src, bool lenient,
                                   int * added) {
    ERR_clear_error();

    char const * unreadable = "could not read PEM CA certificates";
    lean_obj_res err = nullptr;
    BIO * bio = open_pem_bio(src, unreadable, &err);

    if (bio == nullptr) return err;

    STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, reject_encrypted_pem, nullptr);
    BIO_free(bio);

    if (infos == nullptr) {
        if (!lenient) return mk_pem_error(src, unreadable);

        ERR_clear_error();
        return nullptr;
    }

    int cert_count = 0;

    for (int i = 0, n = sk_X509_INFO_num(infos); i < n; i++) {
        // A bundle may hold private keys and CRLs; only certificates are anchors.
        X509 * cert = sk_X509_INFO_value(infos, i)->x509;

        if (cert == nullptr) continue;
        cert_count++;

        if (X509_STORE_add_cert(store, cert) != 1 ||
            (names_for != nullptr && SSL_CTX_add_client_CA(names_for, cert) != 1)) {
            err = mk_openssl_io_error("could not add a CA certificate to the trust store");
            break;
        }
    }

    sk_X509_INFO_pop_free(infos, X509_INFO_free);
    *added += cert_count;

    if (err != nullptr)
        return err;

    if (cert_count == 0 && !lenient)
        return mk_pem_error(src, "the CA material contains no certificates");

    return nullptr;
}

// Loads each bundle of `cas` into `store`, then requires the store to hold an anchor for `trust_id`.
static lean_obj_res load_ca_bundles(X509_STORE * store, SSL_CTX * names_for, b_obj_arg cas, int trust_id) {
    size_t n = lean_array_size(cas);
    int added = 0;

    for (size_t i = 0; i < n; i++) {
        if (lean_obj_res err = load_ca_bundle(store, names_for, lean_array_get_core(cas, i), false, &added))
            return err;
    }

    if (store_has_anchor(store, trust_id)) return nullptr;

    char const * msg = "the CA material holds no certificate a chain may end at: every one is marked "
                       "as distrusted";

    // With several bundles no single file is to blame.
    return n == 1 ? mk_pem_error(lean_array_get_core(cas, 0), msg) : mk_ssl_invalid_argument(msg);
}

// The index of an `SSL_CTX` extra-data slot holding the server's ALPN list, freed with the context.
static int alpn_index() {
    static int const index = SSL_CTX_get_ex_new_index(0, nullptr, nullptr, nullptr,
        [](void *, void * list, CRYPTO_EX_DATA *, int, long, void *) {
            delete static_cast<std::string *>(list);
        });
    return index;
}

// Whether the ALPN wire-format entry at `p` (length byte, then name) is `name`.
static bool alpn_is(unsigned char const * p, char const * name) {
    size_t len = strlen(name);
    return p[0] == len && memcmp(p + 1, name, len) == 0;
}

// Picks the first protocol in the server's list that the client offered. A client offering only other
// protocols is refused with a `no_application_protocol` alert, except that one offering `http/1.1` to a
// server listing `h2` proceeds without ALPN.
static int select_alpn(SSL *, unsigned char const ** out, unsigned char * out_len,
                       unsigned char const * offered, unsigned int offered_len, void * arg) {
    std::string const & list = *static_cast<std::string const *>(arg);
    auto server = reinterpret_cast<unsigned char const *>(list.data());
    bool http11_fallback = false;

    for (size_t i = 0; i < list.size(); i += 1 + server[i]) {
        // libssl has checked that each of the client's entries fits in its list.
        for (unsigned j = 0; j < offered_len; j += 1 + offered[j]) {
            if (server[i] == offered[j] && memcmp(server + i + 1, offered + j + 1, server[i]) == 0) {
                *out = offered + j + 1;
                *out_len = offered[j];
                return SSL_TLSEXT_ERR_OK;
            }

            http11_fallback |= alpn_is(server + i, "h2") && alpn_is(offered + j, "http/1.1");
        }
    }

    return http11_fallback ? SSL_TLSEXT_ERR_NOACK : SSL_TLSEXT_ERR_ALERT_FATAL;
}

// `Context.Server.ClientAuth`'s constructors, in declaration order.
enum client_auth_kind : unsigned { auth_none, auth_request, auth_require_any, auth_verify_if_given,
                                   auth_require_and_verify };

// `Context.Client.Trust`'s constructors, in declaration order.
enum trust_kind : unsigned { trust_system, trust_only, trust_insecure_skip_verify };

// Checks the settings every context shares and builds the ALPN list in the wire format of RFC 7301:
// each `String` of `names` preceded by its length in one byte.
static lean_obj_res check_common(b_obj_arg names, uint8_t min, uint8_t max, std::string * wire) {
    if (min > max) return mk_ssl_invalid_argument("`minVersion` is above `maxVersion`");

    for (size_t i = 0; i < lean_array_size(names); i++) {
        b_obj_arg name = lean_array_get_core(names, i);
        size_t len = lean_string_size(name) - 1;

        if (len == 0 || len > 255) {
            std::string msg = "an ALPN protocol name must be 1 to 255 bytes long: \"" +
                              std::string(lean_string_cstr(name), len) + "\"";
            return mk_ssl_invalid_argument(msg.c_str());
        }

        wire->push_back(static_cast<char>(len));
        wire->append(lean_string_cstr(name), len);
    }

    if (wire->size() > 65535) return mk_ssl_invalid_argument("the ALPN protocol list is longer than 65535 bytes");

    return nullptr;
}

// For the client-authentication modes that take whatever certificate is sent.
static int accept_any_certificate(int, X509_STORE_CTX *) { return 1; }

// `Std.Internal.SSL.Context.Server.mkImpl`. `client_ca` holds the CAs of `client_auth`, loaded.
static lean_obj_res mk_server_ctx(b_obj_arg cert, b_obj_arg key, b_obj_arg client_auth, b_obj_arg client_ca,
                                  b_obj_arg alpn_names, uint8_t min, uint8_t max) {
    unsigned auth = lean_obj_tag(client_auth);
    bool verifies = auth == auth_verify_if_given || auth == auth_require_and_verify;

    if (verifies && lean_array_size(client_ca) == 0)
        return mk_ssl_invalid_argument("verifying client certificates needs at least one CA certificate");

    std::string alpn;
    if (lean_obj_res e = check_common(alpn_names, min, max, &alpn)) return e;

    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_server_method(), min, max, &err);
    if (ctx == nullptr) return err;

    if (lean_obj_res e = load_credentials(ctx.get(), cert, key)) return e;

    int mode = SSL_VERIFY_NONE;
    SSL_verify_cb callback = nullptr;

    switch (auth) {
    case auth_request: mode = SSL_VERIFY_PEER; callback = accept_any_certificate; break;
    case auth_require_any: mode = SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT; callback = accept_any_certificate; break;
    case auth_verify_if_given: mode = SSL_VERIFY_PEER; break;
    case auth_require_and_verify: mode = SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT; break;
    }

    if (lean_array_size(client_ca) > 0) {
        // Kept apart from the context's own store, which a server never needs for its chain.
        x509_store_ptr store(X509_STORE_new());
        if (store == nullptr) return mk_openssl_io_error("could not create the TLS context");

        if (lean_obj_res e = load_ca_bundles(store.get(), ctx.get(), client_ca, X509_TRUST_SSL_CLIENT)) return e;

        SSL_CTX_set0_verify_cert_store(ctx.get(), store.release());
        X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()), X509_V_FLAG_PARTIAL_CHAIN);
    }

    SSL_CTX_set_verify(ctx.get(), mode, callback);

    // Only matters when a session could be resumed, which none can, but a verifying server without it is
    // an error to OpenSSL.
    static unsigned char const session_id_context[] = "lean";
    SSL_CTX_set_session_id_context(ctx.get(), session_id_context, sizeof(session_id_context) - 1);

    if (!alpn.empty()) {
        auto * list = new std::string(std::move(alpn));

        if (SSL_CTX_set_ex_data(ctx.get(), alpn_index(), list) != 1) {
            delete list;
            return mk_openssl_io_error("could not configure ALPN");
        }

        SSL_CTX_set_alpn_select_cb(ctx.get(), select_alpn, list);
    }

    return wrap_ssl_context(std::move(ctx));
}

// `Std.Internal.SSL.Context.Client.mkImpl`. `cas` holds the CAs of `trust`, loaded, and `env_opt` the
// files `SSL_CERT_FILE` and `SSL_CERT_DIR` name for `Trust.system` if either is set, which then replace
// the platform's anchors.
static lean_obj_res mk_client_ctx(b_obj_arg trust, b_obj_arg cas, b_obj_arg env_opt, b_obj_arg cert_opt,
                                  b_obj_arg key_opt, b_obj_arg alpn_names, uint8_t min, uint8_t max) {
    unsigned kind = lean_obj_tag(trust);
    bool verify = kind != trust_insecure_skip_verify;
    bool use_env = !lean_is_scalar(env_opt);
    bool platform = kind == trust_system && !use_env;

    if (kind == trust_only && lean_array_size(cas) == 0)
        return mk_ssl_invalid_argument("`Trust.only` needs at least one CA certificate");

    std::string alpn;
    if (lean_obj_res e = check_common(alpn_names, min, max, &alpn)) return e;

    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_client_method(), min, max, &err);
    if (ctx == nullptr) return err;

    if (!lean_is_scalar(cert_opt)) {
        if (lean_obj_res e = load_credentials(ctx.get(), lean_ctor_get(cert_opt, 0), lean_ctor_get(key_opt, 0)))
            return e;
    }

    // Unlike most OpenSSL functions, 0 is success.
    if (!alpn.empty() &&
        SSL_CTX_set_alpn_protos(ctx.get(), reinterpret_cast<unsigned char const *>(alpn.data()),
                                (unsigned)alpn.size()) != 0) {
        return mk_openssl_io_error("could not configure ALPN");
    }

    if (!verify) {
        SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(std::move(ctx));
    }

    X509_STORE * store = SSL_CTX_get_cert_store(ctx.get());

    // Any certificate in the store may end a chain, so an intermediate can be trusted on its own.
    X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()), X509_V_FLAG_PARTIAL_CHAIN);

    bool has_ca = lean_array_size(cas) > 0;
    bool platform_roots = false;

    if (platform) {
        std::string detail;
        platform_roots = use_system_trust_store(ctx.get(), &detail);

        if (!platform_roots && !has_ca) {
            std::string msg("failed to load system trust store");
            if (!detail.empty()) msg += ": " + detail;

            return lean_io_result_mk_error(lean_mk_io_error_no_such_thing(ENOENT, mk_string(msg)));
        }
    }

    if (use_env) {
        b_obj_arg env = lean_ctor_get(env_opt, 0);
        int added = 0;

        // Like `SSL_CERT_DIR` lookups, files that are not certificates are skipped.
        for (size_t i = 0; i < lean_array_size(env); i++) {
            if (lean_obj_res e = load_ca_bundle(store, nullptr, lean_array_get_core(env, i), true, &added))
                return e;
        }

        if (added == 0 && !has_ca) {
            return lean_io_result_mk_error(lean_mk_io_error_no_such_thing(ENOENT, mk_string(
                "failed to load system trust store: SSL_CERT_FILE and SSL_CERT_DIR name no certificate")));
        }
    }

    // The platform's anchors are not in the store, so the check only applies without them.
    if (has_ca) {
        if (platform_roots) {
            int added = 0;

            for (size_t i = 0; i < lean_array_size(cas); i++) {
                if (lean_obj_res e = load_ca_bundle(store, nullptr, lean_array_get_core(cas, i), false, &added))
                    return e;
            }
        } else if (lean_obj_res e = load_ca_bundles(store, nullptr, cas, X509_TRUST_SSL_SERVER)) {
            return e;
        }
    }

    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(std::move(ctx));
}

// Initializes OpenSSL before any other call can register `atexit(OPENSSL_cleanup)`, and keeps C++
// exceptions out of Lean code.
template<typename F>
static lean_obj_res ssl_entry_point(F && build) {
    try {
        if (!ensure_openssl_initialized()) {
            ERR_clear_error();
            return mk_tls_unsupported("could not initialize the TLS library");
        }

        return build();
    } catch (std::exception & ex) {
        return lean_io_result_mk_error(lean_mk_io_user_error(mk_string(ex.what())));
    }
}

/* Std.Internal.SSL.Context.Server.mkImpl (cert key : @& LoadedPEM) (clientAuth : @& ClientAuth)
     (clientCA : @& Array LoadedPEM) (alpn : @& Array String) (minVersion maxVersion : Version) :
     IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert, b_obj_arg key, b_obj_arg client_auth,
                                                           b_obj_arg client_ca, b_obj_arg alpn, uint8_t min,
                                                           uint8_t max) {
    return ssl_entry_point([&] { return mk_server_ctx(cert, key, client_auth, client_ca, alpn, min, max); });
}

/* Std.Internal.SSL.Context.Client.mkImpl (trust : @& Trust) (ca : @& Array LoadedPEM)
     (env : @& Option (Array LoadedPEM)) (cert key : @& Option LoadedPEM) (alpn : @& Array String)
     (minVersion maxVersion : Version) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg trust, b_obj_arg ca, b_obj_arg env,
                                                           b_obj_arg cert, b_obj_arg key, b_obj_arg alpn,
                                                           uint8_t min, uint8_t max) {
    return ssl_entry_point([&] { return mk_client_ctx(trust, ca, env, cert, key, alpn, min, max); });
}

/* Std.Internal.SSL.Context.Client.envIgnored : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_ssl_env_ignored() {
    // Set-user-ID and set-group-ID programs must not take trust from their caller's environment.
    return OPENSSL_issetugid() != 0;
}

#else

void initialize_openssl_context() {}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg,
                                                           uint8_t, uint8_t) {
    return mk_tls_unsupported("this build of Lean has no TLS support");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg, b_obj_arg,
                                                           b_obj_arg, uint8_t, uint8_t) {
    return mk_tls_unsupported("this build of Lean has no TLS support");
}

extern "C" LEAN_EXPORT uint8_t lean_ssl_env_ignored() {
    return 0;
}

#endif

}
