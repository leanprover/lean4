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
#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstring>
#include <memory>
#include <string>
#include <sys/stat.h>

#endif

namespace lean {

lean_external_class * g_ssl_context_external_class = nullptr;

#ifndef LEAN_EMSCRIPTEN

static lean_obj_res reject_embedded_nul(b_obj_arg path) {
    return strlen(lean_string_cstr(path)) == lean_string_size(path) - 1
        ? nullptr
        : mk_embedded_nul_error(path);
}

// PEM material the caller named: a path when `is_file`, otherwise the bytes themselves.
struct pem_source {
    b_obj_arg obj;
    bool is_file;

    char const * data() const { return lean_string_cstr(obj); }
    size_t size() const { return lean_string_size(obj) - 1; }
};

// Reports a failure against a path. `errnum` is the `errno` the open failed with, or 0 for a
// failure with no OS error behind it (unparsable PEM, a key that does not match its certificate).
static lean_obj_res mk_ssl_file_error(b_obj_arg file, char const * msg, int errnum = 0) {
    ERR_clear_error();

    struct stat st;

    if (stat(lean_string_cstr(file), &st) == 0 && !S_ISREG(st.st_mode)) {
        lean_inc(file);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(
            file, EINVAL, mk_string(std::string(msg) + " (the path is not a regular file)")));
    }

    if (errnum != 0) return lean_io_result_mk_error(decode_io_error(errnum, file));

    lean_inc(file);
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(
        file, EINVAL, mk_string(msg)));
}

static int reject_encrypted_pem(char *, int, int, void *) { return -1; }

// Reports a failure with no errno behind it, discarding the queue so it cannot taint a later one.
static lean_obj_res mk_ssl_invalid_argument(char const * msg) {
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(EINVAL, mk_string(msg)));
}

// Reports a failure against PEM material, naming the path when there is one to name.
static lean_obj_res mk_pem_error(pem_source src, char const * msg, int errnum = 0) {
    return src.is_file ? mk_ssl_file_error(src.obj, msg, errnum) : mk_ssl_invalid_argument(msg);
}

// Opens `src` for reading. On failure returns nullptr and stores an IO error in `*err`.
static BIO * open_pem_bio(pem_source src, char const * unreadable, lean_obj_res * err) {
    if (src.is_file) {
        // Captured here rather than recovered later by re-opening the path, which would both race
        // and lose the distinction between an open failure and an unreadable file.
        errno = 0;
        BIO * bio = BIO_new_file(src.data(), "r");
        if (bio == nullptr) *err = mk_ssl_file_error(src.obj, unreadable, errno);
        return bio;
    }

    if (src.size() > (size_t)INT_MAX) {
        *err = mk_ssl_invalid_argument("the PEM string is too large");
        return nullptr;
    }

    BIO * bio = BIO_new_mem_buf(src.data(), (int)src.size());
    if (bio == nullptr) *err = mk_ssl_invalid_argument(unreadable);
    return bio;
}

// Whether a certificate was turned away on policy grounds rather than being unreadable as PEM.
static bool rejected_by_security_level() {
    unsigned long err = ERR_peek_last_error();

    if (ERR_GET_LIB(err) != ERR_LIB_SSL) return false;

    int reason = ERR_GET_REASON(err);
    return reason == SSL_R_EE_KEY_TOO_SMALL || reason == SSL_R_CA_KEY_TOO_SMALL ||
           reason == SSL_R_CA_MD_TOO_WEAK;
}

lean_object * mk_openssl_error(char const * where) {
    std::string msg(where);

    for (int i = 0; i < 10; i++) {
        unsigned long err = ERR_get_error();
        if (err == 0) break;

        char err_buf[256];
        ERR_error_string_n(err, err_buf, sizeof(err_buf));

        msg += i == 0 ? ": " : "; ";
        msg += err_buf;
    }

    if (ERR_peek_error() != 0) {
        msg += "; ... (truncated)";
        ERR_clear_error();
    }

    return lean_mk_io_user_error(mk_string(msg));
}

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

        // Disables RFC 5077 session tickets in TLS 1.2. In TLS 1.3 it only downgrades them to the
        // stateful form; the call below is what stops those being sent.
        SSL_OP_NO_TICKET
    );

    // Without this a TLS 1.3 server still puts two NewSessionTickets on the wire per connection.
    // Read only by the server state machine.
    SSL_CTX_set_num_tickets(ctx, 0);

    // A backstop. Every read this file performs goes through a bare BIO and passes the callback
    // itself, so nothing here consults this one; it is set so that any OpenSSL path reaching for the
    // context's callback still cannot end up prompting on a terminal.
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

// What `SSL_CTX_use_certificate_chain_file` does, against an arbitrary BIO: the leaf certificate
// plus every intermediate behind it, so the whole chain reaches the peer. There is no public
// `SSL_CTX_use_certificate_chain_bio`, so in-memory material has to go the long way round.
static bool use_certificate_chain_bio(SSL_CTX * ctx, BIO * bio) {
    // `_AUX` so a certificate carrying OpenSSL's trust extensions is read the same way the file
    // variant reads it.
    X509 * leaf = PEM_read_bio_X509_AUX(bio, nullptr, reject_encrypted_pem, nullptr);
    if (leaf == nullptr) return false;

    bool used = SSL_CTX_use_certificate(ctx, leaf) == 1;
    X509_free(leaf);

    if (!used || SSL_CTX_clear_chain_certs(ctx) != 1) return false;

    while (X509 * ca = PEM_read_bio_X509(bio, nullptr, reject_encrypted_pem, nullptr)) {
        // Takes ownership only on success.
        if (SSL_CTX_add0_chain_cert(ctx, ca) != 1) {
            X509_free(ca);
            return false;
        }
    }

    // The loop ends either on a malformed block or on running out of them; only the latter is fine,
    // so a corrupt intermediate is rejected rather than silently dropping the rest of the chain.
    unsigned long err = ERR_peek_last_error();

    if (ERR_GET_LIB(err) != ERR_LIB_PEM || ERR_GET_REASON(err) != PEM_R_NO_START_LINE) return false;

    ERR_clear_error();
    return true;
}

// Loads the certificate chain the server presents and the key it signs with.
static lean_obj_res load_server_credentials(SSL_CTX * ctx, pem_source cert, pem_source key) {
    ERR_clear_error();

    char const * unreadable_cert = "could not read a PEM certificate chain";
    lean_obj_res err = nullptr;
    BIO * cert_bio = open_pem_bio(cert, unreadable_cert, &err);

    if (cert_bio == nullptr) return err;

    bool cert_ok = use_certificate_chain_bio(ctx, cert_bio);
    BIO_free(cert_bio);

    if (!cert_ok) {
        return mk_pem_error(cert, rejected_by_security_level()
            ? "the certificate is rejected by the TLS security level (key too small or signature "
              "digest too weak)"
            : unreadable_cert);
    }

    ERR_clear_error();

    char const * unreadable_key = "could not read an unencrypted PEM private key";
    char const * mismatch = "the private key does not match the certificate";
    BIO * key_bio = open_pem_bio(key, unreadable_key, &err);

    if (key_bio == nullptr) return err;

    EVP_PKEY * pkey = PEM_read_bio_PrivateKey(key_bio, nullptr, reject_encrypted_pem, nullptr);
    BIO_free(key_bio);

    if (pkey == nullptr) return mk_pem_error(key, unreadable_key);

    bool used = SSL_CTX_use_PrivateKey(ctx, pkey) == 1;
    EVP_PKEY_free(pkey);

    // A key of the certificate's own algorithm is compared here and rejected outright; one of a
    // different algorithm lands in an unused slot instead, which only the check below catches.
    if (!used) {
        return mk_pem_error(key, ERR_GET_LIB(ERR_peek_last_error()) == ERR_LIB_X509
            ? mismatch
            : unreadable_key);
    }

    ERR_clear_error();

    if (SSL_CTX_check_private_key(ctx) != 1) return mk_pem_error(key, mismatch);

    return nullptr;
}

static lean_obj_res mk_server_ctx(b_obj_arg cert, uint8_t cert_is_file, b_obj_arg key,
                                  uint8_t key_is_file) {
    pem_source cert_src{cert, cert_is_file != 0};
    pem_source key_src{key, key_is_file != 0};

    // Only a path has to survive the trip through a C string; in-memory PEM is read with a length,
    // so a NUL there is data.
    if (cert_src.is_file) {
        if (lean_obj_res err = reject_embedded_nul(cert)) return err;
    }

    if (key_src.is_file) {
        if (lean_obj_res err = reject_embedded_nul(key)) return err;
    }

    lean_obj_res base_err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_server_method(), &base_err);
    if (ctx == nullptr) return base_err;

    // The server presents its certificate but never authenticates the client (no mutual TLS).
    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);

    if (lean_obj_res err = load_server_credentials(ctx.get(), cert_src, key_src)) return err;

    return wrap_ssl_context(std::move(ctx));
}

// Adds every certificate `src` yields to the trust store, on top of whatever it already holds.
// With `require_self_signed`, the material must also hold a certificate a chain can terminate at.
static lean_obj_res load_ca_bundle(SSL_CTX * ctx, pem_source src, bool require_self_signed) {
    ERR_clear_error();

    char const * unreadable = "could not read PEM CA certificates";
    char const * no_certs = "the CA material contains no certificates";

    lean_obj_res err = nullptr;
    BIO * bio = open_pem_bio(src, unreadable, &err);

    if (bio == nullptr) return err;

    STACK_OF(X509_INFO) * infos = PEM_X509_INFO_read_bio(bio, nullptr, reject_encrypted_pem, nullptr);
    BIO_free(bio);

    if (infos == nullptr) return mk_pem_error(src, unreadable);

    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    int cert_count = 0;
    bool any_self_signed = false;

    for (int i = 0, n = sk_X509_INFO_num(infos); i < n; i++) {
        // A bundle may hold private keys and CRLs; only certificates are anchors.
        X509 * cert = sk_X509_INFO_value(infos, i)->x509;

        if (cert == nullptr) continue;
        cert_count++;

        // `EXFLAG_SS` is the same notion of self-signed that chain building terminates on. A bundle
        // pairing a root with the intermediates below it therefore passes on the strength of the root.
        if ((X509_get_extension_flags(cert) & EXFLAG_SS) != 0) any_self_signed = true;

        if (X509_STORE_add_cert(store, cert) != 1) {
            err = mk_openssl_io_error("X509_STORE_add_cert failed");
            break;
        }
    }

    sk_X509_INFO_pop_free(infos, X509_INFO_free);

    if (err != nullptr) return err;
    if (cert_count == 0) return mk_pem_error(src, no_certs);

    if (require_self_signed && !any_self_signed) {
        return mk_pem_error(src,
            "the CA material holds no self-signed certificate, so no chain can terminate in it "
            "(supply the root, or allow partial chains to anchor at an intermediate)");
    }

    return nullptr;
}

// `has_ca` says whether the caller supplied CA material at all, which decides whether dropping the
// platform anchors would leave nothing behind. `load_ca_bundle` is what enforces that supplied
// material actually yields a certificate, so the two together guarantee a verifying context has an
// anchor.
static lean_obj_res mk_client_ctx(uint8_t verify_peer, uint8_t trust_system_roots,
                                  uint8_t allow_partial_chain, bool has_ca, pem_source ca) {
    if (verify_peer && !trust_system_roots && !has_ca) {
        return mk_ssl_invalid_argument(
            "no trust anchors: peer verification is on, the platform trust anchors are excluded, "
            "and no CA certificate was given");
    }

    lean_obj_res err = nullptr;
    ssl_ctx_ptr ctx = mk_ssl_ctx_base(TLS_client_method(), &err);
    if (ctx == nullptr) return err;

    // With verification off the CA material is never consulted.
    if (!verify_peer) {
        SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_NONE, nullptr);
        return wrap_ssl_context(std::move(ctx));
    }

    if (allow_partial_chain) {
        // Lets chain building stop at any certificate in the store rather than only at a self-signed
        // one, which is what anchoring on an intermediate requires.
        X509_VERIFY_PARAM_set_flags(SSL_CTX_get0_param(ctx.get()), X509_V_FLAG_PARTIAL_CHAIN);
    }

    if (trust_system_roots) {
        std::string detail;

        if (!load_system_trust_store(ctx.get(), &detail)) {
            std::string msg("failed to load system trust store");
            if (!detail.empty()) msg += ": " + detail;

            return lean_io_result_mk_error(mk_openssl_error(msg.c_str()));
        }
    }

    // The caller's own CAs are added to whatever the store already holds: on top of the platform
    // anchors, or into an otherwise empty store when those were excluded.
    if (has_ca) {
        // An anchor that cannot terminate a chain is only a dead configuration when it is the sole
        // source of anchors; alongside the platform roots it is merely redundant.
        bool require_self_signed = !allow_partial_chain && !trust_system_roots;

        if (lean_obj_res ca_err = load_ca_bundle(ctx.get(), ca, require_self_signed)) return ca_err;
    }

    SSL_CTX_set_verify(ctx.get(), SSL_VERIFY_PEER, nullptr);
    return wrap_ssl_context(std::move(ctx));
}

static lean_obj_res mk_client_ctx_checked(b_obj_arg ca, uint8_t ca_is_file, uint8_t has_ca,
                                          uint8_t verify_peer, uint8_t trust_system_roots,
                                          uint8_t allow_partial_chain) {
    pem_source ca_src{ca, ca_is_file != 0};

    // Checked before `verifyPeer` is consulted, so a path that could never be opened is reported as
    // such even where it would not have been read.
    if (has_ca && ca_src.is_file) {
        if (lean_obj_res err = reject_embedded_nul(ca)) return err;
    }

    return mk_client_ctx(verify_peer, trust_system_roots, allow_partial_chain, has_ca != 0, ca_src);
}

// Runs a constructor behind the two guards every entry point needs: OpenSSL initialized before any
// `ERR_*` call can register `atexit(OPENSSL_cleanup)` behind `OPENSSL_INIT_NO_ATEXIT`'s back, and no
// C++ exception escaping into Lean-generated code.
template<typename F>
static lean_obj_res ssl_entry_point(F && build) {
    try {
        if (!ensure_openssl_initialized()) {
            return lean_io_result_mk_error(lean_mk_io_user_error(
                mk_string("OPENSSL_init_ssl failed")));
        }

        return build();
    } catch (std::exception & ex) {
        return lean_io_result_mk_error(lean_mk_io_user_error(mk_string(ex.what())));
    }
}

/* Std.Internal.SSL.Context.Server.mkImpl (cert : @& String) (certIsFile : Bool)
   (key : @& String) (keyIsFile : Bool) : IO Context.Server */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg cert, uint8_t cert_is_file, b_obj_arg key, uint8_t key_is_file) {
    return ssl_entry_point([&] { return mk_server_ctx(cert, cert_is_file, key, key_is_file); });
}

/* Std.Internal.SSL.Context.Client.mkImpl (ca : @& String) (caIsFile hasCA verifyPeer
   trustSystemRoots allowPartialChain : Bool) : IO Context.Client */
extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg ca, uint8_t ca_is_file, uint8_t has_ca, uint8_t verify_peer, uint8_t trust_system_roots, uint8_t allow_partial_chain) {
    return ssl_entry_point([&] {
        return mk_client_ctx_checked(ca, ca_is_file, has_ca, verify_peer, trust_system_roots, allow_partial_chain);
    });
}

#else

void initialize_openssl_context() {}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_server(b_obj_arg /*cert*/,
        uint8_t /*cert_is_file*/, b_obj_arg /*key*/, uint8_t /*key_is_file*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

extern "C" LEAN_EXPORT lean_obj_res lean_ssl_ctx_mk_client(b_obj_arg /*ca*/, uint8_t /*ca_is_file*/,
        uint8_t /*has_ca*/, uint8_t /*verify_peer*/, uint8_t /*trust_system_roots*/,
        uint8_t /*allow_partial_chain*/) {
    lean_always_assert(false && "Please build a version of Lean4 with OpenSSL to invoke this.");
}

#endif

}
