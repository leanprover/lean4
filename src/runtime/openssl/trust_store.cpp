/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/trust_store.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <dirent.h>
#include <string>
#include <sys/stat.h>

#if defined(__APPLE__)
#include <AvailabilityMacros.h>
#include <Security/Security.h>
#include <CoreFoundation/CoreFoundation.h>
#include <memory>
#include <type_traits>
#endif

namespace lean {

static char const * getenv_or_null_if_empty(char const * name) {
    if (OPENSSL_issetugid()) return nullptr;

    char const * value = getenv(name);
    return value != nullptr && value[0] != '\0' ? value : nullptr;
}

// Whether the store holds a certificate; `X509_STORE_load_file` also succeeds on a CRL-only file.
static bool store_holds_certificate(X509_STORE * store) {
    STACK_OF(X509_OBJECT) * objs = X509_STORE_get0_objects(store);

    for (int i = 0, n = sk_X509_OBJECT_num(objs); i < n; i++) {
        if (X509_OBJECT_get_type(sk_X509_OBJECT_value(objs, i)) == X509_LU_X509) return true;
    }

    return false;
}

// The hash directories named by the environment, or null where it names none.
static char const * env_cert_dirs() {
    return getenv_or_null_if_empty(X509_get_default_cert_dir_env());
}

// Loads the anchors named by `SSL_CERT_FILE` and `SSL_CERT_DIR`, and reports whether the named bundle
// could be read. OpenSSL reads them with an empty passphrase, so a block encrypted under one is trusted.
static bool load_env_anchors(X509_STORE * store, std::string * detail) {
    char const * env_file = getenv_or_null_if_empty(X509_get_default_cert_file_env());
    char const * env_dir = env_cert_dirs();

    if (env_dir != nullptr) X509_STORE_load_path(store, env_dir);

    bool env_file_ok = env_file == nullptr ||
                       (X509_STORE_load_file(store, env_file) == 1 && store_holds_certificate(store));

    if (!env_file_ok) {
        *detail = std::string(X509_get_default_cert_file_env()) +
                  " names a file holding no readable certificate";
        return false;
    }

    return true;
}

#if !defined(__APPLE__)

// Whether `path` is a regular file holding a certificate as a hash directory lookup reads it: PEM,
// under an empty passphrase.
static bool hashed_file_has_cert(std::string const & path) {
    struct stat st;
    if (stat(path.c_str(), &st) != 0 || !S_ISREG(st.st_mode)) return false;

    BIO * bio = BIO_new_file(path.c_str(), "rb");
    if (bio == nullptr) return false;

    X509 * cert = PEM_read_bio_X509_AUX(bio, nullptr, nullptr, const_cast<char *>(""));
    bool found = cert != nullptr;

    X509_free(cert);
    BIO_free(bio);
    return found;
}

// Whether a hash directory holds a certificate. A dangling symlink, or a file that is unreadable or
// holds no certificate, does not count.
static bool dir_has_hashed_certs(char const * path) {
    DIR * dir = opendir(path);
    if (dir == nullptr) return false;

    bool found = false;

    while (dirent * entry = readdir(dir)) {
        char const * name = entry->d_name;
        size_t i = 0;

        while (i < 8 && isxdigit((unsigned char)name[i])) i++;
        if (i != 8 || name[i] != '.') continue;

        size_t digits = ++i;
        while (isdigit((unsigned char)name[i])) i++;

        if (i > digits && name[i] == '\0' && hashed_file_has_cert(std::string(path) + "/" + name)) {
            found = true;
            break;
        }
    }

    closedir(dir);
    return found;
}

// Whether any entry of a `SSL_CERT_DIR`-style list names a directory holding a certificate.
static bool any_dir_with_certs(char const * list_str) {
#if defined(LEAN_WINDOWS)
    char const sep = ';';
#else
    char const sep = ':';
#endif
    std::string list(list_str);

    for (size_t p = 0; p <= list.size(); ) {
        size_t end = std::min(list.find(sep, p), list.size());
        std::string entry = list.substr(p, end - p);

        if (!entry.empty() && dir_has_hashed_certs(entry.c_str())) return true;
        p = end + 1;
    }

    return false;
}

// OpenSSL's compiled-in locations. A standalone toolchain skips them: they name directories on the
// build machine.
#if defined(LEAN_WINDOWS) && !defined(LEAN_STANDALONE)
static void load_default_paths(X509_STORE * store) {
    X509_STORE_load_file(store, X509_get_default_cert_file());
    X509_STORE_load_path(store, X509_get_default_cert_dir());
}
#endif

// Whether the store holds a certificate, or one of the hash directories `dirs` does.
static bool trust_store_has_certs(X509_STORE * store, char const * dirs) {
    return (dirs != nullptr && any_dir_with_certs(dirs)) || store_holds_certificate(store);
}

#endif

#if !defined(__APPLE__) && !defined(LEAN_WINDOWS)

// Where the mainstream distributions keep their anchors.
static char const * const g_fallback_cert_files[] = {
    "/etc/ssl/certs/ca-certificates.crt", // Debian, Ubuntu, Arch, Alpine
    "/etc/pki/tls/certs/ca-bundle.crt", // Fedora, RHEL, CentOS
    "/etc/ssl/ca-bundle.pem", // openSUSE
    "/etc/ssl/cert.pem", // Alpine, FreeBSD
};

static char const * const g_fallback_cert_dirs[] = {
    "/etc/ssl/certs",
    "/etc/pki/tls/certs",
};

// Adds the first readable of the well-known bundles, stored in `*bundle`, plus every hash directory
// that exists.
static bool load_fallback_anchors(X509_STORE * store, char const ** bundle) {
    bool any = false;

    for (char const * file : g_fallback_cert_files) {
        if (X509_STORE_load_file(store, file) == 1 && store_holds_certificate(store)) {
            *bundle = file;
            any = true;
            break;
        }
    }

    // `X509_STORE_load_path` succeeds even for a missing directory, since lookups are lazy.
    for (char const * dir : g_fallback_cert_dirs) {
        if (dir_has_hashed_certs(dir) && X509_STORE_load_path(store, dir) == 1) any = true;
    }

    // The caller reports failure in its own terms.
    ERR_clear_error();

    return any;
}

#endif

#if defined(__APPLE__)

template<auto release> struct released_by { void operator()(auto * p) const { release(p); } };
template<typename T> using cf_ptr = std::unique_ptr<std::remove_pointer_t<T>, released_by<CFRelease>>;

static void free_x509_stack(STACK_OF(X509) * sk) { sk_X509_pop_free(sk, X509_free); }
using x509_stack_ptr = std::unique_ptr<STACK_OF(X509), released_by<free_x509_stack>>;

static void free_openssl_string(char * str) { OPENSSL_free(str); }

static bool append_sec_certificate(CFMutableArrayRef certs, X509 * cert) {
    unsigned char * der = nullptr;
    int len = i2d_X509(cert, &der);
    if (len < 0) return false;

    cf_ptr<CFDataRef> data(CFDataCreate(nullptr, der, len));
    OPENSSL_free(der);
    if (data == nullptr) return false;

    cf_ptr<SecCertificateRef> sec_cert(SecCertificateCreateWithData(nullptr, data.get()));
    if (sec_cert == nullptr) return false;

    CFArrayAppendValue(certs, sec_cert.get());
    return true;
}

// What `SecTrustCreateWithCertificates` takes: the peer's certificates, leaf first, then the
// intermediates the store added to the partial chain.
static CFArrayRef copy_candidate_certificates(X509_STORE_CTX * ctx) {
    X509 * leaf = X509_STORE_CTX_get0_cert(ctx);
    STACK_OF(X509) * sent = X509_STORE_CTX_get0_untrusted(ctx);

    cf_ptr<CFMutableArrayRef> certs(CFArrayCreateMutable(nullptr, 0, &kCFTypeArrayCallBacks));
    if (certs == nullptr || leaf == nullptr || !append_sec_certificate(certs.get(), leaf)) return nullptr;

    for (int i = 0; i < sk_X509_num(sent); i++) {
        X509 * cert = sk_X509_value(sent, i);
        if (cert != leaf && !append_sec_certificate(certs.get(), cert)) return nullptr;
    }

    // From `ca`, `SSL_CERT_FILE` or `SSL_CERT_DIR`; with fetching off, Apple may not find them itself.
    STACK_OF(X509) * built = X509_STORE_CTX_get0_chain(ctx);

    for (int i = 1; i < sk_X509_num(built); i++) {
        X509 * cert = sk_X509_value(built, i);

        // A `TRUSTED CERTIFICATE` block rejecting it must not become a hint for Apple's path building.
        if (sk_X509_find(sent, cert) >= 0 ||
            X509_check_trust(cert, X509_TRUST_SSL_SERVER, 0) == X509_TRUST_REJECTED) {
            continue;
        }

        if (!append_sec_certificate(certs.get(), cert)) return nullptr;
    }

    return certs.release();
}

// The chain the evaluation settled on, leaf first and anchor last.
static CFArrayRef copy_evaluated_chain(SecTrustRef trust) {
#if MAC_OS_X_VERSION_MIN_REQUIRED >= 120000
    return SecTrustCopyCertificateChain(trust);
#else
    CFIndex n = SecTrustGetCertificateCount(trust);
    CFMutableArrayRef chain = CFArrayCreateMutable(nullptr, n, &kCFTypeArrayCallBacks);
    if (chain == nullptr) return nullptr;
    for (CFIndex i = 0; i < n; i++) CFArrayAppendValue(chain, SecTrustGetCertificateAtIndex(trust, i));
    return chain;
#endif
}

// Verifies the peer again with OpenSSL, trusting only the anchor the platform settled on, so name,
// purpose and key-strength checks match other platforms. libssl reads the verdict, verified chain and
// peer name back from `ctx`. Only the verification parameters carry over; Lean sets no verify
// callback, CRLs, DANE or stapled OCSP.
static int verify_along_evaluated_chain(X509_STORE_CTX * ctx, SecTrustRef trust) {
    x509_stack_ptr untrusted(sk_X509_new_null());
    x509_stack_ptr anchor(sk_X509_new_null());
    std::unique_ptr<X509_STORE_CTX, released_by<X509_STORE_CTX_free>> check(X509_STORE_CTX_new());

    cf_ptr<CFArrayRef> chain(copy_evaluated_chain(trust));
    CFIndex n = chain != nullptr ? CFArrayGetCount(chain.get()) : 0;
    bool built = chain != nullptr && untrusted != nullptr && anchor != nullptr && check != nullptr;

    for (CFIndex i = 0; built && i < n; i++) {
        cf_ptr<CFDataRef> der(SecCertificateCopyData((SecCertificateRef)CFArrayGetValueAtIndex(chain.get(), i)));
        if (der == nullptr) { built = false; break; }

        unsigned char const * bytes = CFDataGetBytePtr(der.get());
        X509 * cert = d2i_X509(nullptr, &bytes, CFDataGetLength(der.get()));

        built = cert != nullptr && sk_X509_push(i + 1 < n ? untrusted.get() : anchor.get(), cert) > 0;
        if (!built) X509_free(cert);
    }

    if (!built || X509_STORE_CTX_init(check.get(), nullptr, X509_STORE_CTX_get0_cert(ctx), untrusted.get()) != 1) {
        X509_STORE_CTX_set_error(ctx, X509_V_ERR_UNSPECIFIED);
        return 0;
    }

    X509_STORE_CTX_set0_trusted_stack(check.get(), anchor.get());

    X509_VERIFY_PARAM * param = X509_STORE_CTX_get0_param(check.get());
    X509_VERIFY_PARAM_set1(param, X509_STORE_CTX_get0_param(ctx));

    // A trust setting may have placed the anchor on an intermediate or on the leaf itself.
    X509_VERIFY_PARAM_set_flags(param, X509_V_FLAG_PARTIAL_CHAIN);

    int ok = X509_verify_cert(check.get());

    X509_STORE_CTX_set_error(ctx, X509_STORE_CTX_get_error(check.get()));
    X509_STORE_CTX_set0_verified_chain(ctx, X509_STORE_CTX_get1_chain(check.get()));
    X509_VERIFY_PARAM_move_peername(X509_STORE_CTX_get0_param(ctx), param);

    return ok > 0;
}

// Whether `trust`'s chain reaches an anchor the platform trusts at all, Apple's TLS rules aside.
static bool reaches_platform_anchor(SecTrustRef trust) {
    cf_ptr<SecPolicyRef> basic(SecPolicyCreateBasicX509());
    return basic != nullptr && SecTrustSetPolicies(trust, basic.get()) == errSecSuccess &&
           SecTrustEvaluateWithError(trust, nullptr);
}

// The OpenSSL error for the platform's rejection, falling back to the store's verdict. Apple reports
// a TLS rule breach (name mismatch, pinning, validity too long, disallowed usage) ahead of an
// untrusted chain, so it only counts as a rejection once the chain is known to reach a trusted anchor.
static int x509_error_for(SecTrustRef trust, CFErrorRef error, int store_error, bool ip) {
    CFIndex code = error != nullptr ? CFErrorGetCode(error) : 0;

    switch (code) {
    case errSecCertificateExpired: return X509_V_ERR_CERT_HAS_EXPIRED;
    case errSecCertificateNotValidYet: return X509_V_ERR_CERT_NOT_YET_VALID;
    case errSecCertificateRevoked: return X509_V_ERR_CERT_REVOKED;
    }

    if (!reaches_platform_anchor(trust)) return store_error != X509_V_OK ? store_error : X509_V_ERR_CERT_UNTRUSTED;
    if (code == errSecHostNameMismatch) return ip ? X509_V_ERR_IP_ADDRESS_MISMATCH : X509_V_ERR_HOSTNAME_MISMATCH;

    return X509_V_ERR_CERT_REJECTED;
}

// Apple's TLS policy for the peer's name, or null on failure; `*ip` reports an IP address. Apple
// applies its pinned hosts and host-scoped Keychain trust settings only for a named peer, and takes one
// name, so a peer allowed several gets none and is left to the OpenSSL pass.
static SecPolicyRef copy_ssl_policy(X509_VERIFY_PARAM * param, bool * ip) {
    *ip = false;
    if (X509_VERIFY_PARAM_get0_host(param, 1) != nullptr) return SecPolicyCreateSSL(true, nullptr);

    char const * host = X509_VERIFY_PARAM_get0_host(param, 0);
    std::unique_ptr<char, released_by<free_openssl_string>> ip_str(
        host == nullptr ? X509_VERIFY_PARAM_get1_ip_asc(param) : nullptr);
    char const * name = host != nullptr ? host : ip_str.get();

    if (name == nullptr) return SecPolicyCreateSSL(true, nullptr);

    cf_ptr<CFStringRef> cf_name(CFStringCreateWithCString(nullptr, name, kCFStringEncodingUTF8));
    if (cf_name == nullptr) return nullptr;

    *ip = ip_str != nullptr;
    return SecPolicyCreateSSL(true, cf_name.get());
}

// Accepts a chain the store's anchors establish, and otherwise defers to the system's trust
// evaluation (Keychain trust settings and Apple's CA policy).
static int verify_with_platform_fallback(X509_STORE_CTX * ctx, void *) {
    if (X509_verify_cert(ctx) > 0) return 1;

    int store_error = X509_STORE_CTX_get_error(ctx);

    // A name mismatch implies the chain was already built, and a non-verifying session discards the
    // verdict: neither needs the platform.
    SSL * ssl = static_cast<SSL *>(X509_STORE_CTX_get_ex_data(ctx, SSL_get_ex_data_X509_STORE_CTX_idx()));

    if (store_error == X509_V_ERR_HOSTNAME_MISMATCH || store_error == X509_V_ERR_IP_ADDRESS_MISMATCH ||
        store_error == X509_V_ERR_EMAIL_MISMATCH ||
        (ssl != nullptr && (SSL_get_verify_mode(ssl) & SSL_VERIFY_PEER) == 0)) {
        return 0;
    }

    cf_ptr<CFArrayRef> certs(copy_candidate_certificates(ctx));

    bool ip = false;
    cf_ptr<SecPolicyRef> policy(copy_ssl_policy(X509_STORE_CTX_get0_param(ctx), &ip));

    // `SecTrustCreateWithCertificates` accepts a null policy, which would drop the TLS rules.
    SecTrustRef raw_trust = nullptr;
    bool created = certs != nullptr && policy != nullptr &&
                   SecTrustCreateWithCertificates(certs.get(), policy.get(), &raw_trust) == errSecSuccess;
    cf_ptr<SecTrustRef> trust(raw_trust);

    // Fetching downloads issuers named by the unauthenticated peer, synchronously and unbounded per
    // chain, which lets a peer stall the handshake for minutes.
    created = created && SecTrustSetNetworkFetchAllowed(trust.get(), false) == errSecSuccess;

    if (!created) {
        X509_STORE_CTX_set_error(ctx, X509_V_ERR_UNSPECIFIED);
        return 0;
    }

    CFErrorRef raw_error = nullptr;
    bool trusted = SecTrustEvaluateWithError(trust.get(), &raw_error);
    cf_ptr<CFErrorRef> error(raw_error);

    if (!trusted) {
        X509_STORE_CTX_set_error(ctx, x509_error_for(trust.get(), error.get(), store_error, ip));
        return 0;
    }

    return verify_along_evaluated_chain(ctx, trust.get());
}

#endif

bool use_system_trust_store(SSL_CTX * ctx, std::string * detail) {
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    std::string env_detail;

#if defined(__APPLE__)
    // The platform verifier backs the store, so an unreadable `SSL_CERT_FILE` is not an error.
    load_env_anchors(store, &env_detail);
    (void)detail;

    ERR_clear_error();
    SSL_CTX_set_cert_verify_callback(ctx, verify_with_platform_fallback, nullptr);

    return true;
#else
    // Platform anchors are decided first, so the environment's add to them rather than replace them.
#if defined(LEAN_WINDOWS)
    // Opened eagerly, so a missing loader fails here, but certificates load lazily and cannot be
    // counted.
    bool platform = SSL_CTX_load_verify_store(ctx, "org.openssl.winstore://") == 1;

#if !defined(LEAN_STANDALONE)
    if (!platform) {
        load_default_paths(store);
        platform = trust_store_has_certs(store, X509_get_default_cert_dir());
    }
#endif
#else
    // The distribution bundles are always read; the compiled-in paths only add to them.
    char const * bundle = nullptr;
    bool platform = load_fallback_anchors(store, &bundle);

#if !defined(LEAN_STANDALONE)
    // A distribution's OpenSSL usually names the bundle just read, which would parse it twice.
    char const * default_file = X509_get_default_cert_file();
    struct stat read_st, default_st;
    bool same_bundle = bundle != nullptr && stat(bundle, &read_st) == 0 &&
                       stat(default_file, &default_st) == 0 && read_st.st_dev == default_st.st_dev &&
                       read_st.st_ino == default_st.st_ino;

    if (!same_bundle) X509_STORE_load_file(store, default_file);
    X509_STORE_load_path(store, X509_get_default_cert_dir());
    platform = platform || trust_store_has_certs(store, X509_get_default_cert_dir());
#endif
#endif

    bool env_ok = load_env_anchors(store, &env_detail);

    if (platform || trust_store_has_certs(store, env_cert_dirs())) {
        ERR_clear_error();
        return true;
    }

    // With no anchor anywhere, an unreadable `SSL_CERT_FILE` is the likelier cause.
#if defined(LEAN_WINDOWS)
    char const * none = "the Windows ROOT store is unavailable (it needs OpenSSL 3.2 or later) and no CA "
                        "file was configured";
#else
    char const * none = OPENSSL_issetugid()
        ? "no trust anchors: none of the usual system bundles could be read (SSL_CERT_FILE and "
          "SSL_CERT_DIR are ignored in a set-user-ID or set-group-ID process)"
        : "no trust anchors: none of the usual system bundles could be read "
          "(set SSL_CERT_FILE or SSL_CERT_DIR)";
#endif
    *detail = env_ok ? none : env_detail;

    // `detail` already summarizes the load failures.
    ERR_clear_error();

    return false;
#endif
}

}

#endif
