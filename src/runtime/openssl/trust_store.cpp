/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/trust_store.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/crypto.h>
#include <openssl/err.h>
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

// The hash directories named by the environment, or null where it names none.
static char const * env_cert_dirs() {
    return getenv_or_null_if_empty(X509_get_default_cert_dir_env());
}

// Loads the anchors named by `SSL_CERT_FILE` and `SSL_CERT_DIR`, and reports whether the named bundle
// could be read.
static bool load_env_anchors(X509_STORE * store, std::string * detail) {
    char const * env_file = getenv_or_null_if_empty(X509_get_default_cert_file_env());
    char const * env_dir = env_cert_dirs();

    if (env_dir != nullptr) X509_STORE_load_path(store, env_dir);

    if (env_file != nullptr && X509_STORE_load_file(store, env_file) != 1) {
        *detail = std::string(X509_get_default_cert_file_env()) +
                  " names a file holding no readable certificate";
        return false;
    }

    return true;
}

#if !defined(__APPLE__)

// Whether a hash directory holds a certificate. Hash entries are usually symlinks, so one left dangling
// by a removed certificate does not count.
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

        struct stat st;
        if (i > digits && name[i] == '\0' && stat((std::string(path) + "/" + name).c_str(), &st) == 0 && S_ISREG(st.st_mode)) {
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

// Adds the compiled-in locations, whatever the environment says. `SSL_CTX_set_default_verify_paths`
// would read the environment *instead* of them wherever it is set, so a variable naming a file that no
// longer exists would leave nothing behind.
static void load_default_paths(X509_STORE * store) {
    X509_STORE_load_file(store, X509_get_default_cert_file());
    X509_STORE_load_path(store, X509_get_default_cert_dir());
}

// Whether the store demonstrably holds a trust anchor: a certificate loaded into it, or one in the
// hash directories `dirs` names.
static bool trust_store_has_certs(X509_STORE * store, char const * dirs) {
    if (dirs != nullptr && any_dir_with_certs(dirs)) return true;

    STACK_OF(X509) * certs = X509_STORE_get1_all_certs(store);
    if (certs == nullptr) return false;

    bool any = sk_X509_num(certs) > 0;
    sk_X509_pop_free(certs, X509_free);

    return any;
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

// Adds the first readable of the well-known bundles, plus every hash directory that exists.
static bool load_fallback_anchors(X509_STORE * store) {
    bool any = false;

    for (char const * file : g_fallback_cert_files) {
        if (X509_STORE_load_file(store, file) == 1) {
            any = true;
            break;
        }
    }

    // `X509_STORE_load_path` only records the path — the lookup itself is lazy — so it reports
    // success for a directory that does not exist, and the directory has to be examined directly.
    for (char const * dir : g_fallback_cert_dirs) {
        if (dir_has_hashed_certs(dir) && X509_STORE_load_path(store, dir) == 1) any = true;
    }

    // A load that failed leaves its own reason behind, and the caller either succeeds or reports a
    // failure of its own.
    ERR_clear_error();

    return any;
}

#endif

#if defined(__APPLE__)

template<auto release> struct released_by { void operator()(auto * p) const { release(p); } };
template<typename T> using cf_ptr = std::unique_ptr<std::remove_pointer_t<T>, released_by<CFRelease>>;

static void free_x509_stack(STACK_OF(X509) * sk) { sk_X509_pop_free(sk, X509_free); }
using x509_stack_ptr = std::unique_ptr<STACK_OF(X509), released_by<free_x509_stack>>;

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

// The peer's certificates, leaf first, as `SecTrustCreateWithCertificates` takes them.
static CFArrayRef copy_peer_certificates(X509_STORE_CTX * ctx) {
    X509 * leaf = X509_STORE_CTX_get0_cert(ctx);
    STACK_OF(X509) * sent = X509_STORE_CTX_get0_untrusted(ctx);

    cf_ptr<CFMutableArrayRef> certs(CFArrayCreateMutable(nullptr, 0, &kCFTypeArrayCallBacks));
    if (certs == nullptr || leaf == nullptr || !append_sec_certificate(certs.get(), leaf)) return nullptr;

    for (int i = 0; i < sk_X509_num(sent); i++) {
        X509 * cert = sk_X509_value(sent, i);
        if (cert != leaf && !append_sec_certificate(certs.get(), cert)) return nullptr;
    }

    return certs.release();
}

// Verifies `ctx`'s peer again with OpenSSL, trusting only the anchor the platform settled on, so the
// name, purpose and key-strength checks are OpenSSL's own as on every other platform. libssl reads
// the verdict, the verified chain and the peer name back from `ctx`, so all three are moved there.
// Only the verification parameters carry over: the fresh context has no verify callback, CRLs, DANE
// or stapled OCSP response, none of which a Lean context sets.
static int verify_along_evaluated_chain(X509_STORE_CTX * ctx, SecTrustRef trust) {
    x509_stack_ptr untrusted(sk_X509_new_null());
    x509_stack_ptr anchor(sk_X509_new_null());
    std::unique_ptr<X509_STORE_CTX, released_by<X509_STORE_CTX_free>> check(X509_STORE_CTX_new());

    CFIndex n = SecTrustGetCertificateCount(trust);
    bool built = untrusted != nullptr && anchor != nullptr && check != nullptr;

    // The evaluated chain runs from the leaf to the anchor.
    for (CFIndex i = 0; built && i < n; i++) {
        // `SecTrustCopyCertificateChain` replaces this, but only from macOS 12, and releases target 11.
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
        cf_ptr<CFDataRef> der(SecCertificateCopyData(SecTrustGetCertificateAtIndex(trust, i)));
#pragma clang diagnostic pop

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

// The OpenSSL error for what the platform rejected, or the store's own verdict where the platform's
// code is no more precise. Apple ranks a breach of its TLS certificate rules (a leaf valid for too
// long, a disallowed name or usage) above an untrusted chain, so such a code is only reported as a
// rejection once the chain is known to reach a trusted anchor; otherwise the store's verdict stands.
static int x509_error_for(SecTrustRef trust, CFErrorRef error, int store_error) {
    switch (error != nullptr ? CFErrorGetCode(error) : 0) {
    case errSecCertificateExpired: return X509_V_ERR_CERT_HAS_EXPIRED;
    case errSecCertificateNotValidYet: return X509_V_ERR_CERT_NOT_YET_VALID;
    case errSecCertificateRevoked: return X509_V_ERR_CERT_REVOKED;
    case errSecCertificateValidityPeriodTooLong:
    case errSecCertificateNameNotAllowed:
    case errSecCertificatePolicyNotAllowed:
    case errSecInvalidExtendedKeyUsage:
        if (reaches_platform_anchor(trust)) return X509_V_ERR_CERT_REJECTED;
        [[fallthrough]];
    default: return store_error != X509_V_OK ? store_error : X509_V_ERR_CERT_UNTRUSTED;
    }
}

// Accepts a chain the store's own anchors establish, and otherwise defers to the system's trust
// evaluation, which applies the Keychain's trust settings and Apple's CA policy as they stand now.
static int verify_with_platform_fallback(X509_STORE_CTX * ctx, void *) {
    if (X509_verify_cert(ctx) > 0) return 1;

    int store_error = X509_STORE_CTX_get_error(ctx);

    // A name is checked only once the store has built a chain, and a second opinion on the chain
    // cannot change the name. A session that does not verify its peer discards the verdict anyway.
    SSL * ssl = static_cast<SSL *>(X509_STORE_CTX_get_ex_data(ctx, SSL_get_ex_data_X509_STORE_CTX_idx()));

    if (store_error == X509_V_ERR_HOSTNAME_MISMATCH || store_error == X509_V_ERR_IP_ADDRESS_MISMATCH ||
        store_error == X509_V_ERR_EMAIL_MISMATCH ||
        (ssl != nullptr && (SSL_get_verify_mode(ssl) & SSL_VERIFY_PEER) == 0)) {
        return 0;
    }

    cf_ptr<CFArrayRef> certs(copy_peer_certificates(ctx));

    // No name is given: the OpenSSL pass that follows checks it.
    cf_ptr<SecPolicyRef> policy(SecPolicyCreateSSL(true, nullptr));

    // `SecTrustCreateWithCertificates` accepts a null policy, which would drop the TLS rules.
    SecTrustRef raw_trust = nullptr;
    bool created = certs != nullptr && policy != nullptr &&
                   SecTrustCreateWithCertificates(certs.get(), policy.get(), &raw_trust) == errSecSuccess;
    cf_ptr<SecTrustRef> trust(raw_trust);

    // Fetching would download issuers from URLs in the unauthenticated peer's certificates,
    // synchronously, bounded per certificate but not per chain: a peer sending cross-signed copies
    // could hold the handshake for minutes. A chain missing an intermediate fails, as elsewhere.
    created = created && SecTrustSetNetworkFetchAllowed(trust.get(), false) == errSecSuccess;

    if (!created) {
        X509_STORE_CTX_set_error(ctx, X509_V_ERR_UNSPECIFIED);
        return 0;
    }

    CFErrorRef raw_error = nullptr;
    bool trusted = SecTrustEvaluateWithError(trust.get(), &raw_error);
    cf_ptr<CFErrorRef> error(raw_error);

    if (!trusted) {
        X509_STORE_CTX_set_error(ctx, x509_error_for(trust.get(), error.get(), store_error));
        return 0;
    }

    return verify_along_evaluated_chain(ctx, trust.get());
}

#endif

bool use_system_trust_store(SSL_CTX * ctx, std::string * detail) {
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    std::string env_detail;

#if defined(__APPLE__)
    // The platform verifier stands behind the store, so an unreadable `SSL_CERT_FILE` never leaves the
    // context without anchors.
    load_env_anchors(store, &env_detail);
    (void)detail;

    ERR_clear_error();
    SSL_CTX_set_cert_verify_callback(ctx, verify_with_platform_fallback, nullptr);

    return true;
#else
    // The platform's anchors are settled before the environment's are added, so that a variable naming
    // a single private CA adds it to them instead of standing in for them.
#if defined(LEAN_WINDOWS)
    bool platform = SSL_CTX_load_verify_store(ctx, "org.openssl.winstore://") == 1;

    if (!platform) {
        load_default_paths(store);
        platform = trust_store_has_certs(store, X509_get_default_cert_dir());
    }
#else
    load_default_paths(store);
    bool platform = trust_store_has_certs(store, X509_get_default_cert_dir()) || load_fallback_anchors(store);
#endif

    bool env_ok = load_env_anchors(store, &env_detail);

    if (platform || trust_store_has_certs(store, env_cert_dirs())) {
        ERR_clear_error();
        return true;
    }

    // A variable naming an unreadable file is the likelier thing to have gone wrong, so it is what
    // gets reported once nothing else supplied an anchor either.
#if defined(LEAN_WINDOWS)
    char const * none = "the Windows ROOT store is unavailable (it needs OpenSSL 3.2 or later) and no CA "
                        "file was configured";
#else
    char const * none = "no trust anchors: OpenSSL's configured certificate paths hold none, and none of "
                        "the usual system bundles could be read either (set SSL_CERT_FILE or SSL_CERT_DIR)";
#endif
    *detail = env_ok ? none : env_detail;
    return false;
#endif
}

}

#endif
