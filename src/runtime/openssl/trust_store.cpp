/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#if defined(LEAN_WINDOWS)
// Before OpenSSL's headers, which undefine the names `wincrypt.h` takes from them.
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#define NOMINMAX
#include <windows.h>
#include <wincrypt.h>
#endif

#include "runtime/openssl.h"
#include "runtime/openssl/trust_store.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/pem.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <memory>
#include <string>

#if defined(__APPLE__)
#include <AvailabilityMacros.h>
#include <Security/Security.h>
#include <CoreFoundation/CoreFoundation.h>
#include <type_traits>
#elif !defined(LEAN_WINDOWS)
#include <algorithm>
#include <cctype>
#include <dirent.h>
#include <sys/stat.h>
#endif

namespace lean {

#if !defined(__APPLE__) && !defined(LEAN_WINDOWS)

// The certificates in the store, which already holds the caller's own CAs when the system's are
// loaded; `X509_STORE_load_file` also succeeds on a CRL-only file, so the count is what shows a load
// added any.
static int certificate_count(X509_STORE * store) {
    STACK_OF(X509_OBJECT) * objs = X509_STORE_get0_objects(store);
    int count = 0;

    for (int i = 0, n = sk_X509_OBJECT_num(objs); i < n; i++) {
        if (X509_OBJECT_get_type(sk_X509_OBJECT_value(objs, i)) == X509_LU_X509) count++;
    }

    return count;
}

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

        // OpenSSL looks names up in lowercase hex.
        while (i < 8 && isxdigit((unsigned char)name[i]) && !isupper((unsigned char)name[i])) i++;
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

#if !defined(LEAN_STANDALONE)

// Whether any entry of a `:`-separated list names a hash directory holding a certificate.
static bool any_dir_with_certs(char const * list_str) {
    std::string list(list_str);

    for (size_t p = 0; p <= list.size(); ) {
        size_t end = std::min(list.find(':', p), list.size());
        std::string entry = list.substr(p, end - p);

        if (!entry.empty() && dir_has_hashed_certs(entry.c_str())) return true;
        p = end + 1;
    }

    return false;
}

#endif

// Where the mainstream distributions keep their anchors.
static char const * const g_fallback_cert_files[] = {
    "/etc/ssl/certs/ca-certificates.crt", // Debian, Ubuntu, Arch, Alpine
    "/etc/pki/tls/certs/ca-bundle.crt", // Fedora, RHEL, CentOS
    "/etc/ssl/ca-bundle.pem", // openSUSE
    "/etc/pki/tls/cacert.pem", // OpenELEC
    "/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem", // CentOS, RHEL 7
    "/etc/ssl/cert.pem", // Alpine, FreeBSD
};

static char const * const g_fallback_cert_dirs[] = {
    "/etc/ssl/certs",
    "/etc/pki/tls/certs",
};

// Adds the first of the well-known bundles that adds a certificate, stored in `*bundle`, plus every hash
// directory holding one.
static bool load_fallback_anchors(X509_STORE * store, char const ** bundle) {
    bool any = false;

    int before = certificate_count(store);

    for (char const * file : g_fallback_cert_files) {
        if (X509_STORE_load_file(store, file) == 1 && certificate_count(store) > before) {
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

bool push_ref(STACK_OF(X509) * sk, X509 * cert) {
    if (sk_X509_push(sk, cert) <= 0) return false;
    X509_up_ref(cert);
    return true;
}

// Whether `a` and `b` carry the same public key. The keys are compared rather than their encodings, which
// may differ for one key (an RSA key with or without its NULL parameters); keys OpenSSL cannot compare
// still match on identical key bits.
static bool same_key(X509 * a, X509 * b) {
    EVP_PKEY * key_a = X509_get0_pubkey(a);
    EVP_PKEY * key_b = X509_get0_pubkey(b);
    if (key_a != nullptr && key_b != nullptr && EVP_PKEY_eq(key_a, key_b) == 1) return true;

    ASN1_BIT_STRING const * bits_a = X509_get0_pubkey_bitstr(a);
    ASN1_BIT_STRING const * bits_b = X509_get0_pubkey_bitstr(b);
    return bits_a != nullptr && bits_b != nullptr && ASN1_STRING_cmp(bits_a, bits_b) == 0;
}

bool has_distrusted_key(STACK_OF(X509) * distrusted, X509 * cert) {
    // Comparing keys of different types queues an error even though the answer is only "no". It must not
    // outlive the comparison: during a handshake libssl would read it as the handshake's own failure.
    ERR_set_mark();

    bool found = false;
    for (int j = 0; !found && j < sk_X509_num(distrusted); j++) {
        found = same_key(cert, sk_X509_value(distrusted, j));
    }

    ERR_pop_to_mark();
    return found;
}

// Whether `chain` holds a certificate with the key of one in `distrusted`. Distrust follows the key, so a
// re-issued or cross-signed copy of a distrusted CA is distrusted too, whichever copy a chain goes through.
static bool chain_has_distrusted(STACK_OF(X509) * distrusted, STACK_OF(X509) * chain) {
    for (int i = 0; i < sk_X509_num(chain); i++) {
        if (has_distrusted_key(distrusted, sk_X509_value(chain, i))) return true;
    }

    return false;
}

// What the verify callback of a verifying context needs, freed with the context.
struct chain_verifier {
    // The certificates, from the store or the caller's material, that a `TRUSTED CERTIFICATE` block
    // rejects for the peer's role.
    STACK_OF(X509) * distrusted;
    // Whether a chain the store cannot establish goes to the platform (macOS, Windows).
    bool platform;
};

static int chain_verifier_index() {
    static int const index = SSL_CTX_get_ex_new_index(0, nullptr, nullptr, nullptr,
        [](void *, void * verifier, CRYPTO_EX_DATA *, int, long, void *) {
            if (verifier == nullptr) return;
            free_x509_stack(static_cast<chain_verifier *>(verifier)->distrusted);
            delete static_cast<chain_verifier *>(verifier);
        });
    return index;
}

#if defined(__APPLE__) || defined(LEAN_WINDOWS)

// The certificates the platform may build a chain from: the peer's, leaf first, then the certificates
// from `Trust.system`'s extra CAs that the store added to the partial chain, which the platform would
// not find on its own.
static STACK_OF(X509) * candidate_certificates(X509_STORE_CTX * ctx) {
    X509 * leaf = X509_STORE_CTX_get0_cert(ctx);
    STACK_OF(X509) * sent = X509_STORE_CTX_get0_untrusted(ctx);

    x509_stack_ptr certs(sk_X509_new_null());
    if (certs == nullptr || leaf == nullptr || !push_ref(certs.get(), leaf)) return nullptr;

    for (int i = 0; i < sk_X509_num(sent); i++) {
        X509 * cert = sk_X509_value(sent, i);
        if (cert != leaf && !push_ref(certs.get(), cert)) return nullptr;
    }

    STACK_OF(X509) * built = X509_STORE_CTX_get0_chain(ctx);

    for (int i = 1; i < sk_X509_num(built); i++) {
        X509 * cert = sk_X509_value(built, i);

        // A `TRUSTED CERTIFICATE` block rejecting it must not become a hint for the platform's path
        // building.
        if (sk_X509_find(sent, cert) >= 0 ||
            X509_check_trust(cert, X509_TRUST_SSL_SERVER, 0) == X509_TRUST_REJECTED) {
            continue;
        }

        if (!push_ref(certs.get(), cert)) return nullptr;
    }

    return certs.release();
}

// Appends the DER certificate to `sk`.
static bool push_der(STACK_OF(X509) * sk, unsigned char const * der, long len) {
    X509 * cert = d2i_X509(nullptr, &der, len);
    if (cert != nullptr && sk_X509_push(sk, cert) > 0) return true;

    X509_free(cert);
    return false;
}

// Verifies the peer again with OpenSSL along `chain` (leaf first, anchor last), the chain the platform
// settled on, trusting only its anchor, so name, purpose and key-strength checks match other platforms.
// libssl reads the verdict, verified chain and peer name back from `ctx`. Only the verification
// parameters carry over; Lean sets no verify callback, CRLs, DANE or stapled OCSP.
static int verify_along_chain(X509_STORE_CTX * ctx, STACK_OF(X509) * chain) {
    x509_stack_ptr untrusted(sk_X509_new_null());
    x509_stack_ptr anchor(sk_X509_new_null());
    std::unique_ptr<X509_STORE_CTX, released_by<X509_STORE_CTX_free>> check(X509_STORE_CTX_new());

    int n = sk_X509_num(chain);
    bool built = n > 0 && untrusted != nullptr && anchor != nullptr && check != nullptr;

    for (int i = 0; built && i < n; i++) {
        built = push_ref(i + 1 < n ? untrusted.get() : anchor.get(), sk_X509_value(chain, i));
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

#endif

#if defined(__APPLE__)

template<typename T> using cf_ptr = std::unique_ptr<std::remove_pointer_t<T>, released_by<CFRelease>>;

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

// The chain the system's trust evaluation (Keychain trust settings and Apple's CA policy) builds from
// `candidates`, leaf first. On rejection returns null and sets `*error`.
static STACK_OF(X509) * platform_chain(X509_STORE_CTX * ctx, STACK_OF(X509) * candidates, int store_error,
                                       int * error) {
    *error = X509_V_ERR_UNSPECIFIED;

    cf_ptr<CFMutableArrayRef> certs(CFArrayCreateMutable(nullptr, 0, &kCFTypeArrayCallBacks));
    if (certs == nullptr) return nullptr;

    for (int i = 0; i < sk_X509_num(candidates); i++) {
        if (!append_sec_certificate(certs.get(), sk_X509_value(candidates, i))) return nullptr;
    }

    bool ip = false;
    cf_ptr<SecPolicyRef> policy(copy_ssl_policy(X509_STORE_CTX_get0_param(ctx), &ip));

    // `SecTrustCreateWithCertificates` accepts a null policy, which would drop the TLS rules.
    SecTrustRef raw_trust = nullptr;
    bool created = policy != nullptr &&
                   SecTrustCreateWithCertificates(certs.get(), policy.get(), &raw_trust) == errSecSuccess;
    cf_ptr<SecTrustRef> trust(raw_trust);

    // Fetching downloads issuers named by the unauthenticated peer, synchronously and unbounded per
    // chain, which lets a peer stall the handshake for minutes.
    if (!created || SecTrustSetNetworkFetchAllowed(trust.get(), false) != errSecSuccess) return nullptr;

    CFErrorRef raw_error = nullptr;
    bool trusted = SecTrustEvaluateWithError(trust.get(), &raw_error);
    cf_ptr<CFErrorRef> cf_error(raw_error);

    if (!trusted) {
        *error = x509_error_for(trust.get(), cf_error.get(), store_error, ip);
        return nullptr;
    }

    cf_ptr<CFArrayRef> evaluated(copy_evaluated_chain(trust.get()));
    x509_stack_ptr chain(sk_X509_new_null());
    if (evaluated == nullptr || chain == nullptr) return nullptr;

    for (CFIndex i = 0; i < CFArrayGetCount(evaluated.get()); i++) {
        cf_ptr<CFDataRef> der(SecCertificateCopyData((SecCertificateRef)CFArrayGetValueAtIndex(evaluated.get(), i)));
        if (der == nullptr || !push_der(chain.get(), CFDataGetBytePtr(der.get()), CFDataGetLength(der.get())))
            return nullptr;
    }

    return chain.release();
}

#elif defined(LEAN_WINDOWS)

// Defined by `wininet.h` and newer SDKs, which older MinGW headers lack.
#ifndef SECURITY_FLAG_IGNORE_CERT_CN_INVALID
#define SECURITY_FLAG_IGNORE_CERT_CN_INVALID 0x00001000
#endif
#ifndef CERT_CHAIN_DISABLE_AIA
#define CERT_CHAIN_DISABLE_AIA 0x00002000
#endif

static void close_cert_store(HCERTSTORE store) { CertCloseStore(store, 0); }
static void free_cert_context(CERT_CONTEXT const * cert) { CertFreeCertificateContext(cert); }
static void free_chain_context(CERT_CHAIN_CONTEXT const * chain) { CertFreeCertificateChain(chain); }

// The OpenSSL error for the chain engine's rejection, falling back to the store's verdict for a chain
// that reaches no trusted root.
static int x509_error_for(CERT_CHAIN_POLICY_STATUS const & status, CERT_CHAIN_CONTEXT const * chain,
                          int store_error) {
    // The policy reports an `HRESULT`, whose error constants are negative.
    switch (static_cast<HRESULT>(status.dwError)) {
    // Also reported for a certificate that is not valid yet: the one the status points at.
    case CERT_E_EXPIRED: {
        LONG c = status.lChainIndex, e = status.lElementIndex;
        bool located = c >= 0 && (DWORD)c < chain->cChain && e >= 0 && (DWORD)e < chain->rgpChain[c]->cElement;
        bool early = located &&
                     CertVerifyTimeValidity(nullptr, chain->rgpChain[c]->rgpElement[e]->pCertContext->pCertInfo) < 0;
        return early ? X509_V_ERR_CERT_NOT_YET_VALID : X509_V_ERR_CERT_HAS_EXPIRED;
    }
    case CERT_E_REVOKED: case CRYPT_E_REVOKED: return X509_V_ERR_CERT_REVOKED;
    case TRUST_E_CERT_SIGNATURE: return X509_V_ERR_CERT_SIGNATURE_FAILURE;
    case CERT_E_WRONG_USAGE: return X509_V_ERR_INVALID_PURPOSE;
    case TRUST_E_BASIC_CONSTRAINTS: return X509_V_ERR_INVALID_CA;
    case CERT_E_UNTRUSTEDROOT: case CERT_E_CHAINING:
        return store_error != X509_V_OK ? store_error : X509_V_ERR_CERT_UNTRUSTED;
    }

    // Among others: a distrusted certificate, or a root not trusted for server authentication.
    return X509_V_ERR_CERT_REJECTED;
}

// The chain the Windows chain engine builds from `candidates`, leaf first, checked against the
// `Disallowed` store, each certificate's allowed uses, and the SSL server policy. Name checks are left
// to the OpenSSL pass. On rejection returns null and sets `*error`.
static STACK_OF(X509) * platform_chain(X509_STORE_CTX *, STACK_OF(X509) * candidates, int store_error,
                                       int * error) {
    *error = X509_V_ERR_UNSPECIFIED;

    std::unique_ptr<void, released_by<close_cert_store>> extra(
        CertOpenStore(CERT_STORE_PROV_MEMORY, 0, 0, CERT_STORE_CREATE_NEW_FLAG, nullptr));
    if (extra == nullptr) return nullptr;

    // Owned before the store is: a store with an open context outlives `CertCloseStore`.
    std::unique_ptr<CERT_CONTEXT const, released_by<free_cert_context>> leaf;

    for (int i = 0; i < sk_X509_num(candidates); i++) {
        unsigned char * der = nullptr;
        int len = i2d_X509(sk_X509_value(candidates, i), &der);
        if (len < 0) continue;

        CERT_CONTEXT const * added = nullptr;
        CertAddEncodedCertificateToStore(extra.get(), X509_ASN_ENCODING, der, (DWORD)len,
                                         CERT_STORE_ADD_ALWAYS, i == 0 ? &added : nullptr);
        OPENSSL_free(der);

        // An intermediate CryptoAPI cannot parse is left out; the chain engine may find another path.
        if (i == 0) leaf.reset(added);
    }

    if (leaf == nullptr) return nullptr;

    LPSTR server_auth[] = { const_cast<LPSTR>(szOID_PKIX_KP_SERVER_AUTH) };

    CERT_CHAIN_PARA para = {};
    para.cbSize = sizeof(para);
    para.RequestedUsage.dwType = USAGE_MATCH_TYPE_AND;
    para.RequestedUsage.Usage.cUsageIdentifier = 1;
    para.RequestedUsage.Usage.rgpszUsageIdentifier = server_auth;

    // Issuers named by the unauthenticated peer are not downloaded. A root Windows trusts but has not
    // installed yet still is, from Microsoft's update servers, which can hold the handshake for as long
    // as Windows lets such a download take.
    CERT_CHAIN_CONTEXT const * raw_chain = nullptr;
    if (!CertGetCertificateChain(nullptr, leaf.get(), nullptr, extra.get(), &para, CERT_CHAIN_DISABLE_AIA,
                                 nullptr, &raw_chain)) {
        return nullptr;
    }
    std::unique_ptr<CERT_CHAIN_CONTEXT const, released_by<free_chain_context>> chain_ctx(raw_chain);

    SSL_EXTRA_CERT_CHAIN_POLICY_PARA ssl_para = {};
    ssl_para.cbSize = sizeof(ssl_para);
    ssl_para.dwAuthType = AUTHTYPE_SERVER;
    ssl_para.fdwChecks = SECURITY_FLAG_IGNORE_CERT_CN_INVALID;

    CERT_CHAIN_POLICY_PARA policy = {};
    policy.cbSize = sizeof(policy);
    policy.pvExtraPolicyPara = &ssl_para;

    CERT_CHAIN_POLICY_STATUS status = {};
    status.cbSize = sizeof(status);

    if (!CertVerifyCertificateChainPolicy(CERT_CHAIN_POLICY_SSL, chain_ctx.get(), &policy, &status)) return nullptr;

    if (status.dwError != 0) {
        *error = x509_error_for(status, chain_ctx.get(), store_error);
        return nullptr;
    }

    x509_stack_ptr chain(sk_X509_new_null());
    if (chain == nullptr || chain_ctx->cChain == 0) return nullptr;

    CERT_SIMPLE_CHAIN const * simple = chain_ctx->rgpChain[0];

    for (DWORD i = 0; i < simple->cElement; i++) {
        CERT_CONTEXT const * cert = simple->rgpElement[i]->pCertContext;
        if (!push_der(chain.get(), cert->pbCertEncoded, (long)cert->cbCertEncoded)) return nullptr;
    }

    return chain.release();
}

#endif

#if defined(__APPLE__) || defined(LEAN_WINDOWS)

// Defers a chain the store cannot establish to the system's trust decision.
static int verify_with_platform(X509_STORE_CTX * ctx, STACK_OF(X509) * distrusted) {
    int store_error = X509_STORE_CTX_get_error(ctx);

    // A name mismatch implies the chain was already built, and a non-verifying session discards the
    // verdict: neither needs the platform.
    SSL * ssl = static_cast<SSL *>(X509_STORE_CTX_get_ex_data(ctx, SSL_get_ex_data_X509_STORE_CTX_idx()));

    if (store_error == X509_V_ERR_HOSTNAME_MISMATCH || store_error == X509_V_ERR_IP_ADDRESS_MISMATCH ||
        store_error == X509_V_ERR_EMAIL_MISMATCH ||
        (ssl != nullptr && (SSL_get_verify_mode(ssl) & SSL_VERIFY_PEER) == 0)) {
        return 0;
    }

    x509_stack_ptr candidates(candidate_certificates(ctx));
    int error = X509_V_ERR_UNSPECIFIED;
    x509_stack_ptr chain(candidates != nullptr ? platform_chain(ctx, candidates.get(), store_error, &error) : nullptr);

    if (chain == nullptr) {
        X509_STORE_CTX_set_error(ctx, error);
        return 0;
    }

    // The platform does not know the caller's distrust. It applies to the chain the platform settled on,
    // so a distrusted root that merely cross-signs that chain's root does not count.
    if (chain_has_distrusted(distrusted, chain.get())) {
        X509_STORE_CTX_set_error(ctx, X509_V_ERR_CERT_REJECTED);
        return 0;
    }

    return verify_along_chain(ctx, chain.get());
}

#endif

// Verifies against the store, then (with the platform) the system's trust, and refuses the chain either
// settles on if it goes through a distrusted key: OpenSSL's issuer lookup can pass a distrusted copy by.
static int check_chain(X509_STORE_CTX * ctx, chain_verifier const * verifier) {
    if (X509_verify_cert(ctx) > 0) {
        if (!chain_has_distrusted(verifier->distrusted, X509_STORE_CTX_get0_chain(ctx))) return 1;

        X509_STORE_CTX_set_error(ctx, X509_V_ERR_CERT_REJECTED);
        return 0;
    }

#if defined(__APPLE__) || defined(LEAN_WINDOWS)
    if (verifier->platform) return verify_with_platform(ctx, verifier->distrusted);
#endif

    return 0;
}

static int verify_chain(X509_STORE_CTX * ctx, void * arg) {
    // Verification can queue errors even when it succeeds (a peer certificate with an undecodable key, for
    // one), and libssl may read them as the handshake's own failure. The verdict is in `ctx`.
    ERR_set_mark();
    int ok = check_chain(ctx, static_cast<chain_verifier const *>(arg));
    ERR_pop_to_mark();
    return ok;
}

bool install_chain_verifier(SSL_CTX * ctx, X509_STORE * store, int trust_id, bool platform,
                            STACK_OF(X509) * given) {
    x509_stack_ptr stored(X509_STORE_get1_all_certs(store));
    x509_stack_ptr distrusted(sk_X509_new_null());
    if (stored == nullptr || distrusted == nullptr) return false;

    // The store's own, such as a system bundle's, then the caller's, which the store may not have kept.
    for (int i = 0; i < sk_X509_num(stored.get()); i++) {
        X509 * cert = sk_X509_value(stored.get(), i);

        if (X509_check_trust(cert, trust_id, 0) == X509_TRUST_REJECTED && !push_ref(distrusted.get(), cert)) {
            return false;
        }
    }

    for (int i = 0; i < sk_X509_num(given); i++) {
        if (!push_ref(distrusted.get(), sk_X509_value(given, i))) return false;
    }

    auto * verifier = new chain_verifier{distrusted.release(), platform};

    if (SSL_CTX_set_ex_data(ctx, chain_verifier_index(), verifier) != 1) {
        free_x509_stack(verifier->distrusted);
        delete verifier;
        return false;
    }

    SSL_CTX_set_cert_verify_callback(ctx, verify_chain, verifier);
    return true;
}

bool use_system_trust_store(SSL_CTX * ctx, std::string * detail) {
#if defined(__APPLE__) || defined(LEAN_WINDOWS)
    // The platform decides every chain the store cannot (see `install_chain_verifier`), so nothing is
    // loaded up front.
    (void)ctx;
    (void)detail;
    return true;
#else
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);

#if !defined(LEAN_STANDALONE)
    // Counted before any system material: the store already holds the caller's own CAs.
    int before = certificate_count(store);
#endif

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
    platform = platform || any_dir_with_certs(X509_get_default_cert_dir()) || certificate_count(store) > before;
#endif

    ERR_clear_error();

    if (!platform) {
        *detail = OPENSSL_issetugid()
            ? "none of the usual system bundles could be read (list CA certificates in `trust`; "
              "SSL_CERT_FILE and SSL_CERT_DIR are ignored in a set-user-ID or set-group-ID program)"
            : "none of the usual system bundles could be read (list CA certificates in `trust`, or set "
              "SSL_CERT_FILE or SSL_CERT_DIR)";
    }

    return platform;
#endif
}

}

#endif
