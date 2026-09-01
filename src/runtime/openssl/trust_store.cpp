/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/

#include "runtime/openssl/trust_store.h"

#ifndef LEAN_EMSCRIPTEN

#include <openssl/err.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>
#include <openssl/x509v3.h>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <mutex>
#include <string>
#include <sys/stat.h>

#if defined(__APPLE__)
#include <Security/Security.h>
#include <CoreFoundation/CoreFoundation.h>
#endif

namespace lean {

// A variable set to the empty string names no path, so it is reported as unset. OpenSSL's own check is
// a bare non-NULL test, which takes the empty string for a path, finds nothing, and quietly leaves the
// store without those anchors.
static char const * getenv_or_null_if_empty(char const * name) {
    char const * value = getenv(name);
    return value != nullptr && value[0] != '\0' ? value : nullptr;
}

static bool is_dir(char const * path) {
    struct stat st;
    return stat(path, &st) == 0 && S_ISDIR(st.st_mode);
}

// Whether any entry of a `SSL_CERT_DIR`-style list names a directory that exists.
static bool any_existing_dir(char const * list_str) {
#if defined(LEAN_WINDOWS)
    char const sep = ';';
#else
    char const sep = ':';
#endif
    std::string list(list_str);

    for (size_t p = 0; p <= list.size(); ) {
        size_t end = std::min(list.find(sep, p), list.size());
        std::string entry = list.substr(p, end - p);

        if (!entry.empty() && is_dir(entry.c_str())) return true;
        p = end + 1;
    }

    return false;
}

// Whether the store demonstrably holds no trust anchor. A hash directory is consulted lazily, once per
// subject name at verification time, so its certificates are never in the count and its mere existence
// has to stand in for them.
static bool trust_store_has_no_certs(X509_STORE * store) {
    char const * env_dir = getenv_or_null_if_empty(X509_get_default_cert_dir_env());

    if (any_existing_dir(env_dir != nullptr ? env_dir : X509_get_default_cert_dir())) return false;

    STACK_OF(X509) * certs = X509_STORE_get1_all_certs(store);
    if (certs == nullptr) return true;

    bool empty = sk_X509_num(certs) == 0;
    sk_X509_pop_free(certs, X509_free);

    return empty;
}

// Loads the anchors named by `SSL_CERT_FILE` and `SSL_CERT_DIR`, and reports whether the named bundle
// could be read. It is the only one of these loads whose failure can be diagnosed: a hash directory
// resolves lazily, and `SSL_CTX_set_default_verify_paths` discards its result. Left unreported it
// resurfaces much later, as a verification failure against the anchor that never loaded.
static bool load_env_anchors(X509_STORE * store, std::string * detail) {
    char const * env_file = getenv_or_null_if_empty(X509_get_default_cert_file_env());
    char const * env_dir = getenv_or_null_if_empty(X509_get_default_cert_dir_env());

    if (env_dir != nullptr) X509_STORE_load_path(store, env_dir);

    if (env_file != nullptr && X509_STORE_load_file(store, env_file) != 1) {
        *detail = std::string(X509_get_default_cert_file_env()) +
                  " names a file holding no readable certificate";
        return false;
    }

    return true;
}

#if !defined(__APPLE__) && !defined(LEAN_WINDOWS)

// Where the mainstream distributions keep their anchors. A statically linked OpenSSL carries the
// certificate paths of the machine it was built on, which for a release toolchain is a build directory
// present nowhere else, so its compiled-in locations cannot be relied on to name anything.
static char const * const g_fallback_cert_files[] = {
    "/etc/ssl/certs/ca-certificates.crt",  // Debian, Ubuntu, Arch, Alpine
    "/etc/pki/tls/certs/ca-bundle.crt",    // Fedora, RHEL, CentOS
    "/etc/ssl/ca-bundle.pem",              // openSUSE
    "/etc/ssl/cert.pem",                   // Alpine, FreeBSD
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

    for (char const * dir : g_fallback_cert_dirs) {
        if (is_dir(dir) && X509_STORE_load_path(store, dir) == 1) any = true;
    }

    // A load that failed leaves its own reason behind, and the caller either succeeds or reports a
    // failure of its own.
    ERR_clear_error();

    return any;
}

#endif

#if defined(__APPLE__)

// Every anchor the Keychain offers for TLS, or null if even the empty list could not be built.
static STACK_OF(X509) * g_keychain_anchors = nullptr;
static std::once_flag g_keychain_anchors_once;

static bool cf_is(CFTypeRef value, CFTypeID type) {
    return value != nullptr && CFGetTypeID(value) == type;
}

static bool cf_array_contains(CFArrayRef array, CFTypeRef value) {
    return array != nullptr && CFArrayContainsValue(array, CFRangeMake(0, CFArrayGetCount(array)), value);
}

static bool as_number(CFTypeRef value, int64_t * out) {
    return cf_is(value, CFNumberGetTypeID()) && CFNumberGetValue((CFNumberRef)value, kCFNumberSInt64Type, out);
}

// Whether a trust setting's policy governs TLS at all (there are other types of things that the policy
// can deal with).
static bool policy_covers_tls(SecPolicyRef policy) {
    CFDictionaryRef props = SecPolicyCopyProperties(policy);
    if (props == nullptr) return false;

    CFTypeRef oid = CFDictionaryGetValue(props, kSecPolicyOid);
    CFTypeRef client = CFDictionaryGetValue(props, kSecPolicyClient);

    bool tls = cf_is(oid, CFStringGetTypeID()) && CFEqual(oid, kSecPolicyAppleSSL) &&
               !(cf_is(client, CFBooleanGetTypeID()) && CFBooleanGetValue((CFBooleanRef)client));

    CFRelease(props);
    return tls;
}

static bool rule_names_client_policy(CFDictionaryRef rule) {
    CFTypeRef name = CFDictionaryGetValue(rule, CFSTR("kSecTrustSettingsPolicyName"));
    return cf_is(name, CFStringGetTypeID()) && CFEqual(name, CFSTR("sslClient"));
}

// Whether a rule carries a usage constraint beyond its policy that a trust store cannot record.
static bool constrained_beyond_policy(CFDictionaryRef rule) {
    // A host name for the TLS policy, and the application performing the verification.
    if (CFDictionaryGetValue(rule, kSecTrustSettingsPolicyString) != nullptr ||
        CFDictionaryGetValue(rule, kSecTrustSettingsApplication) != nullptr) {
        return true;
    }

    CFTypeRef usage = CFDictionaryGetValue(rule, kSecTrustSettingsKeyUsage);
    if (usage == nullptr) return false;

    int64_t bits = 0;
    return !as_number(usage, &bits) || (bits & kSecTrustSettingsKeyUseSignCert) == 0;
}

enum class trust_setting { unspecified, trusted, denied };

// What one domain's trust settings say about using `cert` as a TLS anchor.
static trust_setting tls_trust_setting(SecCertificateRef cert, SecTrustSettingsDomain domain) {
    CFArrayRef settings = nullptr;

    if (SecTrustSettingsCopyTrustSettings(cert, domain, &settings) != errSecSuccess) {
        if (settings != nullptr) CFRelease(settings);
        return trust_setting::unspecified;
    }

    if (settings == nullptr) return trust_setting::unspecified;

    // An empty settings array is how Apple encodes unconditional trust.
    CFIndex count = CFArrayGetCount(settings);
    trust_setting result = count == 0 ? trust_setting::trusted : trust_setting::unspecified;

    for (CFIndex i = 0; i < count; i++) {
        CFTypeRef entry = CFArrayGetValueAtIndex(settings, i);
        if (!cf_is(entry, CFDictionaryGetTypeID())) continue;

        CFDictionaryRef rule = (CFDictionaryRef)entry;

        if (rule_names_client_policy(rule)) continue;

        CFTypeRef policy = CFDictionaryGetValue(rule, kSecTrustSettingsPolicy);
        if (policy != nullptr &&
            !(cf_is(policy, SecPolicyGetTypeID()) && policy_covers_tls((SecPolicyRef)policy))) {
            continue;
        }

        CFTypeRef result_value = CFDictionaryGetValue(rule, kSecTrustSettingsResult);
        int64_t verdict = kSecTrustSettingsResultTrustRoot;
        if (result_value != nullptr && !as_number(result_value, &verdict)) continue;

        if (verdict == kSecTrustSettingsResultDeny) {
            result = trust_setting::denied;
            break;
        }

        if ((verdict == kSecTrustSettingsResultTrustRoot ||
             verdict == kSecTrustSettingsResultTrustAsRoot) && !constrained_beyond_policy(rule)) {
            result = trust_setting::trusted;
        }
    }

    CFRelease(settings);
    return result;
}

static const SecTrustSettingsDomain g_trust_domains[] = {
    kSecTrustSettingsDomainUser,
    kSecTrustSettingsDomainAdmin,
    kSecTrustSettingsDomainSystem,
};

static constexpr size_t g_trust_domain_count = std::size(g_trust_domains);

// The highest-ranked domain with an opinion about `cert` is the one that decides.
static bool trusted_as_tls_anchor(SecCertificateRef cert, CFArrayRef const * listed,
                                  bool const * unknown, size_t found_in) {
    for (size_t d = 0; d < g_trust_domain_count; d++) {
        if (d != found_in && !unknown[d] && !cf_array_contains(listed[d], cert)) continue;

        switch (tls_trust_setting(cert, g_trust_domains[d])) {
        case trust_setting::trusted: return true;
        case trust_setting::denied: return false;
        case trust_setting::unspecified: break;
        }
    }

    return false;
}

static void collect_keychain_anchors() {
    g_keychain_anchors = sk_X509_new_null();
    if (g_keychain_anchors == nullptr) return;

    CFArrayRef listed[g_trust_domain_count] = {};
    bool unknown[g_trust_domain_count] = {};

    for (size_t d = 0; d < g_trust_domain_count; d++) {
        OSStatus status = SecTrustSettingsCopyCertificates(g_trust_domains[d], &listed[d]);

        if (status != errSecSuccess) {
            if (listed[d] != nullptr) CFRelease(listed[d]);
            listed[d] = nullptr;

            // `errSecNoTrustSettings` is the domain reporting that it holds none, which is the
            // ordinary state of the user and administrator domains. Any other failure leaves its
            // contents unknown, and a domain that could not be listed still has to be asked about
            // every certificate, or a verdict it holds — a deny above all — is skipped unseen.
            unknown[d] = status != errSecNoTrustSettings;
        }
    }

    for (size_t d = 0; d < g_trust_domain_count; d++) {
        if (listed[d] == nullptr) continue;

        for (CFIndex i = 0, n = CFArrayGetCount(listed[d]); i < n; i++) {
            CFTypeRef entry = CFArrayGetValueAtIndex(listed[d], i);
            if (!cf_is(entry, SecCertificateGetTypeID())) continue;

            SecCertificateRef cert = (SecCertificateRef)entry;
            if (!trusted_as_tls_anchor(cert, listed, unknown, d)) continue;

            CFDataRef der = SecCertificateCopyData(cert);
            if (der == nullptr) continue;

            const unsigned char * data = CFDataGetBytePtr(der);
            X509 * x509 = d2i_X509(nullptr, &data, CFDataGetLength(der));
            CFRelease(der);
            if (x509 == nullptr) continue;

            // These certificates are shared by every context, so they are read concurrently. OpenSSL
            // fills a certificate's extension cache on its first use in a verification, under the
            // certificate's own lock; filling it here instead keeps that write on this thread, and so
            // does not rest on how the linked OpenSSL orders it.
            X509_check_purpose(x509, -1, -1);

            if (sk_X509_push(g_keychain_anchors, x509) == 0) X509_free(x509);
        }
    }

    for (size_t d = 0; d < g_trust_domain_count; d++) {
        if (listed[d] != nullptr) CFRelease(listed[d]);
    }
}
#endif

bool load_system_trust_store(SSL_CTX * ctx, std::string * detail) {
#if defined(__APPLE__)
    std::call_once(g_keychain_anchors_once, collect_keychain_anchors);

    X509_STORE * store = SSL_CTX_get_cert_store(ctx);
    int anchor_count = g_keychain_anchors != nullptr ? sk_X509_num(g_keychain_anchors) : 0;
    bool any_anchor = false;

    // The store takes a reference to each anchor. A certificate listed by more than one domain is
    // deduplicated and reported as success.
    for (int i = 0; i < anchor_count; i++) {
        if (X509_STORE_add_cert(store, sk_X509_value(g_keychain_anchors, i)) == 1) any_anchor = true;
    }

    // The env-named locations are loaded on their own because `SSL_CTX_set_default_verify_paths` would
    // also arm the compiled-in sibling of whichever variable is unset, and OpenSSL's bundle is read
    // whole: merging it would put back every anchor the trust settings above turned away, and nothing
    // can take an anchor out of the store again. It is left to the fallback below, where there is no
    // verdict left to contradict.
    std::string env_detail;
    bool env_ok = load_env_anchors(store, &env_detail);

    // An unreadable `SSL_CERT_FILE` is only worth failing over when nothing else answered. The
    // variable adds anchors here rather than replacing them, so ignoring a stale one leaves the store
    // narrower than the caller asked for, never broader — where refusing to build the context at all
    // would strand every process that inherited the variable from a toolchain since removed.
    if (any_anchor || !trust_store_has_no_certs(store)) {
        ERR_clear_error();
        return true;
    }

    if (!env_ok) {
        *detail = env_detail;
        return false;
    }

    SSL_CTX_set_default_verify_paths(ctx);

    if (trust_store_has_no_certs(store)) {
        *detail = "the Keychain yielded no anchor trusted for TLS and OpenSSL's default paths "
                  "hold no certificate either";
        return false;
    }

    // Entries left by a certificate the loop skipped, or by a configured path that does not exist,
    // would otherwise be picked up by a later, unrelated diagnosis as its own.
    ERR_clear_error();
    return true;
#elif defined(LEAN_WINDOWS)
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);

    // The Windows ROOT store is reachable only through OpenSSL's winstore loader (added in OpenSSL
    // 3.2), which `SSL_CTX_set_default_verify_paths` does not consult, so it has to be named explicitly.
    int winstore = SSL_CTX_load_verify_store(ctx, "org.openssl.winstore://");

    std::string env_detail;
    bool env_ok = load_env_anchors(store, &env_detail);

    // A successful load ends the search, for the same reason the Keychain's does: OpenSSL's
    // compiled-in paths are not merged on top of a platform store. A standalone build carries the
    // paths of the machine it was built on, which on an end-user system names a directory that
    // belongs to nobody and that any unprivileged process may create and fill. They are read only
    // below, as the fallback for a build lacking the loader, where there is no anchor to contradict.
    // The load also resolves lazily and never shows up in the count, so the count is only meaningful
    // once winstore is out of the picture.
    if (winstore == 1) {
        ERR_clear_error();
        return true;
    }

    SSL_CTX_set_default_verify_paths(ctx);

    if (!trust_store_has_no_certs(store)) {
        ERR_clear_error();
        return true;
    }

    if (!env_ok) {
        *detail = env_detail;
        return false;
    }

    *detail = "the Windows ROOT store is unavailable (it needs OpenSSL 3.2 or later) and no CA file was configured";
    return false;
#else
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);

    std::string env_detail;
    bool env_ok = load_env_anchors(store, &env_detail);

    // Reports only whether the lookups could be registered, never whether they resolved to a
    // certificate, so the store itself has to be examined afterwards. Here these paths are the
    // primary source rather than a fallback, so they are armed before that examination.
    if (SSL_CTX_set_default_verify_paths(ctx) != 1) {
        *detail = "OpenSSL's default certificate paths could not be registered";
        return false;
    }

    if (!trust_store_has_no_certs(store)) {
        ERR_clear_error();
        return true;
    }

    if (!env_ok) {
        *detail = env_detail;
        return false;
    }

    if (!load_fallback_anchors(store)) {
        *detail = "no trust anchors: OpenSSL's configured certificate paths hold none, and none of "
                  "the usual system bundles could be read either (set SSL_CERT_FILE or SSL_CERT_DIR)";
        return false;
    }

    ERR_clear_error();
    return true;
#endif
}

}

#endif
