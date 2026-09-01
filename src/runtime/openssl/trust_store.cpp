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
#include <cctype>
#include <cstdlib>
#include <dirent.h>
#include <string>

#if defined(__APPLE__)
#include <Security/Security.h>
#include <CoreFoundation/CoreFoundation.h>
#include <cstdint>
#include <iterator>
#include <mutex>
#endif

namespace lean {

// A variable set to the empty string names no path, so it is reported as unset.
static char const * getenv_or_null_if_empty(char const * name) {
    char const * value = getenv(name);
    return value != nullptr && value[0] != '\0' ? value : nullptr;
}

// Whether a hash directory holds a certificate.
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

        if (i > digits && name[i] == '\0') {
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

// The hash directories named by the environment, or null where it names none.
static char const * env_cert_dirs() {
    return getenv_or_null_if_empty(X509_get_default_cert_dir_env());
}

// The hash directories `SSL_CTX_set_default_verify_paths` would consult: the environment's, or the
// compiled-in location it falls back to.
static char const * default_verify_dirs() {
    char const * env_dir = env_cert_dirs();
    return env_dir != nullptr ? env_dir : X509_get_default_cert_dir();
}

// Adds the compiled-in locations, which the environment overrides where it names one of its own —
// `load_env_anchors` has already loaded those. `SSL_CTX_set_default_verify_paths` would do both, but
// it reads the variables with a bare non-NULL test, so one set to the empty string names the path ""
// and displaces the compiled-in default with a location that can hold nothing.
static void load_default_paths(X509_STORE * store) {
    if (getenv_or_null_if_empty(X509_get_default_cert_file_env()) == nullptr) {
        X509_STORE_load_file(store, X509_get_default_cert_file());
    }

    if (env_cert_dirs() == nullptr) X509_STORE_load_path(store, X509_get_default_cert_dir());
}

// Whether the store demonstrably holds no trust anchor.
static bool trust_store_has_no_certs(X509_STORE * store, char const * dirs) {
    if (dirs != nullptr && any_dir_with_certs(dirs)) return false;

    STACK_OF(X509) * certs = X509_STORE_get1_all_certs(store);
    if (certs == nullptr) return true;

    bool empty = sk_X509_num(certs) == 0;
    sk_X509_pop_free(certs, X509_free);

    return empty;
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
static bool trusted_as_tls_anchor(SecCertificateRef cert, CFArrayRef const * listed, bool const * unknown, size_t found_in) {
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

            // These certificates are shared by every context, so they are read concurrently.
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

    for (int i = 0; i < anchor_count; i++) {
        if (X509_STORE_add_cert(store, sk_X509_value(g_keychain_anchors, i)) == 1) any_anchor = true;
    }

    std::string env_detail;
    bool env_ok = load_env_anchors(store, &env_detail);

    if (any_anchor || !trust_store_has_no_certs(store, env_cert_dirs())) {
        ERR_clear_error();
        return true;
    }

    load_default_paths(store);

    if (!trust_store_has_no_certs(store, default_verify_dirs())) {
        ERR_clear_error();
        return true;
    }

    if (!env_ok) {
        *detail = env_detail;
        return false;
    }

    *detail = "the Keychain yielded no anchor trusted for TLS and OpenSSL's default paths "
              "hold no certificate either";
    return false;
#elif defined(LEAN_WINDOWS)
    X509_STORE * store = SSL_CTX_get_cert_store(ctx);

    int winstore = SSL_CTX_load_verify_store(ctx, "org.openssl.winstore://");

    std::string env_detail;
    bool env_ok = load_env_anchors(store, &env_detail);

    if (winstore == 1) {
        ERR_clear_error();
        return true;
    }

    load_default_paths(store);

    if (!trust_store_has_no_certs(store, default_verify_dirs())) {
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

    load_default_paths(store);

    if (!trust_store_has_no_certs(store, default_verify_dirs())) {
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
