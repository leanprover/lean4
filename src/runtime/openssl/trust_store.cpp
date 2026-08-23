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

#if defined(__APPLE__) || defined(LEAN_WINDOWS)

// A variable set to the empty string names no path, so it is reported as unset. OpenSSL's own check is
// a bare non-NULL test, which takes the empty string for a path, finds nothing, and quietly leaves the
// store without those anchors.
static char const * getenv_or_null_if_empty(char const * name) {
    char const * value = getenv(name);
    return value != nullptr && value[0] != '\0' ? value : nullptr;
}

// Whether the store demonstrably holds no trust anchor.
static bool trust_store_has_no_certs(X509_STORE * store) {
    if (char const * dir = getenv_or_null_if_empty(X509_get_default_cert_dir_env())) {
#if defined(LEAN_WINDOWS)
        char const sep = ';';
#else
        char const sep = ':';
#endif
        std::string list(dir);

        for (size_t p = 0; p <= list.size(); ) {
            size_t end = std::min(list.find(sep, p), list.size());
            std::string entry = list.substr(p, end - p);
            struct stat st;

            if (!entry.empty() && stat(entry.c_str(), &st) == 0 && S_ISDIR(st.st_mode)) return false;
            p = end + 1;
        }
    }

    STACK_OF(X509) * certs = X509_STORE_get1_all_certs(store);
    if (certs == nullptr) return true;

    bool empty = sk_X509_num(certs) == 0;
    sk_X509_pop_free(certs, X509_free);

    return empty;
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

    if (SecTrustSettingsCopyTrustSettings(cert, domain, &settings) != errSecSuccess || settings == nullptr) {
        return trust_setting::unspecified;
    }

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

// Every anchor the Keychain offers for TLS, or null if even the empty list could not be built.
static STACK_OF(X509) * g_keychain_anchors = nullptr;
static std::once_flag g_keychain_anchors_once;

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
    // can take an anchor out of the store again. It is left to the `!any_anchor` fallback below, where
    // there is no verdict left to contradict.
    char const * env_file = getenv_or_null_if_empty(X509_get_default_cert_file_env());
    char const * env_dir = getenv_or_null_if_empty(X509_get_default_cert_dir_env());

    // Naming a bundle that cannot be read is a configuration error, and the only one of these loads
    // whose failure can be diagnosed: a hash directory resolves lazily, and the default-paths call
    // discards its result. Unreported it resurfaces much later, as a verification failure against
    // the anchor that never loaded.
    if (env_file != nullptr && X509_STORE_load_file(store, env_file) != 1) {
        *detail = std::string(X509_get_default_cert_file_env()) +
                  " names a file holding no readable certificate";
        return false;
    }

    if (env_dir != nullptr) X509_STORE_load_path(store, env_dir);

    if (!any_anchor) {
        SSL_CTX_set_default_verify_paths(ctx);

        if (trust_store_has_no_certs(store)) {
            *detail = "the Keychain yielded no anchor trusted for TLS and OpenSSL's default paths "
                      "hold no certificate either";
            return false;
        }
    }

    // Entries left by a certificate the loop skipped, or by a configured path that does not exist,
    // would otherwise be picked up by a later, unrelated diagnosis as its own.
    ERR_clear_error();
    return true;
#elif defined(LEAN_WINDOWS)
    // The Windows ROOT store is reachable only through OpenSSL's winstore loader (added in OpenSSL
    // 3.2), which `SSL_CTX_set_default_verify_paths` does not consult, so it has to be named explicitly.
    int winstore = SSL_CTX_load_verify_store(ctx, "org.openssl.winstore://");

    // The fallback for builds without that loader.
    SSL_CTX_set_default_verify_paths(ctx);

    // A successful winstore load resolves lazily and is invisible to the count, so the count is
    // consulted only once winstore is out of the picture. What can still rescue that case is an
    // `SSL_CERT_FILE` bundle, which is read on the spot, or an `SSL_CERT_DIR` that exists.
    if (winstore != 1 && trust_store_has_no_certs(SSL_CTX_get_cert_store(ctx))) {
        *detail = "the Windows ROOT store is unavailable (it needs OpenSSL 3.2 or later) and no CA file was configured";
        return false;
    }

    ERR_clear_error();
    return true;
#else
    // Only registering the lookups can fail here; whether they resolve to any certificate is not
    // reported, so an installation with no CA material at all passes and fails at handshake time.
    if (SSL_CTX_set_default_verify_paths(ctx) != 1) {
        *detail = "OpenSSL's default certificate paths could not be registered";
        return false;
    }

    ERR_clear_error();
    return true;
#endif
}

}

#endif
