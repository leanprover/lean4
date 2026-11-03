/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/openssl.h"
#include <cstring>

#ifndef LEAN_EMSCRIPTEN
#include <openssl/opensslv.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/evp.h>

namespace lean {

void initialize_openssl() {
}

void finalize_openssl() {}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(OPENSSL_VERSION_NUMBER);
}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_linked_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(OpenSSL_version_num());
}

namespace {

EVP_MD * sha256_md() {
    // Fetching once avoids the implicit per-call fetch of `EVP_sha256()`.
    static EVP_MD * md = EVP_MD_fetch(nullptr, "SHA256", nullptr);
    if (!md)
        lean_internal_panic("failed to fetch OpenSSL SHA-256 implementation");
    return md;
}

/* A per-thread digest context; reusing it avoids allocating a context and re-referencing the
   digest implementation on every call. */
struct sha256_ctx {
    EVP_MD_CTX * m_ctx = nullptr;
    ~sha256_ctx() { EVP_MD_CTX_free(m_ctx); }
};

EVP_MD_CTX * sha256_init() {
    static thread_local sha256_ctx ctx;
    if (!ctx.m_ctx) {
        ctx.m_ctx = EVP_MD_CTX_new();
        if (!ctx.m_ctx || !EVP_DigestInit_ex2(ctx.m_ctx, sha256_md(), nullptr))
            lean_internal_panic("OpenSSL SHA-256 initialization failed");
    } else if (!EVP_DigestInit_ex2(ctx.m_ctx, nullptr, nullptr)) {
        lean_internal_panic("OpenSSL SHA-256 initialization failed");
    }
    return ctx.m_ctx;
}

void sha256_update(EVP_MD_CTX * ctx, void const * data, size_t size) {
    if (!EVP_DigestUpdate(ctx, data, size))
        lean_internal_panic("OpenSSL SHA-256 digest failed");
}

uint64_t load_be64(unsigned char const * p) {
    uint64_t r = 0;
    for (unsigned i = 0; i < 8; i++)
        r = (r << 8) | p[i];
    return r;
}

void store_be64(unsigned char * p, uint64_t v) {
    for (unsigned i = 0; i < 8; i++)
        p[i] = static_cast<unsigned char>(v >> (56 - 8 * i));
}

/* Finishes the digest as a `Lean.Internal.Sha256Digest`, i.e., a constructor with four `UInt64`
   scalar fields holding the big-endian words of the digest. */
lean_obj_res sha256_final(EVP_MD_CTX * ctx) {
    unsigned char out[32];
    if (!EVP_DigestFinal_ex(ctx, out, nullptr))
        lean_internal_panic("OpenSSL SHA-256 digest failed");
    lean_object * r = lean_alloc_ctor(0, 0, 32);
    for (unsigned i = 0; i < 4; i++)
        lean_ctor_set_uint64(r, 8 * i, load_be64(out + 8 * i));
    return r;
}

lean_obj_res sha256(void const * data, size_t size) {
    EVP_MD_CTX * ctx = sha256_init();
    sha256_update(ctx, data, size);
    return sha256_final(ctx);
}

}

/* Returns the SHA-256 digest of a `ByteArray`. */
extern "C" LEAN_EXPORT lean_obj_res lean_sha256(b_lean_obj_arg a) {
    return sha256(lean_sarray_cptr(a), lean_sarray_size(a));
}

/* Returns the SHA-256 digest of the UTF-8 encoding of a `String`. */
extern "C" LEAN_EXPORT lean_obj_res lean_sha256_string(b_lean_obj_arg s) {
    return sha256(lean_string_cstr(s), lean_string_size(s) - 1);
}

/* Returns the SHA-256 digest of the UTF-8 encoding of a `String` with each `\r\n` replaced by
   `\n`, like `String.crlfToLf`. Byte `\r` never occurs inside a multi-byte UTF-8 sequence. */
extern "C" LEAN_EXPORT lean_obj_res lean_sha256_text(b_lean_obj_arg s) {
    char const * p = lean_string_cstr(s);
    char const * end = p + lean_string_size(s) - 1;
    EVP_MD_CTX * ctx = sha256_init();
    while (char const * cr = static_cast<char const *>(memchr(p, '\r', end - p))) {
        bool crlf = cr + 1 < end && cr[1] == '\n';
        sha256_update(ctx, p, crlf ? cr - p : cr + 1 - p);
        p = cr + 1;
    }
    sha256_update(ctx, p, end - p);
    return sha256_final(ctx);
}

/* Returns the SHA-256 digest of the concatenation of two digests. */
extern "C" LEAN_EXPORT lean_obj_res lean_sha256_mix(b_lean_obj_arg a, b_lean_obj_arg b) {
    unsigned char buf[64];
    for (unsigned i = 0; i < 4; i++) {
        store_be64(buf + 8 * i, lean_ctor_get_uint64(a, 8 * i));
        store_be64(buf + 32 + 8 * i, lean_ctor_get_uint64(b, 8 * i));
    }
    return sha256(buf, sizeof(buf));
}

#else

namespace lean {

void initialize_openssl() {}
void finalize_openssl() {}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_linked_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_sha256(b_lean_obj_arg) {
    lean_internal_panic("SHA-256 is not supported on this platform");
}

extern "C" LEAN_EXPORT lean_obj_res lean_sha256_string(b_lean_obj_arg) {
    lean_internal_panic("SHA-256 is not supported on this platform");
}

extern "C" LEAN_EXPORT lean_obj_res lean_sha256_text(b_lean_obj_arg) {
    lean_internal_panic("SHA-256 is not supported on this platform");
}

extern "C" LEAN_EXPORT lean_obj_res lean_sha256_mix(b_lean_obj_arg, b_lean_obj_arg) {
    lean_internal_panic("SHA-256 is not supported on this platform");
}

#endif
