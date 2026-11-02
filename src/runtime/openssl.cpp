/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/openssl.h"

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

static lean_obj_res sha256(void const * data, size_t size) {
    // Fetching once avoids the implicit per-call fetch of `EVP_sha256()`.
    static EVP_MD * md = EVP_MD_fetch(nullptr, "SHA256", nullptr);
    if (!md)
        lean_internal_panic("failed to fetch OpenSSL SHA-256 implementation");
    lean_object * r = lean_alloc_sarray(1, 32, 32);
    if (!EVP_Digest(data, size, lean_sarray_cptr(r), nullptr, md, nullptr))
        lean_internal_panic("OpenSSL SHA-256 digest failed");
    return r;
}

/* Returns the SHA-256 digest of a `ByteArray` as a 32-byte `ByteArray`. */
extern "C" LEAN_EXPORT lean_obj_res lean_sha256(b_lean_obj_arg a) {
    return sha256(lean_sarray_cptr(a), lean_sarray_size(a));
}

/* Returns the SHA-256 digest of the UTF-8 encoding of a `String` as a 32-byte `ByteArray`. */
extern "C" LEAN_EXPORT lean_obj_res lean_sha256_string(b_lean_obj_arg s) {
    return sha256(lean_string_cstr(s), lean_string_size(s) - 1);
}

#else

namespace lean {

void initialize_openssl() {}
void finalize_openssl() {}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_sha256(b_lean_obj_arg) {
    lean_internal_panic("SHA-256 is not supported on this platform");
}

extern "C" LEAN_EXPORT lean_obj_res lean_sha256_string(b_lean_obj_arg) {
    lean_internal_panic("SHA-256 is not supported on this platform");
}

#endif
