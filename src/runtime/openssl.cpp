/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/openssl.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/opensslv.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>

namespace lean {

void initialize_openssl() {
}

void finalize_openssl() {}

bool ensure_openssl_initialized() {
    // `OPENSSL_INIT_NO_ATEXIT` is the load-bearing flag. By default OpenSSL registers
    // `atexit(OPENSSL_cleanup)`, which tears down global state — among it the ENGINE lock that
    // `SSL_CTX_new` reads — while other threads may still be inside OpenSSL, dereferencing the
    // freed lock. Lean hands work to a thread pool that can outlive `main`, so that handler
    // must not be installed. Nothing then frees OpenSSL's globals, which is intended: they stay
    // reachable from static storage for the life of the process.
    static const bool ok = OPENSSL_init_ssl(OPENSSL_INIT_NO_ATEXIT, nullptr) == 1;

    return ok;
}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    // The linked library rather than the headers it was compiled against, so a Lean binary running
    // against an upgraded shared OpenSSL reports what it actually loaded (as `lean_libuv_version`
    // does for libuv).
    return lean_unsigned_to_nat(OpenSSL_version_num());
}

#else

namespace lean {

void initialize_openssl() {}
void finalize_openssl() {}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_box(0);
}

#endif
