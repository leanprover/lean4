/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/openssl.h"
#include "runtime/openssl/context.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/opensslv.h>
#include <openssl/err.h>
#include <openssl/ssl.h>

namespace lean {

bool ensure_openssl_initialized() {
    // `NO_ATEXIT`: the default `atexit(OPENSSL_cleanup)` frees global state that thread-pool tasks
    // outliving `main` may still be using. A standalone toolchain skips `openssl.cnf`, whose
    // compiled-in path names a directory on the build machine; a system OpenSSL reads the
    // distribution's crypto policy like any other consumer.
#ifdef LEAN_STANDALONE
    uint64_t const config = OPENSSL_INIT_NO_LOAD_CONFIG;
#else
    uint64_t const config = OPENSSL_INIT_LOAD_CONFIG;
#endif

    static const bool ok = OPENSSL_init_ssl(OPENSSL_INIT_NO_ATEXIT | config, nullptr) == 1;

    return ok;
}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(OPENSSL_VERSION_NUMBER);
}

#else

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_box(0);
}

#endif

namespace lean {
void initialize_openssl() {
    initialize_openssl_context();
}
}
