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

namespace lean {

bool ensure_openssl_initialized() {
    // `OPENSSL_INIT_NO_ATEXIT` is the load-bearing flag. By default OpenSSL registers
    // `atexit(OPENSSL_cleanup)`, which tears down global state — among it the ENGINE lock that
    // `SSL_CTX_new` reads — while other threads may still be inside OpenSSL, dereferencing the
    // freed lock. Lean hands work to a thread pool that can outlive `main`, so that handler
    // must not be installed. Nothing then frees OpenSSL's globals, which is intended: they stay
    // reachable from static storage for the life of the process.
    //
    // Whether `openssl.cnf` is read follows who owns the OpenSSL being linked. A toolchain bundling
    // its own carries that build's compiled-in configuration path, which names a directory on the
    // machine the toolchain was built on; on the machine it runs on that directory can belong to
    // anyone, and a file there can load a provider module or lower the security level of every
    // context, so `OPENSSL_INIT_NO_LOAD_CONFIG` keeps it out. Against a system OpenSSL the same file
    // is the distribution's own, carrying its crypto policy and FIPS settings, and Lean reads it as
    // every other consumer of that library does.
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
