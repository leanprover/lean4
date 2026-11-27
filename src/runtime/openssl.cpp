/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/openssl.h"
#include "runtime/openssl/context.h"

#ifndef LEAN_EMSCRIPTEN
#include <openssl/crypto.h>
#include <openssl/opensslv.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include "runtime/thread.h"

namespace lean {

bool ensure_openssl_initialized() {
    // `NO_ATEXIT`: OpenSSL 3 otherwise registers `atexit(OPENSSL_cleanup)`, which frees global state
    // that thread-pool tasks outliving `main` may still be using. A standalone toolchain skips `openssl.cnf`, whose
    // compiled-in path names a directory on the build machine; a system OpenSSL reads the
    // distribution's crypto policy like any other consumer.
#ifdef LEAN_STANDALONE
    uint64_t const config = OPENSSL_INIT_NO_LOAD_CONFIG;
#else
    uint64_t const config = OPENSSL_INIT_LOAD_CONFIG;
#endif

    static const bool ok = OPENSSL_init_ssl(OPENSSL_INIT_NO_ATEXIT | config, nullptr) == 1;

#ifdef LEAN_WINDOWS
    // A statically linked libcrypto has no `DllMain` to free a thread's OpenSSL state when it exits.
    LEAN_THREAD_VALUE(bool, g_thread_stop_registered, false);

    if (ok && !g_thread_stop_registered) {
        register_thread_finalizer([](void *) { OPENSSL_thread_stop(); }, nullptr);
        g_thread_stop_registered = true;
    }
#endif

    return ok;
}

}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(OPENSSL_VERSION_NUMBER);
}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_linked_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(OpenSSL_version_num());
}

#else

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT lean_obj_res lean_openssl_linked_version(lean_obj_arg o) {
    return lean_box(0);
}

#endif

namespace lean {
void initialize_openssl() {
#if defined(LEAN_STANDALONE) && !defined(LEAN_EMSCRIPTEN)
    // OpenSSL takes its configuration flags from whichever call initializes it first, which could
    // otherwise be one made before `ensure_openssl_initialized`. Loads no providers.
    OPENSSL_init_crypto(OPENSSL_INIT_NO_LOAD_CONFIG | OPENSSL_INIT_NO_ATEXIT, nullptr);
#endif
    initialize_openssl_context();
}
}
