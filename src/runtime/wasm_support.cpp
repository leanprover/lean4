/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Pehle
*/
#include "runtime/interrupt.h"
#include "runtime/object.h"
#include <cstddef>
#include <cstdint>

#if defined(LEAN_WASI)
namespace lean {

/* Tasks are outside the language-core WASI profile, but object.cpp keeps the
   heartbeat reset on its cold task paths. */
void reset_heartbeat() {}

}

/*
  wasi-sdk's stock libc++abi (as of 25+) is often built without the WebAssembly
  C++ exception personality / `__cxa_*` entry points. The language-core runtime
  still emits throws on panic paths. Provide minimal aborting stubs so objects
  link; cold paths call `lean_internal_panic` instead of unwinding.
*/
extern "C" {

LEAN_EXPORT void * __cxa_allocate_exception(size_t thrown_size) {
    (void)thrown_size;
    lean_internal_panic("WebAssembly core runtime: C++ exception allocate");
    return nullptr;
}

LEAN_EXPORT void __cxa_free_exception(void * thrown_object) {
    (void)thrown_object;
}

LEAN_EXPORT void __cxa_throw(void * thrown_object, void * tinfo, void (*dest)(void *)) {
    (void)thrown_object;
    (void)tinfo;
    (void)dest;
    lean_internal_panic("WebAssembly core runtime: C++ exception throw");
}

LEAN_EXPORT void * __cxa_begin_catch(void * exc) {
    (void)exc;
    lean_internal_panic("WebAssembly core runtime: C++ exception catch");
    return nullptr;
}

LEAN_EXPORT void __cxa_end_catch() {
    lean_internal_panic("WebAssembly core runtime: C++ exception end catch");
}

LEAN_EXPORT void __cxa_rethrow() {
    lean_internal_panic("WebAssembly core runtime: C++ exception rethrow");
}

LEAN_EXPORT void * __cxa_get_exception_ptr(void * exc) {
    (void)exc;
    return nullptr;
}

}

#endif
