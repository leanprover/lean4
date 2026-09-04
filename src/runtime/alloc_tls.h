/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/
#pragma once
#include <stdint.h>

/* The runtime's hot thread-local state, combined into one struct so that the allocation fast path
   reaches all of it through a single TLS address computation. Kept free of other runtime and
   mimalloc header dependencies.

   `heartbeat` is the heartbeat counter of the current thread, incremented on every small-object
   allocation.

   With mimalloc, `mi_theap_default` caches the current thread's default mimalloc theap for
   `lean_alloc_small_object_core`, following the embedding pattern of the Koka runtime. It always
   points to a valid theap, so the fast path needs no initialization check: mimalloc's read-only
   empty theap until `lean_mi_theap_cache_init` (called from `initialize_alloc` on the main thread
   and from `lean_initialize_thread` on every other thread the runtime starts or is told about),
   and the real theap from then on. The empty theap routes every allocation through mimalloc's
   generic path — correct, but slow, so foreign threads running Lean code should call
   `lean_initialize_thread`. The cache is never reset: the real theap stays valid until mimalloc
   frees it during its own thread-local teardown at thread exit, which runs only after
   `thread_main` has returned (the main thread's theap is static and never freed). Lean code must
   therefore not allocate from thread-local destructors that run after mimalloc's. Unused in
   non-mimalloc builds.

   Defined in `runtime/mimalloc.cpp` when built with mimalloc (the initial value is mimalloc's
   internal empty-theap sentinel), in `runtime/alloc.cpp` otherwise. */
struct mi_theap_s;
extern "C" {
typedef struct lean_runtime_tls {
    uint64_t heartbeat;
    struct mi_theap_s * mi_theap_default;
} lean_runtime_tls;
#ifdef _MSC_VER
extern __declspec(thread) lean_runtime_tls lean_g_tls;
#else
extern __thread lean_runtime_tls lean_g_tls;
#endif
/* Defined in `runtime/mimalloc.cpp`; only available (and only needed) with mimalloc. */
void lean_mi_theap_cache_init(void);
}
