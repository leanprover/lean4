/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/
#pragma once
#include <stdint.h>

/* The runtime's hot thread-local state, combined into one struct so that the allocation fast path
   reaches all of it through a single TLS address computation. Kept free of other runtime and
   mimalloc header dependencies: `runtime/mimalloc.cpp` includes it next to all of mimalloc.
   Defined in `runtime/alloc.cpp`.

   `heartbeat` is the heartbeat counter of the current thread, incremented on every small-object
   allocation.

   With mimalloc, `mi_theap_default` caches the current thread's default mimalloc theap
   (`mi_theap_get_default()`) for `lean_alloc_small_object_core`, following the embedding pattern
   of the Koka runtime: filled in `lean_initialize_thread` or lazily on the first allocation,
   cleared in `lean_finalize_thread`, and `NULL` while not cached. mimalloc frees the theap during
   its own thread-local teardown at thread exit, so Lean code must not allocate after that point;
   allocating between `lean_finalize_thread` and thread exit is still safe as the cleared cache
   refills from the live default. Unused in non-mimalloc builds. */
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
}
