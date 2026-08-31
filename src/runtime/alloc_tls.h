/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Julia M. Himmel
*/
#pragma once
#include <stdint.h>

/* The runtime's hot thread-local state, combined into one struct so that the allocation fast path
   reaches all of it through a single TLS address computation. Kept free of other runtime and
   mimalloc header dependencies: `runtime/mimalloc.cpp` must include it before all of mimalloc.

   `heartbeat` is the heartbeat counter of the current thread, incremented on every small-object
   allocation. With mimalloc on `MI_TLS_MODEL_LOCAL` platforms (e.g. Linux), `mi_theap_default`
   hosts the storage of mimalloc's default theap of the current thread (see
   `MI_THEAP_DEFAULT_TLS_FIELD` in `script/mimalloc-lean.patch`); it is unused otherwise.

   Defined in `runtime/mimalloc.cpp` when built with mimalloc (the initial value of
   `mi_theap_default` needs mimalloc's internal `_mi_theap_empty`), in `runtime/alloc.cpp`
   otherwise. */
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
