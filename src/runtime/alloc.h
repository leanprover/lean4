/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stddef.h>
#include <stdint.h>
#include <lean/lean.h>

/* The heartbeat counter of the current thread; incremented on every small-object allocation.
   Non-static so that the fused allocation entry points in `mimalloc.cpp` can increment it without
   a function call. */
extern "C" {
#ifdef _MSC_VER
extern __declspec(thread) uint64_t lean_g_heartbeat;
#else
extern __thread uint64_t lean_g_heartbeat;
#endif
}

namespace lean {
LEAN_EXPORT void * alloc(size_t sz);
LEAN_EXPORT void dealloc(void * o, size_t sz);
LEAN_EXPORT void set_heartbeats(uint64_t count);
LEAN_EXPORT void add_heartbeats(uint64_t count);
LEAN_EXPORT uint64_t get_num_heartbeats();
void initialize_alloc();
void finalize_alloc();
}
