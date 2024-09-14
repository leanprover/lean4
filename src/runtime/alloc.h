/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stddef.h>
#include <stdint.h>
#include <lean/lean.h>

namespace lean {
void init_thread_heap();
LEAN_EXPORT void * alloc(size_t sz);
LEAN_EXPORT void dealloc(void * o, size_t sz);
LEAN_EXPORT void add_heartbeats(uint64_t count);
LEAN_EXPORT uint64_t get_num_heartbeats();
void initialize_alloc();
void finalize_alloc();
}
