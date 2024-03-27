/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <stddef.h>
#include <stdint.h>
// #include <lean/lean.h>
// #include "runtime/thread.h"
// #include "runtime/debug.h"
// #include "runtime/alloc.h"

namespace lean {
void init_thread_heap();
void * alloc(size_t sz);
void dealloc(void * o, size_t sz);
uint64_t get_num_heartbeats();
void initialize_alloc();
void finalize_alloc();

namespace allocator {
uint64_t get_num_alloc();
uint64_t get_num_small_alloc();
uint64_t get_num_dealloc();
uint64_t get_num_small_dealloc();
uint64_t get_num_segments();
uint64_t get_num_pages();
uint64_t get_num_exports();
uint64_t get_num_recycled_pages();

}
}

extern "C" {
// dump allocator info into logfile.
void research_dump_allocator_log();
}
