/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>

namespace lean {
/** \brief Set maximum amount of memory in bytes */
void set_max_memory(size_t max);
/** \brief Set maximum amount of memory in megabytes */
void set_max_memory_megabyte(unsigned max);
void check_memory(char const * component_name);
size_t get_allocated_memory();

#ifdef LEAN_TRACK_CUSTOM_ALLOCATORS
/* We use report_memory_deallocated to track memory released by custom allocators such
   as memory_pool and small_object_allocator. */
void report_memory_deallocated(size_t s);
size_t get_memory_deallocated();
#define lean_report_memory_deallocated(s) report_memory_deallocated(s)
#else
#define lean_report_memory_deallocated(s)
#endif
}
