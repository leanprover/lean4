/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>
#include <lean/lean.h>

namespace lean {
/** \brief Set maximum amount of memory in bytes */
LEAN_EXPORT void set_max_memory(size_t max);
/** \brief Set maximum amount of memory in megabytes */
LEAN_EXPORT void set_max_memory_megabyte(unsigned max);
LEAN_EXPORT void check_memory(char const * component_name);
LEAN_EXPORT size_t get_allocated_memory();
}
