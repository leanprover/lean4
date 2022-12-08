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
}
