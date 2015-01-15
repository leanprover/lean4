/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>

namespace lean {
void set_max_memory(size_t max);
void check_memory(char const * component_name);
size_t get_allocated_memory();
void * malloc(size_t sz);
void * realloc(void * ptr, size_t sz);
void free(void * ptr);
}
