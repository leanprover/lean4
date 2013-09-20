/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <gmp.h>
#include "util/memory.h"

extern "C" void * cxx_malloc(size_t size) { return lean::malloc(size); }
extern "C" void * cxx_realloc(void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }
extern "C" void cxx_free(void * p, size_t) { return lean::free(p); }

/**
   \brief Auxiliary class for initializing the GMP memory allocation
   functions. We overhide the default ones because we want to sign
   the C++ exception std::bad_alloc when we run out-of-memory.
*/
class gmp_init {
public:
    gmp_init() {
        mp_set_memory_functions(cxx_malloc, cxx_realloc, cxx_free);
    }
};

gmp_init g_gmp_init;
