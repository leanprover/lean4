/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <new>
#include <gmp.h>
#include <cstdlib>

extern "C" void * cxx_malloc(size_t size) {
    void * p = malloc(size);
    if (p != 0 || size == 0)
        return p;

    throw std::bad_alloc();
}

extern "C" void * cxx_realloc(void * q, size_t, size_t new_size) {
    void* p = realloc(q, new_size);
    if (p != 0 || new_size == 0)
        return p;

    throw std::bad_alloc();
}

extern "C" void cxx_free(void * p, size_t) {
    free(p);
}

class gmp_init {
public:
    gmp_init() {
        mp_set_memory_functions(cxx_malloc, cxx_realloc, cxx_free);
    }
};

gmp_init g_gmp_init;
