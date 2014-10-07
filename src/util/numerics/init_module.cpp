/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstddef>
#include <gmp.h>
#include "util/memory.h"
#include "util/numerics/mpz.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/mpfp.h"
#include "util/numerics/zpz.h"
#include "util/numerics/primes.h"

namespace lean {
extern "C" void * cxx_malloc(size_t size) { return lean::malloc(size); }
extern "C" void * cxx_realloc(void * q, size_t, size_t new_size) { return lean::realloc(q, new_size); }
extern "C" void cxx_free(void * p, size_t) { return lean::free(p); }

void initialize_numerics_module() {
    mp_set_memory_functions(cxx_malloc, cxx_realloc, cxx_free);
    initialize_mpz();
    initialize_mpq();
    initialize_mpbq();
    initialize_mpfp();
    initialize_zpz();
    initialize_primes();
}

void finalize_numerics_module() {
    finalize_primes();
    finalize_zpz();
    finalize_mpfp();
    finalize_mpbq();
    finalize_mpq();
    finalize_mpz();
}
}
