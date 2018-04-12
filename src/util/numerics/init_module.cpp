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
#include "util/numerics/primes.h"

namespace lean {
void initialize_numerics_module() {
    initialize_mpz();
    initialize_mpq();
    initialize_primes();
}

void finalize_numerics_module() {
    finalize_primes();
    finalize_mpq();
    finalize_mpz();
}
}
