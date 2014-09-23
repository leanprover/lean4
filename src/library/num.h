/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/numerics/mpz.h"
#include "kernel/environment.h"

namespace lean {
/**
   \brief Return true iff the environment \c env contains the following declarations
   in the namespace 'num'
       one   : pos_num
       bit0  : pos_num -> pos_num
       bit1  : pos_num -> pos_num
       zero  : num
       pos   : pos_num -> num
*/
bool has_num_decls(environment const & env);

/**
    \brief Return an expression that encodes the given numeral in binary using
    the declarations one, bit0, bit1, zero, pos.

    \see has_num_decls

    \pre n >= 0
    \post *to_num(from_num(n)) == n
*/
expr from_num(mpz const & n);

/**
   \brief If the given expression encodes a numeral, then convert it back to mpz numeral.

   \see from_num
*/
optional<mpz> to_num(expr const & e);

void initialize_num();
void finalize_num();
}
