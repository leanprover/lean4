/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/numerics/mpz.h"
#include "kernel/environment.h"

namespace lean {
/** \brief Return true iff the given environment contains the declarations needed to encode numerals:
    zero, one, bit0, bit1 */
bool has_num_decls(environment const & env);

/** \brief Return true iff the given expression encodes a numeral. */
bool is_num(expr const & e);

bool is_zero(expr const & e);
bool is_one(expr const & e);
optional<expr> is_bit0(expr const & e);
optional<expr> is_bit1(expr const & e);

/** \brief If the given expression encodes a numeral, then convert it back to mpz numeral.
    \see from_num */
optional<mpz> to_num(expr const & e);

/** \brief If the given expression is a numeral encode the num and pos_num types, return the encoded numeral */
optional<mpz> to_num_core(expr const & e);

void initialize_num();
void finalize_num();
}
