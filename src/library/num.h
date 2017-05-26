/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/numerics/mpz.h"
#include "kernel/environment.h"

namespace lean {
bool is_const_app(expr const &, name const &, unsigned);

/** \brief Return true iff the given expression encodes a numeral. */
bool is_num(expr const & e);

/** \brief Return true iff is_num(e) or \c e is of the form (- e') where to_num(e') */
bool is_signed_num(expr const & e);

bool is_zero(expr const & e);
bool is_one(expr const & e);
optional<expr> is_bit0(expr const & e);
optional<expr> is_bit1(expr const & e);
optional<expr> is_neg(expr const & e);

/** \brief Return true iff \c n is zero, one, bit0 or bit1 */
bool is_numeral_const_name(name const & n);

/** Unfold \c e it is is_zero, is_one, is_bit0 or is_bit1 application */
optional<expr> unfold_num_app(environment const & env, expr const & e);

/** \brief If the given expression encodes a numeral, then convert it back to mpz numeral.
    \see from_num */
optional<mpz> to_num(expr const & e);

/** \brief Return true iff n is zero/one/has_zero.zero/has_one.one.
    These constants are used to encode numerals, and some tactics may have to treat them in a special way.

    \remark This kind of hard-coded solution is not ideal. One alternative solution is to have yet another
    annotation to let user mark constants that should be treated in a different way by some tactics. */
bool is_num_leaf_constant(name const & n);

/** \brief Encode \c n as an expression using bit0/bit1/one/zero constants */
expr to_nat_expr(mpz const & n);

void initialize_num();
void finalize_num();
}
