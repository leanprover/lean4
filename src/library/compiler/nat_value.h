/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "util/numerics/mpz.h"

namespace lean {
/** \brief Replace nat numerals encoded using bit0, bit1, one with an auxiliary nat_value macro.
    This macro wraps a mpz number. */
expr find_nat_values(environment const & env, expr const & e);
/** \brief Create a nat_value macro expression. This macro should only be used in the compiler. */
expr mk_nat_value(mpz const & v);
/** \brief Return true iff \c e is a nat_value macro expression. */
bool is_nat_value(expr const & e);
/** \brief Return the mpz stored in the nat_value macro.
    \pre is_nat_value(e) */
mpz const & get_nat_value_value(expr const & e);

/** \brief If \c e encodes a nat numeral, then convert it into a nat_value macro */
optional<expr> to_nat_value(type_context_old & ctx, expr const & e);

void initialize_nat_value();
void finalize_nat_value();
}
