/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/mpz.h"
#include "library/type_context.h"

namespace lean {
/** \brief Replace nat numerals encoded using bit0, bit1, one with an expression literal.*/
expr find_nat_values(environment const & env, expr const & e);
/** \brief Create a nat literal */
expr mk_nat_value(mpz const & v);
/** \brief Return true iff \c e is a nat literal */
bool is_nat_value(expr const & e);
/** \brief Return the mpz stored in the nat literal.
    \pre is_nat_value(e) */
mpz get_nat_value_value(expr const & e);

/** \brief If \c e encodes a nat numeral, then convert it into an expression literal. */
optional<expr> to_nat_value(type_context_old & ctx, expr const & e);

void initialize_nat_value();
void finalize_nat_value();
}
