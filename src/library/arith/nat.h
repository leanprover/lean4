/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "kernel/expr.h"
#include "kernel/kernel.h"
#include "util/numerics/mpz.h"
#include "library/arith/Nat_decls.h"

namespace lean {
/** \brief Natural numbers type */
expr mk_nat_type();
extern expr const Nat;

/** \brief Return the value of type Natural number that represents \c v. */
expr mk_nat_value(mpz const & v);
inline expr mk_nat_value(unsigned v) { return mk_nat_value(mpz(v)); }
inline expr nVal(unsigned v) { return mk_nat_value(v); }
bool is_nat_value(expr const & e);
mpz const & nat_value_numeral(expr const & e);

expr mk_Nat_add_fn();
inline expr mk_Nat_add(expr const & e1, expr const & e2) { return mk_app(mk_Nat_add_fn(), e1, e2); }
expr mk_Nat_mul_fn();
inline expr mk_Nat_mul(expr const & e1, expr const & e2) { return mk_app(mk_Nat_mul_fn(), e1, e2); }
expr mk_Nat_le_fn();
inline expr mk_Nat_le(expr const & e1, expr const & e2) { return mk_app(mk_Nat_le_fn(), e1, e2); }

class environment;
/** \brief Import Natural number library in the given environment (if it has not been imported already). */
void import_nat(environment const & env, io_state const & ios);

void open_nat(lua_State * L);
}
