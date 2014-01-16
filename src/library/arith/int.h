/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "util/numerics/mpz.h"
#include "kernel/expr.h"
#include "kernel/kernel.h"
#include "library/arith/Int_decls.h"

namespace lean {
/** \brief Integer numbers type */
expr mk_int_type();
extern expr const Int;

/** \brief Return the value of type Integer that represents \c v. */
expr mk_int_value(mpz const & v);
inline expr mk_int_value(int v) { return mk_int_value(mpz(v)); }
inline expr iVal(int v) { return mk_int_value(v); }
bool is_int_value(expr const & e);
mpz const & int_value_numeral(expr const & e);

expr mk_Int_add_fn();
inline expr mk_Int_add(expr const & e1, expr const & e2) { return mk_app(mk_Int_add_fn(), e1, e2); }
expr mk_Int_mul_fn();
inline expr mk_Int_mul(expr const & e1, expr const & e2) { return mk_app(mk_Int_mul_fn(), e1, e2); }
expr mk_Int_div_fn();
inline expr mk_Int_div(expr const & e1, expr const & e2) { return mk_app(mk_Int_div_fn(), e1, e2); }
expr mk_Int_le_fn();
inline expr mk_Int_le(expr const & e1, expr const & e2) { return mk_app(mk_Int_le_fn(), e1, e2); }
expr mk_nat_to_int_fn();
inline expr mk_nat_to_int(expr const & e) { return mk_app(mk_nat_to_int_fn(), e); }

class environment;
/**
    \brief Import Integer number library in the given environment (if it has not been imported already).
    It will also load the natural number library.
*/
void import_int(environment const & env, io_state const & ios);

void open_int(lua_State * L);
}
