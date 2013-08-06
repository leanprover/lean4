/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "builtin.h"
#include "mpz.h"
#include "mpq.h"

namespace lean {
expr mk_int_type();
#define Int mk_int_type()
bool is_int_type(expr const & e);

expr mk_int_value(mpz const & v);
inline expr mk_int_value(int v) { return mk_int_value(mpz(v)); }
inline expr iVal(int v) { return mk_int_value(v); }
bool is_int_value(expr const & e);
mpz const & int_value_numeral(expr const & e);

expr mk_int_add_fn();
bool is_int_add_fn(expr const & e);
inline expr iAdd(expr const & e1, expr const & e2) { return mk_app(mk_int_add_fn(), e1, e2); }

expr mk_int_sub_fn();
bool is_int_sub_fn(expr const & e);
inline expr iSub(expr const & e1, expr const & e2) { return mk_app(mk_int_sub_fn(), e1, e2); }

expr mk_int_mul_fn();
bool is_int_mul_fn(expr const & e);
inline expr iMul(expr const & e1, expr const & e2) { return mk_app(mk_int_mul_fn(), e1, e2); }

expr mk_int_div_fn();
bool is_int_div_fn(expr const & e);
inline expr iDiv(expr const & e1, expr const & e2) { return mk_app(mk_int_div_fn(), e1, e2); }

expr mk_int_le_fn();
bool is_int_le_fn(expr const & e);
inline expr iLe(expr const & e1, expr const & e2) { return mk_app(mk_int_le_fn(), e1, e2); }

expr mk_int_ge_fn();
bool is_int_ge_fn(expr const & e);
inline expr iGe(expr const & e1, expr const & e2) { return mk_app(mk_int_ge_fn(), e1, e2); }

expr mk_int_lt_fn();
bool is_int_lt_fn(expr const & e);
inline expr iLt(expr const & e1, expr const & e2) { return mk_app(mk_int_lt_fn(), e1, e2); }

expr mk_int_gt_fn();
bool is_int_gt_fn(expr const & e);
inline expr iGt(expr const & e1, expr const & e2) { return mk_app(mk_int_gt_fn(), e1, e2); }

inline expr iIf(expr const & c, expr const & t, expr const & e) { return mk_if(Int, c, t, e); }

class environment;
void add_int_theory(environment & env);
}
