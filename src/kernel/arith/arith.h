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
expr mk_nat_type();
extern expr const Nat;

expr mk_nat_value(mpz const & v);
inline expr mk_nat_value(unsigned v) { return mk_nat_value(mpz(v)); }
inline expr nVal(unsigned v) { return mk_nat_value(v); }
bool is_nat_value(expr const & e);
mpz const & nat_value_numeral(expr const & e);

expr mk_nat_add_fn();
inline expr nAdd(expr const & e1, expr const & e2) { return mk_app(mk_nat_add_fn(), e1, e2); }

expr mk_nat_mul_fn();
inline expr nMul(expr const & e1, expr const & e2) { return mk_app(mk_nat_mul_fn(), e1, e2); }

expr mk_nat_le_fn();
inline expr nLe(expr const & e1, expr const & e2) { return mk_app(mk_nat_le_fn(), e1, e2); }

expr mk_nat_ge_fn();
inline expr nGe(expr const & e1, expr const & e2) { return mk_app(mk_nat_ge_fn(), e1, e2); }

expr mk_nat_lt_fn();
inline expr nLt(expr const & e1, expr const & e2) { return mk_app(mk_nat_lt_fn(), e1, e2); }

expr mk_nat_gt_fn();
inline expr nGt(expr const & e1, expr const & e2) { return mk_app(mk_nat_gt_fn(), e1, e2); }

inline expr nIf(expr const & c, expr const & t, expr const & e) { return mk_if(Nat, c, t, e); }

expr mk_int_type();
extern expr const Int;

expr mk_int_value(mpz const & v);
inline expr mk_int_value(int v) { return mk_int_value(mpz(v)); }
inline expr iVal(int v) { return mk_int_value(v); }
bool is_int_value(expr const & e);
mpz const & int_value_numeral(expr const & e);

expr mk_int_add_fn();
inline expr iAdd(expr const & e1, expr const & e2) { return mk_app(mk_int_add_fn(), e1, e2); }

expr mk_int_sub_fn();
inline expr iSub(expr const & e1, expr const & e2) { return mk_app(mk_int_sub_fn(), e1, e2); }

expr mk_int_mul_fn();
inline expr iMul(expr const & e1, expr const & e2) { return mk_app(mk_int_mul_fn(), e1, e2); }

expr mk_int_div_fn();
inline expr iDiv(expr const & e1, expr const & e2) { return mk_app(mk_int_div_fn(), e1, e2); }

expr mk_int_le_fn();
inline expr iLe(expr const & e1, expr const & e2) { return mk_app(mk_int_le_fn(), e1, e2); }

expr mk_int_ge_fn();
inline expr iGe(expr const & e1, expr const & e2) { return mk_app(mk_int_ge_fn(), e1, e2); }

expr mk_int_lt_fn();
inline expr iLt(expr const & e1, expr const & e2) { return mk_app(mk_int_lt_fn(), e1, e2); }

expr mk_int_gt_fn();
inline expr iGt(expr const & e1, expr const & e2) { return mk_app(mk_int_gt_fn(), e1, e2); }

inline expr iIf(expr const & c, expr const & t, expr const & e) { return mk_if(Int, c, t, e); }

expr mk_nat_to_int_fn();
inline expr n2i(expr const & e) { return mk_app(mk_nat_to_int_fn(), e); }

class environment;
void add_int_theory(environment & env);
}
