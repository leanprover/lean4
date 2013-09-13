/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/builtin.h"
#include "util/numerics/mpz.h"

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

/** \brief Addition, Nat::add : Nat -> Nat -> Nat */
expr mk_nat_add_fn();
inline expr nAdd(expr const & e1, expr const & e2) { return mk_app(mk_nat_add_fn(), e1, e2); }

/** \brief Multiplication, Nat::mul : Nat -> Nat -> Nat */
expr mk_nat_mul_fn();
inline expr nMul(expr const & e1, expr const & e2) { return mk_app(mk_nat_mul_fn(), e1, e2); }

/** \brief Less than or equal to, Nat::le : Nat -> Nat -> Bool */
expr mk_nat_le_fn();
inline expr nLe(expr const & e1, expr const & e2) { return mk_app(mk_nat_le_fn(), e1, e2); }

/** \brief Greater than or equal to, Nat::ge : Nat -> Nat -> Bool */
expr mk_nat_ge_fn();
inline expr nGe(expr const & e1, expr const & e2) { return mk_app(mk_nat_ge_fn(), e1, e2); }

/** \brief Less than, Nat::lt : Nat -> Nat -> Bool */
expr mk_nat_lt_fn();
inline expr nLt(expr const & e1, expr const & e2) { return mk_app(mk_nat_lt_fn(), e1, e2); }

/** \brief Greater than, Nat::gt : Nat -> Nat -> Bool */
expr mk_nat_gt_fn();
inline expr nGt(expr const & e1, expr const & e2) { return mk_app(mk_nat_gt_fn(), e1, e2); }

/** \brief Identity function for natural numbers, Nat::id : Nat -> Nat */
expr mk_nat_id_fn();
inline expr nId(expr const & e) { return mk_app(mk_nat_id_fn(), e); }

/** \brief If-then-else for natural numbers */
inline expr nIf(expr const & c, expr const & t, expr const & e) { return mk_if(Nat, c, t, e); }

class environment;
/** \brief Import Natural number library in the given environment (if it has not been imported already). */
void import_natlib(environment & env);
}
