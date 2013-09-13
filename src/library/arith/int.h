/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/numerics/mpz.h"
#include "kernel/expr.h"
#include "kernel/builtin.h"

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

/** \brief Addition, Int::add : Int -> Int -> Int */
expr mk_int_add_fn();
inline expr iAdd(expr const & e1, expr const & e2) { return mk_app(mk_int_add_fn(), e1, e2); }

/** \brief Subtraction, Int::sub : Int -> Int -> Int */
expr mk_int_sub_fn();
inline expr iSub(expr const & e1, expr const & e2) { return mk_app(mk_int_sub_fn(), e1, e2); }

/** \brief Unary minus, Int::neg : Int -> Int */
expr mk_int_neg_fn();
inline expr iNeg(expr const & e) { return mk_app(mk_int_neg_fn(), e); }

/** \brief Multiplication, Int::mul : Int -> Int -> Int */
expr mk_int_mul_fn();
inline expr iMul(expr const & e1, expr const & e2) { return mk_app(mk_int_mul_fn(), e1, e2); }

/** \brief Integer division, Int::mul : Int -> Int -> Int */
expr mk_int_div_fn();
inline expr iDiv(expr const & e1, expr const & e2) { return mk_app(mk_int_div_fn(), e1, e2); }

/** \brief Modulus, Int::mul : Int -> Int -> Int */
expr mk_int_mod_fn();
inline expr iMod(expr const & e1, expr const & e2) { return mk_app(mk_int_mod_fn(), e1, e2); }

/** \brief Divides predicate, Int::mul : Int -> Int -> Bool */
expr mk_int_divides_fn();
inline expr iDivides(expr const & e1, expr const & e2) { return mk_app(mk_int_divides_fn(), e1, e2); }

/** \brief Absolute value function, Int::abs : Int -> Int */
expr mk_int_abs_fn();
inline expr iAbs(expr const & e) { return mk_app(mk_int_abs_fn(), e); }

/** \brief Less than or equal to, Int::le : Int -> Int -> Bool */
expr mk_int_le_fn();
inline expr iLe(expr const & e1, expr const & e2) { return mk_app(mk_int_le_fn(), e1, e2); }

/** \brief Greater than or equal to, Int::ge : Int -> Int -> Bool */
expr mk_int_ge_fn();
inline expr iGe(expr const & e1, expr const & e2) { return mk_app(mk_int_ge_fn(), e1, e2); }

/** \brief Less than, Int::lt : Int -> Int -> Bool */
expr mk_int_lt_fn();
inline expr iLt(expr const & e1, expr const & e2) { return mk_app(mk_int_lt_fn(), e1, e2); }

/** \brief Greater than, Int::gt : Int -> Int -> Bool */
expr mk_int_gt_fn();
inline expr iGt(expr const & e1, expr const & e2) { return mk_app(mk_int_gt_fn(), e1, e2); }

/** \brief If-then-else for integers */
inline expr iIf(expr const & c, expr const & t, expr const & e) { return mk_if(Int, c, t, e); }

/** \brief Coercion from natural to integer */
expr mk_nat_to_int_fn();
inline expr n2i(expr const & e) { return mk_app(mk_nat_to_int_fn(), e); }

/** \brief Subtraction (for naturals), Nat::sub : Nat -> Nat -> Int */
expr mk_nat_sub_fn();
inline expr nSub(expr const & e1, expr const & e2) { return mk_app(mk_nat_sub_fn(), e1, e2); }

/** \brief Unary minus (for naturals), Nat::neg : Nat -> Int */
expr mk_nat_neg_fn();
inline expr nNeg(expr const & e1, expr const & e2) { return mk_app(mk_nat_neg_fn(), e1, e2); }

class environment;
/**
    \brief Import Integer number library in the given environment (if it has not been imported already).
    It will also load the natural number library.
*/
void import_int(environment & env);
}
