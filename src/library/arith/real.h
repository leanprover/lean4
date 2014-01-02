/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include "util/numerics/mpq.h"
#include "kernel/expr.h"
#include "kernel/builtin.h"

namespace lean {
/** \brief Real numbers type */
expr mk_real_type();
extern expr const Real;

/** \brief Return the value of type Real that represents \c v. */
expr mk_real_value(mpq const & v);
inline expr mk_real_value(int v) { return mk_real_value(mpq(v)); }
inline expr rVal(int v) { return mk_real_value(v); }
bool is_real_value(expr const & e);
mpq const & real_value_numeral(expr const & e);

/** \brief Addition, Real::add : Real -> Real -> Real */
expr mk_real_add_fn();
inline expr rAdd(expr const & e1, expr const & e2) { return mk_app(mk_real_add_fn(), e1, e2); }

/** \brief Subtraction, Real::sub : Real -> Real -> Real */
expr mk_real_sub_fn();
inline expr rSub(expr const & e1, expr const & e2) { return mk_app(mk_real_sub_fn(), e1, e2); }

/** \brief Unary minus, Real::neg : Real -> Real */
expr mk_real_neg_fn();
inline expr rNeg(expr const & e) { return mk_app(mk_real_neg_fn(), e); }

/** \brief Multiplication, Real::mul : Real -> Real -> Real */
expr mk_real_mul_fn();
inline expr rMul(expr const & e1, expr const & e2) { return mk_app(mk_real_mul_fn(), e1, e2); }

/** \brief Division, Real::mul : Real -> Real -> Real */
expr mk_real_div_fn();
inline expr rDiv(expr const & e1, expr const & e2) { return mk_app(mk_real_div_fn(), e1, e2); }

/** \brief Absolute value function, Real::abs : Real -> Real */
expr mk_real_abs_fn();
inline expr rAbs(expr const & e) { return mk_app(mk_real_abs_fn(), e); }

/** \brief Less than or equal to, Real::le : Real -> Real -> Bool */
expr mk_real_le_fn();
inline expr rLe(expr const & e1, expr const & e2) { return mk_app(mk_real_le_fn(), e1, e2); }

/** \brief Greater than or equal to, Real::ge : Real -> Real -> Bool */
expr mk_real_ge_fn();
inline expr rGe(expr const & e1, expr const & e2) { return mk_app(mk_real_ge_fn(), e1, e2); }

/** \brief Less than, Real::lt : Real -> Real -> Bool */
expr mk_real_lt_fn();
inline expr rLt(expr const & e1, expr const & e2) { return mk_app(mk_real_lt_fn(), e1, e2); }

/** \brief Greater than, Real::gt : Real -> Real -> Bool */
expr mk_real_gt_fn();
inline expr rGt(expr const & e1, expr const & e2) { return mk_app(mk_real_gt_fn(), e1, e2); }

/** \brief If-then-else for reals */
inline expr rIf(expr const & c, expr const & t, expr const & e) { return mk_if(Real, c, t, e); }

class environment;
/** \brief Import (basic) Real number library in the given environment (if it has not been imported already). */
void import_real(environment const & env, io_state const & ios);

/** \brief Coercion from int to real */
expr mk_int_to_real_fn();
inline expr i2r(expr const & e) { return mk_app(mk_int_to_real_fn(), e); }
/** \brief Coercion from nat to real */
expr mk_nat_to_real_fn();
inline expr n2r(expr const & e) { return mk_app(mk_nat_to_real_fn(), e); }

/** \brief Import the coercions \c i2r and \c n2r. The Integer and (basic) Real libraries are also imported. */
void import_int_to_real_coercions(environment const & env);

void open_real(lua_State * L);
}
