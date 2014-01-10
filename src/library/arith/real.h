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
#include "library/arith/Real_decls.h"

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

expr mk_Real_add_fn();
inline expr mk_Real_add(expr const & e1, expr const & e2) { return mk_app(mk_Real_add_fn(), e1, e2); }
expr mk_Real_mul_fn();
inline expr mk_Real_mul(expr const & e1, expr const & e2) { return mk_app(mk_Real_mul_fn(), e1, e2); }
expr mk_Real_div_fn();
inline expr mk_Real_div(expr const & e1, expr const & e2) { return mk_app(mk_Real_div_fn(), e1, e2); }
expr mk_Real_le_fn();
inline expr mk_Real_le(expr const & e1, expr const & e2) { return mk_app(mk_Real_le_fn(), e1, e2); }

class environment;
/** \brief Import (basic) Real number library in the given environment (if it has not been imported already). */
void import_real(environment const & env, io_state const & ios);

/** \brief Coercion from int to real */
expr mk_int_to_real_fn();
inline expr mk_int_to_real(expr const & e) { return mk_app(mk_int_to_real_fn(), e); }

/** \brief Import the coercions \c i2r and \c n2r. The Integer and (basic) Real libraries are also imported. */
void import_int_to_real_coercions(environment const & env);

void open_real(lua_State * L);
}
