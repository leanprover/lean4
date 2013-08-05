/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"
#include "mpz.h"
#include "mpq.h"

namespace lean {
expr int_type();
bool is_int_type(expr const & e);

expr int_value(mpz const & v);
inline expr int_value(int v) { return int_value(mpz(v)); }
bool is_int_value(expr const & e);
mpz const & int_value_numeral(expr const & e);

expr int_add();
bool is_int_add(expr const & e);

expr int_sub();
bool is_int_sub(expr const & e);

expr int_mul();
bool is_int_mul(expr const & e);

expr int_div();
bool is_int_div(expr const & e);

expr int_leq();
bool is_int_leq(expr const & e);

expr int_geq();
bool is_int_geq(expr const & e);

expr int_lt();
bool is_int_lt(expr const & e);

expr int_gt();
bool is_int_gt(expr const & e);

class environment;
void add_int_theory(environment & env);
}
