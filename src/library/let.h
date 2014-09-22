/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_let_value(expr const & e);
bool is_let_value(expr const & e);
expr get_let_value_expr(expr const e);

expr mk_let(name const & n, expr const & v, expr const & b);
bool is_let(expr const & e);
name const & get_let_var_name(expr const & e);
expr const & get_let_value(expr const & e);
expr const & get_let_body(expr const & e);

void initialize_let();
void finalize_let();
}
