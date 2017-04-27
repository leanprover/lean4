/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
expr mk_pexpr_quote(expr const &e);
bool is_quote(expr const & e);
bool is_expr_quote(expr const &e);
expr const & get_quote_expr(expr const & e);
expr mk_quote_core(expr const & e, bool is_expr);
expr mk_reflected(expr const & e, expr const & ty, level const & l);

expr mk_antiquote(expr const & e);
bool is_antiquote(expr const & e);
expr const & get_antiquote_expr(expr const & e);

void initialize_quote();
void finalize_quote();
}
