/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
bool is_expr_quote(expr const &e);
bool is_pexpr_quote(expr const &e);
expr const & get_expr_quote_value(expr const & e);
expr const & get_pexpr_quote_value(expr const & e);
expr mk_unelaborated_expr_quote(expr const & e);
expr mk_elaborated_expr_quote(expr const & e);
expr mk_pexpr_quote(expr const & e);

expr mk_antiquote(expr const & e);
bool is_antiquote(expr const & e);
expr const & get_antiquote_expr(expr const & e);

expr mk_pexpr_quote_and_substs(expr const & e, bool is_strict);

void initialize_quote();
void finalize_quote();
}
