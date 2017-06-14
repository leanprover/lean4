/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parse_table.h"
namespace lean {
bool is_sort_wo_universe(expr const & e);

expr mk_anonymous_constructor(expr const & e);
bool is_anonymous_constructor(expr const & e);
expr const & get_anonymous_constructor_arg(expr const & e);

bool is_do_failure_eq(expr const & e);

parse_table get_builtin_nud_table();
parse_table get_builtin_led_table();

bool is_infix_function(expr const & e);

bool is_hole(expr const & e);
std::tuple<expr, optional<pos_info>, optional<pos_info>> get_hole_info(expr const & e);
expr update_hole_args(expr const & e, expr const & new_args);

void initialize_builtin_exprs();
void finalize_builtin_exprs();
}
