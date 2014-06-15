/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
environment add_token(environment const & env, char const * val, unsigned prec);
environment add_nud_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a);
environment add_led_notation(environment const & env, unsigned num, notation::transition const * ts, expr const & a);
environment add_nud_notation(environment const & env, std::initializer_list<notation::transition> const & ts, expr const & a);
environment add_led_notation(environment const & env, std::initializer_list<notation::transition> const & ts, expr const & a);
token_table const & get_token_table(environment const & env);
parse_table const & get_nud_table(environment const & env);
parse_table const & get_led_table(environment const & env);
cmd_table const & get_cmd_table(environment const & env);
tactic_cmd_table const & get_tactic_cmd_table(environment const & env);
}
