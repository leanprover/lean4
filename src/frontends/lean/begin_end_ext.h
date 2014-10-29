/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/cmd_table.h"

namespace lean {
environment add_begin_end_pre_tactic(environment const & env, expr const & pre_tac);
environment reset_begin_end_pre_tactic(environment const & env, expr const & pre_tac);
optional<expr> get_begin_end_pre_tactic(environment const & env);
void register_begin_end_cmds(cmd_table & r);

expr mk_begin_end_annotation(expr const & e);
expr mk_begin_end_element_annotation(expr const & e);
bool is_begin_end_annotation(expr const & e);
bool is_begin_end_element_annotation(expr const & e);

void initialize_begin_end_ext();
void finalize_begin_end_ext();
}
