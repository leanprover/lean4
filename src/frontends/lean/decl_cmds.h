/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/buffer.h"
#include "kernel/expr.h"
#include "frontends/lean/cmd_table.h"
namespace lean {
class parser;
void parse_univ_params(parser & p, buffer<name> & ps);
void update_parameters(buffer<name> & ls_buffer, name_set const & found, parser const & p);
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<parameter> & section_ps);
void register_decl_cmds(cmd_table & r);
}
