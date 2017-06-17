/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "frontends/lean/cmd_table.h"
#include "frontends/lean/decl_attributes.h"
namespace lean {
struct single_inductive_decl {
    decl_attributes m_attrs;
    expr            m_expr;
    buffer<expr>    m_intros;
};

struct inductive_decl {
    buffer<name>                  m_lp_names;
    buffer<expr>                  m_params;
    buffer<single_inductive_decl> m_decls;
};

inductive_decl parse_inductive_decl(parser & p, cmd_meta const & meta);
environment inductive_cmd(parser & p, cmd_meta const & meta);

void register_inductive_cmds(cmd_table & r);
void initialize_inductive_cmds();
void finalize_inductive_cmds();
}
