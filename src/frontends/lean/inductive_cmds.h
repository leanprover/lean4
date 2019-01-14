/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "frontends/lean/cmd_table.h"
#include "frontends/lean/decl_attributes.h"
namespace lean {

void parse_inductive_decl(parser & p, cmd_meta const & meta);
environment inductive_cmd(parser & p, cmd_meta const & meta);

void elaborate_inductive_decls(parser & p, cmd_meta const & meta, buffer<decl_attributes> mut_attrs, buffer<name> lp_names,
                               name_map<implicit_infer_kind> implicit_infer_map,
                               buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules);

void register_inductive_cmds(cmd_table & r);
void initialize_inductive_cmds();
void finalize_inductive_cmds();
}
