/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "frontends/lean/cmd_table.h"
#include "frontends/lean/decl_attributes.h"
namespace lean {
environment inductive_cmd_ex(parser & p, decl_attributes const & attrs, bool is_meta);
environment mutual_inductive_cmd_ex(parser & p, decl_attributes const & attrs, bool is_meta);
environment coinductive_cmd_ex(parser & p, decl_attributes const & attrs);
environment mutual_coinductive_cmd_ex(parser & p, decl_attributes const & attrs);

void register_inductive_cmds(cmd_table & r);
void initialize_inductive_cmds();
void finalize_inductive_cmds();
}
