/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
#include "frontends/lean/parse_table.h"
namespace lean {
void init_structure_instance_parsing_rules(parse_table & r);
bool is_structure_instance(expr const & e);
void destruct_structure_instance(expr const & e, expr & t, buffer<name> & field_names,
                                 buffer<expr> & field_values, buffer<expr> & using_exprs);
void get_structure_fields(environment const & env, name const & S, buffer<name> & fields);
void register_structure_cmd(cmd_table & r);
/** \brief Return true iff \c S is a structure created with the structure command */
bool is_structure(environment const & env, name const & S);
void initialize_structure_cmd();
void finalize_structure_cmd();
}
