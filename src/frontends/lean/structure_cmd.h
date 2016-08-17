/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/cmd_table.h"
namespace lean {
environment structure_cmd_ex(parser & p, decl_attributes const & attrs, bool is_private);
void get_structure_fields(environment const & env, name const & S, buffer<name> & fields);
void register_structure_cmd(cmd_table & r);
environment private_structure_cmd(parser & p);
/** \brief Return true iff \c S is a structure created with the structure command */
bool is_structure(environment const & env, name const & S);
}
