/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/cmd_table.h"
namespace lean {
bool is_structure(environment const & env, name const & S);
void get_structure_fields(environment const & env, name const & S, buffer<name> & fields);
void register_structure_cmd(cmd_table & r);
void initialize_structure_cmd();
void finalize_structure_cmd();
}
