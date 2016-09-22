/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parse_table.h"
namespace lean {
expr mk_structure_instance(name const & s, buffer<name> const & fns, buffer<expr> const & fvs);
expr mk_structure_instance(expr const & src, buffer<name> const & fns, buffer<expr> const & fvs);
bool is_structure_instance(expr const & e);
void get_structure_instance_info(expr const & e, name & struct_name, optional<expr> & source,
                                 buffer<name> & field_names, buffer<expr> & field_values);
void initialize_structure_instance();
void finalize_structure_instance();
}
