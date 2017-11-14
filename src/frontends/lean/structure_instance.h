/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parse_table.h"
namespace lean {
struct structure_instance_info {
    name m_struct_name; // empty if omitted
    buffer<name> m_field_names;
    buffer<expr> m_field_values;
    buffer<expr> m_sources;
    bool m_catchall; // "..." syntax: fill in placeholders for remaining fields
};
expr mk_structure_instance(name const & s = {}, buffer<name> const & fns = {}, buffer<expr> const & fvs = {},
                           buffer<expr> const & sources = {}, bool catchall = false);
expr mk_structure_instance(structure_instance_info const & info);
bool is_structure_instance(expr const & e);
structure_instance_info get_structure_instance_info(expr const & e);
void initialize_structure_instance();
void finalize_structure_instance();
}
