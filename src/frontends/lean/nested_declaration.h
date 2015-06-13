/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/flet.h"
#include "kernel/expr.h"
namespace lean {
class parser;
// auxiliary object used to temporarily enable nested declarations
class allow_nested_decls_scope {
    bool m_saved;
public:
    allow_nested_decls_scope(bool enable = true);
    ~allow_nested_decls_scope();
};
expr parse_nested_declaration(parser & p, unsigned, expr const *, pos_info const & pos);
std::tuple<environment, expr> extract_nested_declarations(environment const & env, io_state const & ios,
                                                          name const & def_name, expr const & e);
void initialize_nested_declaration();
void finalize_nested_declaration();
}
