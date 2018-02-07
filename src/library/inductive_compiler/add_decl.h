/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "library/util.h"

namespace lean {
environment add_inductive_declaration(environment const & env, options const & opts,
                                      name_map<implicit_infer_kind> implicit_infer_map,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules,
                                      bool is_trusted);

environment add_structure_declaration_aux(environment const & env, options const & opts, buffer <name> const & lp_names,
                                          buffer <expr> const & params, expr const & ind, expr const & intro_rule,
                                          bool is_trusted);

void initialize_inductive_compiler_add_decl();
void finalize_inductive_compiler_add_decl();
}
