/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/inductive_compiler/ginductive.h"
#include "library/inductive_compiler/add_decl.h"
#include "library/inductive_compiler/compiler.h"
#include "library/constructions/has_sizeof.h"
#include "library/constants.h"

namespace lean {
environment add_inductive_declaration(environment const & old_env, options const & opts,
                                      name_map<implicit_infer_kind> implicit_infer_map,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules,
                                      bool is_trusted) {
    ginductive_decl decl(old_env, 0, lp_names, params, inds, intro_rules);
    environment env = add_inner_inductive_declaration(old_env, opts, implicit_infer_map, decl, is_trusted);
    return env;
}

environment add_structure_declaration_aux(environment const & old_env, options const &,
                                          buffer<name> const & lp_names, buffer<expr> const & params,
                                          expr const & ind, expr const & intro_rule) {
    buffer<expr> inds;
    inds.push_back(ind);

    buffer<buffer<expr> > intro_rules;
    intro_rules.emplace_back();
    intro_rules.back().push_back(intro_rule);

    ginductive_decl decl(old_env, 0, lp_names, params, inds, intro_rules);

    environment env = old_env;
    if (mlocal_name(ind) != get_has_sizeof_name())
        env = mk_has_sizeof(env, mlocal_name(ind));

    return register_ginductive_decl(env, decl, ginductive_kind::BASIC);
}

}
