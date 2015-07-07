/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/module.h"
#include "library/reducible.h"
#include "library/protected.h"
#include "library/normalize.h"

namespace lean {
environment mk_rec_on(environment const & env, name const & n) {
    if (!inductive::is_inductive_decl(env, n))
        throw exception(sstream() << "error in 'rec_on' generation, '" << n << "' is not an inductive datatype");
    name rec_on_name(n, "rec_on");
    name_generator ngen;
    declaration rec_decl = env.get(inductive::get_elim_name(n));

    buffer<expr> locals;
    expr rec_type = rec_decl.get_type();
    while (is_pi(rec_type)) {
        expr local = mk_local(ngen.next(), binding_name(rec_type), binding_domain(rec_type), binding_info(rec_type));
        rec_type   = instantiate(binding_body(rec_type), local);
        locals.push_back(local);
    }

    // locals order
    //   A C minor_premises indices major-premise

    // new_locals order
    //   A C indices major-premise minor-premises
    buffer<expr> new_locals;
    unsigned idx_major_sz = *inductive::get_num_indices(env, n) + 1;
    unsigned minor_sz     = *inductive::get_num_minor_premises(env, n);
    unsigned AC_sz        = locals.size() - minor_sz - idx_major_sz;
    for (unsigned i = 0; i < AC_sz; i++)
        new_locals.push_back(locals[i]);
    for (unsigned i = 0; i < idx_major_sz; i++)
        new_locals.push_back(locals[AC_sz + minor_sz + i]);
    unsigned rec_on_major_idx = new_locals.size() - 1;
    for (unsigned i = 0; i < minor_sz; i++)
        new_locals.push_back(locals[AC_sz + i]);
    expr rec_on_type = Pi(new_locals, rec_type);

    levels ls = param_names_to_levels(rec_decl.get_univ_params());
    expr rec  = mk_constant(rec_decl.get_name(), ls);
    expr rec_on_val = Fun(new_locals, mk_app(rec, locals));

    bool use_conv_opt = true;
    environment new_env = module::add(env,
                                      check(env, mk_definition(env, rec_on_name, rec_decl.get_univ_params(),
                                                               rec_on_type, rec_on_val, use_conv_opt)));
    new_env = set_reducible(new_env, rec_on_name, reducible_status::Reducible);
    new_env = add_unfold_hint(new_env, rec_on_name, rec_on_major_idx);
    return add_protected(new_env, rec_on_name);
}
}
