/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/module.h"
#include "library/reducible.h"
#include "library/protected.h"
#include "library/normalize.h"
#include "library/aux_recursors.h"
#include "library/scoped_ext.h"
#include "library/constructions/util.h"

namespace lean {
environment mk_rec_on(environment const & env, name const & n) {
    if (!inductive::is_inductive_decl(env, n))
        throw exception(sstream() << "error in 'rec_on' generation, '" << n << "' is not an inductive datatype");
    name_generator ngen = mk_constructions_name_generator();
    name rec_on_name(n, "rec_on");
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
    for (unsigned i = 0; i < minor_sz; i++)
        new_locals.push_back(locals[AC_sz + i]);
    expr rec_on_type = Pi(new_locals, rec_type);

    levels ls = param_names_to_levels(rec_decl.get_univ_params());
    expr rec  = mk_constant(rec_decl.get_name(), ls);
    expr rec_on_val = Fun(new_locals, mk_app(rec, locals));

    environment new_env = module::add(env,
                                      check(env, mk_definition_inferring_trusted(env, rec_on_name, rec_decl.get_univ_params(),
                                                                                 rec_on_type, rec_on_val, reducibility_hints::mk_abbreviation())));
    new_env = set_reducible(new_env, rec_on_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, rec_on_name);
    return add_protected(new_env, rec_on_name);
}
}
