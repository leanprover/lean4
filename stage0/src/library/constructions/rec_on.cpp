/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive.h"
#include "library/reducible.h"
#include "library/protected.h"
#include "library/suffixes.h"
#include "library/aux_recursors.h"
#include "library/constructions/util.h"

namespace lean {
environment mk_rec_on(environment const & env, name const & n) {
    constant_info ind_info = env.get(n);
    if (!ind_info.is_inductive())
        throw exception(sstream() << "error in '" << g_rec_on << "' generation, '" << n << "' is not an inductive datatype");
    name_generator ngen = mk_constructions_name_generator();
    local_ctx lctx;
    name rec_on_name(n, g_rec_on);
    constant_info rec_info = env.get(mk_rec_name(n));
    recursor_val  rec_val  = rec_info.to_recursor_val();
    buffer<expr> locals;
    expr rec_type = rec_info.get_type();
    while (is_pi(rec_type)) {
        expr local = lctx.mk_local_decl(ngen, binding_name(rec_type), binding_domain(rec_type), binding_info(rec_type));
        rec_type   = instantiate(binding_body(rec_type), local);
        locals.push_back(local);
    }

    // locals order
    //   As Cs minor_premises indices major-premise

    // new_locals order
    //   As Cs indices major-premise minor-premises
    buffer<expr> new_locals;
    unsigned num_indices  = rec_val.get_nindices();
    unsigned num_minors   = rec_val.get_nminors();
    unsigned AC_sz        = locals.size() - num_minors - num_indices - 1;
    for (unsigned i = 0; i < AC_sz; i++)
        new_locals.push_back(locals[i]);
    for (unsigned i = 0; i < num_indices + 1; i++)
        new_locals.push_back(locals[AC_sz + num_minors + i]);
    for (unsigned i = 0; i < num_minors; i++)
        new_locals.push_back(locals[AC_sz + i]);
    expr rec_on_type = lctx.mk_pi(new_locals, rec_type);

    levels ls = lparams_to_levels(rec_info.get_lparams());
    expr rec  = mk_constant(rec_info.get_name(), ls);
    expr rec_on_val = lctx.mk_lambda(new_locals, mk_app(rec, locals));

    environment new_env = env.add(mk_definition_inferring_unsafe(env, rec_on_name, rec_info.get_lparams(),
                                                                 rec_on_type, rec_on_val, reducibility_hints::mk_abbreviation()));
    new_env = set_reducible(new_env, rec_on_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, rec_on_name);
    return add_protected(new_env, rec_on_name);
}

extern "C" LEAN_EXPORT object * lean_mk_rec_on(object * env, object * n) {
    return catch_kernel_exceptions<environment>([&]() { return mk_rec_on(environment(env), name(n, true)); });
}
}
