/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/util.h"
#include "library/aux_recursors.h"

namespace lean {
environment mk_induction_on(environment const & env, name const & n) {
    if (!env.impredicative())
        throw exception("induction_on generation failed, Prop/Type.{0} is not impredicative in the given environment");
    if (!inductive::is_inductive_decl(env, n))
        throw exception(sstream() << "error in 'induction_on' generation, '" << n << "' is not an inductive datatype");
    name rec_on_name(n, "rec_on");
    name induction_on_name(n, "induction_on");
    declaration rec_on_decl   = env.get(rec_on_name);
    declaration ind_decl      = env.get(n);
    unsigned rec_on_num_univs = rec_on_decl.get_num_univ_params();
    unsigned ind_num_univs    = ind_decl.get_num_univ_params();
    bool use_conv_opt         = true;
    environment new_env       = env;
    if (rec_on_num_univs == ind_num_univs) {
        // easy case, induction_on is just an alias for rec_on
        certified_declaration cdecl = check(new_env,
                                            mk_definition(new_env, induction_on_name, rec_on_decl.get_univ_params(),
                                                          rec_on_decl.get_type(), rec_on_decl.get_value(),
                                                          use_conv_opt));
        new_env = module::add(new_env, cdecl);
    } else {
        level_param_names induction_on_univs = tail(rec_on_decl.get_univ_params());
        name              from  = head(rec_on_decl.get_univ_params());
        level             to    = mk_level_zero();
        expr induction_on_type  = instantiate_univ_param(rec_on_decl.get_type(), from, to);
        expr induction_on_value = instantiate_univ_param(rec_on_decl.get_value(), from, to);
        certified_declaration cdecl = check(new_env,
                                            mk_definition(new_env, induction_on_name, induction_on_univs,
                                                          induction_on_type, induction_on_value,
                                                          use_conv_opt));
        new_env = add_aux_recursor(new_env, induction_on_name);
        new_env = module::add(new_env, cdecl);
    }
    return add_protected(new_env, induction_on_name);
}
}
