/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/aux_recursors.h"
#include "library/constants.h"

namespace lean {
expr head_beta_const_fn(expr const & e) {
    if (!is_app(e)) return e;
    expr fn = get_app_fn(e);
    if (!is_lambda(fn)) return e;
    buffer<expr> args;
    get_app_args(e, args);
    unsigned i = 0;
    while (is_lambda(fn) && i < args.size()) {
        expr const & body = binding_body(fn);
        if (has_loose_bvars(body))
            break;
        i++;
        fn = body;
    }
    if (i == 0) return e;
    return mk_app(fn, args.size() - i, args.data() + i);
}

bool is_cases_on_recursor(environment const & env, name const & n) {
    return ::lean::is_aux_recursor(env, n) && n.get_string() == "cases_on";
}

expr mk_lc_unreachable(type_checker::state & s, local_ctx const & lctx, expr const & type) {
    type_checker tc(s, lctx);
    level lvl = sort_level(tc.ensure_type(type));
    return mk_app(mk_constant(get_lc_unreachable_name(), {lvl}), type);
}
}
