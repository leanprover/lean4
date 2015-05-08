/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/aliases.h"
#include "library/constants.h"
#include "library/tactic/util.h"
#include "library/tactic/proof_state.h"

namespace lean {
bool is_tactic_namespace_open(environment const & env) {
    for (name const & a : get_expr_aliases(env, "apply")) {
        if (a == get_tactic_apply_name()) {
            // make sure the type is the expected one
            if (auto d = env.find(a)) {
                expr t = d->get_type();
                if (is_pi(t)) {
                    expr b = binding_body(t);
                    if (!is_constant(b) || const_name(b) != get_tactic_name())
                        throw exception("tactic namespace declarations have been modified, "
                                        "function 'tactic.apply' is expected to return a 'tactic'");
                }
            }
            return true;
        }
    }
    return false;
}

pair<expr, justification> update_meta(expr const & meta, substitution s) {
    buffer<expr> args;
    expr mvar = get_app_args(meta, args);
    justification j;
    auto p = s.instantiate_metavars(mlocal_type(mvar));
    mvar   = update_mlocal(mvar, p.first);
    j      = p.second;
    for (expr & arg : args) {
        auto p = s.instantiate_metavars(mlocal_type(arg));
        arg    = update_mlocal(arg, p.first);
        j      = mk_composite1(j, p.second);
    }
    return mk_pair(mk_app(mvar, args), j);
}

expr instantiate_meta(expr const & meta, substitution & subst) {
    lean_assert(is_meta(meta));
    buffer<expr> locals;
    expr mvar = get_app_args(meta, locals);
    mvar = update_mlocal(mvar, subst.instantiate_all(mlocal_type(mvar)));
    for (auto & local : locals)
        local = subst.instantiate_all(local);
    return mk_app(mvar, locals);
}

justification mk_failed_to_synthesize_jst(environment const & env, expr const & m) {
    return mk_justification(m, [=](formatter const & fmt, substitution const & subst) {
            substitution tmp(subst);
            expr new_m    = instantiate_meta(m, tmp);
            expr new_type = type_checker(env).infer(new_m).first;
            proof_state ps = to_proof_state(new_m, new_type, name_generator("dontcare"));
            return format("failed to synthesize placeholder") + line() + ps.pp(fmt);
        });
}
}
