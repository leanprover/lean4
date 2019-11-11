/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "library/replace_visitor.h"

namespace lean {
static name * g_aux_match_suffix = nullptr;

name const & get_aux_match_suffix() {
    return *g_aux_match_suffix;
}

name mk_aux_match_suffix(unsigned idx) {
    return g_aux_match_suffix->append_after(idx);
}

bool is_aux_match(name const & n) {
    return
        is_internal_name(n) && !n.is_atomic() && n.is_string() &&
        strncmp(n.get_string().data(), "_match", 6) == 0;
}

struct unfold_aux_match_fn : public replace_visitor {
    environment const & m_env;
    unfold_aux_match_fn(environment const & env):m_env(env) {}

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        expr new_fn   = visit(fn);
        bool modified = !is_eqp(fn, new_fn);
        for (expr & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(new_arg, arg))
                modified = true;
            arg = new_arg;
        }
        if (is_constant(new_fn)) {
            name const & n = const_name(new_fn);
            if (is_aux_match(n)) {
                new_fn = instantiate_value_lparams(m_env.get(n), const_levels(new_fn));
                std::reverse(args.begin(), args.end());
                return visit(apply_beta(new_fn, args.size(), args.data()));
            }
        }
        if (!modified)
            return e;
        else
            return mk_app(new_fn, args);
    }
};

expr unfold_aux_match(environment const & env, expr const & e) {
    return unfold_aux_match_fn(env)(e);
}

void initialize_aux_match() {
    g_aux_match_suffix = new name("_match");
}

void finalize_aux_match() {
    delete g_aux_match_suffix;
}
}
