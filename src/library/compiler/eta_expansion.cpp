/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/eta_expansion.h"

namespace lean {
class eta_expand_fn : public compiler_step_visitor {
    optional<expr> expand_core(expr const & e) {
        lean_assert(!is_lambda(e));
        expr t = ctx().whnf(ctx().infer(e));
        if (!is_pi(t))
            return none_expr();
        expr r = copy_tag(e, mk_lambda(name("x"), binding_domain(t), mk_app(e, mk_var(0))));
        return some_expr(visit(r));
    }

    expr expand(expr const & e) {
        if (auto r = expand_core(e))
            return *r;
        else
            return e;
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_marked_as_comp_irrelevant(e))
            return e;
        else if (auto r = expand_core(e))
            return copy_tag(e, expr(*r));
        else
            return compiler_step_visitor::visit_macro(e);
    }

    virtual expr visit_constant(expr const & e) override { return expand(e); }

    virtual expr visit_local(expr const & e) override { return expand(e); }

    virtual expr visit_app(expr const & e) override {
        if (auto r = expand_core(e)) {
            return *r;
        } else {
            buffer<expr> args;
            expr f = get_app_args(e, args);
            bool modified = false;
            for (unsigned i = 0; i < args.size(); i++) {
                expr arg     = args[i];
                expr new_arg = visit(arg);
                if (!is_eqp(arg, new_arg))
                    modified = true;
                args[i] = new_arg;
            }
            if (!modified)
                return e;
            else
                return copy_tag(e, mk_app(f, args));
        }
    }

public:
    eta_expand_fn(environment const & env):compiler_step_visitor(env) {}
};

expr eta_expand(environment const & env, expr const & e) {
    return eta_expand_fn(env)(e);
}
}
