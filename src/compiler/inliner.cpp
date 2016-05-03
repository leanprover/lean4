/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "compiler/compiler_step_visitor.h"

namespace lean {
class inline_simple_definitions_fn : public compiler_step_visitor {
    /* Return true if fn should be unfolded when applied to nargs. */
    bool is_candidate(expr const & fn, unsigned nargs) {
        if (!is_constant(fn))
            return false;
        declaration d = env().get(const_name(fn));
        if (!d.is_definition() || d.is_theorem())
            return false;
        expr v = d.get_value();
        unsigned arity = 0;
        while (is_lambda(v)) {
            arity++;
            v = binding_body(v);
        }
        if (arity > nargs)
            return false;
        buffer<expr> ys;
        buffer<bool> bitmap;
        expr const & g = get_app_args(v, ys);
        if (!is_constant(g) && !is_var(g))
            return false;
        for (expr const & y : ys) {
            if (!is_var(y) && !is_constant(y))
                return false;
            if (is_var(y)) {
                unsigned vidx = var_idx(y);
                if (vidx >= bitmap.size())
                    bitmap.resize(vidx+1, false);
                if (bitmap[vidx]) {
                    /* y_i's are not pairwise distinct */
                    return false;
                }
                bitmap[vidx] = true;
            }
        }
        return true;
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        unsigned nargs  = get_app_num_args(e);
        if (is_candidate(fn, nargs)) {
            if (auto r = unfold_term(env(), e))
                return visit(*r);
        } else if (auto r = ctx().reduce_projection(e)) {
            return visit(*r);
        }
        return compiler_step_visitor::visit_app(e);
    }

public:
    inline_simple_definitions_fn(environment const & env):compiler_step_visitor(env) {}
};

expr inline_simple_definitions(environment const & env, expr const & e) {
    return inline_simple_definitions_fn(env)(e);
}
}
