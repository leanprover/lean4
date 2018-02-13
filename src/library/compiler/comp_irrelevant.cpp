/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/annotation.h"
#include "library/quote.h"
#include "library/compiler/util.h"
#include "library/compiler/compiler_step_visitor.h"

namespace lean {
static name * g_comp_irrel = nullptr;

expr mark_comp_irrelevant(expr const & e) {
    return copy_tag(e, mk_annotation(*g_comp_irrel, e));
}

bool is_marked_as_comp_irrelevant(expr const & e) {
    return is_annotation(e, *g_comp_irrel);
}

class mark_comp_irrelevant_fn : public compiler_step_visitor {
protected:
    optional<expr> mark_if_irrel_core(expr const & e) {
        if (is_comp_irrelevant(ctx(), e))
            return some_expr(mark_comp_irrelevant(e));
        else
            return none_expr();
    }

    expr mark_if_irrel(expr const & e) {
        if (auto v = mark_if_irrel_core(e))
            return *v;
        else
            return e;
    }

    expr mark_lambda_let(expr const & e) {
        /* if body is marked as computationally irrelevant, then mark e */
        expr body = e;
        while (true) {
            if (is_lambda(body))
                body = binding_body(body);
            else if (is_let(body))
                body = let_body(body);
            else
                break;
        }
        if (is_marked_as_comp_irrelevant(body))
            return mark_comp_irrelevant(e);
        else
            return e;
    }

    virtual expr visit_sort(expr const & e) override {
        return mark_comp_irrelevant(e);
    }

    virtual expr visit_pi(expr const & e) override {
        return mark_comp_irrelevant(e);
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_marked_as_comp_irrelevant(e))
            return e;
        else if (auto v = mark_if_irrel_core(e))
            return *v;
        else
            return compiler_step_visitor::visit_macro(e);
    }

    virtual expr visit_constant(expr const & e) override {
        return mark_if_irrel(e);
    }

    virtual expr visit_local(expr const & e) override {
        return mark_if_irrel(e);
    }

    virtual expr visit_app(expr const & e) override {
        if (auto v = mark_if_irrel_core(e))
            return *v;
        else
            return compiler_step_visitor::visit_app(e);
    }

    virtual expr visit_lambda(expr const & e) override {
        return mark_lambda_let(compiler_step_visitor::visit_lambda(e));
    }

    virtual expr visit_let(expr const & e) override {
        return mark_lambda_let(compiler_step_visitor::visit_let(e));
    }

public:
    mark_comp_irrelevant_fn(environment const & env, abstract_context_cache & cache):
        compiler_step_visitor(env, cache) {}
};

expr mark_comp_irrelevant_subterms(environment const & env, abstract_context_cache & cache, expr const & e) {
    return mark_comp_irrelevant_fn(env, cache)(e);
}

void initialize_comp_irrelevant() {
    g_comp_irrel = new name("comp_irrel");
    register_annotation(*g_comp_irrel);
}

void finalize_comp_irrelevant() {
    delete g_comp_irrel;
}
}
