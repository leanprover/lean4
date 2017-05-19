/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/replace_visitor.h"
#include "library/inverse.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"
#include "library/tactic/unfold_tactic.h"
#include "frontends/lean/elaborator.h"

namespace lean {
/* Recursive equation pattern validation.*/
class validate_equation_lhs_fn : public replace_visitor {
    elaborator &   m_elab;
    bool           m_has_invalid_pattern = false;
    expr           m_ref;

    type_context & ctx() { return m_elab.m_ctx; }
    environment const & env() { return m_elab.env(); }

    optional<expr> expand(expr const & e) {
        /* We don't simply use whnf because we want to avoid exposing the internal implementation
           of definitions compiled using the equation compiler */
        {
            /* Try without use delta reduction */
            type_context::transparency_scope scope(ctx(), transparency_mode::None);
            expr new_e = ctx().whnf(e);
            if (new_e != e) return some_expr(new_e);
        }
        if (auto new_e = ctx().reduce_projection(e))
            return new_e;
        /* Try to unfold using refl equations */
        if (auto new_e = dunfold(ctx(), e))
            return new_e;
        /* Last resort, whnf using current setting */
        expr new_e = ctx().whnf(e);
        if (new_e != e) return some_expr(new_e);
        return none_expr();
    }

    void throw_invalid_pattern(char const * msg, expr const & e) {
        m_elab.report_or_throw(
            elaborator_exception(m_ref, format(msg)
                + format(" (possible solution, mark term as inaccessible using '.( )')")
                + m_elab.pp_indent(e))
            .ignore_if(m_elab.has_synth_sorry(e)));
        m_has_invalid_pattern = true;
    }

    virtual expr visit_local(expr const & e) override {
        return e;
    }

    virtual expr visit_lambda(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of lambda expression in pattern", e);
        return e;
    }

    virtual expr visit_pi(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of pi/forall expression in pattern", e);
        return e;
    }

    virtual expr visit_let(expr const & e) override {
        return visit(instantiate(let_body(e), let_value(e)));
    }

    virtual expr visit_sort(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of sort in pattern", e);
        return e;
    }

    virtual expr visit_meta(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of metavariable in pattern", e);
        return e;
    }

    void throw_invalid_app(expr const & e) {
        if (is_constant(e))
            throw_invalid_pattern("invalid constant in pattern, it cannot be reduced to a constructor", e);
        else
            throw_invalid_pattern("invalid function application in pattern, it cannot be reduced to a constructor", e);
    }

    virtual expr visit_app(expr const & e) override {
        expr it = e;
        while (true) {
            if (is_nat_int_char_string_name_value(ctx(), it))
                return e;
            if (!is_app(it) && !is_constant(it))
                return visit(it);
            buffer<expr> args;
            expr const & fn = get_app_args(it, args);
            if (!is_constant(fn)) {
                throw_invalid_app(e);
                return e;
            }

            if (optional<name> I = is_ginductive_intro_rule(env(), const_name(fn))) {
                unsigned num_params = get_ginductive_num_params(env(), *I);
                for (unsigned i = num_params; i < args.size(); i++) {
                    visit(args[i]);
                }
                return e;
            } else if (optional<inverse_info> info = has_inverse(env(), const_name(fn))) {
                visit(args.back());
                return e;
            } else {
                if (auto r = expand(it)) {
                    it = *r;
                } else {
                    throw_invalid_app(e);
                    return e;
                }
            }
        }
    }

    virtual expr visit_constant(expr const & e) override {
        return visit_app(e);
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_inaccessible(e)) {
            return e;
        } else if (auto r = ctx().expand_macro(e)) {
            return visit(*r);
        } else if (is_synthetic_sorry(e)) {
            return e;
        } else {
            throw_invalid_pattern("invalid occurrence of macro expression in pattern", e);
            return e;
        }
    }

public:
    validate_equation_lhs_fn(elaborator & elab, expr const & ref):
        m_elab(elab), m_ref(ref) {
    }

    bool validate(expr const & lhs) {
        buffer<expr> args;
        get_app_args(lhs, args);
        for (expr & arg : args)
            visit(arg);
        return m_has_invalid_pattern;
    }
};

bool validate_equation_lhs(elaborator & elab, expr const & lhs, expr const & ref) {
    return validate_equation_lhs_fn(elab, ref).validate(elab.instantiate_mvars(lhs));
}
}
