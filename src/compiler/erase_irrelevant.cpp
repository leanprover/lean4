/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/aux_recursors.h"
#include "compiler/util.h"
#include "compiler/compiler_step_visitor.h"

namespace lean {
static expr * g_neutral_expr     = nullptr;
static expr * g_unreachable_expr = nullptr;
class erase_irrelevant_fn : public compiler_step_visitor {

    virtual expr visit_constant(expr const & e) override {
        /* Erase universe level information */
        return mk_constant(const_name(e));
    }

    /* We keep only the major and minor premises in cases_on applications. */
    expr visit_cases_on(expr const & fn, buffer<expr> & args) {
        name const & rec_name       = const_name(fn);
        name const & I_name         = rec_name.get_prefix();
        unsigned nparams            = *inductive::get_num_params(env(), I_name);
        unsigned nminors            = *inductive::get_num_minor_premises(env(), I_name);
        unsigned nindices           = *inductive::get_num_indices(env(), I_name);
        unsigned arity              = nparams + 1 /* typeformer/motive */ + nindices + 1 /* major premise */ + nminors;
        lean_assert(args.size() >= arity);
        for (unsigned i = nparams + 1 + nindices; i < args.size(); i++) {
            args[i] = visit(args[i]);
        }
        return mk_app(fn, args.size() - nparams - 1 - nindices, args.data() + nparams + 1 + nindices);
    }

    /* Remove eq.rec applications since they are just "type-casting" operations. */
    expr visit_eq_rec(buffer<expr> & args) {
        lean_assert(args.size() >= 6);
        expr major = visit(args[3]);
        for (unsigned i = 6; i < args.size(); i++)
            args[i] = visit(args[i]);
        return beta_reduce(mk_app(major, args.size() - 6, args.data() + 6));
    }

    expr consume_lambdas(type_context::tmp_locals & locals, expr e) {
        while (true) {
            if (is_lambda(e)) {
                expr local = locals.push_local_from_binding(e);
                e = instantiate(binding_body(e), local);
            } else {
                return beta_reduce(e);
            }
        }
    }

    /* We can eliminate no_confusion applications, they do not add any relevant information to the environment */
    expr visit_no_confusion(expr const & fn, buffer<expr> const & args) {
        lean_assert(is_constant(fn));
        name const & no_confusion_name = const_name(fn);
        name const & I_name            = no_confusion_name.get_prefix();
        unsigned nparams               = *inductive::get_num_params(env(), I_name);
        unsigned nindices              = *inductive::get_num_indices(env(), I_name);
        unsigned basic_arity           = nparams + nindices + 1 /* motive */ + 2 /* lhs/rhs */ + 1 /* equality */;
        lean_assert(args.size() >= basic_arity);
        expr lhs                       = ctx().whnf(args[nparams + nindices + 1]);
        expr rhs                       = ctx().whnf(args[nparams + nindices + 2]);
        optional<name> lhs_constructor = is_constructor_app(env(), lhs);
        optional<name> rhs_constructor = is_constructor_app(env(), rhs);
        if (!lhs_constructor || !rhs_constructor)
            throw exception(sstream() << "code generation failed, unsupported occurrence of '" << no_confusion_name << "', constructors expected");
        if (lhs_constructor != rhs_constructor)
            return *g_unreachable_expr;
        lean_assert(args.size() >= basic_arity + 1);
        expr major = args[nparams + nindices + 4];
        type_context::tmp_locals locals(ctx());
        major = consume_lambdas(locals, major);
        major = visit(major);
        major = locals.mk_lambda(major);
        expr r = major;

        unsigned c_data_sz = get_constructor_arity(env(), *lhs_constructor) - nparams;
        for (unsigned i = 0; i < c_data_sz; i++)
            r = mk_app(r, *g_neutral_expr); // add dummy proofs
        /* add remaining arguments */
        for (unsigned i = nparams + nindices + 5; i < args.size(); i++)
            r = mk_app(r, visit(args[i]));
        return beta_reduce(r);
    }

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (is_lambda(fn)) {
            return visit(beta_reduce(e));
        } else if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (is_cases_on_recursor(env(), n)) {
                return visit_cases_on(fn, args);
            } else if (is_no_confusion(env(), n)) {
                return visit_no_confusion(fn, args);
            } else if (n == get_eq_rec_name()) {
                return visit_eq_rec(args);
            }
        }
        return compiler_step_visitor::visit_app(e);
    }

public:
    erase_irrelevant_fn(environment const & env):compiler_step_visitor(env) {}
};

expr erase_irrelevant(environment const & env, expr const & e) {
    return erase_irrelevant_fn(env)(e);
}

bool is_neutral_expr(expr const & e) {
    return e == *g_neutral_expr;
}

bool is_unreachable_expr(expr const & e) {
    return e == *g_unreachable_expr;
}

void initialize_erase_irrelevant() {
    g_neutral_expr     = new expr(mk_constant("_neutral_"));
    g_unreachable_expr = new expr(mk_constant("_unreachable_"));
}

void finalize_erase_irrelevant() {
    delete g_neutral_expr;
    delete g_unreachable_expr;
}
}
