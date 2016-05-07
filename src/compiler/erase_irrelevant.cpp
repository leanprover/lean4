/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "compiler/util.h"
#include "compiler/compiler_step_visitor.h"

namespace lean {
static expr * g_neutral_expr = nullptr;

class erase_irrelevant_fn : public compiler_step_visitor {

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

    virtual expr visit_app(expr const & e) override {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (is_lambda(fn)) {
            return visit(beta_reduce(e));
        } else if (is_constant(fn) && is_cases_on_recursor(env(), const_name(fn))) {
            return visit_cases_on(fn, args);
        } else if (is_constant(fn, get_eq_rec_name())) {
            return visit_eq_rec(args);
        } else {
            return compiler_step_visitor::visit_app(e);
        }
    }

public:
    erase_irrelevant_fn(environment const & env):compiler_step_visitor(env) {}
};

expr erase_irrelevant(environment const & env, expr const & e) {
    return erase_irrelevant_fn(env)(e);
}

bool is_neutral_term(expr const & e) {
    return e == *g_neutral_expr;
}

void initialize_erase_irrelevant() {
    g_neutral_expr = new expr(mk_constant("_neutral_"));
}



void finalize_erase_irrelevant() {
    delete g_neutral_expr;
}
}
