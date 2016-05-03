/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/aux_recursors.h"
#include "library/user_recursors.h"
#include "library/util.h"
#include "compiler/compiler_step_visitor.h"
#include "compiler/comp_irrelevant.h"
#include "compiler/eta_expansion.h"
#include "compiler/simp_pr1_rec.h"
#include "compiler/inliner.h"
#include "compiler/lambda_lifting.h"

void pp_detail(lean::environment const & env, lean::expr const & e);
void pp(lean::environment const & env, lean::expr const & e);

namespace lean {
class expand_aux_recursors_fn : public compiler_step_visitor {
    bool is_aux_recursor(expr const & e) {
        if (!is_app(e))
            return false;
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return false;
        return ::lean::is_aux_recursor(env(), const_name(fn)) || is_user_defined_recursor(env(), const_name(fn));
    }

    virtual expr visit_app(expr const & e) override {
        if (is_aux_recursor(e)) {
            return compiler_step_visitor::visit(ctx().whnf_pred(e, [&](expr const & e) { return is_aux_recursor(e); }));
        } else {
            expr new_e = ctx().whnf_pred(e, [&](expr const &) { return false; });
            if (is_eqp(new_e, e))
                return compiler_step_visitor::visit_app(new_e);
            else
                return compiler_step_visitor::visit(new_e);
        }
    }

public:
    expand_aux_recursors_fn(environment const & env):compiler_step_visitor(env) {}
};

static expr expand_aux_recursors(environment const & env, expr const & e) {
    return expand_aux_recursors_fn(env)(e);
}

static name * g_tmp_prefix = nullptr;

class preprocess_rec_fn {
    environment    m_env;
    buffer<name> & m_aux_decls;

    bool check(declaration const & d, expr const & v) {
        type_checker tc(m_env);
        expr t = tc.check(v, d.get_univ_params());
        if (!tc.is_def_eq(d.get_type(), t))
            throw exception("preprocess_rec failed");
        return true;
    }

    void display(expr const & v) {
        for (name const & n : m_aux_decls) {
            std::cout << ">> " << n << "\n";
            declaration d = m_env.get(n);
            ::pp_detail(m_env, d.get_value());
        }
        std::cout << ">> main\n";
        ::pp_detail(m_env, v);
    }

public:
    preprocess_rec_fn(environment const & env, buffer<name> & aux_decls):
        m_env(env), m_aux_decls(aux_decls) {}

    environment operator()(declaration const & d) {
        expr v = d.get_value();
        v = expand_aux_recursors(m_env, v);
        v = mark_comp_irrelevant(m_env, v);
        v = eta_expand(m_env, v);
        v = simp_pr1_rec(m_env, v);
        v = inline_simple_definitions(m_env, v);
        v = lambda_lifting(m_env, v, m_aux_decls, d.is_trusted());
        display(v);
        // TODO(Leo)
        check(d, v);
        return m_env;
    }
};

environment preprocess_rec(environment const & env, declaration const & d, buffer<name> & aux_decls) {
    return preprocess_rec_fn(env, aux_decls)(d);
}

void initialize_preprocess_rec() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_preprocess_rec() {
    delete g_tmp_prefix;
}
}
