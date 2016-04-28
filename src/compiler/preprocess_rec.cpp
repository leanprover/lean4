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
#include "library/replace_visitor.h"
#include "compiler/eta_expansion.h"
#include "compiler/simp_pr1_rec.h"

void pp_detail(lean::environment const & env, lean::expr const & e);
void pp(lean::environment const & env, lean::expr const & e);

namespace lean {
class expand_aux_recursors_fn : public replace_visitor {
    environment const & m_env;
    type_checker        m_tc;

    virtual expr visit_binding(expr const & e) override {
        lean_assert(is_binding(e));
        expr new_d = visit(binding_domain(e));
        push_local_fn push_local(m_tc);
        expr new_l = push_local(binding_name(e), new_d, binding_info(e));
        expr new_b = visit(instantiate(binding_body(e), new_l));
        return update_binding(e, new_d, m_tc.abstract_locals(new_b, 1, &new_l));
    }

    bool is_recursor(expr const & e) {
        if (!is_app(e))
            return false;
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return false;
        return is_aux_recursor(m_env, const_name(fn)) || is_user_defined_recursor(m_env, const_name(fn));
    }

    virtual expr visit_app(expr const & e) override {
        if (is_recursor(e)) {
            return replace_visitor::visit_app(m_tc.whnf_pred(e, [&](expr const & e) { return is_recursor(e); }));
        } else {
            return replace_visitor::visit_app(e);
        }
    }
public:
    expand_aux_recursors_fn(environment const & env):m_env(env), m_tc(env) {}
};

static expr expand_aux_recursors(environment const & env, expr const & e) {
    return expand_aux_recursors_fn(env)(e);
}

static name * g_tmp_prefix = nullptr;

class preprocess_rec_fn {
    environment    m_env;
    // buffer<name> & m_aux_decls; // TODO(Leo):

    bool check(declaration const & d, expr const & v) {
        type_checker tc(m_env);
        expr t = tc.check(v, d.get_univ_params());
        if (!tc.is_def_eq(d.get_type(), t))
            throw exception("preprocess_rec failed");
        return true;
    }

public:
    preprocess_rec_fn(environment const & env, buffer<name> & /* aux_decls */): m_env(env) {} // , m_aux_decls(aux_decls) {}

    environment operator()(declaration const & d) {
        expr v = d.get_value();
        v = expand_aux_recursors(m_env, v);
        v = eta_expand(m_env, v);
        v = simp_pr1_rec(m_env, v);
        ::pp(m_env, v);
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
