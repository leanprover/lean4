/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "library/compiler/util.h"

#include "library/trace.h"

namespace lean {
class specialize_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;

    environment const & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr visit_lambda(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            expr new_type = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_type);
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), new_type, new_val);
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_cases_on(expr const & e) {
        lean_assert(is_cases_on_app(env(), e));
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        /* visit minor premises */
        unsigned minor_idx; unsigned minors_end;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(env(), const_name(c));
        for (; minor_idx < minors_end; minor_idx++) {
            args[minor_idx] = visit(args[minor_idx]);
        }
        return mk_app(c, args);
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases_on(e);
        } else {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (!is_constant(fn)) return e;
            lean_trace(name({"compiler", "specialize"}), tout() << e << "\n";);
            // TODO(Leo):
            return e;
        }
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    specialize_fn(environment const & env):
        m_st(env) {}

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        m_base_name = d.fst();
        expr new_v = visit(d.snd());
        comp_decl new_d(d.fst(), new_v);
        return mk_pair(m_st.env(), comp_decls(new_d, comp_decls(m_new_decls)));
    }
};

pair<environment, comp_decls> specialize(environment const & env, comp_decl const & d) {
    return specialize_fn(env)(d);
}

void initialize_specialize() {
}

void finalize_specialize() {
}
}
