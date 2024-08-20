/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/compiler/util.h"

namespace lean {

/* Find join-points */
class find_jp_fn {
    elab_environment const & m_env;
    local_ctx           m_lctx;
    name_generator      m_ngen;
    name_map<unsigned>  m_candidates;

    /* Remove all candidates occurring in `e`. */
    void remove_candidates_occurring_at(expr const & e) {
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_fvar(e)) return false;
                if (is_fvar(e)) {
                    m_candidates.erase(fvar_name(e));
                }
                return true;
            });
    }

    expr visit_lambda(expr e) {
        buffer<expr> fvars;
        while (is_lambda(e)) {
            expr domain     = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            remove_candidates_occurring_at(domain);
            expr fvar       = m_lctx.mk_local_decl(m_ngen, binding_name(e), domain, binding_info(e));
            fvars.push_back(fvar);
            e = binding_body(e);
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, e);
    }

    expr visit_cases(expr const & e) {
        lean_assert(is_cases_on_app(m_env, e));
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        /* simplify minor premises */
        unsigned minor_idx; unsigned minors_end;
        bool before_erasure = true;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(m_env, const_name(c), before_erasure);
        for (unsigned i = 0; i < minor_idx; i++) {
            remove_candidates_occurring_at(args[i]);
        }
        for (; minor_idx < minors_end; minor_idx++) {
            args[minor_idx] = visit(args[minor_idx]);
        }
        for (unsigned i = minors_end; i < args.size(); i++) {
            remove_candidates_occurring_at(args[i]);
        }
        return mk_app(c, args);
    }

    expr visit_app(expr const & e) {
        lean_assert(is_app(e));
        if (is_cases_on_app(m_env, e)) {
            return visit_cases(e);
        } else {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            for (expr const & arg : args)
                remove_candidates_occurring_at(arg);
            if (is_fvar(fn)) {
                if (unsigned const * arity = m_candidates.find(fvar_name(fn))) {
                    if (args.size() != *arity)
                        remove_candidates_occurring_at(fn);
                }
            }
            return e;
        }
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            remove_candidates_occurring_at(new_type);
            expr new_val  = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            expr fvar     = m_lctx.mk_local_decl(m_ngen, let_name(e), new_type, new_val);
            fvars.push_back(fvar);
            if (is_lambda(new_val)) {
                unsigned arity = get_num_nested_lambdas(new_val);
                m_candidates.insert(fvar_name(fvar), arity);
            }
            e = let_body(e);
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        e = visit(e);
        e = abstract(e, fvars.size(), fvars.data());
        unsigned i = fvars.size();
        while (i > 0) {
            --i;
            expr const & fvar    = fvars[i];
            local_decl fvar_decl = m_lctx.get_local_decl(fvar);
            expr type            = fvar_decl.get_type();
            expr value           = *fvar_decl.get_value();
            name n               = fvar_decl.get_user_name();
            if (m_candidates.contains(fvar_name(fvar))) {
                value = visit(value);
                n     = mk_join_point_name(n);
            } else {
                remove_candidates_occurring_at(value);
            }
            type  = abstract(type, i, fvars.data());
            value = abstract(value, i, fvars.data());
            e = mk_let(n, type, value, e);
        }
        return e;
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::MData:  return update_mdata(e, visit(mdata_expr(e)));
        default:                return e;
        }
    }

public:
    find_jp_fn(elab_environment const & env):
        m_env(env) {}

    expr operator()(expr const & e) {
        return visit(e);
    }
};

expr find_jp(elab_environment const & env, expr const & e) {
    return find_jp_fn(env)(e);
}
}
