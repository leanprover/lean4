/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/compiler/util.h"

namespace lean {
class lambda_lifting_fn {
    environment         m_env;
    name_generator      m_ngen;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    unsigned            m_next_idx{1};
    name                m_y;
    unsigned            m_next_let_idx{1};


    typedef std::unordered_set<name, name_hash> name_set;

    environment const & env() { return m_env; }

    name_generator & ngen() { return m_ngen; }

    expr visit_lambda_core(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e));
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    name next_let_name() {
        name r = m_y.append_after(m_next_let_idx);
        m_next_let_idx++;
        return r;
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            bool not_root = false;
            bool jp       = is_join_point_name(let_name(e));
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()), not_root, jp);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), next_let_name(), let_type(e), new_val);
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
        /* Remark: lambda lifting is applied after we have erased most type information,
           and `cases_on` applications have major premise and minor premises only. */
        for (unsigned i = 1; i < args.size(); i++) {
            args[i] = visit_lambda_core(args[i]);
        }
        return mk_app(c, args);
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases_on(e);
        } else {
            return e;
        }
    }

    void collect_fvars(expr const & e, buffer<expr> & fvars) {
        if (!has_fvar(e)) return;
        name_set collected;
        for_each(e, [&](expr const & x, unsigned) {
                if (!has_fvar(x)) return false;
                if (is_fvar(x)) {
                    if (collected.find(fvar_name(x)) == collected.end()) {
                        collected.insert(fvar_name(x));
                        fvars.push_back(x);
                    }
                }
                return true;
            });
    }

    /* Try to apply eta-reduction to reduce number of auxiliary declarations. */
    optional<expr> try_eta_reduction(expr const & e) {
        expr r = ::lean::try_eta(e);
        expr const & f = get_app_fn(r);

        if (is_fvar(f))
            return some_expr(r);

        if (is_constant(f)) {
            name const & n = const_name(f);
            if (!is_constructor(env(), n) && !is_cases_on_recursor(env(), n))
                return some_expr(r);
        }
        return none_expr();
    }

    name next_name(bool join_point) {
        name r(m_base_name, join_point ? "_join_point" : "_lambda");
        r = r.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    /* Creates `fun <fvar>, e`. Remark: it is different from `m_lctx.mk_lambda` because
       it will create a lambda expression even if for free variables in `fvars` that correspond
       to let declarations. */
    expr mk_lambda(buffer<expr> const & fvars, expr e) {
        e = abstract(e, fvars.size(), fvars.data());
        unsigned i = fvars.size();
        while (i > 0) {
            --i;
            expr const & fvar = fvars[i];
            local_decl decl   = m_lctx.get_local_decl(fvar);
            lean_assert(!has_loose_bvars(decl.get_type()));
            e = ::lean::mk_lambda(decl.get_user_name(), decl.get_type(), e);
        }
        return e;
    }

    expr visit_lambda(expr e, bool root, bool join_point) {
        e = visit_lambda_core(e);
        if (root)
            return e;
        if (optional<expr> r = try_eta_reduction(e))
            return *r;
        buffer<expr> fvars;
        collect_fvars(e, fvars);
        e = mk_lambda(fvars, e);
        name new_fn = next_name(join_point);
        m_new_decls.push_back(comp_decl(new_fn, e));
        return mk_app(mk_constant(new_fn), fvars);
    }

    expr visit(expr const & e, bool root = false, bool join_point = false) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e, root, join_point);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    lambda_lifting_fn(environment const & env):
        m_env(env), m_y("_y") {}

    comp_decls operator()(comp_decl const & cdecl) {
        m_base_name = cdecl.fst();
        expr r = visit(cdecl.snd(), true);
        comp_decl new_cdecl(cdecl.fst(), r);
        return comp_decls(new_cdecl, comp_decls(m_new_decls));
    }
};

comp_decls lambda_lifting(environment const & env, comp_decl const & cdecl) {
    return lambda_lifting_fn(env)(cdecl);
}
}
