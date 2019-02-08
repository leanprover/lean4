/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "library/compiler/util.h"
#include "library/compiler/builtin.h"

namespace lean {
/* Infer type of expressions in ENF or LLNF. */
class ll_infer_type_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr infer_lambda(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e));
            fvars.push_back(fvar);
            e = binding_body(e);
        }
        expr r = infer(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_pi(fvars, r);
    }

    expr infer_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr type;
            if (is_join_point_name(let_name(e))) {
                expr val = instantiate_rev(let_value(e), fvars.size(), fvars.data());
                type     = infer(val);
            } else {
                type     = let_type(e);
            }
            expr fvar = m_lctx.mk_local_decl(ngen(), let_name(e), type);
            fvars.push_back(fvar);
            e = let_body(e);
        }
        return infer(instantiate_rev(e, fvars.size(), fvars.data()));
    }

    expr infer_cases(expr const & e) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() >= 2);
        bool first = true;
        expr r;
        for (unsigned i = 1; i < args.size(); i++) {
            expr minor = args[i];
            buffer<expr> fvars;
            while (is_lambda(minor)) {
                lean_assert(!has_loose_bvars(binding_domain(minor)));
                expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(minor), binding_domain(minor));
                fvars.push_back(fvar);
                minor = binding_body(minor);
            }
            expr minor_type = infer(instantiate_rev(minor, fvars.size(), fvars.data()));
            if (minor_type == mk_enf_object_type()) {
                /* If one of the branches return `_obj`, then the resultant type is `_obj`,
                   and the other branches should box result if it is not `_obj`. */
                return minor_type;
            } else if (first) {
                r = minor_type;
            } else if (minor_type != r) {
                /* All branches should return the same type, otherwise we box them. */
                return mk_enf_object_type();
            }
        }
        return r;
    }

    expr infer_constructor_type(expr const & e) {
        name I_name = env().get(const_name(get_app_fn(e))).to_constructor_val().get_induct();
        if (optional<unsigned> sz = ::lean::is_enum_type(env(), I_name)) {
            if (optional<expr> uint = to_uint_type(*sz))
                return *uint;
        }
        return mk_enf_object_type();
    }

    expr infer_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return infer_cases(e);
        } else if (is_constructor_app(env(), e)) {
            return infer_constructor_type(e);
        } else {
            expr fn_type   = infer(get_app_fn(e));
            unsigned nargs = get_app_num_args(e);
            for (unsigned i = 0; i < nargs; i++) {
                if (!is_pi(fn_type)) {
                    return mk_enf_object_type();
                } else {
                    fn_type = binding_body(fn_type);
                    lean_assert(!has_loose_bvars(fn_type));
                }
            }
            if (is_pi(fn_type)) {
                /* Application is creating a closure. */
                return mk_enf_object_type();
            } else {
                return fn_type;
            }
        }
    }

    optional<unsigned> is_enum_type(expr const & type) {
        expr const & I = get_app_fn(type);
        if (!is_constant(I)) return optional<unsigned>();
        return ::lean::is_enum_type(env(), const_name(I));
    }

    expr infer_proj(expr const & e) {
        name const & I_name   = proj_sname(e);
        inductive_val I_val   = env().get(I_name).to_inductive_val();
        lean_assert(I_val.get_ncnstrs() == 1);
        name const & k_name   = head(I_val.get_cnstrs());
        constant_info k_info  = env().get(k_name);
        expr type             = k_info.get_type();
        unsigned nparams      = I_val.get_nparams();
        buffer<expr> telescope;
        local_ctx lctx;
        to_telescope(env(), lctx, ngen(), type, telescope);
        lean_assert(telescope.size() >= nparams);
        lean_assert(nparams + proj_idx(e).get_small_value() < telescope.size());
        type_checker tc(m_st, lctx);
        expr ftype = lctx.get_type(telescope[nparams + proj_idx(e).get_small_value()]);
        ftype      = tc.whnf(ftype);
        if (is_constant(ftype) && is_runtime_scalar_type(const_name(ftype))) {
            return ftype;
        } else if (optional<unsigned> sz = is_enum_type(ftype)) {
            if (optional<expr> uint = to_uint_type(*sz))
                return *uint;
        }
        return mk_enf_object_type();
    }

    expr infer_constant(expr const & e) {
        if (optional<expr> type = get_native_constant_ll_type(env(), const_name(e))) {
            return *type;
        } else if (is_constructor(env(), const_name(e))) {
            return infer_constructor_type(e);
        } else {
            name c = mk_cstage2_name(const_name(e));
            optional<constant_info> info = env().find(c);
            if (info) return info->get_type();
            info = env().find(const_name(e));
            if (info) return mk_runtime_type(m_st, m_lctx, info->get_type());
            return mk_enf_object_type();
        }
    }

    expr infer(expr const & e) {
        switch (e.kind()) {
        case expr_kind::App:    return infer_app(e);
        case expr_kind::Lambda: return infer_lambda(e);
        case expr_kind::Let:    return infer_let(e);
        case expr_kind::Proj:   return infer_proj(e);
        case expr_kind::Const:  return infer_constant(e);
        case expr_kind::MData:  return infer(mdata_expr(e));
        case expr_kind::Lit:    return mk_enf_object_type();
        case expr_kind::FVar:   return m_lctx.get_local_decl(e).get_type();
        case expr_kind::Sort:   return mk_enf_neutral_type();
        case expr_kind::Pi:     return mk_enf_neutral_type();
        case expr_kind::BVar:   lean_unreachable();
        case expr_kind::MVar:   lean_unreachable();
        }
        lean_unreachable();
    }

public:
    ll_infer_type_fn(environment const & env, local_ctx const & lctx):m_st(env), m_lctx(lctx) {}

    expr operator()(expr const & e) { return infer(e); }
};

expr ll_infer_type(environment const & env, local_ctx const & lctx, expr const & e) {
    return ll_infer_type_fn(env, lctx)(e);
}
}
