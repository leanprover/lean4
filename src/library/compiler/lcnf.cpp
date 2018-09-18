/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "runtime/flet.h"
#include "runtime/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/expr_lt.h"
#include "library/util.h"
#include "library/aux_recursors.h"
#include "library/constants.h"
#include "library/projection.h"
#include "library/compiler/util.h"

namespace lean {
class to_lcnf_fn {
    typedef rb_expr_map<expr> cache;
    type_checker::state m_st;
    local_ctx           m_lctx;
    cache               m_cache;
    buffer<expr>        m_fvars;
    name                m_x;
    unsigned            m_next_idx{1};
public:
    to_lcnf_fn(environment const & env, local_ctx const & lctx):
        m_st(env), m_lctx(lctx), m_x("_x") {}

    environment & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr infer_type(expr const & e) { return type_checker(m_st, m_lctx).infer(e); }

    expr whnf(expr const & e) { return type_checker(m_st, m_lctx).whnf(e); }

    expr whnf_infer_type(expr const & e) {
        type_checker tc(m_st, m_lctx);
        return tc.whnf(tc.infer(e));
    }

    static bool is_lc_proof(expr const & e) {
        return is_app_of(e, get_lc_proof_name());
    }

    expr mk_let_decl(expr const & e) {
        expr type = cheap_beta_reduce(infer_type(e));
        /* Remark: we use `m_x.append_after(m_next_idx)` instead of `name(m_x, m_next_idx)`
           because the resulting name is confusing during debugging: it looks like a projection application.
           We should replace it with `name(m_x, m_next_idx)` when the compiler code gets more stable. */
        expr fvar = m_lctx.mk_local_decl(ngen(), m_x.append_after(m_next_idx), type, e);
        m_next_idx++;
        m_fvars.push_back(fvar);
        return fvar;
    }

    expr eta_expand(expr e, unsigned num_extra) {
        lean_assert(num_extra > 0);
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> args;
        lean_assert(!is_lambda(e));
        expr e_type = whnf_infer_type(e);
        for (unsigned i = 0; i < num_extra; i++) {
            if (!is_pi(e_type)) {
                throw exception("compiler error, unexpected type at LCNF conversion");
            }
            expr arg = m_lctx.mk_local_decl(ngen(), binding_name(e_type), binding_domain(e_type), binding_info(e_type));
            args.push_back(arg);
            e_type = whnf(instantiate(binding_body(e_type), arg));
        }
        return m_lctx.mk_lambda(args, mk_app(e, args));
    }

    expr visit_projection(expr const & fn, buffer<expr> & args, bool root) {
        constant_info info = env().get(const_name(fn));
        expr fn_val        = instantiate_value_lparams(info, const_levels(fn));
        std::reverse(args.begin(), args.end());
        return visit(apply_beta(fn_val, args.size(), args.data()), root);
    }

    unsigned get_constructor_nfields(name const & n) {
        return env().get(n).to_constructor_val().get_nfields();
    }

    expr visit_cases_on(expr const & fn, buffer<expr> & args, bool root) {
        name const & rec_name = const_name(fn);
        name const & I_name   = rec_name.get_prefix();
        lean_assert(is_inductive(env(), I_name));
        constant_info I_info        = env().get(I_name);
        inductive_val I_val         = I_info.to_inductive_val();
        unsigned nparams            = I_val.get_nparams();
        names cnstrs                = I_val.get_cnstrs();
        unsigned nminors            = length(cnstrs);
        unsigned nindices           = I_val.get_nindices();
        unsigned first_minor_idx    = nparams + 1 /* typeformer/motive */ + nindices + 1 /* major premise */;
        unsigned arity              = first_minor_idx + nminors;
        if (args.size() < arity) {
            return visit(eta_expand(mk_app(fn, args), arity - args.size()), root);
        } else if (args.size() > arity) {
            expr new_cases = visit(mk_app(fn, arity, args.data()), false);
            return visit(mk_app(new_cases, args.size() - arity, args.data() + arity), root);
        } else {
            for (unsigned i = 0; i < first_minor_idx; i++) {
                args[i] = visit(args[i], false);
            }
            lean_assert(first_minor_idx + nminors == arity);
            for (unsigned i = first_minor_idx; i < arity; i++) {
                name cnstr_name     = head(cnstrs);
                cnstrs              = tail(cnstrs);
                expr minor          = args[i];
                unsigned num_fields = get_constructor_nfields(cnstr_name);
                flet<local_ctx> save_lctx(m_lctx, m_lctx);
                buffer<expr> minor_fvars;
                unsigned j = 0;
                while (is_lambda(minor) && j < num_fields) {
                    expr new_d    = instantiate_rev(binding_domain(minor), minor_fvars.size(), minor_fvars.data());
                    expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(minor), new_d, binding_info(minor));
                    minor_fvars.push_back(new_fvar);
                    minor = binding_body(minor);
                    j++;
                }
                minor = instantiate_rev(minor, minor_fvars.size(), minor_fvars.data());
                if (j < num_fields) {
                    minor = eta_expand(minor, num_fields - j);
                }
                flet<cache> save_cache(m_cache, m_cache);
                unsigned m_fvars_init_size = m_fvars.size();
                expr new_minor             = visit(minor, false);
                // add let-decls
                new_minor      = m_lctx.mk_lambda(m_fvars.size() - m_fvars_init_size, m_fvars.data() + m_fvars_init_size, new_minor);
                m_fvars.shrink(m_fvars_init_size);
                new_minor      = m_lctx.mk_lambda(minor_fvars, new_minor);
                args[i]        = new_minor;
            }
            return mk_let_decl(mk_app(fn, args));
        }
    }

    expr visit_no_confusion(expr const & fn, buffer<expr> & args, bool root) {
        name const & no_confusion_name  = const_name(fn);
        name const & I_name             = no_confusion_name.get_prefix();
        constant_info I_info            = env().get(I_name);
        inductive_val I_val             = I_info.to_inductive_val();
        unsigned nparams                = I_val.get_nparams();
        unsigned nindices               = I_val.get_nindices();
        unsigned basic_arity            = nparams + nindices + 1 /* motive */ + 2 /* lhs/rhs */ + 1 /* equality */;
        if (args.size() < basic_arity) {
            return visit(eta_expand(mk_app(fn, args), basic_arity - args.size()), root);
        }
        lean_assert(args.size() >= basic_arity);
        type_checker tc(m_st, m_lctx);
        expr lhs                        = tc.whnf(args[nparams + nindices + 1]);
        expr rhs                        = tc.whnf(args[nparams + nindices + 2]);
        optional<name> lhs_constructor  = is_constructor_app(env(), lhs);
        optional<name> rhs_constructor  = is_constructor_app(env(), rhs);
        if (!lhs_constructor || !rhs_constructor)
            throw exception(sstream() << "compiler error, unsupported occurrence of '" << no_confusion_name << "', constructors expected");
        if (lhs_constructor != rhs_constructor) {
            expr type = tc.whnf(tc.infer(mk_app(fn, args)));
            level lvl = sort_level(tc.ensure_type(type));
            return mk_let_decl(mk_app(mk_constant(get_lc_unreachable_name(), {lvl}), type));
        } else if (args.size() < basic_arity + 1 /* major */) {
            return visit(eta_expand(mk_app(fn, args), basic_arity + 1 - args.size()), root);
        } else {
            lean_assert(args.size() >= basic_arity + 1);
            unsigned major_idx = basic_arity;
            expr major         = args[major_idx];
            unsigned nfields   = get_constructor_nfields(*lhs_constructor);
            while (nfields > 0) {
                if (!is_lambda(major))
                    major = eta_expand(major, nfields);
                lean_assert(is_lambda(major));
                expr type  = binding_domain(major);
                lean_assert(tc.is_prop(type));
                expr proof = mk_app(mk_constant(get_lc_proof_name()), type);
                major      = instantiate(binding_body(major), proof);
                nfields--;
            }
            expr new_e = mk_app(major, args.size() - major_idx - 1, args.data() + major_idx + 1);
            return visit(new_e, root);
        }
    }

    expr visit_eq_rec(expr const & fn, buffer<expr> & args, bool root) {
        lean_assert(const_name(fn) == get_eq_rec_name() ||
                    const_name(fn) == get_eq_ndrec_name() ||
                    const_name(fn) == get_eq_cases_on_name());
        if (args.size() < 6) {
            return visit(eta_expand(mk_app(fn, args), 6 - args.size()), root);
        } else {
            unsigned eq_rec_nargs = 6;
            unsigned minor_idx;
            if (const_name(fn) == get_eq_cases_on_name())
                minor_idx = 5;
            else
                minor_idx = 3;
            type_checker tc(m_st, m_lctx);
            expr minor       = args[minor_idx];
            expr minor_type  = tc.whnf(tc.infer(minor));
            expr eq_rec_type = tc.whnf(tc.infer(mk_app(fn, eq_rec_nargs, args.data())));
            expr new_e;
            if (tc.is_def_eq(minor_type, eq_rec_type)) {
                /* Type cast is not needed */
                new_e = minor;
            } else {
                level minor_lvl  = sort_level(tc.ensure_type(minor_type));
                level eq_rec_lvl = sort_level(tc.ensure_type(eq_rec_type));
                new_e            = visit(mk_app(mk_constant(get_lc_cast_name(), {eq_rec_lvl, minor_lvl}), minor_type, eq_rec_type, minor), false);
            }
            new_e            = mk_app(new_e, args.size() - eq_rec_nargs, args.data() + eq_rec_nargs);
            return visit(new_e, root);
        }
    }

    expr visit_false_rec(expr const & fn, buffer<expr> & args, bool root) {
        if (args.size() < 2) {
            return visit(eta_expand(mk_app(fn, args), 2 - args.size()), root);
        } else {
            /* Remark: args.size() may be greater than 2, but
               (lc_unreachable a_1 ... a_n) is equivalent to (lc_unreachable) */
            expr type = infer_type(mk_app(fn, args));
            return mk_let_decl(mk_lc_unreachable(m_st, m_lctx, type));
        }
    }

    expr visit_and_rec(expr const & fn, buffer<expr> & args, bool root) {
        lean_assert(const_name(fn) == get_and_rec_name() || const_name(fn) == get_and_cases_on_name());
        if (args.size() < 5) {
            return visit(eta_expand(mk_app(fn, args), 5 - args.size()), root);
        } else {
            expr a    = args[0];
            expr b    = args[1];
            expr pr_a = mk_app(mk_constant(get_lc_proof_name()), a);
            expr pr_b = mk_app(mk_constant(get_lc_proof_name()), b);
            expr minor;
            if (const_name(fn) == get_and_rec_name())
                minor = args[3];
            else
                minor = args[4];
            return visit(mk_app(minor, pr_a, pr_b), root);
        }
    }

    expr visit_constructor(expr const & fn, buffer<expr> & args, bool root) {
        constructor_val cval = env().get(const_name(fn)).to_constructor_val();
        unsigned arity       = cval.get_nparams() + cval.get_nfields();
        if (args.size() < arity) {
            return visit(eta_expand(mk_app(fn, args), arity - args.size()), root);
        } else {
            return visit_app_default(fn, args);
        }
    }

    bool should_create_let_decl(expr const & e, expr e_type) {
        switch (e.kind()) {
        case expr_kind::BVar:  case expr_kind::MVar:
        case expr_kind::FVar:  case expr_kind::Sort:
        case expr_kind::Const: case expr_kind::Lit:
        case expr_kind::Pi:
            return false;
        default:
            break;
        }

        if (is_lc_proof(e)) return false;

        type_checker tc(m_st, m_lctx);
        e_type = tc.whnf(e_type);
        if (is_sort(e_type)) {
            return false;
        } else if (tc.is_prop(e_type)) {
            return false;
        } else if (is_pi(e_type)) {
            /* Functions that return types are not relevant */
            flet<local_ctx> save_lctx(m_lctx, m_lctx);
            while (is_pi(e_type)) {
                expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(e_type), binding_domain(e_type));
                e_type = whnf(instantiate(binding_body(e_type), fvar));
            }
            if (is_sort(e_type))
                return false;
        }
        return true;
    }

    expr visit_app_default(expr const & fn, buffer<expr> & args) {
        for (expr & arg : args) {
            arg = visit(arg, false);
        }
        return mk_let_decl(mk_app(fn, args));
    }

    expr visit_app(expr const & e, bool root) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (is_constant(fn)) {
            if (const_name(fn) == get_and_rec_name() || const_name(fn) == get_and_cases_on_name()) {
                return visit_and_rec(fn, args, root);
            } else if (const_name(fn) == get_eq_rec_name() || const_name(fn) == get_eq_ndrec_name() ||
                       const_name(fn) == get_eq_cases_on_name()) {
                return visit_eq_rec(fn, args, root);
            } else if (const_name(fn) == get_false_rec_name() || const_name(fn) == get_false_cases_on_name()) {
                return visit_false_rec(fn, args, root);
            } else if (is_cases_on_recursor(env(), const_name(fn))) {
                return visit_cases_on(fn, args, root);
            } else if (is_projection(env(), const_name(fn))) {
                return visit_projection(fn, args, root);
            } else if (const_name(fn) == get_id_rhs_name()) {
                if (args.size() < 2) {
                    return visit(eta_expand(e, 2 - args.size()), root);
                } else {
                    expr new_e = args[1];
                    return visit(mk_app(new_e, args.size() - 2, args.data() + 2), root);
                }
            } else if (is_no_confusion(env(), const_name(fn))) {
                return visit_no_confusion(fn, args, root);
            } else if (is_constructor(env(), const_name(fn))) {
                return visit_constructor(fn, args, root);
            } else if (optional<name> n = is_meta_rec_name(const_name(fn))) {
                fn = mk_constant(*n, const_levels(fn));
                return visit_app_default(fn, args);
            }
        }
        fn = visit(fn, false);
        return visit_app_default(fn, args);
    }

    expr visit_proj(expr const & e) {
        expr v = visit(proj_expr(e), false);
        expr r = mk_proj(proj_idx(e), v);
        return mk_let_decl(r);
    }

    expr visit_mdata(expr const & e, bool root) {
        if (is_lc_mdata(e)) {
            expr v = visit(mdata_expr(e), false);
            expr r = mk_mdata(mdata_data(e), v);
            return mk_let_decl(r);
        } else {
            return visit(mdata_expr(e), root);
        }
    }

    expr visit_lambda(expr e, bool root) {
        lean_assert(is_lambda(e));
        expr r;
        {
            flet<local_ctx> save_lctx(m_lctx, m_lctx);
            flet<cache>     save_cache(m_cache, m_cache);
            unsigned m_fvars_init_size = m_fvars.size();
            buffer<expr> binding_fvars;
            while (is_lambda(e)) {
                /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
                expr new_d    = instantiate_rev(binding_domain(e), binding_fvars.size(), binding_fvars.data());
                expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_d, binding_info(e));
                binding_fvars.push_back(new_fvar);
                e = binding_body(e);
            }
            expr new_body = visit(instantiate_rev(e, binding_fvars.size(), binding_fvars.data()), true);
            new_body      = m_lctx.mk_lambda(m_fvars.size() - m_fvars_init_size, m_fvars.data() + m_fvars_init_size, new_body);
            m_fvars.shrink(m_fvars_init_size);
            r = m_lctx.mk_lambda(binding_fvars, new_body);
        }
        if (root)
            return r;
        else
            return mk_let_decl(r);
    }

    expr visit_let(expr e, bool root) {
        buffer<expr> let_fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), let_fvars.size(), let_fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), let_fvars.size(), let_fvars.data()), false);
            if (should_create_let_decl(new_val, new_type)) {
                expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), new_type, new_val);
                let_fvars.push_back(new_fvar);
                m_fvars.push_back(new_fvar);
            } else {
                let_fvars.push_back(new_val);
            }
            e = let_body(e);
        }
        return visit(instantiate_rev(e, let_fvars.size(), let_fvars.data()), root);
    }

    expr cache_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(e, r);
        return r;
    }

    expr visit(expr const & e, bool root) {
        switch (e.kind()) {
        case expr_kind::BVar:  case expr_kind::MVar:
            lean_unreachable();
        case expr_kind::FVar:  case expr_kind::Sort:
        case expr_kind::Const: case expr_kind::Lit:
        case expr_kind::Pi:
            return e;
        default:
            break;
        }

        if (is_lc_proof(e)) return e;

        bool shared = is_shared(e);
        if (shared) {
            if (auto it = m_cache.find(e))
                return *it;
        }

        {
            type_checker tc(m_st, m_lctx);
            expr type = tc.whnf(tc.infer(e));
            if (is_sort(type)) {
                /* Types are not pre-processed */
                return cache_result(e, e, shared);
            } else if (tc.is_prop(type)) {
                /* We replace proofs using `lc_proof` constant */
                expr r = mk_app(mk_constant(get_lc_proof_name()), type);
                return cache_result(e, r, shared);
            } else if (is_pi(type)) {
                /* Functions that return types are not pre-processed. */
                flet<local_ctx> save_lctx(m_lctx, m_lctx);
                while (is_pi(type)) {
                    expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(type), binding_domain(type));
                    type = whnf(instantiate(binding_body(type), fvar));
                }
                if (is_sort(type))
                    return cache_result(e, e, shared);
            }
        }

        switch (e.kind()) {
        case expr_kind::App:    return cache_result(e, visit_app(e, root), shared);
        case expr_kind::Proj:   return cache_result(e, visit_proj(e), shared);
        case expr_kind::MData:  return cache_result(e, visit_mdata(e, root), shared);
        case expr_kind::Lambda: return cache_result(e, visit_lambda(e, root), shared);
        case expr_kind::Let:    return cache_result(e, visit_let(e, root), shared);
        default: lean_unreachable();
        }
    }

    expr operator()(expr const & e) {
        expr r = visit(e, true);
        return m_lctx.mk_lambda(m_fvars, r);
    }
};

expr to_lcnf(environment const & env, local_ctx const & lctx, expr const & e) {
    return to_lcnf_fn(env, lctx)(e);
}

void initialize_lcnf() {
}

void finalize_lcnf() {
}
}
