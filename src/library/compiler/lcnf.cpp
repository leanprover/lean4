/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "runtime/flet.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/expr_lt.h"
#include "library/util.h"
#include "library/aux_recursors.h"
#include "library/constants.h"
#include "library/projection.h"
#include "library/compiler/lc_util.h"

#include "library/trace.h"
#include "kernel/for_each_fn.h"

namespace lean {
static name * g_lcnf_fresh = nullptr;

class to_lcnf_fn {
    typedef rb_expr_map<expr> cache;
    environment         m_env;
    local_ctx           m_lctx;
    name_generator      m_ngen;
    type_checker::cache m_tc_cache;
    cache               m_cache;
    buffer<expr>        m_fvars;
    name                m_x;
    unsigned            m_next_idx{1};
public:
    to_lcnf_fn(environment const & env, local_ctx const & lctx):
        m_env(env), m_lctx(lctx), m_ngen(*g_lcnf_fresh), m_x("_x") {}

    expr infer_type(expr const & e) { return type_checker(m_env, m_lctx, m_tc_cache).infer(e); }

    expr whnf(expr const & e) { return type_checker(m_env, m_lctx, m_tc_cache).whnf(e); }

    expr whnf_infer_type(expr const & e) {
        type_checker tc(m_env, m_lctx, m_tc_cache);
        return tc.whnf(tc.infer(e));
    }

    static bool is_lc_proof(expr const & e) {
        return is_app_of(e, get_lc_proof_name());
    }

    expr mk_let_decl(expr const & e, bool root) {
        if (root) {
            return e;
        } else {
            expr type = infer_type(e);
            /* Remark: we use `m_x.append_after(m_next_idx)` instead of `name(m_x, m_next_idx)`
               because the resulting name is confusing during debugging: it looks like a projection application.
               We should replace it with `name(m_x, m_next_idx)` when the compiler code gets more stable. */
            expr fvar = m_lctx.mk_local_decl(m_ngen, m_x.append_after(m_next_idx), type, e);
            m_next_idx++;
            m_fvars.push_back(fvar);
            return fvar;
        }
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
            expr arg = m_lctx.mk_local_decl(m_ngen, binding_name(e_type), binding_domain(e_type), binding_info(e_type));
            args.push_back(arg);
            e_type = whnf(instantiate(binding_body(e_type), arg));
        }
        return m_lctx.mk_lambda(args, mk_app(e, args));
    }

    expr visit_projection(expr const & fn, buffer<expr> & args, bool root) {
        constant_info info = m_env.get(const_name(fn));
        expr fn_val        = instantiate_value_lparams(info, const_levels(fn));
        std::reverse(args.begin(), args.end());
        return visit(apply_beta(fn_val, args.size(), args.data()), root);
    }

    pair<unsigned, unsigned> get_constructor_arity_nfields(name const & n) {
        constant_info cnstr_info = m_env.get(n);
        lean_assert(cnstr_info.is_constructor());
        unsigned nparams         = cnstr_info.to_constructor_val().get_nparams();
        unsigned cnstr_arity     = 0;
        expr cnstr_type          = cnstr_info.get_type();
        while (is_pi(cnstr_type)) {
            cnstr_arity++;
            cnstr_type = binding_body(cnstr_type);
        }
        lean_assert(cnstr_arity >= nparams);
        unsigned num_fields = cnstr_arity - nparams;
        return mk_pair(cnstr_arity, num_fields);
    }

    unsigned get_constructor_nfields(name const & n) {
        return get_constructor_arity_nfields(n).second;
    }

    expr visit_cases_on(expr const & fn, buffer<expr> & args, bool root) {
        name const & rec_name = const_name(fn);
        name const & I_name   = rec_name.get_prefix();
        lean_assert(is_inductive(m_env, I_name));
        constant_info I_info        = m_env.get(I_name);
        inductive_val I_val         = I_info.to_inductive_val();
        unsigned nparams            = I_val.get_nparams();
        names cnstrs                = I_val.get_cnstrs();
        unsigned nminors            = length(cnstrs);
        unsigned nindices           = I_val.get_nindices();
        unsigned first_minor_idx    = nparams + 1 /* typeformer/motive */ + nindices + 1 /* major premise */;
        unsigned arity              = first_minor_idx + nminors;
        if (args.size() < arity) {
            return visit(eta_expand(mk_app(fn, args), arity - args.size()), root);
        } else {
            for (unsigned i = 0; i < first_minor_idx; i++) {
                args[i] = visit(args[i], false);
            }
            for (unsigned i = first_minor_idx; i < first_minor_idx + nminors; i++) {
                name cnstr_name     = head(cnstrs);
                cnstrs              = tail(cnstrs);
                expr minor          = args[i];
                unsigned num_fields = get_constructor_nfields(cnstr_name);
                flet<local_ctx> save_lctx(m_lctx, m_lctx);
                buffer<expr> minor_fvars;
                unsigned j = 0;
                while (is_lambda(minor) && j < num_fields) {
                    expr new_d    = instantiate_rev(binding_domain(minor), minor_fvars.size(), minor_fvars.data());
                    expr new_fvar = m_lctx.mk_local_decl(m_ngen, binding_name(minor), new_d, binding_info(minor));
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
                expr new_minor = visit(minor, true);
                if (is_lambda(new_minor) && m_fvars.size() == m_fvars_init_size) {
                    // create an aux let declaration to make sure we separate the cases_on binders from the result.
                    new_minor = mk_let_decl(new_minor, false);
                }
                // add let-decls
                new_minor      = m_lctx.mk_lambda(m_fvars.size() - m_fvars_init_size, m_fvars.data() + m_fvars_init_size, new_minor);
                m_fvars.shrink(m_fvars_init_size);
                new_minor      = m_lctx.mk_lambda(minor_fvars, new_minor);
                args[i]        = new_minor;
            }
            for (unsigned i = first_minor_idx + nminors; i < args.size(); i++) {
                args[i] = visit(args[i], false);
            }
            return mk_let_decl(mk_app(fn, args), root);
        }
    }

    expr visit_no_confusion(expr const & fn, buffer<expr> & args, bool root) {
        name const & no_confusion_name  = const_name(fn);
        name const & I_name             = no_confusion_name.get_prefix();
        constant_info I_info            = m_env.get(I_name);
        inductive_val I_val             = I_info.to_inductive_val();
        unsigned nparams                = I_val.get_nparams();
        unsigned nindices               = I_val.get_nindices();
        unsigned basic_arity            = nparams + nindices + 1 /* motive */ + 2 /* lhs/rhs */ + 1 /* equality */;
        if (args.size() < basic_arity) {
            return visit(eta_expand(mk_app(fn, args), basic_arity - args.size()), root);
        }
        lean_assert(args.size() >= basic_arity);
        type_checker tc(m_env, m_lctx, m_tc_cache);
        expr lhs                        = tc.whnf(args[nparams + nindices + 1]);
        expr rhs                        = tc.whnf(args[nparams + nindices + 2]);
        optional<name> lhs_constructor  = is_constructor_app(m_env, lhs);
        optional<name> rhs_constructor  = is_constructor_app(m_env, rhs);
        if (!lhs_constructor || !rhs_constructor)
            throw exception(sstream() << "compiler error, unsupported occurrence of '" << no_confusion_name << "', constructors expected");
        if (lhs_constructor != rhs_constructor) {
            expr type = tc.whnf(tc.infer(mk_app(fn, args)));
            level lvl = sort_level(tc.ensure_type(type));
            return mk_let_decl(mk_app(mk_constant(get_lc_unreachable_name(), {lvl}), type), root);
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
        lean_assert(const_name(fn) == get_eq_rec_name() || const_name(fn) == get_eq_ndrec_name());
        if (args.size() < 6) {
            return visit(eta_expand(mk_app(fn, args), 6 - args.size()), root);
        } else {
            unsigned eq_rec_nargs = 6;
            unsigned minor_idx    = 3;
            type_checker tc(m_env, m_lctx, m_tc_cache);
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
                new_e            = mk_app(mk_constant(get_lc_cast_name(), {eq_rec_lvl, minor_lvl}), minor_type, eq_rec_type, minor);
            }
            new_e            = mk_app(new_e, args.size() - eq_rec_nargs, args.data() + eq_rec_nargs);
            return visit(new_e, root);
        }
    }

    expr visit_app_default(expr const & fn, buffer<expr> & args, bool root) {
        for (expr & arg : args) {
            arg = visit(arg, false);
        }
        return mk_let_decl(mk_app(fn, args), root);
    }

    expr visit_app(expr const & e, bool root) {
        buffer<expr> args;
        expr fn = visit(get_app_args(e, args), false);
        if (is_constant(fn)) {
            if (is_cases_on_recursor(m_env, const_name(fn))) {
                return visit_cases_on(fn, args, root);
            } else if (is_projection(m_env, const_name(fn))) {
                return visit_projection(fn, args, root);
            } else if (const_name(fn) == get_id_rhs_name()) {
                if (args.size() < 2) {
                    return visit(eta_expand(e, 2 - args.size()), root);
                } else {
                    expr new_e = args[1];
                    return visit(mk_app(new_e, args.size() - 2, args.data() + 2), root);
                }
            } else if (is_no_confusion(m_env, const_name(fn))) {
                return visit_no_confusion(fn, args, root);
            } else if (const_name(fn) == get_eq_rec_name() ||
                       const_name(fn) == get_eq_ndrec_name()) {
                return visit_eq_rec(fn, args, root);
            }
        }
        return visit_app_default(fn, args, root);
    }

    expr visit_proj(expr const & e, bool root) {
        expr v = visit(proj_expr(e), false);
        expr r = mk_proj(proj_idx(e), v);
        return mk_let_decl(r, root);
    }

    expr visit_mdata(expr const & e, bool root) {
        if (is_lc_mdata(e)) {
            expr v = visit(mdata_expr(e), false);
            expr r = mk_mdata(mdata_data(e), v);
            return mk_let_decl(r, root);
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
                expr new_fvar = m_lctx.mk_local_decl(m_ngen, binding_name(e), new_d, binding_info(e));
                binding_fvars.push_back(new_fvar);
                e = binding_body(e);
            }
            expr new_body = visit(instantiate_rev(e, binding_fvars.size(), binding_fvars.data()), true);
            new_body      = m_lctx.mk_lambda(m_fvars.size() - m_fvars_init_size, m_fvars.data() + m_fvars_init_size, new_body);
            m_fvars.shrink(m_fvars_init_size);
            r = m_lctx.mk_lambda(binding_fvars, new_body);
        }
        return mk_let_decl(r, root);
    }

    expr visit_let(expr e, bool root) {
        buffer<expr> let_fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), let_fvars.size(), let_fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), let_fvars.size(), let_fvars.data()), false);
            if (is_fvar(new_val)) {
                let_fvars.push_back(new_val);
            } else {
                expr new_fvar = m_lctx.mk_local_decl(m_ngen, let_name(e), new_type, new_val);
                let_fvars.push_back(new_fvar);
                m_fvars.push_back(new_fvar);
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
            type_checker tc(m_env, m_lctx, m_tc_cache);
            expr type = tc.whnf(tc.infer(e));
            if (is_sort(type)) {
                // Types are not pre-processed
                return cache_result(e, e, shared);
            } else if (is_pi(type)) {
                // Functions that return types are not pre-processed
                while (is_pi(type))
                    type = binding_body(type);
                if (is_sort(type))
                    return cache_result(e, e, shared);
            } else if (tc.is_prop(type)) {
                // We replace proofs using `lc_proof` constant
                expr r = mk_app(mk_constant(get_lc_proof_name()), type);
                return cache_result(e, r, shared);
            }
        }

        switch (e.kind()) {
        case expr_kind::App:    return cache_result(e, visit_app(e, root), shared);
        case expr_kind::Proj:   return cache_result(e, visit_proj(e, root), shared);
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
    g_lcnf_fresh = new name("_lcnf_fresh");
    register_name_generator_prefix(*g_lcnf_fresh);
}

void finalize_lcnf() {
    delete g_lcnf_fresh;
}
}
