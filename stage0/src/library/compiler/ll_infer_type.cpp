/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/inductive.h"
#include "library/compiler/util.h"
#include "library/compiler/extern_attribute.h"

namespace lean {
static expr * g_bot = nullptr;

/* Infer type of expressions in ENF or LLNF. */
class ll_infer_type_fn {
    elab_environment     m_env;
    type_checker::state  m_st;
    local_ctx            m_lctx;
    buffer<name> const * m_new_decl_names{nullptr};
    buffer<expr> const * m_new_decl_types{nullptr};

    elab_environment const & env() const { return m_env; }
    name_generator & ngen() { return m_st.ngen(); }

    bool may_use_bot() const { return m_new_decl_types != nullptr; }

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
                type = infer(val);
            } else {
                type = let_type(e);
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
        if (args.size() == 1) {
            // This can happen for empty types. That is, the only argument is the major premise.
            return mk_enf_object_type();
        }
        lean_assert(args.size() >= 2);
        bool first = true;
        expr r     = *g_bot;
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
            } else if (minor_type == *g_bot) {
                /* Ignore*/
            } else if (first) {
                r     = minor_type;
                first = false;
            } else if (minor_type != r) {
                /* All branches should return the same type, otherwise we box them. */
                return mk_enf_object_type();
            }
        }
        lean_assert(may_use_bot() || r != *g_bot);
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
        } else if (is_app_of(e, get_panic_name())) {
            /*
               We should treat `panic` as `unreachable`.
               Otherwise, we will not infer the correct type IRType for
               ```
               def f (n : UInt32) : UInt32 :=
               if n == 0 then panic! "foo"
               else n+1
               ```
               Reason: `panic! "foo"` is expanded into
               ```
               let _x_1 : String := mkPanicMessage "<file-name>" 2 15 "foo" in @panic.{0} UInt32 UInt32.Inhabited _x_1
               ```
               and `panic` can't be specialize because it is a primitive implemented in C++, and if we don't
               do anything it will assume `panic` returns an `_obj`.
             */
            return may_use_bot() ? *g_bot : mk_enf_object_type();
        } else {
            expr const & fn = get_app_fn(e);
            expr fn_type    = infer(fn);
            lean_assert(may_use_bot() || fn_type != *g_bot);
            if (fn_type == *g_bot)
                return *g_bot;
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
        if (optional<expr> type = get_extern_constant_ll_type(env(), const_name(e))) {
            return *type;
        } else if (is_constructor(env(), const_name(e))) {
            return infer_constructor_type(e);
        } else if (is_enf_neutral(e)) {
            return mk_enf_neutral_type();
        } else if (is_enf_unreachable(e)) {
            return may_use_bot() ? *g_bot : mk_enf_object_type();
        } else {
            name c = mk_cstage2_name(const_name(e));
            optional<constant_info> info = env().find(c);
            if (info) return info->get_type();
            if (m_new_decl_types) {
                lean_assert(m_new_decl_names->size() == m_new_decl_types->size());
                for (unsigned i = 0; i < m_new_decl_names->size(); i++) {
                    if (const_name(e) == (*m_new_decl_names)[i])
                        return (*m_new_decl_types)[i];
                }
                return *g_bot;
            }
            throw exception(sstream() << "failed to compile definition, consider marking it as 'noncomputable' because it depends on '" << const_name(e) << "', and it does not have executable code");
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
    ll_infer_type_fn(elab_environment const & env, buffer<name> const & ns, buffer<expr> const & ts):
        m_env(env), m_st(env), m_new_decl_names(&ns), m_new_decl_types(&ts) {}
    ll_infer_type_fn(elab_environment const & env, local_ctx const & lctx):
        m_env(env), m_st(env), m_lctx(lctx) {}
    expr operator()(expr const & e) { return infer(e); }
};

void ll_infer_type(elab_environment const & env, comp_decls const & ds, buffer<expr> & ts) {
    buffer<name> ns;
    ts.clear();
    /* Initialize `ts` */
    for (comp_decl const & d : ds) {
        /* For mutually recursive declarations `t` may contain `_bot`. */
        expr t = ll_infer_type_fn(env, ns, ts)(d.snd());
        ns.push_back(d.fst());
        ts.push_back(t);
    }
    /* Keep refining types in `ts` until fix point */
    while (true) {
        bool modified = false;
        unsigned i = 0;
        for (comp_decl const & d : ds) {
            expr t1 = ll_infer_type_fn(env, ns, ts)(d.snd());
            if (t1 != ts[i]) {
                modified = true;
                ts[i]    = t1;
            }
            i++;
        }
        if (!modified)
            break;
    }
    /* `ts` may still contain `_bot` for non-terminating or bogus programs.
       Example: `def f (x) := f (f x)`.

       It is safe to replace `_bot` with `_obj`. */
    for (expr & t : ts) {
        t = replace(t, [&](expr const & e, unsigned) {
                if (e == *g_bot) return some_expr(mk_enf_object_type());
                else return none_expr();
            });
    }
    lean_assert(ts.size() == length(ds));
}

expr ll_infer_type(elab_environment const & env, local_ctx const & lctx, expr const & e) {
    return ll_infer_type_fn(env, lctx)(e);
}

void initialize_ll_infer_type() {
    g_bot = new expr(mk_constant("_bot"));
    mark_persistent(g_bot->raw());
}

void finalize_ll_infer_type() {
    delete g_bot;
}
}
