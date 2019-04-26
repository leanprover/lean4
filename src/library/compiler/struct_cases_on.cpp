/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/trace.h"
#include "library/suffixes.h"
#include "library/compiler/util.h"

namespace lean {
class struct_cases_on_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    name_set            m_scrutinies;
    name                m_fld{"_d"};
    unsigned            m_next_idx{1};

    environment const & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    name next_field_name() {
        name r = m_fld.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr visit_cases(expr const & e) {
        flet<name_set> save(m_scrutinies, m_scrutinies);
        buffer<expr> args;
        expr const & c     = get_app_args(e, args);
        expr const & major = args[0];
        if (is_fvar(major))
            m_scrutinies.insert(fvar_name(major));
        for (unsigned i = 1; i < args.size(); i++) {
            args[i] = visit(args[i]);
        }
        return mk_app(c, args);
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else {
            return e;
        }
    }

    expr visit_lambda(expr e) {
        buffer<expr> fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), binding_domain(e), binding_info(e));
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        e = instantiate_rev(e, fvars.size(), fvars.data());
        e = visit(e);
        return m_lctx.mk_lambda(fvars, e);
    }

    bool is_candidate(expr const & rhs) {
        if (!is_proj(rhs)) return false;
        expr const & s = proj_expr(rhs);
        if (!is_fvar(s)) return false;
        if (m_scrutinies.contains(fvar_name(s))) return false;
        return true;
    }

    /* Return true iff `e` is a constructor application of inductive type `S_name` and containg `x`. */
    bool is_ctor_of(expr const & e, name const & S_name, expr const & x) {
        if (!is_constructor_app(env(), e)) return false;
        buffer<expr> args;
        expr const & k = get_app_args(e, args);
        lean_assert(is_constant(k));
        constructor_val k_val = env().get(const_name(k)).to_constructor_val();
        if (k_val.get_induct() != S_name) return false;
        for (unsigned i = k_val.get_nparams(); i < args.size(); i++) {
            if (args[i] == x)
                return true;
        }
        return false;
    }

    /* Return true iff `e` contains a constructor application of inductive type `S_name` and containg `x`. */
    bool has_ctor_with(expr e, name const & S_name, expr const & x) {
        while (is_lambda(e)) {
            e = binding_body(e);
        }
        while (is_let(e)) {
            if (is_ctor_of(let_value(e), S_name, x))
                return true;
            e = let_body(e);
        }
        if (is_cases_on_app(env(), e)) {
            buffer<expr> args;
            get_app_args(e, args);
            for (unsigned i = 1; i < args.size(); i++) {
                if (has_ctor_with(args[i], S_name, x))
                    return true;
            }
            return false;
        } else {
            return is_ctor_of(e, S_name, x);
        }
    }

    static void get_struct_field_types(type_checker::state & st, name const & S_name, buffer<expr> & result) {
        environment const & env = st.env();
        constant_info info      = env.get(S_name);
        lean_assert(info.is_inductive());
        inductive_val I_val     = info.to_inductive_val();
        lean_assert(length(I_val.get_cnstrs()) == 1);
        constant_info ctor_info = env.get(head(I_val.get_cnstrs()));
        expr type               = ctor_info.get_type();
        unsigned nparams        = I_val.get_nparams();
        local_ctx lctx;
        buffer<expr> telescope;
        to_telescope(env, lctx, st.ngen(), type, telescope);
        lean_assert(telescope.size() >= nparams);
        for (unsigned i = nparams; i < telescope.size(); i++) {
            expr ftype = lctx.get_type(telescope[i]);
            if (is_irrelevant_type(st, lctx, ftype)) {
                result.push_back(mk_enf_neutral_type());
            } else {
                type_checker tc(st, lctx);
                ftype = tc.whnf(ftype);
                if (is_usize_type(ftype)) {
                    result.push_back(ftype);
                } else if (is_builtin_scalar(ftype)) {
                    result.push_back(ftype);
                } else if (optional<unsigned> sz = is_enum_type(env, ftype)) {
                    optional<expr> uint = to_uint_type(*sz);
                    if (!uint) throw exception("code generation failed, enumeration type is too big");
                    result.push_back(*uint);
                } else {
                    result.push_back(mk_enf_object_type());
                }
            }
        }
    }

    expr visit_let(expr e) {
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr type     = let_type(e);
            expr val      = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            name n        = let_name(e);
            e             = let_body(e);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), n, type, val);
            fvars.push_back(new_fvar);
            if (is_candidate(val)) {
                lean_assert(is_proj(val));
                lean_assert(proj_idx(val).is_small());
                name const & S_name = proj_sname(val);
                e = instantiate_rev(e, fvars.size(), fvars.data());
                if (has_ctor_with(e, S_name, new_fvar)) {
                    /* Introduce a casesOn application. */
                    e          = m_lctx.mk_lambda(new_fvar, e);
                    fvars.pop_back();
                    expr major = proj_expr(val);
                    buffer<expr> field_types;
                    get_struct_field_types(m_st, S_name, field_types);
                    unsigned i = field_types.size();
                    while (i > 0) {
                        --i;
                        e = mk_lambda(next_field_name(), field_types[i], e);
                    }
                    e = mk_app(mk_constant(name(S_name, g_cases_on)), major, e);
                }
                e = visit(e);
                return m_lctx.mk_lambda(fvars, e);
            }
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, e);
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
    struct_cases_on_fn(environment const & env):
        m_st(env) {
    }

    expr operator()(expr const & e) {
        return visit(e);
    }
};

expr struct_cases_on(environment const & env, expr const & e) {
    return struct_cases_on_fn(env)(e);
}
}
