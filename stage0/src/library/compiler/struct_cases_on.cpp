/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive.h"
#include "kernel/trace.h"
#include "library/suffixes.h"
#include "library/compiler/util.h"

namespace lean {
class struct_cases_on_fn {
    elab_environment    m_env;
    type_checker::state m_st;
    local_ctx           m_lctx;
    name_set            m_scrutinies; /* Set of variables `x` such that there is `casesOn x ...` in the context */
    name_map<name>      m_first_proj; /* Map from variable `x` to the first projection `y := x.i` in the context */
    name_set            m_updated;    /* Set of variables `x` such that there is a `S.mk ... x.i ... */
    name                m_fld{"_d"};
    unsigned            m_next_idx{1};

    elab_environment const & env() { return m_env; }

    name_generator & ngen() { return m_st.ngen(); }

    name next_field_name() {
        name r = m_fld.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr find(expr const & e) const {
        if (is_fvar(e)) {
            if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
                if (optional<expr> v = decl->get_value()) {
                    if (!is_join_point_name(decl->get_user_name()))
                        return find(*v);
                }
            }
        } else if (is_mdata(e)) {
            return find(mdata_expr(e));
        }
        return e;
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
        } else if (is_constructor_app(env(), e)) {
            buffer<expr> args;
            expr const & k = get_app_args(e, args);
            lean_assert(is_constant(k));
            constructor_val k_val = env().get(const_name(k)).to_constructor_val();
            for (unsigned i = k_val.get_nparams(), idx = 0; i < args.size(); i++, idx++) {
                expr arg = find(args[i]);
                if (is_proj(arg) && proj_idx(arg) == idx && is_fvar(proj_expr(arg))) {
                    m_updated.insert(fvar_name(proj_expr(arg)));
                }
            }
            return e;
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

    /* Return `some s` if `rhs` is of the form `s.i`, and `s` is a free variables that has not been
       scrutinized yet, and `s.i` is the first time it is being projected. */
    optional<name> is_candidate(expr const & rhs) {
        if (!is_proj(rhs)) return optional<name>();
        expr const & s = proj_expr(rhs);
        if (!is_fvar(s)) return optional<name>();
        name const & s_name = fvar_name(s);
        if (m_scrutinies.contains(s_name)) return optional<name>();
        if (m_first_proj.contains(s_name)) return optional<name>();
        return optional<name>(s_name);
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

    bool should_add_cases_on(local_decl const & decl) {
        expr val = *decl.get_value();
        if (!is_proj(val)) return false;
        expr const & s = proj_expr(val);
        if (!is_fvar(s) || !m_updated.contains(fvar_name(s))) return false;
        name const * x = m_first_proj.find(fvar_name(s));
        return x && *x == decl.get_name();
    }

    expr visit_let(expr e) {
        flet<name_map<name>> save(m_first_proj, m_first_proj);
        buffer<expr> fvars;
        while (is_let(e)) {
            lean_assert(!has_loose_bvars(let_type(e)));
            expr type     = let_type(e);
            expr val      = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            name n        = let_name(e);
            e             = let_body(e);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), n, type, val);
            fvars.push_back(new_fvar);
            if (optional<name> s = is_candidate(val)) {
                m_first_proj.insert(*s, fvar_name(new_fvar));
            }
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        e = abstract(e, fvars.size(), fvars.data());
        unsigned i = fvars.size();
        while (i > 0) {
            --i;
            expr const & x  = fvars[i];
            lean_assert(is_fvar(x));
            local_decl decl = m_lctx.get_local_decl(x);
            expr type       = decl.get_type();
            expr val        = *decl.get_value();
            expr aval       = abstract(val, i, fvars.data());
            e = mk_let(decl.get_user_name(), type, aval, e);
            if (should_add_cases_on(decl)) {
                lean_assert(is_proj(val));
                expr major = proj_expr(aval);
                buffer<expr> field_types;
                get_struct_field_types(m_st, proj_sname(val), field_types);
                e = lift_loose_bvars(e, field_types.size());
                unsigned i = field_types.size();
                while (i > 0) {
                    --i;
                    e = mk_lambda(next_field_name(), field_types[i], e);
                }
                e = mk_app(mk_constant(name(proj_sname(val), g_cases_on)), major, e);
            }
        }
        return e;
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
    struct_cases_on_fn(elab_environment const & env):
        m_env(env), m_st(env) {
    }

    expr operator()(expr const & e) {
        return visit(e);
    }
};

expr struct_cases_on(elab_environment const & env, expr const & e) {
    return struct_cases_on_fn(env)(e);
}
}
