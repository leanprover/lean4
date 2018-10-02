/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/compiler/util.h"

namespace lean {
class erase_irrelevant_fn {
    typedef std::tuple<name, expr, expr> let_entry;
    type_checker::state  m_st;
    local_ctx            m_lctx;
    buffer<expr>         m_let_fvars;
    buffer<let_entry>    m_let_entries;
    name_map<list<bool>> m_constructor_info;
    name                 m_x;
    unsigned             m_next_idx{1};

    environment & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    name next_name() {
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr infer_type(expr const & e) {
        try {
            return type_checker(m_st, m_lctx).infer(e);
        } catch (kernel_exception &) {
            return mk_enf_object_type();
        }
    }

    void get_constructor_info(name const & n, buffer<bool> & rel_fields) {
        if (auto r = m_constructor_info.find(n)) {
            to_buffer(*r, rel_fields);
        } else {
            get_constructor_relevant_fields(env(), n, rel_fields);
            m_constructor_info.insert(n, to_list(rel_fields));
        }
    }

    /* Return (some idx) iff inductive datatype `I_name` has only one constructor,
       and this constructor has only one relevant field, `idx` is the field position. */
    optional<unsigned> has_trivial_structure(name const & I_name) {
        if (is_runtime_builtin_type(I_name))
            return optional<unsigned>();
        inductive_val I_val = env().get(I_name).to_inductive_val();
        if (I_val.get_ncnstrs() != 1)
            return optional<unsigned>();
        buffer<bool> rel_fields;
        get_constructor_info(head(I_val.get_cnstrs()), rel_fields);
        /* The following #pragma is to disable a bogus g++ 4.9 warning at `optional<unsigned> r` */
        #if defined(__GNUC__) && !defined(__CLANG__)
        #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
        #endif
        optional<unsigned> result;
        for (unsigned i = 0; i < rel_fields.size(); i++) {
            if (rel_fields[i]) {
                if (result)
                    return optional<unsigned>();
                result = i;
            }
        }
        return result;
    }

    expr mk_runtime_type(expr e, bool atomic_only = false) {
        try {
            type_checker tc(m_st, m_lctx);
            e = tc.whnf(e);
            if (is_constant(e)) {
                name const & c = const_name(e);
                if (is_runtime_scalar_type(c))
                    return e;
                else if (c == get_char_name())
                    return mk_constant(get_uint32_name());
                else
                    return mk_enf_object_type();
            } else if (!atomic_only && is_app_of(e, get_array_name(), 1)) {
                expr t = mk_runtime_type(app_arg(e), true);
                return mk_app(app_fn(e), t);
            } else if (is_sort(e)) {
                return is_zero(sort_level(e)) ? mk_Prop() : mk_Type();
            } else if (tc.is_prop(e)) {
                return mk_true();
            } else {
                return mk_enf_object_type();
            }
        } catch (kernel_exception &) {
            return mk_enf_object_type();
        }
    }

    expr visit_constant(expr const & e) {
        lean_assert(!is_enf_neutral(e));
        name const & c = const_name(e);
        if (c == get_lc_unreachable_name()) {
            return mk_enf_unreachable();
        } else if (c == get_lc_proof_name()) {
            return mk_enf_neutral();
        }
        try {
            type_checker tc(m_st, m_lctx);
            expr e_type = tc.whnf(tc.infer(e));
            if (tc.is_prop(e_type) || is_sort(e_type))
                return mk_enf_neutral();
            else
                return mk_constant(const_name(e));
        } catch (kernel_exception &) {
            return mk_constant(const_name(e));
        }
    }

    bool is_atom(expr const & e) {
        switch (e.kind()) {
        case expr_kind::FVar:   return true;
        case expr_kind::Lit:    return true;
        case expr_kind::Const:  return true;
        default: return false;
        }
    }

    bool is_irrelevant(expr const & e) {
        try {
            type_checker tc(m_st, m_lctx);
            expr type = tc.whnf(tc.infer(e));
            if (is_sort(type) || tc.is_prop(type))
                return true;
            if (is_pi(type)) {
                flet<local_ctx> save_lctx(m_lctx, m_lctx);
                while (is_pi(type)) {
                    expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(type), binding_domain(type));
                    type = type_checker(m_st, m_lctx).whnf(instantiate(binding_body(type), fvar));
                }
                if (is_sort(type))
                    return true;
            }
            return false;
        } catch (kernel_exception &) {
            /* failed to infer type or normalize, assume it is relevant */
            return false;
        }
    }

    expr visit_lambda_core(expr e, bool is_minor) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> bfvars;
        buffer<pair<name, expr>> entries;
        while (is_lambda(e)) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            expr d    = instantiate_rev(binding_domain(e), bfvars.size(), bfvars.data());
            expr fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), d, binding_info(e));
            bfvars.push_back(fvar);
            entries.emplace_back(binding_name(e), mk_runtime_type(d));
            e = binding_body(e);
        }
        unsigned saved_let_fvars_size = m_let_fvars.size();
        lean_assert(m_let_entries.size() == m_let_fvars.size());
        e = instantiate_rev(e, bfvars.size(), bfvars.data());
        if (is_irrelevant(e))
            return mk_enf_neutral();
        expr r = visit(e);
        r      = mk_let(saved_let_fvars_size, r);
        if (is_minor && is_lambda(r)) {
            /* Remark: we don't want to mix the lambda for minor premise fields, with the result. */
            r = ::lean::mk_let("_x", mk_enf_object_type(), r, mk_bvar(0));
        }
        r      = abstract(r, bfvars.size(), bfvars.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            r = mk_lambda(entries[i].first, entries[i].second, r);
        }
        return r;
    }

    expr visit_lambda(expr const & e) {
        return visit_lambda_core(e, false);
    }

    expr visit_minor(expr const & e) {
        return visit_lambda_core(e, true);
    }

    /* Remark: we only keep major and minor premises. */
    expr visit_cases_on(expr const & c, buffer<expr> & args) {
        name const & I_name = const_name(c).get_prefix();
        unsigned minors_begin; unsigned minors_end;
        std::tie(minors_begin, minors_end) = get_cases_on_minors_range(env(), const_name(c));
        if (!is_runtime_builtin_type(I_name) && minors_end == minors_begin + 1) {
            expr major = visit(args[minors_begin - 1]);
            lean_assert(is_atom(major));
            expr minor = args[minors_begin];
            if (optional<unsigned> fidx = has_trivial_structure(const_name(c).get_prefix())) {
                lean_assert(minors_begin + 1 == minors_end);
                unsigned i = 0;
                buffer<expr> fields;
                while (is_lambda(minor)) {
                    if (i == *fidx) {
                        fields.push_back(major);
                    } else {
                        fields.push_back(mk_enf_neutral());
                    }
                    i++;
                    minor = binding_body(minor);
                }
                expr r = instantiate_rev(minor, fields.size(), fields.data());
                return visit(r);
            } else {
                /*
                  ```
                  prod.cases_on M (\fun a b, t)
                  ```
                  ==>
                  ```
                  let a := M.0 in
                  let b := M.1 in
                  t
                */
                unsigned i = 0;
                buffer<expr> fields;
                while (is_lambda(minor)) {
                    expr v = mk_proj(I_name, i, major);
                    expr t = infer_type(v);
                    name n = next_name();
                    expr fvar = m_lctx.mk_local_decl(ngen(), n, t, v);
                    fields.push_back(fvar);
                    expr new_t = mk_runtime_type(t);
                    expr new_v = visit(v);
                    m_let_fvars.push_back(fvar);
                    m_let_entries.emplace_back(n, new_t, new_v);
                    i++;
                    minor = binding_body(minor);
                }
                expr r = instantiate_rev(minor, fields.size(), fields.data());
                return visit(r);
            }
        } else {
            buffer<expr> new_args;
            new_args.push_back(visit(args[minors_begin - 1]));
            for (unsigned i = minors_begin; i < minors_end; i++) {
                new_args.push_back(visit_minor(args[i]));
            }
            return mk_app(c, new_args);
        }
    }

    expr visit_app_default(expr const & fn, buffer<expr> & args) {
        for (expr & arg : args) {
            if (!is_atom(arg)) {
                // In LCNF, relevant arguments are atomic
                arg = mk_enf_neutral();
            } else if (is_constant(arg)) {
                arg = visit_constant(arg);
            }
        }
        return mk_app(fn, args);
    }

    expr visit_quot_lift(buffer<expr> & args) {
        lean_assert(args.size() >= 6);
        expr f = visit(args[3]);
        buffer<expr> new_args;
        for (unsigned i = 5; i < args.size(); i++)
            new_args.push_back(args[i]);
        return visit_app_default(f, new_args);
    }

    expr visit_quot_mk(buffer<expr> const & args) {
        lean_assert(args.size() == 3);
        return visit(args[2]);
    }

    expr visit_constructor(expr const & fn, buffer<expr> & args) {
        constructor_val c_val   = env().get(const_name(fn)).to_constructor_val();
        name const & I_name     = c_val.get_induct();
        if (optional<unsigned> fidx = has_trivial_structure(I_name)) {
            unsigned nparams      = c_val.get_nparams();
            lean_assert(nparams + *fidx < args.size());
            return visit(args[nparams + *fidx]);
        } else {
            return visit_app_default(fn, args);
        }
    }

    expr visit_app(expr const & e) {
        buffer<expr> args;
        expr f = get_app_args(e, args);
        if (is_constant(f)) {
            name const & fn = const_name(f);
            if (fn == get_lc_proof_name()) {
                return mk_enf_neutral();
            } else if (fn == get_lc_unreachable_name()) {
                return mk_enf_unreachable();
            } else if (is_constructor(env(), fn)) {
                return visit_constructor(f, args);
            } else if (is_cases_on_recursor(env(), fn)) {
                return visit_cases_on(f, args);
            } else if (fn == get_quot_mk_name()) {
                return visit_quot_mk(args);
            } else if (fn == get_quot_lift_name()) {
                return visit_quot_lift(args);
            }
        }
        f = visit(f);
        return visit_app_default(f, args);
    }

    expr visit_proj(expr const & e) {
        if (optional<unsigned> fidx = has_trivial_structure(proj_sname(e))) {
            if (*fidx != proj_idx(e).get_small_value())
                return mk_enf_neutral();
            else
                return visit(proj_expr(e));
        } else {
            return e;
        }
    }

    expr mk_let(unsigned saved_fvars_size, expr r) {
        lean_assert(saved_fvars_size <= m_let_fvars.size());
        lean_assert(m_let_fvars.size() == m_let_entries.size());
        if (saved_fvars_size == m_let_fvars.size())
            return r;
        r      = abstract(r, m_let_fvars.size() - saved_fvars_size, m_let_fvars.data() + saved_fvars_size);
        unsigned i = m_let_fvars.size();
        while (i > saved_fvars_size) {
            --i;
            expr v = abstract(std::get<2>(m_let_entries[i]), i - saved_fvars_size, m_let_fvars.data() + saved_fvars_size);
            r      = ::lean::mk_let(std::get<0>(m_let_entries[i]), std::get<1>(m_let_entries[i]), v, r);
        }
        m_let_fvars.shrink(saved_fvars_size);
        m_let_entries.shrink(saved_fvars_size);
        return r;
    }

    expr visit_let(expr e) {
        lean_assert(m_let_entries.size() == m_let_fvars.size());
        buffer<expr> curr_fvars;
        while (is_let(e)) {
            expr t     = instantiate_rev(let_type(e), curr_fvars.size(), curr_fvars.data());
            expr v     = instantiate_rev(let_value(e), curr_fvars.size(), curr_fvars.data());
            name n     = let_name(e);
            if (is_internal_name(n) && !is_join_point_name(n)) {
                n = next_name();
            }
            expr fvar  = m_lctx.mk_local_decl(ngen(), n, t, v);
            curr_fvars.push_back(fvar);
            expr new_t = mk_runtime_type(t);
            expr new_v = visit(v);
            m_let_fvars.push_back(fvar);
            m_let_entries.emplace_back(n, new_t, new_v);
            e = let_body(e);
        }
        lean_assert(m_let_entries.size() == m_let_fvars.size());
        return visit(instantiate_rev(e, curr_fvars.size(), curr_fvars.data()));
    }

    expr visit(expr const & e) {
        lean_assert(m_let_entries.size() == m_let_fvars.size());
        switch (e.kind()) {
        case expr_kind::BVar:  case expr_kind::MVar:
            lean_unreachable();
        case expr_kind::FVar:   return e;
        case expr_kind::Sort:   return mk_enf_neutral();
        case expr_kind::Lit:    return e;
        case expr_kind::Pi:     return mk_enf_neutral();
        case expr_kind::Const:  return visit_constant(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Proj:   return visit_proj(e);
        case expr_kind::MData:  return e;
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        }
        lean_unreachable();
    }
public:
    erase_irrelevant_fn(environment const & env, local_ctx const & lctx):
        m_st(env), m_lctx(lctx), m_x("_x") {}
    expr operator()(expr const & e) {
        return mk_let(0, visit(e));
    }
};

expr erase_irrelevant(environment const & env, local_ctx const & lctx, expr const & e) {
    return erase_irrelevant_fn(env, lctx)(e);
}
}
