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
#include "kernel/inductive.h"
#include "library/compiler/util.h"
#include "library/compiler/implemented_by_attribute.h"

namespace lean {
class erase_irrelevant_fn {
    typedef std::tuple<name, expr, expr> let_entry;
    elab_environment     m_env;
    type_checker::state  m_st;
    local_ctx            m_lctx;
    buffer<expr>         m_let_fvars;
    buffer<let_entry>    m_let_entries;
    name                 m_x;
    unsigned             m_next_idx{1};
    expr_map<bool>       m_irrelevant_cache;

    elab_environment & env() { return m_env; }

    name_generator & ngen() { return m_st.ngen(); }

    name next_name() {
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr infer_type(expr const & e) {
        return type_checker(m_st, m_lctx).infer(e);
    }

    optional<unsigned> has_trivial_structure(name const & I_name) {
        return ::lean::has_trivial_structure(env(), I_name);
    }

    expr mk_runtime_type(expr e) {
        return ::lean::mk_runtime_type(m_st, m_lctx, e);
    }

    bool cache_is_irrelevant(expr const & e, bool r) {
        if (is_constant(e) || is_fvar(e))
            m_irrelevant_cache.insert(mk_pair(e, r));
        return r;
    }

    bool is_irrelevant(expr const & e) {
        if (is_constant(e) || is_fvar(e)) {
            auto it1 = m_irrelevant_cache.find(e);
            if (it1 != m_irrelevant_cache.end())
                return it1->second;
        }
        try {
            type_checker tc(m_st, m_lctx);
            expr type = tc.whnf(tc.infer(e));
            bool r    = is_irrelevant_type(m_st, m_lctx, type);
            return cache_is_irrelevant(e, r);
        } catch (kernel_exception &) {
            /* failed to infer type or normalize, assume it is relevant */
            return cache_is_irrelevant(e, false);
        }
    }

    expr visit_constant(expr const & e) {
        lean_always_assert(!is_enf_neutral(e));
        name const & c = const_name(e);
        if (c == get_lc_unreachable_name()) {
            return mk_enf_unreachable();
        } else if (c == get_lc_proof_name()) {
            return mk_enf_neutral();
        } else if (is_irrelevant(e)) {
            return mk_enf_neutral();
        } else if (optional<name> n = get_implemented_by_attribute(env(), c)) {
            if (has_inline_attribute(env(), *n)) {
                // csimp ignores @[inline] after erasure, so inline it now
                if (optional<expr> e3 = unfold_term(env(), mk_const(mk_cstage1_name(*n), const_levels(e))))
                    return visit(*e3);
            }
            return visit(mk_const(*n, const_levels(e)));
        } else {
            return mk_constant(const_name(e));
        }
    }

    expr visit_fvar(expr const & e) {
        if (is_irrelevant(e)) {
            return mk_enf_neutral();
        } else {
            return e;
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
        lean_always_assert(m_let_entries.size() == m_let_fvars.size());
        e = instantiate_rev(e, bfvars.size(), bfvars.data());
        if (is_irrelevant(e) && !is_minor)
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

    expr mk_simple_decl(expr const & e, expr const & e_type) {
        name n         = next_name();
        expr x         = m_lctx.mk_local_decl(ngen(), n, e_type, e);
        m_let_fvars.push_back(x);
        m_let_entries.emplace_back(n, mk_runtime_type(e_type), e);
        return x;
    }

    static expr mk_list_char() {
        return mk_app(mk_constant(get_list_name(), {mk_level_zero()}), mk_constant(get_char_name()));
    }

    expr elim_string_cases(buffer<expr> & args) {
        lean_always_assert(args.size() == 3);
        expr major     = visit(args[1]);
        expr x         = mk_simple_decl(mk_app(mk_constant(get_string_data_name()), major), mk_list_char());
        expr minor     = args[2];
        minor = instantiate(binding_body(minor), x);
        return visit(minor);
    }

    expr elim_nat_cases(buffer<expr> & args) {
        lean_always_assert(args.size() == 4);
        expr major       = visit(args[1]);
        expr zero        = mk_lit(literal(nat(0)));
        expr one         = mk_lit(literal(nat(1)));
        expr nat_type    = mk_constant(get_nat_name());
        expr dec_eq      = mk_app(mk_constant(get_nat_dec_eq_name()), major, zero);
        expr dec_eq_type = mk_bool();
        expr c           = mk_simple_decl(dec_eq, dec_eq_type);
        expr minor_z     = args[2];
        minor_z          = visit_minor(minor_z);
        expr minor_s     = args[3];
        expr pred        = mk_app(mk_constant(get_nat_sub_name()), major, one);
        minor_s          = ::lean::mk_let(next_name(), nat_type, pred, binding_body(minor_s));
        minor_s          = visit_minor(minor_s);
        return mk_app(mk_constant(get_bool_cases_on_name()), c, minor_s, minor_z);
    }

    expr elim_int_cases(buffer<expr> & args) {
        lean_always_assert(args.size() == 4);
        expr major       = visit(args[1]);
        expr zero        = mk_lit(literal(nat(0)));
        expr int_type    = mk_constant(get_int_name());
        expr nat_type    = mk_constant(get_nat_name());
        expr izero       = mk_simple_decl(mk_app(mk_constant(get_int_of_nat_name()), zero), int_type);
        expr dec_lt      = mk_app(mk_constant(get_int_dec_lt_name()), major, izero);
        expr dec_lt_type = mk_bool();
        expr c           = mk_simple_decl(dec_lt, dec_lt_type);
        expr abs         = mk_app(mk_constant(get_int_nat_abs_name()), major);
        expr minor_p     = args[2];
        minor_p          = ::lean::mk_let(next_name(), nat_type, abs, binding_body(minor_p));
        minor_p          = visit_minor(minor_p);
        expr one         = mk_lit(literal(nat(1)));
        expr minor_n     = args[3];
        minor_n          = ::lean::mk_let(next_name(), nat_type, abs,
                           ::lean::mk_let(next_name(), nat_type, mk_app(mk_constant(get_nat_sub_name()), mk_bvar(0), one),
                                          binding_body(minor_n)));
        minor_n          = visit_minor(minor_n);
        return mk_app(mk_constant(get_bool_cases_on_name()), c, minor_p, minor_n);
    }

    expr elim_array_cases(buffer<expr> & args) {
        lean_always_assert(args.size() == 4);
        expr major       = visit(args[2]);
        expr minor       = visit_minor(args[3]);
        lean_always_assert(is_lambda(minor));
        return
            ::lean::mk_let(next_name(), mk_enf_object_type(), mk_app(mk_constant(get_array_to_list_name()), mk_enf_neutral(), major),
                           binding_body(minor));
    }

    expr elim_float_array_cases(buffer<expr> & args) {
        lean_always_assert(args.size() == 3);
        expr major       = visit(args[1]);
        expr minor       = visit_minor(args[2]);
        lean_always_assert(is_lambda(minor));
        return
            ::lean::mk_let(next_name(), mk_enf_object_type(), mk_app(mk_constant(get_float_array_data_name()), major),
                           binding_body(minor));
    }

    expr elim_byte_array_cases(buffer<expr> & args) {
        lean_always_assert(args.size() == 3);
        expr major       = visit(args[1]);
        expr minor       = visit_minor(args[2]);
        lean_always_assert(is_lambda(minor));
        return
            ::lean::mk_let(next_name(), mk_enf_object_type(), mk_app(mk_constant(get_byte_array_data_name()), major),
                           binding_body(minor));
    }

    expr elim_uint_cases(name const & uint_name, buffer<expr> & args) {
        lean_always_assert(args.size() == 3);
        expr major = visit(args[1]);
        expr minor = visit_minor(args[2]);
        lean_always_assert(is_lambda(minor));
        return
          ::lean::mk_let(next_name(), mk_enf_object_type(), mk_app(mk_const(name(uint_name, "toNat")), major),
                         binding_body(minor));
    }

    expr decidable_to_bool_cases(buffer<expr> const & args) {
        lean_always_assert(args.size() == 5);
        expr const & major  = args[2];
        expr minor1 = args[3];
        expr minor2 = args[4];
        minor1 = visit_minor(minor1);
        minor2 = visit_minor(minor2);
        lean_always_assert(is_lambda(minor1));
        lean_always_assert(is_lambda(minor2));
        minor1 = instantiate(binding_body(minor1), mk_enf_neutral());
        minor2 = instantiate(binding_body(minor2), mk_enf_neutral());
        return mk_app(mk_constant(get_bool_cases_on_name()), major, minor1, minor2);
    }

    /* Remark: we only keep major and minor premises. */
    expr visit_cases_on(expr const & c, buffer<expr> & args) {
        name const & I_name = const_name(c).get_prefix();
        if (I_name == get_string_name()) {
            return elim_string_cases(args);
        } else if (I_name == get_nat_name()) {
            return elim_nat_cases(args);
        } else if (I_name == get_int_name()) {
            return elim_int_cases(args);
        } else if (I_name == get_array_name()) {
            return elim_array_cases(args);
        } else if (I_name == get_float_array_name()) {
            return elim_float_array_cases(args);
        } else if (I_name == get_byte_array_name()) {
            return elim_byte_array_cases(args);
        } else if (I_name == get_uint8_name() || I_name == get_uint16_name() || I_name == get_uint32_name() || I_name == get_uint64_name() || I_name == get_usize_name()) {
          return elim_uint_cases(I_name, args);
        } else if (I_name == get_decidable_name()) {
            return decidable_to_bool_cases(args);
        } else {
            unsigned minors_begin; unsigned minors_end;
            std::tie(minors_begin, minors_end) = get_cases_on_minors_range(env(), const_name(c));
            if (optional<unsigned> fidx = has_trivial_structure(const_name(c).get_prefix())) {
                /* Eliminate `cases_on` of trivial structure */
                lean_always_assert(minors_end == minors_begin + 1);
                expr major = args[minors_begin - 1];
                lean_always_assert(is_atom(major));
                expr minor = args[minors_begin];
                unsigned i = 0;
                buffer<expr> fields;
                while (is_lambda(minor)) {
                    expr v = mk_proj(I_name, i, major);
                    expr t = instantiate_rev(binding_domain(minor), fields.size(), fields.data());
                    name n = next_name();
                    expr fvar = m_lctx.mk_local_decl(ngen(), n, t, v);
                    fields.push_back(fvar);
                    expr new_t; expr new_v;
                    if (*fidx == i) {
                        expr major_type = infer_type(major);
                        new_t = mk_runtime_type(major_type);
                        new_v = visit(major);
                    } else {
                        new_t = mk_enf_object_type();
                        new_v = mk_enf_neutral();
                    }
                    m_let_fvars.push_back(fvar);
                    m_let_entries.emplace_back(n, new_t, new_v);
                    i++;
                    minor = binding_body(minor);
                }
                expr r = instantiate_rev(minor, fields.size(), fields.data());
                return visit(r);
            } else {
                buffer<expr> new_args;
                new_args.push_back(visit(args[minors_begin - 1]));
                for (unsigned i = minors_begin; i < minors_end; i++) {
                    new_args.push_back(visit_minor(args[i]));
                }
                return mk_app(c, new_args);
            }
        }
    }

    expr visit_app_default(expr fn, buffer<expr> & args) {
        fn = visit(fn);
        for (expr & arg : args) {
            if (!is_atom(arg)) {
                // In LCNF, relevant arguments are atomic
                arg = mk_enf_neutral();
            } else {
                arg = visit(arg);
            }
        }
        return mk_app(fn, args);
    }

    expr visit_quot_lift(buffer<expr> & args) {
        lean_always_assert(args.size() >= 6);
        expr f = args[3];
        buffer<expr> new_args;
        for (unsigned i = 5; i < args.size(); i++)
            new_args.push_back(args[i]);
        return visit_app_default(f, new_args);
    }

    expr visit_quot_mk(buffer<expr> const & args) {
        lean_always_assert(args.size() == 3);
        return visit(args[2]);
    }

    expr visit_constructor(expr const & fn, buffer<expr> & args) {
        constructor_val c_val   = env().get(const_name(fn)).to_constructor_val();
        name const & I_name     = c_val.get_induct();
        if (optional<unsigned> fidx = has_trivial_structure(I_name)) {
            unsigned nparams      = c_val.get_nparams();
            lean_always_assert(nparams + *fidx < args.size());
            return visit(args[nparams + *fidx]);
        } else {
            return visit_app_default(fn, args);
        }
    }

    expr visit_app(expr const & e) {
        buffer<expr> args;
        expr f = get_app_args(e, args);
        while (is_constant(f)) {
            name const & fn = const_name(f);
            if (fn == get_lc_proof_name()) {
                return mk_enf_neutral();
            } else if (fn == get_lc_unreachable_name()) {
                return mk_enf_unreachable();
            } else if (optional<name> n = get_implemented_by_attribute(env(), fn)) {
                if (is_cases_on_recursor(env(), fn) || has_inline_attribute(env(), *n)) {
                    // casesOn has a different representation in the LCNF than applications,
                    // so we can't just replace the constant by the implemented_by override.
                    // Additionally, csimp ignores inline annotation after erase so inline now.
                    expr e2 = mk_app(mk_const(mk_cstage1_name(*n), const_levels(f)), to_list(args));
                    if (optional<expr> e3 = unfold_app(env(), e2)) {
                        return visit(*e3);
                    } else {
                        throw exception(sstream() << "code generation failed, unsupported implemented_by for '" << fn << "'");
                    }
                } else {
                    f = mk_const(*n, const_levels(f));
                }
            } else if (fn == get_decidable_is_true_name()) {
                return mk_constant(get_bool_true_name());
            } else if (fn == get_decidable_is_false_name()) {
                return mk_constant(get_bool_false_name());
            } else if (is_constructor(env(), fn)) {
                return visit_constructor(f, args);
            } else if (is_cases_on_recursor(env(), fn)) {
                return visit_cases_on(f, args);
            } else if (fn == get_quot_mk_name()) {
                return visit_quot_mk(args);
            } else if (fn == get_quot_lift_name()) {
                return visit_quot_lift(args);
            } else if (fn == get_decidable_decide_name() && args.size() == 2) {
                /* Decidable.decide is the "identify" function since Decidable and Bool have
                   the same runtime representation. */
                return args[1];
            } else {
                break;
            }
        }
        return visit_app_default(f, args);
    }

    expr visit_proj(expr const & e) {
        if (optional<unsigned> fidx = has_trivial_structure(proj_sname(e))) {
            if (*fidx != proj_idx(e).get_small_value())
                return mk_enf_neutral();
            else
                return visit(proj_expr(e));
        } else {
            return update_proj(e, visit(proj_expr(e)));
        }
    }

    expr mk_let(unsigned saved_fvars_size, expr r) {
        lean_always_assert(saved_fvars_size <= m_let_fvars.size());
        lean_always_assert(m_let_fvars.size() == m_let_entries.size());
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
        lean_always_assert(m_let_entries.size() == m_let_fvars.size());
        buffer<expr> curr_fvars;
        while (is_let(e)) {
            expr t     = instantiate_rev(let_type(e), curr_fvars.size(), curr_fvars.data());
            expr v     = instantiate_rev(let_value(e), curr_fvars.size(), curr_fvars.data());
            name n     = let_name(e);
            /* Pseudo "do" joinpoints are used to implement a temporary HACK. See `visit_let` method at `lcnf.cpp` */
            if (is_internal_name(n) && !is_join_point_name(n) && !is_pseudo_do_join_point_name(n)) {
                n = next_name();
            }
            expr fvar  = m_lctx.mk_local_decl(ngen(), n, t, v);
            curr_fvars.push_back(fvar);
            expr new_t = mk_runtime_type(t);
            expr new_v = is_enf_neutral(new_t) ? mk_enf_neutral() : visit(v);
            m_let_fvars.push_back(fvar);
            m_let_entries.emplace_back(n, new_t, new_v);
            e = let_body(e);
        }
        lean_always_assert(m_let_entries.size() == m_let_fvars.size());
        return visit(instantiate_rev(e, curr_fvars.size(), curr_fvars.data()));
    }

    expr visit_mdata(expr const & e) {
        return update_mdata(e, visit(mdata_expr(e)));
    }

    expr visit(expr const & e) {
        lean_always_assert(m_let_entries.size() == m_let_fvars.size());
        switch (e.kind()) {
        case expr_kind::BVar:  case expr_kind::MVar:
            lean_unreachable();
        case expr_kind::FVar:   return visit_fvar(e);
        case expr_kind::Sort:   return mk_enf_neutral();
        case expr_kind::Lit:    return e;
        case expr_kind::Pi:     return mk_enf_neutral();
        case expr_kind::Const:  return visit_constant(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Proj:   return visit_proj(e);
        case expr_kind::MData:  return visit_mdata(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        }
        lean_unreachable();
    }
public:
    erase_irrelevant_fn(elab_environment const & env, local_ctx const & lctx):
        m_env(env), m_st(env), m_lctx(lctx), m_x("_x") {}
    expr operator()(expr const & e) {
        return mk_let(0, visit(e));
    }
};

expr erase_irrelevant_core(elab_environment const & env, local_ctx const & lctx, expr const & e) {
    return erase_irrelevant_fn(env, lctx)(e);
}
}
