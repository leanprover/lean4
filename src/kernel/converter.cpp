/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/lbool.h"
#include "kernel/converter.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/type_checker.h"

namespace lean {
/**
   \brief Predicate for deciding whether \c d is an opaque definition or not.

   Here is the basic idea:

   1) Each definition has an opaque flag. This flag cannot be modified after a definition is added to the environment.
   The opaque flag affects the convertability check. The idea is to minimize the number of delta-reduction steps.
   We also believe it increases the modularity of Lean developments by minimizing the dependency on how things are defined.
   We should view non-opaque definitions as "inline definitions" used in programming languages such as C++.

   2) Whenever type checking an expression, the user can provide an additional set of definition names (m_extra_opaque) that
   should be considered opaque. Note that, if \c t type checks when using an extra_opaque set S, then t also type checks
   (modulo resource constraints) with the empty set. Again, the purpose of extra_opaque is to mimimize the number
   of delta-reduction steps.

   3) To be able to prove theorems about an opaque definition, we treat an opaque definition D in a module M as
   transparent when we are type checking another definition/theorem D' also in M. This rule only applies if
   D is not a theorem, nor D is in the set m_extra_opaque. To implement this feature, this class has a field
   m_module_idx that is not none when this rule should be applied.
*/
bool is_opaque(declaration const & d, name_set const & extra_opaque, optional<module_idx> const & mod_idx) {
    lean_assert(d.is_definition());
    if (d.is_theorem()) return true;                               // theorems are always opaque
    if (extra_opaque.contains(d.get_name())) return true;          // extra_opaque set overrides opaque flag
    if (!d.is_opaque()) return false;                              // d is a transparent definition
    if (mod_idx && d.get_module_idx() == *mod_idx) return false;   // the opaque definitions in mod_idx are considered transparent
    return true;                                                   // d is opaque
}

/** \brief Auxiliary method for \c is_delta */
static optional<declaration> is_delta_core(environment const & env, expr const & e, name_set const & extra_opaque,
                                           optional<module_idx> const & mod_idx) {
    if (is_constant(e)) {
        if (auto d = env.find(const_name(e)))
            if (d->is_definition() && !is_opaque(*d, extra_opaque, mod_idx))
                return d;
    }
    return none_declaration();
}

/**
   \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
   to be expanded.
*/
optional<declaration> is_delta(environment const & env, expr const & e, name_set const & extra_opaque, optional<module_idx> const & mod_idx) {
    return is_delta_core(env, get_app_fn(e), extra_opaque, mod_idx);
}

static optional<module_idx> g_opt_main_module_idx(g_main_module_idx);
optional<declaration> is_delta(environment const & env, expr const & e, name_set const & extra_opaque) {
    return is_delta(env, e, extra_opaque, g_opt_main_module_idx);
}

static no_delayed_justification g_no_delayed_jst;
pair<bool, constraint_seq> converter::is_def_eq(expr const & t, expr const & s, type_checker & c) {
    return is_def_eq(t, s, c, g_no_delayed_jst);
}

/** \brief Do nothing converter */
struct dummy_converter : public converter {
    virtual pair<expr, constraint_seq> whnf(expr const & e, type_checker &) {
        return mk_pair(e, constraint_seq());
    }
    virtual pair<bool, constraint_seq> is_def_eq(expr const &, expr const &, type_checker &, delayed_justification &) {
        return mk_pair(true, constraint_seq());
    }
    virtual optional<module_idx> get_module_idx() const { return optional<module_idx>(); }
};

std::unique_ptr<converter> mk_dummy_converter() {
    return std::unique_ptr<converter>(new dummy_converter());
}

name converter::mk_fresh_name(type_checker & tc) { return tc.mk_fresh_name(); }
pair<expr, constraint_seq> converter::infer_type(type_checker & tc, expr const & e) { return tc.infer_type(e); }
extension_context & converter::get_extension(type_checker & tc) { return tc.get_extension(); }
static expr g_dont_care(Const("dontcare"));

struct default_converter : public converter {
    environment                                 m_env;
    optional<module_idx>                        m_module_idx;
    bool                                        m_memoize;
    name_set                                    m_extra_opaque;
    expr_struct_map<expr>                       m_whnf_core_cache;
    expr_struct_map<pair<expr, constraint_seq>> m_whnf_cache;

    default_converter(environment const & env, optional<module_idx> mod_idx, bool memoize, name_set const & extra_opaque):
        m_env(env), m_module_idx(mod_idx), m_memoize(memoize), m_extra_opaque(extra_opaque) {
    }

    constraint mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j) {
        return ::lean::mk_eq_cnstr(lhs, rhs, j, static_cast<bool>(m_module_idx));
    }

    optional<expr> expand_macro(expr const & m, type_checker & c) {
        lean_assert(is_macro(m));
        return macro_def(m).expand(m, get_extension(c));
    }

    /** \brief Apply normalizer extensions to \c e. */
    optional<pair<expr, constraint_seq>> norm_ext(expr const & e, type_checker & c) {
        return m_env.norm_ext()(e, get_extension(c));
    }

    optional<expr> d_norm_ext(expr const & e, type_checker & c, constraint_seq & cs) {
        if (auto r = norm_ext(e, c)) {
            cs = cs + r->second;
            return some_expr(r->first);
        } else {
            return none_expr();
        }
    }

    /** \brief Return true if \c e may be reduced later after metavariables are instantiated. */
    bool may_reduce_later(expr const & e, type_checker & c) {
        return m_env.norm_ext().may_reduce_later(e, get_extension(c));
    }

    /** \brief Try to apply eta-reduction to \c e. */
    expr try_eta(expr const & e) {
        lean_assert(is_lambda(e));
        expr const & b = binding_body(e);
        if (is_lambda(b)) {
            expr new_b = try_eta(b);
            if (is_eqp(b, new_b)) {
                return e;
            } else if (is_app(new_b) && is_var(app_arg(new_b), 0) && !has_free_var(app_fn(new_b), 0)) {
                return lower_free_vars(app_fn(new_b), 1);
            } else {
                return update_binding(e, binding_domain(e), new_b);
            }
        } else if (is_app(b) && is_var(app_arg(b), 0) && !has_free_var(app_fn(b), 0)) {
            return lower_free_vars(app_fn(b), 1);
        } else {
            return e;
        }
    }

    /** \brief Weak head normal form core procedure. It does not perform delta reduction nor normalization extensions. */
    expr whnf_core(expr const & e, type_checker & c) {
        check_system("whnf");

        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Var:  case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
        case expr_kind::Pi:   case expr_kind::Constant:
            return e;
        case expr_kind::Lambda: case expr_kind::Macro: case expr_kind::App:
            break;
        }

        // check cache
        if (m_memoize) {
            auto it = m_whnf_core_cache.find(e);
            if (it != m_whnf_core_cache.end())
                return it->second;
        }

        // do the actual work
        expr r;
        switch (e.kind()) {
        case expr_kind::Var:    case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
        case expr_kind::Pi:   case expr_kind::Constant:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Lambda:
            r = (m_env.eta()) ? try_eta(e) : e;
            break;
        case expr_kind::Macro:
            if (auto m = expand_macro(e, c))
                r = whnf_core(*m, c);
            else
                r = e;
            break;
        case expr_kind::App: {
            buffer<expr> args;
            expr f0 = get_app_rev_args(e, args);
            expr f = whnf_core(f0, c);
            if (is_lambda(f)) {
                unsigned m = 1;
                unsigned num_args = args.size();
                while (is_lambda(binding_body(f)) && m < num_args) {
                    f = binding_body(f);
                    m++;
                }
                lean_assert(m <= num_args);
                r = whnf_core(mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)), num_args - m, args.data()), c);
            } else {
                r = is_eqp(f, f0) ? e : mk_rev_app(f, args.size(), args.data());
            }
            break;
        }}

        if (m_memoize)
            m_whnf_core_cache.insert(mk_pair(e, r));
        return r;
    }

    bool is_opaque(declaration const & d) const {
        return ::lean::is_opaque(d, m_extra_opaque, m_module_idx);
    }

    /** \brief Expand \c e if it is non-opaque constant with weight >= w */
    expr unfold_name_core(expr e, unsigned w) {
        if (is_constant(e)) {
            if (auto d = m_env.find(const_name(e))) {
                if (d->is_definition() && !is_opaque(*d) && d->get_weight() >= w)
                    return unfold_name_core(instantiate_value_univ_params(*d, const_levels(e)), w);
            }
        }
        return e;
    }

    /**
       \brief Expand constants and application where the function is a constant.

       The unfolding is only performend if the constant corresponds to
       a non-opaque definition with weight >= w.
    */
    expr unfold_names(expr const & e, unsigned w) {
        if (is_app(e)) {
            expr f0 = get_app_fn(e);
            expr f  = unfold_name_core(f0, w);
            if (is_eqp(f, f0)) {
                return e;
            } else {
                buffer<expr> args;
                get_app_rev_args(e, args);
                return mk_rev_app(f, args);
            }
        } else {
            return unfold_name_core(e, w);
        }
    }

    /**
        \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
        to be expanded.
    */
    optional<declaration> is_delta(expr const & e) {
        return ::lean::is_delta(m_env, get_app_fn(e), m_extra_opaque, m_module_idx);
    }

    /**
        \brief Weak head normal form core procedure that perform delta reduction for non-opaque constants with
        weight greater than or equal to \c w.

        This method is based on <tt>whnf_core(expr const &)</tt> and \c unfold_names.

        \remark This method does not use normalization extensions attached in the environment.
    */
    expr whnf_core(expr e, unsigned w, type_checker & c) {
        while (true) {
            expr new_e = unfold_names(whnf_core(e, c), w);
            if (is_eqp(e, new_e))
                return e;
            e = new_e;
        }
    }

    /** \brief Put expression \c t in weak head normal form */
    virtual pair<expr, constraint_seq> whnf(expr const & e_prime, type_checker & c) {
        // Do not cache easy cases
        switch (e_prime.kind()) {
        case expr_kind::Var: case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local: case expr_kind::Pi:
            return to_ecs(e_prime);
        case expr_kind::Lambda: case expr_kind::Macro: case expr_kind::App: case expr_kind::Constant:
            break;
        }

        expr e = e_prime;
        // check cache
        if (m_memoize) {
            auto it = m_whnf_cache.find(e);
            if (it != m_whnf_cache.end())
                return it->second;
        }

        expr t = e;
        constraint_seq cs;
        while (true) {
            expr t1 = whnf_core(t, 0, c);
            if (auto new_t = d_norm_ext(t1, c, cs)) {
                t  = *new_t;
            } else {
                auto r = mk_pair(t1, cs);
                if (m_memoize)
                    m_whnf_cache.insert(mk_pair(e, r));
                return r;
            }
        }
    }

    expr whnf(expr const & e_prime, type_checker & c, constraint_seq & cs) {
        auto r = whnf(e_prime, c);
        cs = cs + r.second;
        return r.first;
    }

    pair<bool, constraint_seq> to_bcs(bool b) { return mk_pair(b, constraint_seq()); }
    pair<bool, constraint_seq> to_bcs(bool b, constraint const & c) { return mk_pair(b, constraint_seq(c)); }
    pair<bool, constraint_seq> to_bcs(bool b, constraint_seq const & cs) { return mk_pair(b, cs); }

    /**
        \brief Given lambda/Pi expressions \c t and \c s, return true iff \c t is def eq to \c s.

        t and s are definitionally equal
           iff
        domain(t) is definitionally equal to domain(s)
        and
        body(t) is definitionally equal to body(s)
    */
    bool is_def_eq_binding(expr t, expr s, type_checker & c, delayed_justification & jst, constraint_seq & cs) {
        lean_assert(t.kind() == s.kind());
        lean_assert(is_binding(t));
        expr_kind k = t.kind();
        buffer<expr> subst;
        do {
            optional<expr> var_s_type;
            if (binding_domain(t) != binding_domain(s)) {
                var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
                expr var_t_type = instantiate_rev(binding_domain(t), subst.size(), subst.data());
                if (!is_def_eq(var_t_type, *var_s_type, c, jst, cs))
                    return false;
            }
            if (!closed(binding_body(t)) || !closed(binding_body(s))) {
                // local is used inside t or s
                if (!var_s_type)
                    var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
                subst.push_back(mk_local(mk_fresh_name(c), binding_name(s), *var_s_type, binding_info(s)));
            } else {
                subst.push_back(g_dont_care); // don't care
            }
            t = binding_body(t);
            s = binding_body(s);
        } while (t.kind() == k && s.kind() == k);
        return is_def_eq(instantiate_rev(t, subst.size(), subst.data()),
                         instantiate_rev(s, subst.size(), subst.data()), c, jst, cs);
    }

    bool is_def_eq(level const & l1, level const & l2, delayed_justification & jst, constraint_seq & cs) {
        if (is_equivalent(l1, l2)) {
            return true;
        } else if (has_meta(l1) || has_meta(l2)) {
            cs = cs + constraint_seq(mk_level_eq_cnstr(l1, l2, jst.get()));
            return true;
        } else {
            return false;
        }
    }

    bool is_def_eq(levels const & ls1, levels const & ls2, type_checker & c, delayed_justification & jst, constraint_seq & cs) {
        if (is_nil(ls1) && is_nil(ls2)) {
            return true;
        } else if (!is_nil(ls1) && !is_nil(ls2)) {
            return
                is_def_eq(head(ls1), head(ls2), jst, cs) &&
                is_def_eq(tail(ls1), tail(ls2), c, jst, cs);
        } else {
            return false;
        }
    }

    static pair<lbool, constraint_seq> to_lbcs(lbool l) { return mk_pair(l, constraint_seq()); }
    static pair<lbool, constraint_seq> to_lbcs(lbool l, constraint const & c) { return mk_pair(l, constraint_seq(c)); }
    static pair<lbool, constraint_seq> to_lbcs(pair<bool, constraint_seq> const & bcs) {
        return mk_pair(to_lbool(bcs.first), bcs.second);
    }

    /** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
    lbool quick_is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst, constraint_seq & cs) {
        if (t == s)
            return l_true; // t and s are structurally equal
        if (is_meta(t) || is_meta(s)) {
            // if t or s is a metavariable (or the application of a metavariable), then add constraint
            cs = cs + constraint_seq(mk_eq_cnstr(t, s, jst.get()));
            return l_true;
        }
        if (t.kind() == s.kind()) {
            switch (t.kind()) {
            case expr_kind::Lambda: case expr_kind::Pi:
                return to_lbool(is_def_eq_binding(t, s, c, jst, cs));
            case expr_kind::Sort:
                return to_lbool(is_def_eq(sort_level(t), sort_level(s), c, jst, cs));
            case expr_kind::Meta:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::Var: case expr_kind::Local: case expr_kind::App:
            case expr_kind::Constant: case expr_kind::Macro:
                // We do not handle these cases in this method.
                break;
            }
        }
        return l_undef; // This is not an "easy case"
    }

    /**
       \brief Return true if arguments of \c t are definitionally equal to arguments of \c s.
       This method is used to implement an optimization in the method \c is_def_eq.
    */
    bool is_def_eq_args(expr t, expr s, type_checker & c, delayed_justification & jst, constraint_seq & cs) {
        while (is_app(t) && is_app(s)) {
            if (!is_def_eq(app_arg(t), app_arg(s), c, jst, cs))
                return false;
            t = app_fn(t);
            s = app_fn(s);
        }
        return !is_app(t) && !is_app(s);
    }

    /** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_k) */
    bool is_app_of(expr t, name const & f_name) {
        t = get_app_fn(t);
        return is_constant(t) && const_name(t) == f_name;
    }

    /** \brief Try to solve (fun (x : A), B) =?= s by trying eta-expansion on s */
    bool try_eta_expansion(expr const & t, expr const & s, type_checker & c, delayed_justification & jst, constraint_seq & cs) {
        if (is_lambda(t) && !is_lambda(s)) {
            auto tcs    = infer_type(c, s);
            auto wcs    = whnf(tcs.first, c);
            expr s_type = wcs.first;
            if (!is_pi(s_type))
                return false;
            expr new_s  = mk_lambda(binding_name(s_type), binding_domain(s_type), mk_app(s, Var(0)), binding_info(s_type));
            auto dcs    = is_def_eq(t, new_s, c, jst);
            if (!dcs.first)
                return false;
            cs = cs + dcs.second + wcs.second + tcs.second;
            return true;
        } else {
            return false;
        }
    }

    bool is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst, constraint_seq & cs) {
        auto bcs = is_def_eq(t, s, c, jst);
        if (bcs.first) {
            cs = cs + bcs.second;
            return true;
        } else {
            return false;
        }
    }

    /** Return true iff t is definitionally equal to s. */
    virtual pair<bool, constraint_seq> is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst) {
        check_system("is_definitionally_equal");
        constraint_seq cs;
        lbool r = quick_is_def_eq(t, s, c, jst, cs);
        if (r != l_undef) return to_bcs(r == l_true, cs);

        // apply whnf (without using delta-reduction or normalizer extensions)
        expr t_n = whnf_core(t, c);
        expr s_n = whnf_core(s, c);
        if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
            r = quick_is_def_eq(t_n, s_n, c, jst, cs);
            if (r != l_undef) return to_bcs(r == l_true, cs);
        }

        // lazy delta-reduction and then normalizer extensions
        while (true) {
            // first, keep applying lazy delta-reduction while applicable
            while (true) {
                auto d_t = is_delta(t_n);
                auto d_s = is_delta(s_n);
                if (!d_t && !d_s) {
                    break;
                } else if (d_t && !d_s) {
                    t_n = whnf_core(unfold_names(t_n, 0), c);
                } else if (!d_t && d_s) {
                    s_n = whnf_core(unfold_names(s_n, 0), c);
                } else if (d_t->get_weight() > d_s->get_weight()) {
                    t_n = whnf_core(unfold_names(t_n, d_s->get_weight() + 1), c);
                } else if (d_t->get_weight() < d_s->get_weight()) {
                    s_n = whnf_core(unfold_names(s_n, d_t->get_weight() + 1), c);
                } else {
                    lean_assert(d_t && d_s && d_t->get_weight() == d_s->get_weight());
                    if (is_app(t_n) && is_app(s_n) && is_eqp(*d_t, *d_s)) {
                        // If t_n and s_n are both applications of the same (non-opaque) definition,
                        if (has_expr_metavar(t_n) || has_expr_metavar(s_n)) {
                            // We let the unifier deal with cases such as
                            // (f ...) =?= (f ...)
                            // when t_n or s_n contains metavariables
                            break;
                        } else {
                            // Optimization:
                            // We try to check if their arguments are definitionally equal.
                            // If they are, then t_n and s_n must be definitionally equal, and we can
                            // skip the delta-reduction step.
                            // If the flag use_conv_opt() is not true, then we skip this optimization
                            if (!is_opaque(*d_t) && d_t->use_conv_opt() &&
                                is_def_eq_args(t_n, s_n, c, jst, cs))
                                return to_bcs(true, cs);
                        }
                    }
                    t_n = whnf_core(unfold_names(t_n, d_t->get_weight() - 1), c);
                    s_n = whnf_core(unfold_names(s_n, d_s->get_weight() - 1), c);
                }
                r = quick_is_def_eq(t_n, s_n, c, jst, cs);
                if (r != l_undef) return to_bcs(r == l_true, cs);
            }
            // try normalizer extensions
            auto new_t_n = d_norm_ext(t_n, c, cs);
            auto new_s_n = d_norm_ext(s_n, c, cs);
            if (!new_t_n && !new_s_n)
                break; // t_n and s_n are in weak head normal form
            if (new_t_n)
                t_n = whnf_core(*new_t_n, c);
            if (new_s_n)
                s_n = whnf_core(*new_s_n, c);
            r = quick_is_def_eq(t_n, s_n, c, jst, cs);
            if (r != l_undef) return to_bcs(r == l_true, cs);
        }

        if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n) &&
            is_def_eq(const_levels(t_n), const_levels(s_n), c, jst, cs))
            return to_bcs(true, cs);

        if (is_local(t_n) && is_local(s_n) && mlocal_name(t_n) == mlocal_name(s_n) &&
            is_def_eq(mlocal_type(t_n), mlocal_type(s_n), c, jst, cs))
            return to_bcs(true, cs);

        optional<declaration> d_t, d_s;
        bool delay_check = false;
        if (has_expr_metavar(t_n) || has_expr_metavar(s_n)) {
            d_t = is_delta(t_n);
            d_s = is_delta(s_n);
            if (d_t && d_s && is_eqp(*d_t, *d_s))
                delay_check = true;
            else if (may_reduce_later(t_n, c) && may_reduce_later(s_n, c))
                delay_check = true;
        }

        // At this point, t_n and s_n are in weak head normal form (modulo meta-variables and proof irrelevance)
        if (!delay_check && is_app(t_n) && is_app(s_n)) {
            buffer<expr> t_args;
            buffer<expr> s_args;
            expr t_fn = get_app_args(t_n, t_args);
            expr s_fn = get_app_args(s_n, s_args);
            constraint_seq cs_prime = cs;
            if (is_def_eq(t_fn, s_fn, c, jst, cs_prime) && t_args.size() == s_args.size()) {
                unsigned i = 0;
                for (; i < t_args.size(); i++) {
                    if (!is_def_eq(t_args[i], s_args[i], c, jst, cs_prime))
                        break;
                }
                if (i == t_args.size()) {
                    return to_bcs(true, cs_prime);
                }
            }
        }

        if (try_eta_expansion(t_n, s_n, c, jst, cs) ||
            try_eta_expansion(s_n, t_n, c, jst, cs))
            return to_bcs(true, cs);

        if (m_env.prop_proof_irrel()) {
            // Proof irrelevance support for Prop (aka Type.{0})
            auto tcs    = infer_type(c, t);
            auto scs    = infer_type(c, s);
            expr t_type = tcs.first;
            expr s_type = scs.first;
            // remark: is_prop returns true only if t_type reducible to Prop.
            // If t_type contains metavariables, then reduction can get stuck, and is_prop will return false.
            auto pcs    = is_prop(t_type, c);
            if (pcs.first) {
                auto dcs = is_def_eq(t_type, s_type, c, jst);
                if (dcs.first)
                    return to_bcs(true, dcs.second + scs.second + pcs.second + tcs.second);
            } else {
                // If we can't stablish whether t_type is Prop, we try s_type.
                pcs = is_prop(s_type, c);
                if (pcs.first) {
                    auto dcs = is_def_eq(t_type, s_type, c, jst);
                    if (dcs.first)
                        return to_bcs(true, dcs.second + scs.second + pcs.second + tcs.second);
                }
                // This procedure will miss the case where s_type and t_type cannot be reduced to Prop
                // because they contain metavariables.
            }
        }

        list<name> const & cls_proof_irrel = m_env.cls_proof_irrel();
        if (!is_nil(cls_proof_irrel)) {
            // Proof irrelevance support for classes
            auto tcs    = infer_type(c, t);
            auto wcs    = whnf(tcs.first, c);
            expr t_type = wcs.first;
            if (std::any_of(cls_proof_irrel.begin(), cls_proof_irrel.end(), [&](name const & cls_name) { return is_app_of(t_type, cls_name); })) {
                auto ccs = infer_type(c, s);
                auto cs_prime = tcs.second + wcs.second + ccs.second;
                if (is_def_eq(t_type, ccs.first, c, jst, cs_prime))
                    return to_bcs(true, cs_prime);
            }
        }

        if (may_reduce_later(t_n, c) || may_reduce_later(s_n, c) || delay_check) {
            cs = cs + constraint_seq(mk_eq_cnstr(t_n, s_n, jst.get()));
            return to_bcs(true, cs);
        }

        return to_bcs(false);
    }

    pair<bool, constraint_seq> is_prop(expr const & e, type_checker & c) {
        auto tcs = infer_type(c, e);
        auto wcs = whnf(tcs.first, c);
        if (wcs.first == Prop)
            return to_bcs(true, wcs.second + tcs.second);
        else
            return to_bcs(false);
    }

    virtual optional<module_idx> get_module_idx() const {
        return m_module_idx;
    }
};

std::unique_ptr<converter> mk_default_converter(environment const & env, optional<module_idx> mod_idx,
                                                bool memoize, name_set const & extra_opaque) {
    return std::unique_ptr<converter>(new default_converter(env, mod_idx, memoize, extra_opaque));
}
std::unique_ptr<converter> mk_default_converter(environment const & env, bool unfold_opaque_main, bool memoize,
                                                name_set const & extra_opaque) {
    if (unfold_opaque_main)
        return mk_default_converter(env, optional<module_idx>(0), memoize, extra_opaque);
    else
        return mk_default_converter(env, optional<module_idx>(), memoize, extra_opaque);
}
}
