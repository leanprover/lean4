/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/flet.h"
#include "kernel/default_converter.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/type_checker.h"

namespace lean {
static expr * g_dont_care = nullptr;

default_converter::default_converter(environment const & env, bool memoize):
    m_env(env), m_memoize(memoize) {
    m_tc  = nullptr;
    m_jst = nullptr;
}

constraint default_converter::mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j) {
    return ::lean::mk_eq_cnstr(lhs, rhs, j);
}

optional<expr> default_converter::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, get_extension(*m_tc));
}

/** \brief Apply normalizer extensions to \c e. */
optional<pair<expr, constraint_seq>> default_converter::norm_ext(expr const & e) {
    return m_env.norm_ext()(e, get_extension(*m_tc));
}

optional<expr> default_converter::d_norm_ext(expr const & e, constraint_seq & cs) {
    if (auto r = norm_ext(e)) {
        cs += r->second;
        return some_expr(r->first);
    } else {
        return none_expr();
    }
}

/** \brief Return true if \c e may be reduced later after metavariables are instantiated. */
bool default_converter::is_stuck(expr const & e) {
    return static_cast<bool>(m_env.norm_ext().is_stuck(e, get_extension(*m_tc)));
}

bool default_converter::is_stuck(expr const & e, type_checker & c) {
    return static_cast<bool>(m_env.norm_ext().is_stuck(e, get_extension(c)));
}

/** \brief Weak head normal form core procedure. It does not perform delta reduction nor normalization extensions. */
expr default_converter::whnf_core(expr const & e) {
    check_system("whnf");

    // handle easy cases
    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
    case expr_kind::Pi:   case expr_kind::Constant: case expr_kind::Lambda:
        return e;
    case expr_kind::Macro: case expr_kind::App:
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
    case expr_kind::Pi:   case expr_kind::Constant: case expr_kind::Lambda:
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::Macro:
        if (auto m = expand_macro(e))
            r = whnf_core(*m);
        else
            r = e;
        break;
    case expr_kind::App: {
        buffer<expr> args;
        expr f0 = get_app_rev_args(e, args);
        expr f = whnf_core(f0);
        if (is_lambda(f)) {
            unsigned m = 1;
            unsigned num_args = args.size();
            while (is_lambda(binding_body(f)) && m < num_args) {
                f = binding_body(f);
                m++;
            }
            lean_assert(m <= num_args);
            r = whnf_core(mk_rev_app(instantiate(binding_body(f), m, args.data() + (num_args - m)), num_args - m, args.data()));
        } else {
            r = f == f0 ? e : whnf_core(mk_rev_app(f, args.size(), args.data()));
        }
        break;
    }}

    if (m_memoize)
        m_whnf_core_cache.insert(mk_pair(e, r));
    return r;
}

bool default_converter::is_opaque(declaration const &) const {
    return false;
}

/** \brief Expand \c e if it is non-opaque constant with weight >= w */
expr default_converter::unfold_name_core(expr e, unsigned w) {
    if (is_constant(e)) {
        if (auto d = m_env.find(const_name(e))) {
            if (d->is_definition() && !is_opaque(*d) && d->get_weight() >= w &&
                length(const_levels(e)) == d->get_num_univ_params())
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
expr default_converter::unfold_names(expr const & e, unsigned w) {
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
optional<declaration> default_converter::is_delta(expr const & e) const {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        if (auto d = m_env.find(const_name(f)))
            if (d->is_definition() && !is_opaque(*d))
                return d;
    }
    return none_declaration();
}

/**
   \brief Weak head normal form core procedure that perform delta reduction for non-opaque constants with
   weight greater than or equal to \c w.

   This method is based on <tt>whnf_core(expr const &)</tt> and \c unfold_names.

   \remark This method does not use normalization extensions attached in the environment.
*/
expr default_converter::whnf_core(expr e, unsigned w) {
    while (true) {
        expr new_e = unfold_names(whnf_core(e), w);
        if (is_eqp(e, new_e))
            return e;
        e = new_e;
    }
}

/** \brief Put expression \c t in weak head normal form */
pair<expr, constraint_seq> default_converter::whnf(expr const & e_prime) {
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
        expr t1 = whnf_core(t, 0);
        if (auto new_t = d_norm_ext(t1, cs)) {
            t  = *new_t;
        } else {
            auto r = mk_pair(t1, cs);
            if (m_memoize)
                m_whnf_cache.insert(mk_pair(e, r));
            return r;
        }
    }
}

expr default_converter::whnf(expr const & e_prime, constraint_seq & cs) {
    auto r = whnf(e_prime);
    cs += r.second;
    return r.first;
}

/**
   \brief Given lambda/Pi expressions \c t and \c s, return true iff \c t is def eq to \c s.

        t and s are definitionally equal
           iff
        domain(t) is definitionally equal to domain(s)
        and
        body(t) is definitionally equal to body(s)
*/
bool default_converter::is_def_eq_binding(expr t, expr s, constraint_seq & cs) {
    lean_assert(t.kind() == s.kind());
    lean_assert(is_binding(t));
    expr_kind k = t.kind();
    buffer<expr> subst;
    do {
        optional<expr> var_s_type;
        if (binding_domain(t) != binding_domain(s)) {
            var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            expr var_t_type = instantiate_rev(binding_domain(t), subst.size(), subst.data());
            if (!is_def_eq(var_t_type, *var_s_type, cs))
                return false;
        }
        if (!closed(binding_body(t)) || !closed(binding_body(s))) {
            // local is used inside t or s
            if (!var_s_type)
                var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            subst.push_back(mk_local(mk_fresh_name(*m_tc), binding_name(s), *var_s_type, binding_info(s)));
        } else {
            subst.push_back(*g_dont_care); // don't care
        }
        t = binding_body(t);
        s = binding_body(s);
    } while (t.kind() == k && s.kind() == k);
    return is_def_eq(instantiate_rev(t, subst.size(), subst.data()),
                     instantiate_rev(s, subst.size(), subst.data()), cs);
}

bool default_converter::is_def_eq(level const & l1, level const & l2, constraint_seq & cs) {
    if (is_equivalent(l1, l2)) {
        return true;
    } else if (has_meta(l1) || has_meta(l2)) {
        cs += constraint_seq(mk_level_eq_cnstr(l1, l2, m_jst->get()));
        return true;
    } else {
        return false;
    }
}

bool default_converter::is_def_eq(levels const & ls1, levels const & ls2, constraint_seq & cs) {
    if (is_nil(ls1) && is_nil(ls2)) {
        return true;
    } else if (!is_nil(ls1) && !is_nil(ls2)) {
        return
            is_def_eq(head(ls1), head(ls2), cs) &&
            is_def_eq(tail(ls1), tail(ls2), cs);
    } else {
        return false;
    }
}

/** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
lbool default_converter::quick_is_def_eq(expr const & t, expr const & s, constraint_seq & cs, bool use_hash) {
    if (m_eqv_manager.is_equiv(t, s, use_hash))
        return l_true;
    if (is_meta(t) || is_meta(s)) {
        // if t or s is a metavariable (or the application of a metavariable), then add constraint
        cs += constraint_seq(mk_eq_cnstr(t, s, m_jst->get()));
        return l_true;
    }
    if (t.kind() == s.kind()) {
        switch (t.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(t, s, cs));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(t), sort_level(s), cs));
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
bool default_converter::is_def_eq_args(expr t, expr s, constraint_seq & cs) {
    while (is_app(t) && is_app(s)) {
        if (!is_def_eq(app_arg(t), app_arg(s), cs))
            return false;
        t = app_fn(t);
        s = app_fn(s);
    }
    return !is_app(t) && !is_app(s);
}

/** \brief Return true iff t is a constant named f_name or an application of the form (f_name a_1 ... a_k) */
bool default_converter::is_app_of(expr t, name const & f_name) {
    t = get_app_fn(t);
    return is_constant(t) && const_name(t) == f_name;
}

/** \brief Try to solve (fun (x : A), B) =?= s by trying eta-expansion on s */
bool default_converter::try_eta_expansion_core(expr const & t, expr const & s, constraint_seq & cs) {
    if (is_lambda(t) && !is_lambda(s)) {
        auto tcs    = infer_type(s);
        auto wcs    = whnf(tcs.first);
        expr s_type = wcs.first;
        if (!is_pi(s_type))
            return false;
        expr new_s  = mk_lambda(binding_name(s_type), binding_domain(s_type), mk_app(s, Var(0)), binding_info(s_type));
        auto dcs    = is_def_eq(t, new_s);
        if (!dcs.first)
            return false;
        cs += dcs.second + wcs.second + tcs.second;
        return true;
    } else {
        return false;
    }
}

/** \brief Return true iff \c t and \c s are definitionally equal.

    \remark Store in \c cs any generated constraints.
*/
bool default_converter::is_def_eq(expr const & t, expr const & s, constraint_seq & cs) {
    auto bcs = is_def_eq(t, s);
    if (bcs.first) {
        cs += bcs.second;
        return true;
    } else {
        return false;
    }
}

/** \brief Return true if \c t and \c s are definitionally equal because they are applications of the form
    <tt>(f a_1 ... a_n)</tt> <tt>(g b_1 ... b_n)</tt>, and \c f and \c g are definitionally equal, and
    \c a_i and \c b_i are also definitionally equal for every 1 <= i <= n.
    Return false otherwise.

    \remark Store in \c cs any generated constraints
*/
bool default_converter::is_def_eq_app(expr const & t, expr const & s, constraint_seq & cs) {
    if (is_app(t) && is_app(s)) {
        buffer<expr> t_args;
        buffer<expr> s_args;
        expr t_fn = get_app_args(t, t_args);
        expr s_fn = get_app_args(s, s_args);
        constraint_seq cs_prime = cs;
        if (is_def_eq(t_fn, s_fn, cs_prime) && t_args.size() == s_args.size()) {
            unsigned i = 0;
            for (; i < t_args.size(); i++) {
                if (!is_def_eq(t_args[i], s_args[i], cs_prime))
                    break;
            }
            if (i == t_args.size()) {
                cs = cs_prime;
                return true;
            }
        }
    }
    return false;
}

/** \brief remark: is_prop returns true only if \c e is reducible to Prop.
    If \c e contains metavariables, then reduction can get stuck, and is_prop will return false.
*/
pair<bool, constraint_seq> default_converter::is_prop(expr const & e) {
    auto tcs = infer_type(e);
    auto wcs = whnf(tcs.first);
    if (wcs.first == mk_Prop())
        return to_bcs(true, wcs.second + tcs.second);
    else
        return to_bcs(false);
}

/** \brief Return true if \c t and \c s are definitionally equal due to proof irrelevant.
    Return false otherwise.

    \remark Store in \c cs any generated constraints.
*/
bool default_converter::is_def_eq_proof_irrel(expr const & t, expr const & s, constraint_seq & cs) {
    if (!m_env.prop_proof_irrel())
        return false;
    // Proof irrelevance support for Prop (aka Type.{0})
    auto tcs    = infer_type(t);
    auto scs    = infer_type(s);
    expr t_type = tcs.first;
    expr s_type = scs.first;
    auto pcs    = is_prop(t_type);
    if (pcs.first) {
        auto dcs = is_def_eq(t_type, s_type);
        if (dcs.first) {
            cs += dcs.second + scs.second + pcs.second + tcs.second;
            return true;
        }
    } else {
        // If we can't stablish whether t_type is Prop, we try s_type.
        pcs = is_prop(s_type);
        if (pcs.first) {
            auto dcs = is_def_eq(t_type, s_type);
            if (dcs.first) {
                cs += dcs.second + scs.second + pcs.second + tcs.second;
                return true;
            }
        }
        // This procedure will miss the case where s_type and t_type cannot be reduced to Prop
        // because they contain metavariables.
    }
    return false;
}

pair<bool, constraint_seq> default_converter::is_def_eq_core(expr const & t, expr const & s) {
    check_system("is_definitionally_equal");
    constraint_seq cs;
    bool use_hash = true;
    lbool r = quick_is_def_eq(t, s, cs, use_hash);
    if (r != l_undef) return to_bcs(r == l_true, cs);

    // apply whnf (without using delta-reduction or normalizer extensions)
    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        r = quick_is_def_eq(t_n, s_n, cs);
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
                t_n = whnf_core(unfold_names(t_n, 0));
            } else if (!d_t && d_s) {
                s_n = whnf_core(unfold_names(s_n, 0));
            } else if (d_t->get_weight() > d_s->get_weight()) {
                t_n = whnf_core(unfold_names(t_n, d_s->get_weight() + 1));
            } else if (d_t->get_weight() < d_s->get_weight()) {
                s_n = whnf_core(unfold_names(s_n, d_t->get_weight() + 1));
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
                        constraint_seq tmp_cs;
                        if (!is_opaque(*d_t) && d_t->use_conv_opt() &&
                            is_def_eq(const_levels(get_app_fn(t_n)), const_levels(get_app_fn(s_n)), tmp_cs) &&
                            is_def_eq_args(t_n, s_n, tmp_cs)) {
                            cs += tmp_cs;
                            return to_bcs(true, cs);
                        }
                    }
                }
                t_n = whnf_core(unfold_names(t_n, d_t->get_weight() - 1));
                s_n = whnf_core(unfold_names(s_n, d_s->get_weight() - 1));
            }
            r = quick_is_def_eq(t_n, s_n, cs);
            if (r != l_undef) return to_bcs(r == l_true, cs);
        }
        // try normalizer extensions
        auto new_t_n = d_norm_ext(t_n, cs);
        auto new_s_n = d_norm_ext(s_n, cs);
        if (!new_t_n && !new_s_n)
            break; // t_n and s_n are in weak head normal form
        if (new_t_n)
            t_n = whnf_core(*new_t_n);
        if (new_s_n)
            s_n = whnf_core(*new_s_n);
        r = quick_is_def_eq(t_n, s_n, cs);
        if (r != l_undef) return to_bcs(r == l_true, cs);
    }

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n) &&
        is_def_eq(const_levels(t_n), const_levels(s_n), cs))
        return to_bcs(true, cs);

    if (is_local(t_n) && is_local(s_n) && mlocal_name(t_n) == mlocal_name(s_n))
        return to_bcs(true, cs);

    optional<declaration> d_t, d_s;
    bool delay_check = false;
    if (has_expr_metavar(t_n) || has_expr_metavar(s_n)) {
        d_t = is_delta(t_n);
        d_s = is_delta(s_n);
        if (d_t && d_s && is_eqp(*d_t, *d_s))
            delay_check = true;
        else if (is_stuck(t_n) && is_stuck(s_n))
            delay_check = true;
    }

    // At this point, t_n and s_n are in weak head normal form (modulo meta-variables and proof irrelevance)
    if (!delay_check && is_def_eq_app(t_n, s_n, cs))
        return to_bcs(true, cs);

    if (try_eta_expansion(t_n, s_n, cs))
        return to_bcs(true, cs);

    constraint_seq pi_cs;
    if (is_def_eq_proof_irrel(t, s, pi_cs))
        return to_bcs(true, pi_cs);

    if (is_stuck(t_n) || is_stuck(s_n) || delay_check) {
        cs += constraint_seq(mk_eq_cnstr(t_n, s_n, m_jst->get()));
        return to_bcs(true, cs);
    }

    return to_bcs(false);
}

pair<bool, constraint_seq> default_converter::is_def_eq(expr const & t, expr const & s) {
    auto r = is_def_eq_core(t, s);
    if (r.first && !r.second)
        m_eqv_manager.add_equiv(t, s);
    return r;
}

/** Return true iff t is definitionally equal to s. */
pair<bool, constraint_seq> default_converter::is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst) {
    flet<type_checker*>          set_tc(m_tc, &c);
    flet<delayed_justification*> set_js(m_jst, &jst);
    return is_def_eq(t, s);
}

pair<expr, constraint_seq> default_converter::whnf(expr const & e, type_checker & c) {
    flet<type_checker*>          set_tc(m_tc, &c);
    return whnf(e);
}

void initialize_default_converter() {
    g_dont_care = new expr(Const("dontcare"));
}

void finalize_default_converter() {
    delete g_dont_care;
}
}
