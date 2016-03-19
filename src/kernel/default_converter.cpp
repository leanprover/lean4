/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/flet.h"
#include "util/fresh_name.h"
#include "kernel/default_converter.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/type_checker.h"
#include "kernel/error_msgs.h"
#include "library/metavar.h"
#include "library/constraint.h"

namespace lean {
static expr * g_dont_care = nullptr;

default_converter::default_converter(environment const & env, bool memoize):
    m_env(env), m_memoize(memoize) {
    m_tc  = nullptr;
    m_jst = nullptr;
}

optional<expr> default_converter::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, *m_tc);
}

/** \brief Apply normalizer extensions to \c e. */
optional<expr> default_converter::norm_ext(expr const & e) {
    return m_env.norm_ext()(e, *m_tc);
}

/** \brief Return true if \c e may be reduced later after metavariables are instantiated. */
bool default_converter::is_stuck(expr const & e) {
    return static_cast<bool>(m_env.norm_ext().is_stuck(e, *m_tc));
}

optional<expr> default_converter::is_stuck(expr const & e, type_checker & c) {
    if (is_meta(e)) {
        return some_expr(e);
    } else {
        return m_env.norm_ext().is_stuck(e, c);
    }
}

/** \brief Weak head normal form core procedure. It does not perform delta reduction nor normalization extensions. */
expr default_converter::whnf_core(expr const & e) {
    check_system("whnf");

    // handle easy cases
    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
    case expr_kind::Pi:   case expr_kind::Constant: case expr_kind::Lambda:
        return e;
    case expr_kind::Macro: case expr_kind::App: case expr_kind::Let:
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
    case expr_kind::Var:  case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
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
    }
    case expr_kind::Let:
        r = whnf_core(instantiate(let_body(e), let_value(e)));
        break;
    }

    if (m_memoize)
        m_whnf_core_cache.insert(mk_pair(e, r));
    return r;
}

bool default_converter::is_opaque(declaration const &) const {
    return false;
}

/** \brief Expand \c e if it is non-opaque constant with height >= h */
expr default_converter::unfold_name_core(expr e, unsigned h) {
    if (is_constant(e)) {
        if (auto d = m_env.find(const_name(e))) {
            if (d->is_definition() && !is_opaque(*d) && d->get_height() >= h &&
                length(const_levels(e)) == d->get_num_univ_params())
                return unfold_name_core(instantiate_value_univ_params(*d, const_levels(e)), h);
        }
    }
    return e;
}

/**
   \brief Expand constants and application where the function is a constant.

   The unfolding is only performend if the constant corresponds to
   a non-opaque definition with height >= h.
*/
expr default_converter::unfold_names(expr const & e, unsigned h) {
    if (is_app(e)) {
        expr f0 = get_app_fn(e);
        expr f  = unfold_name_core(f0, h);
        if (is_eqp(f, f0)) {
            return e;
        } else {
            buffer<expr> args;
            get_app_rev_args(e, args);
            return mk_rev_app(f, args);
        }
    } else {
        return unfold_name_core(e, h);
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
   height greater than or equal to \c h.

   This method is based on <tt>whnf_core(expr const &)</tt> and \c unfold_names.

   \remark This method does not use normalization extensions attached in the environment.
*/
expr default_converter::whnf_core(expr e, unsigned h) {
    while (true) {
        expr new_e = unfold_names(whnf_core(e), h);
        if (is_eqp(e, new_e))
            return e;
        e = new_e;
    }
}

/** \brief Put expression \c t in weak head normal form */
expr default_converter::whnf(expr const & e_prime) {
    // Do not cache easy cases
    switch (e_prime.kind()) {
    case expr_kind::Var: case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local: case expr_kind::Pi:
        return e_prime;
    case expr_kind::Lambda:   case expr_kind::Macro: case expr_kind::App:
    case expr_kind::Constant: case expr_kind::Let:
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
    while (true) {
        expr t1 = whnf_core(t, 0);
        if (auto new_t = norm_ext(t1)) {
            t  = *new_t;
        } else {
            auto r = t1;
            if (m_memoize)
                m_whnf_cache.insert(mk_pair(e, r));
            return r;
        }
    }
}

/**
   \brief Given lambda/Pi expressions \c t and \c s, return true iff \c t is def eq to \c s.

        t and s are definitionally equal
           iff
        domain(t) is definitionally equal to domain(s)
        and
        body(t) is definitionally equal to body(s)
*/
bool default_converter::is_def_eq_binding(expr t, expr s) {
    lean_assert(t.kind() == s.kind());
    lean_assert(is_binding(t));
    expr_kind k = t.kind();
    buffer<expr> subst;
    do {
        optional<expr> var_s_type;
        if (binding_domain(t) != binding_domain(s)) {
            var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            expr var_t_type = instantiate_rev(binding_domain(t), subst.size(), subst.data());
            if (!is_def_eq(var_t_type, *var_s_type))
                return false;
        }
        if (!closed(binding_body(t)) || !closed(binding_body(s))) {
            // local is used inside t or s
            if (!var_s_type)
                var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            subst.push_back(mk_local(mk_fresh_name(), binding_name(s), *var_s_type, binding_info(s)));
        } else {
            subst.push_back(*g_dont_care); // don't care
        }
        t = binding_body(t);
        s = binding_body(s);
    } while (t.kind() == k && s.kind() == k);
    return is_def_eq(instantiate_rev(t, subst.size(), subst.data()),
                     instantiate_rev(s, subst.size(), subst.data()));
}

bool default_converter::is_def_eq(level const & l1, level const & l2) {
    if (is_equivalent(l1, l2)) {
        return true;
    } else {
        return false;
    }
}

bool default_converter::is_def_eq(levels const & ls1, levels const & ls2) {
    if (is_nil(ls1) && is_nil(ls2)) {
        return true;
    } else if (!is_nil(ls1) && !is_nil(ls2)) {
        return
            is_def_eq(head(ls1), head(ls2)) &&
            is_def_eq(tail(ls1), tail(ls2));
    } else {
        return false;
    }
}

/** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
lbool default_converter::quick_is_def_eq(expr const & t, expr const & s, bool use_hash) {
    if (m_eqv_manager.is_equiv(t, s, use_hash))
        return l_true;
    if (t.kind() == s.kind()) {
        switch (t.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return to_lbool(is_def_eq_binding(t, s));
        case expr_kind::Sort:
            return to_lbool(is_def_eq(sort_level(t), sort_level(s)));
        case expr_kind::Meta:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Var:      case expr_kind::Local: case expr_kind::App:
        case expr_kind::Constant: case expr_kind::Macro: case expr_kind::Let:
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
bool default_converter::is_def_eq_args(expr t, expr s) {
    while (is_app(t) && is_app(s)) {
        if (!is_def_eq(app_arg(t), app_arg(s)))
            return false;
        t = app_fn(t);
        s = app_fn(s);
    }
    return !is_app(t) && !is_app(s);
}

/** \brief Try to solve (fun (x : A), B) =?= s by trying eta-expansion on s */
bool default_converter::try_eta_expansion_core(expr const & t, expr const & s) {
    if (is_lambda(t) && !is_lambda(s)) {
        expr s_type = whnf(infer_type(s));
        constraint_seq aux_cs;
        if (!is_pi(s_type))
            return false;
        expr new_s  = mk_lambda(binding_name(s_type), binding_domain(s_type), mk_app(s, Var(0)), binding_info(s_type));
        if (!is_def_eq(t, new_s))
            return false;
        return true;
    } else {
        return false;
    }
}

/** \brief Return true if \c t and \c s are definitionally equal because they are applications of the form
    <tt>(f a_1 ... a_n)</tt> <tt>(g b_1 ... b_n)</tt>, and \c f and \c g are definitionally equal, and
    \c a_i and \c b_i are also definitionally equal for every 1 <= i <= n.
    Return false otherwise.
*/
bool default_converter::is_def_eq_app(expr const & t, expr const & s) {
    if (is_app(t) && is_app(s)) {
        buffer<expr> t_args;
        buffer<expr> s_args;
        expr t_fn = get_app_args(t, t_args);
        expr s_fn = get_app_args(s, s_args);
        if (is_def_eq(t_fn, s_fn) && t_args.size() == s_args.size()) {
            unsigned i = 0;
            for (; i < t_args.size(); i++) {
                if (!is_def_eq(t_args[i], s_args[i]))
                    break;
            }
            if (i == t_args.size())
                return true;
        }
    }
    return false;
}

/** \brief remark: is_prop returns true only if \c e is reducible to Prop.
*/
bool default_converter::is_prop(expr const & e) {
    return whnf(infer_type(e)) == mk_Prop();
}

/** \brief Return true if \c t and \c s are definitionally equal due to proof irrelevant.
    Return false otherwise.
*/
bool default_converter::is_def_eq_proof_irrel(expr const & t, expr const & s) {
    if (!m_env.prop_proof_irrel())
        return false;
    // Proof irrelevance support for Prop (aka Type.{0})
    expr t_type = infer_type(t);
    expr s_type = infer_type(s);
    return is_prop(t_type) && is_def_eq(t_type, s_type);
}

bool default_converter::failed_before(expr const & t, expr const & s) const {
    if (t.hash() < s.hash()) {
        return m_failure_cache.find(mk_pair(t, s)) != m_failure_cache.end();
    } else if (t.hash() > s.hash()) {
        return m_failure_cache.find(mk_pair(s, t)) != m_failure_cache.end();
    } else {
        return
            m_failure_cache.find(mk_pair(t, s)) != m_failure_cache.end() ||
            m_failure_cache.find(mk_pair(s, t)) != m_failure_cache.end();
    }
}

void default_converter::cache_failure(expr const & t, expr const & s) {
    if (t.hash() <= s.hash())
        m_failure_cache.insert(mk_pair(t, s));
    else
        m_failure_cache.insert(mk_pair(s, t));
}

/**
   \brief Perform one lazy delta-reduction step.
   Return
   - l_true if t_n and s_n are definitionally equal.
   - l_false if they are not definitionally equal.
   - l_undef it the step did not manage to establish whether they are definitionally equal or not.

   \remark t_n, s_n and cs are updated.
*/
auto default_converter::lazy_delta_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto d_t = is_delta(t_n);
    auto d_s = is_delta(s_n);
    if (!d_t && !d_s) {
        return reduction_status::DefUnknown;
    } else if (d_t && !d_s) {
        t_n = whnf_core(unfold_names(t_n, 0));
    } else if (!d_t && d_s) {
        s_n = whnf_core(unfold_names(s_n, 0));
    } else if (!d_t->is_theorem() && d_s->is_theorem()) {
        t_n = whnf_core(unfold_names(t_n, d_t->get_height()));
    } else if (!d_s->is_theorem() && d_t->is_theorem()) {
        s_n = whnf_core(unfold_names(s_n, d_s->get_height()));
    } else if (!d_t->is_theorem() && d_t->get_height() > d_s->get_height()) {
        t_n = whnf_core(unfold_names(t_n, d_s->get_height() + 1));
    } else if (!d_s->is_theorem() && d_t->get_height() < d_s->get_height()) {
        s_n = whnf_core(unfold_names(s_n, d_t->get_height() + 1));
    } else {
        if (is_app(t_n) && is_app(s_n) && is_eqp(*d_t, *d_s)) {
            // If t_n and s_n are both applications of the same (non-opaque) definition,
            if (has_expr_metavar(t_n) || has_expr_metavar(s_n)) {
                // We let the unifier deal with cases such as
                // (f ...) =?= (f ...)
                // when t_n or s_n contains metavariables
                return reduction_status::DefUnknown;
            } else {
                // Optimization:
                // We try to check if their arguments are definitionally equal.
                // If they are, then t_n and s_n must be definitionally equal, and we can
                // skip the delta-reduction step.
                // If the flag use_conv_opt() is not true, then we skip this optimization
                if (!is_opaque(*d_t) && d_t->use_conv_opt() && !failed_before(t_n, s_n)) {
                    if (is_def_eq(const_levels(get_app_fn(t_n)), const_levels(get_app_fn(s_n))) &&
                        is_def_eq_args(t_n, s_n)) {
                        return reduction_status::DefEqual;
                    } else {
                        cache_failure(t_n, s_n);
                    }
                }
            }
        }
        t_n = whnf_core(unfold_names(t_n, d_t->get_height() - 1));
        s_n = whnf_core(unfold_names(s_n, d_s->get_height() - 1));
    }
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

lbool default_converter::lazy_delta_reduction(expr & t_n, expr & s_n) {
    while (true) {
        switch (lazy_delta_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

auto default_converter::ext_reduction_step(expr & t_n, expr & s_n) -> reduction_status {
    auto new_t_n = norm_ext(t_n);
    auto new_s_n = norm_ext(s_n);
    if (!new_t_n && !new_s_n)
        return reduction_status::DefUnknown;
    if (new_t_n)
        t_n = whnf_core(*new_t_n);
    if (new_s_n)
        s_n = whnf_core(*new_s_n);
    switch (quick_is_def_eq(t_n, s_n)) {
    case l_true:  return reduction_status::DefEqual;
    case l_false: return reduction_status::DefDiff;
    case l_undef: return reduction_status::Continue;
    }
    lean_unreachable();
}

// Apply lazy delta-reduction and then normalizer extensions
lbool default_converter::reduce_def_eq(expr & t_n, expr & s_n) {
    while (true) {
        // first, keep applying lazy delta-reduction while applicable
        lbool r = lazy_delta_reduction(t_n, s_n);
        if (r != l_undef) return r;

        // try normalizer extensions
        switch (ext_reduction_step(t_n, s_n)) {
        case reduction_status::Continue:   break;
        case reduction_status::DefUnknown: return l_undef;
        case reduction_status::DefEqual:   return l_true;
        case reduction_status::DefDiff:    return l_false;
        }
    }
}

bool default_converter::postpone_is_def_eq(expr const & t, expr const & s) {
    if (has_expr_metavar(t) || has_expr_metavar(s)) {
        optional<declaration> d_t = is_delta(t);
        optional<declaration> d_s = is_delta(s);
        if (d_t && d_s && is_eqp(*d_t, *d_s))
            return true;
        else if (is_stuck(t) && is_stuck(s))
            return true;
    }
    return false;
}

bool default_converter::is_def_eq_core(expr const & t, expr const & s) {
    check_system("is_definitionally_equal");
    bool use_hash = true;
    lbool r = quick_is_def_eq(t, s, use_hash);
    if (r != l_undef) return r == l_true;

    // apply whnf (without using delta-reduction or normalizer extensions)
    expr t_n = whnf_core(t);
    expr s_n = whnf_core(s);

    if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
        r = quick_is_def_eq(t_n, s_n);
        if (r != l_undef) return r == l_true;
    }

    r = reduce_def_eq(t_n, s_n);
    if (r != l_undef) return r == l_true;

    if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n) &&
        is_def_eq(const_levels(t_n), const_levels(s_n)))
        return true;

    if (is_local(t_n) && is_local(s_n) && mlocal_name(t_n) == mlocal_name(s_n))
        return true;

    bool postpone = postpone_is_def_eq(t_n, s_n);

    // At this point, t_n and s_n are in weak head normal form (modulo meta-variables and proof irrelevance)
    if (!postpone && is_def_eq_app(t_n, s_n))
        return true;

    if (try_eta_expansion(t_n, s_n))
        return true;

    if (is_def_eq_proof_irrel(t, s))
        return true;

    return false;
}

bool default_converter::is_def_eq(expr const & t, expr const & s) {
    bool r = is_def_eq_core(t, s);
    if (r)
        m_eqv_manager.add_equiv(t, s);
    return r;
}

/** Return true iff t is definitionally equal to s. */
bool default_converter::is_def_eq(expr const & t, expr const & s, type_checker & c) {
    flet<type_checker*>          set_tc(m_tc, &c);
    return is_def_eq(t, s);
}

expr default_converter::whnf(expr const & e, type_checker & c) {
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
