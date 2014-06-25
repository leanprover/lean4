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
static no_delayed_justification g_no_delayed_jst;
bool converter::is_def_eq(expr const & t, expr const & s, type_checker & c) {
    return is_def_eq(t, s, c, g_no_delayed_jst);
}

/** \brief Do nothing converter */
struct dummy_converter : public converter {
    virtual expr whnf(expr const & e, type_checker &) { return e; }
    virtual bool is_def_eq(expr const &, expr const &, type_checker &, delayed_justification &) { return true; }
};

std::unique_ptr<converter> mk_dummy_converter() {
    return std::unique_ptr<converter>(new dummy_converter());
}

name converter::mk_fresh_name(type_checker & tc) { return tc.mk_fresh_name(); }
expr converter::infer_type(type_checker & tc, expr const & e) { return tc.infer_type(e); }
void converter::add_cnstr(type_checker & tc, constraint const & c) { return tc.add_cnstr(c); }
extension_context & converter::get_extension(type_checker & tc) { return tc.get_extension(); }

struct default_converter : public converter {
    environment           m_env;
    optional<module_idx>  m_module_idx;
    bool                  m_memoize;
    name_set              m_extra_opaque;
    expr_struct_map<expr> m_whnf_core_cache;
    expr_struct_map<expr> m_whnf_cache;

    default_converter(environment const & env, optional<module_idx> mod_idx, bool memoize, name_set const & extra_opaque):
        m_env(env), m_module_idx(mod_idx), m_memoize(memoize), m_extra_opaque(extra_opaque) {}

    optional<expr> expand_macro(expr const & m, type_checker & c) {
        lean_assert(is_macro(m));
        return macro_def(m).expand(m, get_extension(c));
    }

    /** \brief Apply normalizer extensions to \c e. */
    optional<expr> norm_ext(expr const & e, type_checker & c) {
        return m_env.norm_ext()(e, get_extension(c));
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
    bool is_opaque(declaration const & d) const {
        lean_assert(d.is_definition());
        if (d.is_theorem()) return true;                                       // theorems are always opaque
        if (m_extra_opaque.contains(d.get_name())) return true;                // extra_opaque set overrides opaque flag
        if (!d.is_opaque()) return false;                                      // d is a transparent definition
        if (m_module_idx && d.get_module_idx() == *m_module_idx) return false; // the opaque definitions in module_idx are considered transparent
        return true;                                                           // d is opaque
    }

    /** \brief Expand \c e if it is non-opaque constant with weight >= w */
    expr unfold_name_core(expr e, unsigned w) {
        if (is_constant(e)) {
            if (auto d = m_env.find(const_name(e))) {
                if (d->is_definition() && !is_opaque(*d) && d->get_weight() >= w)
                    return unfold_name_core(instantiate_params(d->get_value(), d->get_univ_params(), const_levels(e)), w);
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

    /** \brief Auxiliary method for \c is_delta */
    optional<declaration> is_delta_core(expr const & e) {
        if (is_constant(e)) {
            if (auto d = m_env.find(const_name(e)))
                if (d->is_definition() && !is_opaque(*d))
                    return d;
        }
        return none_declaration();
    }

    /**
        \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
        to be expanded.
    */
    optional<declaration> is_delta(expr const & e) { return is_delta_core(get_app_fn(e)); }

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
    virtual expr whnf(expr const & e_prime, type_checker & c) {
        expr e = e_prime;
        // check cache
        if (m_memoize) {
            auto it = m_whnf_cache.find(e);
            if (it != m_whnf_cache.end())
                return it->second;
        }

        expr t = e;
        while (true) {
            expr t1 = whnf_core(t, 0, c);
            auto new_t = norm_ext(t1, c);
            if (new_t) {
                t = *new_t;
            } else {
                if (m_memoize)
                    m_whnf_cache.insert(mk_pair(e, t1));
                return t1;
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
    bool is_def_eq_binding(expr t, expr s, type_checker & c, delayed_justification & jst) {
        lean_assert(t.kind() == s.kind());
        lean_assert(is_binding(t));
        expr_kind k = t.kind();
        buffer<expr> subst;
        do {
            expr var_t_type = instantiate_rev(binding_domain(t), subst.size(), subst.data());
            expr var_s_type = instantiate_rev(binding_domain(s), subst.size(), subst.data());
            if (!is_def_eq(var_t_type, var_s_type, c, jst))
                return false;
            subst.push_back(mk_local(mk_fresh_name(c), binding_name(s), var_s_type));
            t = binding_body(t);
            s = binding_body(s);
        } while (t.kind() == k && s.kind() == k);
        return is_def_eq(instantiate_rev(t, subst.size(), subst.data()),
                         instantiate_rev(s, subst.size(), subst.data()), c, jst);
    }

    bool is_def_eq(level const & l1, level const & l2, type_checker & c, delayed_justification & jst) {
        if (is_equivalent(l1, l2)) {
            return true;
        } else if (has_meta(l1) || has_meta(l2)) {
            add_cnstr(c, mk_level_eq_cnstr(l1, l2, jst.get()));
            return true;
        } else {
            return false;
        }
    }

    bool is_def_eq(levels const & ls1, levels const & ls2, type_checker & c, delayed_justification & jst) {
        if (is_nil(ls1) && is_nil(ls2))
            return true;
        else if (!is_nil(ls1) && !is_nil(ls2))
            return is_def_eq(head(ls1), head(ls2), c, jst) && is_def_eq(tail(ls1), tail(ls2), c, jst);
        else
            return false;
    }

    /** \brief This is an auxiliary method for is_def_eq. It handles the "easy cases". */
    lbool quick_is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst) {
        if (t == s)
            return l_true; // t and s are structurally equal
        if (is_meta(t) || is_meta(s)) {
            // if t or s is a metavariable (or the application of a metavariable), then add constraint
            add_cnstr(c, mk_eq_cnstr(t, s, jst.get()));
            return l_true;
        }
        if (t.kind() == s.kind()) {
            switch (t.kind()) {
            case expr_kind::Lambda: case expr_kind::Pi:
                return to_lbool(is_def_eq_binding(t, s, c, jst));
            case expr_kind::Sort:
                return to_lbool(is_def_eq(sort_level(t), sort_level(s), c, jst));
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
    bool is_def_eq_args(expr t, expr s, type_checker & c, delayed_justification & jst) {
        while (is_app(t) && is_app(s)) {
            if (!is_def_eq(app_arg(t), app_arg(s), c, jst))
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

    /** Return true iff t is definitionally equal to s. */
    virtual bool is_def_eq(expr const & t, expr const & s, type_checker & c, delayed_justification & jst) {
        check_system("is_definitionally_equal");
        lbool r = quick_is_def_eq(t, s, c, jst);
        if (r != l_undef) return r == l_true;

        // apply whnf (without using delta-reduction or normalizer extensions)
        expr t_n = whnf_core(t, c);
        expr s_n = whnf_core(s, c);
        if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
            r = quick_is_def_eq(t_n, s_n, c, jst);
            if (r != l_undef) return r == l_true;
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
                    // If t_n and s_n are both applications of the same (non-opaque) definition,
                    // then we try to check if their arguments are definitionally equal.
                    // If they are, then t_n and s_n must be definitionally equal, and we can
                    // skip the delta-reduction step.
                    // We only apply the optimization if t_n and s_n do not contain metavariables.
                    // In this way we don't have to backtrack constraints if the optimization fail.
                    if (is_app(t_n) && is_app(s_n) &&
                        is_eqp(*d_t, *d_s) &&          // same definition
                        !has_metavar(t_n) &&
                        !has_metavar(s_n) &&
                        !is_opaque(*d_t) &&            // if d_t is opaque, we don't need to try this optimization
                        d_t->use_conv_opt() &&         // the flag use_conv_opt() can be used to disable this optimization
                        is_def_eq_args(t_n, s_n, c, jst)) {
                        return true;
                    }
                    t_n = whnf_core(unfold_names(t_n, d_t->get_weight() - 1), c);
                    s_n = whnf_core(unfold_names(s_n, d_s->get_weight() - 1), c);
                }
                r = quick_is_def_eq(t_n, s_n, c, jst);
                if (r != l_undef) return r == l_true;
            }
            // try normalizer extensions
            auto new_t_n = norm_ext(t_n, c);
            auto new_s_n = norm_ext(s_n, c);
            if (!new_t_n && !new_s_n)
                break; // t_n and s_n are in weak head normal form
            if (new_t_n)
                t_n = whnf_core(*new_t_n, c);
            if (new_s_n)
                s_n = whnf_core(*new_s_n, c);
            r = quick_is_def_eq(t_n, s_n, c, jst);
            if (r != l_undef) return r == l_true;
        }

        if (is_constant(t_n) && is_constant(s_n) && const_name(t_n) == const_name(s_n) &&
            is_def_eq(const_levels(t_n), const_levels(s_n), c, jst))
            return true;

        // At this point, t_n and s_n are in weak head normal form (modulo meta-variables and proof irrelevance)
        if (is_app(t_n) && is_app(s_n)) {
            type_checker::scope scope(c);
            buffer<expr> t_args;
            buffer<expr> s_args;
            expr t_fn = get_app_args(t_n, t_args);
            expr s_fn = get_app_args(s_n, s_args);
            if (is_def_eq(t_fn, s_fn, c, jst) && t_args.size() == s_args.size()) {
                unsigned i = 0;
                for (; i < t_args.size(); i++) {
                    if (!is_def_eq(t_args[i], s_args[i], c, jst))
                        break;
                }
                if (i == t_args.size()) {
                    scope.keep();
                    return true;
                }
            }
        }

        if (m_env.prop_proof_irrel()) {
            // Proof irrelevance support for Prop/Bool (aka Type.{0})
            type_checker::scope scope(c);
            expr t_type = infer_type(c, t);
            if (is_prop(t_type, c) && is_def_eq(t_type, infer_type(c, s), c, jst)) {
                scope.keep();
                return true;
            }
        }

        list<name> const & cls_proof_irrel = m_env.cls_proof_irrel();
        if (!is_nil(cls_proof_irrel)) {
            // Proof irrelevance support for classes
            type_checker::scope scope(c);
            expr t_type = whnf(infer_type(c, t), c);
            if (std::any_of(cls_proof_irrel.begin(), cls_proof_irrel.end(),
                            [&](name const & cls_name) { return is_app_of(t_type, cls_name); }) &&
                is_def_eq(t_type, infer_type(c, s), c, jst)) {
                scope.keep();
                return true;
            }
        }

        return false;
    }

    bool is_prop(expr const & e, type_checker & c) {
        return whnf(infer_type(c, e), c) == Bool;
    }
};

std::unique_ptr<converter> mk_default_converter(environment const & env, optional<module_idx> mod_idx,
                                                bool memoize, name_set const & extra_opaque) {
    return std::unique_ptr<converter>(new default_converter(env, mod_idx, memoize, extra_opaque));
}
}
