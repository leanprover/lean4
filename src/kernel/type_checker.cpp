/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/lbool.h"
#include "util/flet.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/max_sharing.h"
#include "kernel/free_vars.h"

namespace lean {
/** \brief Auxiliary functional object used to implement type checker. */
struct type_checker::imp {
    environment           m_env;
    name_generator        m_gen;
    constraint_handler &  m_chandler;
    optional<module_idx>  m_module_idx;
    bool                  m_memoize;
    name_set              m_extra_opaque;
    max_sharing_fn        m_sharing;
    expr_map<expr>        m_cache;
    expr_map<expr>        m_whnf_core_cache;
    expr_map<expr>        m_whnf_cache;

    imp(environment const & env, name_generator const & g, constraint_handler & h,
        optional<module_idx> mod_idx, bool memoize, name_set const & extra_opaque):
        m_env(env), m_gen(g), m_chandler(h), m_module_idx(mod_idx), m_memoize(memoize), m_extra_opaque(extra_opaque) {}

    class normalizer_context : public normalizer_extension::context {
        imp & m_imp;
    public:
        normalizer_context(imp & i):m_imp(i) {}
        virtual environment const & env() const { return m_imp.m_env; }
        virtual expr whnf(expr const & e) { return m_imp.whnf(e); }
        virtual expr infer_type(expr const & e) { return m_imp.infer_type(e); }
        virtual name mk_fresh_name() { return m_imp.m_gen.next(); }
        virtual void add_cnstr(constraint const & c) { m_imp.add_cnstr(c); }
    };

    expr max_sharing(expr const & e) { return m_memoize ? m_sharing(e) : e; }
    expr instantiate(expr const & e, unsigned n, expr const * s) { return max_sharing(lean::instantiate(e, n, s)); }
    expr instantiate(expr const & e, expr const & s) { return max_sharing(lean::instantiate(e, s)); }
    expr mk_rev_app(expr const & f, unsigned num, expr const * args) { return max_sharing(lean::mk_rev_app(f, num, args)); }
    optional<expr> expand_macro(expr const & m, unsigned num, expr const * args) {
        lean_assert(is_macro(m));
        if (auto new_m = to_macro(m).expand(num, args))
            return some_expr(max_sharing(*new_m));
        else
            return none_expr();
    }
    expr instantiate_params(expr const & e, param_names const & ps, levels const & ls) {
        return max_sharing(lean::instantiate_params(e, ps, ls));
    }
    /** \brief Apply normalizer extensions to \c e. */
    optional<expr> norm_ext(expr const & e) {
        normalizer_context ctx(*this);
        if (auto new_e = m_env.norm_ext()(e, ctx))
            return some_expr(max_sharing(*new_e));
        else
            return none_expr();
    }

    bool check_memoized(expr const & e) const {
        return !m_memoize || m_sharing.already_processed(e);
    }

    /** \brief Weak head normal form core procedure. It does not perform delta reduction nor normalization extensions. */
    expr whnf_core(expr const & e) {
        check_system("whnf");
        lean_assert(check_memoized(e));

        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Var:    case expr_kind::Sort: case expr_kind::Meta: case expr_kind::Local:
        case expr_kind::Lambda: case expr_kind::Pi:   case expr_kind::Constant:
            return e;
        case expr_kind::Macro:  case expr_kind::Let:  case expr_kind::App:
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
        case expr_kind::Lambda: case expr_kind::Pi:   case expr_kind::Constant:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Macro:
            if (auto m = expand_macro(e, 0, 0))
                r = whnf_core(*m);
            else
                r = e;
            break;
        case expr_kind::Let:
            r = whnf_core(instantiate(let_body(e), let_value(e)));
            break;
        case expr_kind::App: {
            buffer<expr> args;
            expr const * it = &e;
            while (is_app(*it)) {
                args.push_back(app_arg(*it));
                it = &(app_fn(*it));
            }
            expr f = whnf_core(*it);
            if (is_lambda(f)) {
                unsigned m = 1;
                unsigned num_args = args.size();
                while (is_lambda(binder_body(f)) && m < num_args) {
                    f = binder_body(f);
                    m++;
                }
                lean_assert(m <= num_args);
                r = whnf_core(mk_rev_app(instantiate(binder_body(f), m, args.data() + (num_args - m)), num_args - m, args.data()));
                break;
            } else if (is_macro(f)) {
                auto m = expand_macro(f, args.size(), args.data());
                if (m) {
                    r = whnf_core(*m);
                    break;
                }
            }
            r = is_eqp(f, *it) ? e : mk_rev_app(f, args.size(), args.data());
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
    bool is_opaque(definition const & d) const {
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
                    return unfold_name_core(instantiate_params(d->get_value(), d->get_params(), const_level_params(e)), w);
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
            expr const * it = &e;
            while (is_app(*it)) {
                it = &(app_fn(*it));
            }
            expr f = unfold_name_core(*it, w);
            if (is_eqp(f, *it)) {
                return e;
            } else {
                buffer<expr> args;
                expr const * it = &e;
                while (is_app(*it)) {
                    args.push_back(app_arg(*it));
                    it = &(app_fn(*it));
                }
                return mk_rev_app(f, args.size(), args.data());
            }
        } else {
            return unfold_name_core(e, w);
        }
    }

    /** \brief Auxiliary method for \c is_delta */
    optional<definition> is_delta_core(expr const & e) {
        if (is_constant(e)) {
            if (auto d = m_env.find(const_name(e)))
                if (d->is_definition() && !is_opaque(*d))
                    return d;
        }
        return none_definition();
    }

    /**
        \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
        to be expanded.
    */
    optional<definition> is_delta(expr const & e) {
        if (is_app(e)) {
            expr const * it = &e;
            while (is_app(*it)) {
                it = &(app_fn(*it));
            }
            return is_delta_core(*it);
        } else {
            return is_delta_core(e);
        }
    }

    /**
        \brief Weak head normal form core procedure that perform delta reduction for non-opaque constants with
        weight greater than or equal to \c w.

        This method is based on <tt>whnf_core(expr const &)</tt> and \c unfold_names.

        \remark This method does not use normalization extensions attached in the environment.
    */
    expr whnf_core(expr e, unsigned w) {
        while (true) {
            expr new_e = unfold_names(whnf_core(e), w);
            if (is_eqp(e, new_e))
                return e;
            e = new_e;
        }
    }

    /** \brief Put expression \c e in weak head normal form */
    expr whnf(expr const & e) {
        // check cache
        if (m_memoize) {
            auto it = m_whnf_cache.find(e);
            if (it != m_whnf_cache.end())
                return it->second;
        }

        expr t = e;
        while (true) {
            expr t1 = unfold_names(whnf_core(t), 0);
            auto new_t = norm_ext(t1);
            if (new_t) {
                t = *new_t;
            } else {
                if (m_memoize)
                    m_whnf_cache.insert(mk_pair(e, t1));
                return t1;
            }
        }
    }

    /** \brief Add given constraint to the constraint handler m_chandler. */
    void add_cnstr(constraint const & c) {
        m_chandler.add_cnstr(c);
    }

    /** \brief Return the current/latest justification object created by the type checker. */
    justification get_curr_justification() {
        // TODO(Leo)
        return mk_assumption_justification(0);
    }

    /** \brief Eta-expand \c s and check if it is definitionally equal to \c t. */
    bool try_eta(expr const & t, expr const & s) {
        lean_assert(is_lambda(t));
        lean_assert(!is_lambda(s));
        expr t_s = whnf(infer_type(s));
        if (is_pi(t_s)) {
            // new_s := lambda x : domain(t_s), s x
            expr new_s = mk_lambda(m_gen.next(), binder_domain(t_s), mk_app(lift_free_vars(s, 1), mk_var(0)));
            return is_def_eq(t, new_s);
        } else {
            return false;
        }
    }

    /**
       \brief This is an auxiliary method for is_conv. It handles the "easy cases".

       If \c def_eq is true, then it checks for definitional equality.
    */
    lbool quick_is_conv(expr const & t, expr const & s, bool def_eq) {
        if (t == s)
            return l_true; // t and s are structurally equal
        if (is_meta(t) || is_meta(s)) {
            // if t or s is a metavariable (or the application of a metavariable), then add constraint
            if (def_eq)
                add_cnstr(mk_eq_cnstr(t, s, get_curr_justification()));
            else
                add_cnstr(mk_conv_cnstr(t, s, get_curr_justification()));
            return l_true;
        }
        if (t.kind() == s.kind()) {
            switch (t.kind()) {
            case expr_kind::Lambda:
                // t and s are lambda expression, then then t is convertible to s
                // iff
                // domain(t) is definitionally equal to domain(s)
                // and
                // body(t) is definitionally equal to body(s)
                return to_lbool(is_def_eq(binder_domain(t), binder_domain(s)) && is_def_eq(binder_body(t), binder_body(s)));
            case expr_kind::Pi:
                // t and s are Pi expressions, then then t is convertible to s
                // iff
                // domain(t) is definitionally equal to domain(s)
                // and
                // body(t) is convertible to body(s)
                return to_lbool(is_def_eq(binder_domain(t), binder_domain(s)) && is_conv(binder_body(t), binder_body(s), def_eq));
            case expr_kind::Sort:
                // t and s are Sorts
                if (is_trivial(sort_level(t), sort_level(s)) && (!def_eq || is_trivial(sort_level(s), sort_level(t))))
                    return l_true;
                add_cnstr(mk_level_cnstr(sort_level(t), sort_level(s), get_curr_justification()));
                if (def_eq)
                    add_cnstr(mk_level_cnstr(sort_level(s), sort_level(t), get_curr_justification()));
                return l_true;
            case expr_kind::Meta:
                lean_unreachable(); // LCOV_EXCL_LINE
            case expr_kind::Var: case expr_kind::Local: case expr_kind::App:
            case expr_kind::Constant: case expr_kind::Macro:  case expr_kind::Let:
                // We do not handle these cases in this method.
                break;
            }
        }
        return l_undef; // This is not an "easy case"
    }

    /**
        \brief If def_eq is false, then return true iff t is convertible to s.
               If def_eq is true,  then return true iff t is definitionally equal to s.
    */
    bool is_conv(expr const & t, expr const & s, bool def_eq) {
        check_system("is_convertible");
        lbool r = quick_is_conv(t, s, def_eq);
        if (r != l_undef) return r == l_true;

        // apply whnf (without using delta-reduction or normalizer extensions)
        expr t_n = whnf_core(t);
        expr s_n = whnf_core(s);
        if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
            r = quick_is_conv(t_n, s_n, def_eq);
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
                        // try backtracking trick to avoild delta-reduction
                        // TODO(Leo)
                    }
                    t_n = whnf_core(unfold_names(t_n, d_t->get_weight() - 1));
                    s_n = whnf_core(unfold_names(s_n, d_s->get_weight() - 1));
                }
                r = quick_is_conv(t_n, s_n, def_eq);
                if (r != l_undef) return r == l_true;
            }
            // try normalizer extensions
            auto new_t_n = norm_ext(t_n);
            auto new_s_n = norm_ext(s_n);
            if (!new_t_n && !new_s_n)
                break; // t_n and s_n are in weak head normal form
            if (new_t_n)
                t_n = whnf_core(*new_t_n);
            if (new_s_n)
                s_n = whnf_core(*new_s_n);
            r = quick_is_conv(t_n, s_n, def_eq);
            if (r != l_undef) return r == l_true;
        }

        // At this point, t_n and s_n are in weak head normal form (modulo meta-variables)

        if (m_env.eta()) {
            lean_assert(!is_lambda(t_n) || !is_lambda(s_n));
            // Eta-reduction support
            if ((is_lambda(t_n) && try_eta(t_n, s_n)) ||
                (is_lambda(s_n) && try_eta(s_n, t_n)))
                return true;
        }

        if (is_app(t_n) && is_app(s_n)) {
            expr it1 = t_n;
            expr it2 = s_n;
            bool ok  = true;
            do {
                if (!is_def_eq(app_arg(it1), app_arg(it2))) {
                    ok = false;
                    break;
                }
                it1 = app_fn(it1);
                it2 = app_fn(it2);
            } while (is_app(it1) && is_app(it2));
            if (ok && is_def_eq(it1, it2))
                return true;
        }

        if (m_env.proof_irrel()) {
            // Proof irrelevance support
            expr t_type = infer_type(t);
            return is_proposition(t_type) && is_def_eq(t_type, infer_type(s));
        }

        return false;
    }

    /** \brief Return true iff \c t and \c s are definitionally equal */
    bool is_def_eq(expr const & t, expr const & s) {
        return is_conv(t, s, true);
    }

    /** \brief Return true iff \c e is a proposition */
    bool is_proposition(expr const & e) {
        return whnf(infer_type(e)) == Bool;
    }

    expr infer_type(expr const &) {
        // TODO(Leo)
        return expr();
    }
};
}
