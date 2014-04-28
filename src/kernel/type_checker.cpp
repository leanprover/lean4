/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/interrupt.h"
#include "util/lbool.h"
#include "util/flet.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/max_sharing.h"
#include "kernel/free_vars.h"
#include "kernel/metavar.h"
#include "kernel/error_msgs.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {
static name g_x_name("x");

no_constraints_allowed_exception::no_constraints_allowed_exception():exception("constraints are not allowed in this type checker") {}
exception * no_constraints_allowed_exception::clone() const { return new no_constraints_allowed_exception(); }
void no_constraints_allowed_exception::rethrow() const { throw *this; }

void no_constraint_handler::add_cnstr(constraint const &) {
    throw no_constraints_allowed_exception();
}

/** \brief Auxiliary functional object used to implement type checker. */
struct type_checker::imp {
    environment           m_env;
    name_generator        m_gen;
    constraint_handler &  m_chandler;
    optional<module_idx>  m_module_idx;
    bool                  m_memoize;
    name_set              m_extra_opaque;
    max_sharing_fn        m_sharing;
    expr_map<expr>        m_infer_type_cache;
    expr_map<expr>        m_whnf_core_cache;
    expr_map<expr>        m_whnf_cache;
    // The following mapping is used to store the relationship
    // between temporary expressions created during type checking and the original ones.
    // We need that to be able to produce error messages containing position information.
    expr_map<expr>        m_trace;

    imp(environment const & env, name_generator const & g, constraint_handler & h,
        optional<module_idx> mod_idx, bool memoize, name_set const & extra_opaque):
        m_env(env), m_gen(g), m_chandler(h), m_module_idx(mod_idx), m_memoize(memoize), m_extra_opaque(extra_opaque) {}

    class type_checker_context : public extension_context {
        imp & m_imp;
    public:
        type_checker_context(imp & i):m_imp(i) {}
        virtual environment const & env() const { return m_imp.m_env; }
        virtual expr whnf(expr const & e) { return m_imp.whnf(e); }
        virtual expr infer_type(expr const & e) { return m_imp.infer_type(e); }
        virtual name mk_fresh_name() { return m_imp.m_gen.next(); }
        virtual void add_cnstr(constraint const & c) { m_imp.add_cnstr(c); }
    };

    bool check_memoized(expr const & e) const { return !m_memoize || m_sharing.already_processed(e); }
    expr max_sharing(expr const & e) { return m_memoize ? m_sharing(e) : e; }
    expr instantiate(expr const & e, unsigned n, expr const * s) { return max_sharing(lean::instantiate(e, n, s)); }
    expr instantiate(expr const & e, expr const & s) { return max_sharing(lean::instantiate(e, s)); }
    expr mk_app(expr const & f, unsigned num, expr const * args) { return max_sharing(lean::mk_app(f, num, args)); }
    expr mk_app(expr const & f, expr const & a) { return max_sharing(lean::mk_app(f, a)); }
    expr mk_rev_app(expr const & f, unsigned num, expr const * args) { return max_sharing(lean::mk_rev_app(f, num, args)); }
    expr mk_app_vars(expr const & f, unsigned num) { return max_sharing(lean::mk_app_vars(f, num)); }
    optional<expr> expand_macro(expr const & m) {
        lean_assert(is_macro(m));
        type_checker_context ctx(*this);
        if (auto new_m = macro_def(m).expand(macro_num_args(m), macro_args(m), ctx))
            return some_expr(max_sharing(*new_m));
        else
            return none_expr();
    }
    expr instantiate_params(expr const & e, param_names const & ps, levels const & ls) {
        return max_sharing(lean::instantiate_params(e, ps, ls));
    }
    /** \brief Apply normalizer extensions to \c e. */
    optional<expr> norm_ext(expr const & e) {
        type_checker_context ctx(*this);
        if (auto new_e = m_env.norm_ext()(e, ctx))
            return some_expr(max_sharing(*new_e));
        else
            return none_expr();
    }

    /** \brief Add entry <tt>new_e -> old_e</tt> in the traceability mapping */
    void add_trace(expr const & old_e, expr const & new_e) {
        if (!is_eqp(old_e, new_e))
            m_trace.insert(mk_pair(new_e, old_e));
    }

    /** \brief Return the input (sub) expression that corresponds to the (temporary) expression \c e. */
    expr trace_back(expr e) const {
        while (true) {
            auto it = m_trace.find(e);
            if (it != m_trace.end())
                e = it->second;
            else
                return e;
        }
    }

    /** \brief Replace free variable \c 0 with \c s in \c e, and trace new sub-expressions created in the process. */
    expr instantiate_with_trace(expr const & e, expr const & s) {
        return lean::instantiate(e, s, [&](expr const & old_e, expr const & new_e) { add_trace(old_e, new_e); });
    }

    /**
        \brief Return the body of the given binder, where the free variable #0 is replaced with a fresh local constant.
        It also returns the fresh local constant.
     */
    std::pair<expr, expr> open_binder_body(expr const & e) {
        expr local     = mk_local(m_gen.next() + binder_name(e), binder_domain(e));
        return mk_pair(instantiate_with_trace(binder_body(e), local), local);
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
            if (auto m = expand_macro(e))
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
    expr whnf(expr e) {
        // check cache
        if (m_memoize) {
            e = max_sharing(e);
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

    /** \brief Object to simulate delayed justification creation. */
    class delayed_justification {
        optional<justification>        m_jst;
        std::function<justification()> m_mk;
    public:
        template<typename Mk> delayed_justification(Mk && mk):m_mk(mk) {}
        justification get() { if (!m_jst) { m_jst = m_mk(); } return *m_jst; }
    };

    /** \brief Eta-expand \c s and check if it is definitionally equal to \c t. */
    bool try_eta(expr const & t, expr const & s, delayed_justification & jst) {
        lean_assert(is_lambda(t));
        lean_assert(!is_lambda(s));
        expr t_s = whnf(infer_type(s));
        if (is_pi(t_s)) {
            // new_s := lambda x : domain(t_s), s x
            expr new_s = mk_lambda(m_gen.next(), binder_domain(t_s), mk_app(lift_free_vars(s, 1), mk_var(0)));
            return is_def_eq(t, new_s, jst);
        } else {
            return false;
        }
    }

    /**
        \brief Given lambda/Pi expressions \c t and \c s, return true iff \c t is convertible to \c s.

        The argument \c def_eq is used to decide whether the body of the binder is checked for
        definitional equality or convertability.

        If t and s are lambda expressions, then then t is convertible to s
           iff
        domain(t) is definitionally equal to domain(s)
        and
        body(t) is definitionally equal to body(s)

        For Pi expressions, it is slighly different.
        If t and s are Pi expressions, then then t is convertible to s
           iff
        domain(t) is definitionally equal to domain(s)
        and
        body(t) is convertible to body(s)
    */
    bool is_conv_binder(expr t, expr s, bool def_eq, delayed_justification & jst) {
        lean_assert(t.kind() == s.kind());
        lean_assert(is_binder(t));
        expr_kind k = t.kind();
        buffer<expr> subst;
        do {
            expr var_t_type = instantiate(binder_domain(t), subst.size(), subst.data());
            expr var_s_type = instantiate(binder_domain(s), subst.size(), subst.data());
            if (!is_def_eq(var_t_type, var_s_type, jst))
                return false;
            subst.push_back(mk_local(m_gen.next() + binder_name(s), var_s_type));
            t = binder_body(t);
            s = binder_body(s);
        } while (t.kind() == k && s.kind() == k);
        return is_conv(instantiate(t, subst.size(), subst.data()), instantiate(s, subst.size(), subst.data()), def_eq, jst);
    }

    /**
       \brief This is an auxiliary method for is_conv. It handles the "easy cases".

       If \c def_eq is true, then it checks for definitional equality.
    */
    lbool quick_is_conv(expr const & t, expr const & s, bool def_eq, delayed_justification & jst) {
        if (t == s)
            return l_true; // t and s are structurally equal
        if (is_meta(t) || is_meta(s)) {
            // if t or s is a metavariable (or the application of a metavariable), then add constraint
            if (def_eq)
                add_cnstr(mk_eq_cnstr(t, s, jst.get()));
            else
                add_cnstr(mk_conv_cnstr(t, s, jst.get()));
            return l_true;
        }
        if (t.kind() == s.kind()) {
            switch (t.kind()) {
            case expr_kind::Lambda:
                return to_lbool(is_conv_binder(t, s, true, jst));
            case expr_kind::Pi:
                return to_lbool(is_conv_binder(t, s, def_eq, jst));
            case expr_kind::Sort:
                // t and s are Sorts
                if (is_trivial(sort_level(t), sort_level(s)) && (!def_eq || is_trivial(sort_level(s), sort_level(t))))
                    return l_true;
                add_cnstr(mk_level_cnstr(sort_level(t), sort_level(s), jst.get()));
                if (def_eq)
                    add_cnstr(mk_level_cnstr(sort_level(s), sort_level(t), jst.get()));
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
    bool is_conv(expr const & t, expr const & s, bool def_eq, delayed_justification & jst) {
        check_system("is_convertible");
        lbool r = quick_is_conv(t, s, def_eq, jst);
        if (r != l_undef) return r == l_true;

        // apply whnf (without using delta-reduction or normalizer extensions)
        expr t_n = whnf_core(t);
        expr s_n = whnf_core(s);
        if (!is_eqp(t_n, t) || !is_eqp(s_n, s)) {
            r = quick_is_conv(t_n, s_n, def_eq, jst);
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
                r = quick_is_conv(t_n, s_n, def_eq, jst);
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
            r = quick_is_conv(t_n, s_n, def_eq, jst);
            if (r != l_undef) return r == l_true;
        }

        // At this point, t_n and s_n are in weak head normal form (modulo meta-variables)

        if (m_env.eta()) {
            lean_assert(!is_lambda(t_n) || !is_lambda(s_n));
            // Eta-reduction support
            if ((is_lambda(t_n) && try_eta(t_n, s_n, jst)) ||
                (is_lambda(s_n) && try_eta(s_n, t_n, jst)))
                return true;
        }

        if (is_app(t_n) && is_app(s_n)) {
            expr it1 = t_n;
            expr it2 = s_n;
            bool ok  = true;
            do {
                if (!is_def_eq(app_arg(it1), app_arg(it2), jst)) {
                    ok = false;
                    break;
                }
                it1 = app_fn(it1);
                it2 = app_fn(it2);
            } while (is_app(it1) && is_app(it2));
            if (ok && is_def_eq(it1, it2, jst))
                return true;
        }

        if (m_env.proof_irrel()) {
            // Proof irrelevance support
            expr t_type = infer_type(t);
            return is_prop(t_type) && is_def_eq(t_type, infer_type(s), jst);
        }

        return false;
    }

    /** \brief Return true iff \c t is convertible to s */
    bool is_conv(expr const & t, expr const & s, delayed_justification & jst) {
        return is_conv(t, s, false, jst);
    }

    /** \brief Return true iff \c t and \c s are definitionally equal */
    bool is_def_eq(expr const & t, expr const & s, delayed_justification & jst) {
        return is_conv(t, s, true, jst);
    }

    /** \brief Return true iff \c e is a proposition */
    bool is_prop(expr const & e) {
        return whnf(infer_type(e)) == Bool;
    }

    /**
       \brief Given a metavariable application ((?m t_1) ... t_k)
       Create a telescope with the types of t_1 ... t_k.
       If t_i is a local constant, then we abstract the occurrences of t_i in the types of t_{i+1} ... t_k.
       Return false if the telescope still contains local constants after the abstraction step.
    */
    bool meta_to_telescope(expr const & e, buffer<expr> & telescope) {
        lean_assert(is_meta(e));
        lean_assert(closed(e));
        buffer<optional<expr>> locals;
        return meta_to_telescope_core(e, telescope, locals);
    }

    /**
       \brief Auxiliary method for meta_to_telescope
    */
    bool meta_to_telescope_core(expr const & e, buffer<expr> & telescope, buffer<optional<expr>> & locals) {
        lean_assert(is_meta(e));
        if (is_app(e)) {
            if (!meta_to_telescope_core(app_fn(e), telescope, locals))
                return false;
            // infer type and abstract local constants
            unsigned n = locals.size();
            expr t = replace(infer_type(app_arg(e)),
                             [&](expr const & e, unsigned offset) -> optional<expr> {
                                 if (is_local(e)) {
                                     for (unsigned i = 0; i < n; i++) {
                                         if (locals[i] && is_eqp(*locals[i], e))
                                             return some_expr(mk_var(offset + n - i - 1));
                                     }
                                 }
                                 return none_expr();
                             });
            if (has_local(t))
                return false;
            telescope.push_back(t);
            if (is_local(e))
                locals.push_back(some_expr(e));
            else
                locals.push_back(none_expr());
        }
        return true;
    }

    /**
       \brief Make sure \c e "is" a sort, and return the corresponding sort.
       If \c e is not a sort, then the whnf procedure is invoked. Then, there are
       two options: the normalize \c e is a sort, or it is a meta. If it is a meta,
       a new constraint is created forcing it to be a sort.

       \remark \c s is used to extract position (line number information) when an
       error message is produced
    */
    expr ensure_sort(expr e, expr const & s) {
        if (is_sort(e))
            return e;
        e = whnf(e);
        if (is_sort(e)) {
            return e;
        } else if (is_meta(e)) {
            expr r = mk_sort(mk_meta_univ(m_gen.next()));
            justification j = mk_justification(trace_back(s),
                                               [=](formatter const & fmt, options const & o, substitution const & subst) {
                                                   return pp_type_expected(fmt, o, subst.instantiate_metavars_wo_jst(s));
                                               });
            add_cnstr(mk_eq_cnstr(e, r, j));
            return r;
        } else {
            throw_kernel_exception(m_env, trace_back(s),
                                   [=](formatter const & fmt, options const & o) { return pp_type_expected(fmt, o, s); });
        }
    }

    expr mk_tele_pi(buffer<expr> const & telescope, expr const & range) {
        expr r = range;
        unsigned i = telescope.size();
        while (i > 0) {
            --i;
            r = mk_pi(name(g_x_name, i), telescope[i], r);
        }
        return r;
    }

    /** \brief Similar to \c ensure_sort, but makes sure \c e "is" a Pi. */
    expr ensure_pi(expr e, expr const & s) {
        if (is_pi(e))
            return e;
        e = whnf(e);
        if (is_pi(e)) {
            return e;
        } else if (is_meta(e)) {
            buffer<expr> telescope;
            if (!meta_to_telescope(e, telescope))
                throw_kernel_exception(m_env, trace_back(s),
                                       [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, o, s); });
            expr ta    = mk_sort(mk_meta_univ(m_gen.next()));
            expr A     = mk_metavar(m_gen.next(), mk_tele_pi(telescope, ta));
            expr A_xs  = mk_app_vars(A, telescope.size());
            telescope.push_back(A_xs);
            expr tb    = mk_sort(mk_meta_univ(m_gen.next()));
            expr B     = mk_metavar(m_gen.next(), mk_tele_pi(telescope, tb));
            buffer<expr> args;
            get_app_args(e, args);
            expr A_args = mk_app(A, args.size(), args.data());
            args.push_back(Var(0));
            expr B_args = mk_app(B, args.size(), args.data());
            expr r      = mk_pi(g_x_name, A, B);
            justification j = mk_justification(trace_back(s),
                                               [=](formatter const & fmt, options const & o, substitution const & subst) {
                                                   return pp_function_expected(fmt, o, subst.instantiate_metavars_wo_jst(s));
                                               });
            add_cnstr(mk_eq_cnstr(e, r, j));
            return r;
        } else {
            throw_kernel_exception(m_env, trace_back(s),
                                   [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, o, s); });
        }
    }

    /** \brief Create a justification for the level constraint <tt>lhs <= rhs</tt> associated with constanc \c c. */
    justification mk_lvl_cnstr_jst(expr const & c, level const & lhs, level const & rhs) {
        lean_assert(is_constant(c));
        return mk_justification(trace_back(c),
                                [=](formatter const & fmt, options const & o, substitution const & subst) {
                                    return pp_def_lvl_cnstrs_satisfied(fmt, o,
                                                                       subst.instantiate_metavars_wo_jst(c),
                                                                       subst.instantiate_metavars_wo_jst(lhs),
                                                                       subst.instantiate_metavars_wo_jst(rhs));
                                });
    }

    /**
        \brief Create a justification for a application type mismatch,
        \c e is the application, \c fn_type and \c arg_type are the function and argument type.
    */
    justification mk_app_mismatch_jst(expr const & e, expr const & fn_type, expr const & arg_type) {
        lean_assert(is_app(e));
        return mk_justification(trace_back(e),
                                [=](formatter const & fmt, options const & o, substitution const & subst) {
                                    return pp_app_type_mismatch(fmt, o,
                                                                subst.instantiate_metavars_wo_jst(e),
                                                                subst.instantiate_metavars_wo_jst(binder_domain(fn_type)),
                                                                subst.instantiate_metavars_wo_jst(arg_type));
                                });
    }

    /**
        \brief Create a justification for a let definition type mismatch,
        \c e is the let expression, and \c val_type is the type inferred for the let value.
    */
    justification mk_let_mismatch_jst(expr const & e, expr const & val_type) {
        lean_assert(is_let(e));
        return mk_justification(trace_back(e),
                                [=](formatter const & fmt, options const & o, substitution const & subst) {
                                    return pp_def_type_mismatch(fmt, o, let_name(e),
                                                                subst.instantiate_metavars_wo_jst(let_type(e)),
                                                                subst.instantiate_metavars_wo_jst(val_type));
                                });
    }

    static constexpr char const * g_macro_error_msg = "failed to type check macro expansion";

    justification mk_macro_jst(expr const & e) {
        return mk_justification(trace_back(e),
                                [=](formatter const &, options const &, substitution const &) {
                                    return format(g_macro_error_msg);
                                });
    }

    /**
        \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.

        \pre closed(e)
    */
    expr infer_type_core(expr const & e, bool infer_only) {
        lean_assert(closed(e));
        check_system("type checker");

        bool shared = false;
        if (m_memoize && is_shared(e)) {
            shared = true;
            auto it = m_infer_type_cache.find(e);
            if (it != m_infer_type_cache.end())
                return it->second;
        }

        expr r;
        switch (e.kind()) {
        case expr_kind::Local: case expr_kind::Meta:
            r = mlocal_type(e);
            break;
        case expr_kind::Var:
            throw_kernel_exception(m_env, "type checker does not support free variables, replace them with local constants before invoking it");
        case expr_kind::Sort:
            r = mk_sort(mk_succ(sort_level(e)));
            break;
        case expr_kind::Constant: {
            definition d    = m_env.get(const_name(e));
            auto const & ps = d.get_params();
            auto const & ls = const_level_params(e);
            auto const & cs = d.get_level_cnstrs();
            if (!infer_only && !is_nil(cs)) {
                // add level constraints associated with the definition
                for (auto const & c : cs) {
                    level lhs = lean::instantiate(c.first,  ps, ls);
                    level rhs = lean::instantiate(c.second, ps, ls);
                    if (!is_trivial(lhs, rhs))
                        add_cnstr(mk_level_cnstr(lhs, rhs, mk_lvl_cnstr_jst(e, lhs, rhs)));
                }
            }
            r = instantiate_params(d.get_type(), ps, ls);
            break;
        }
        case expr_kind::Macro: {
            buffer<expr> arg_types;
            for (unsigned i = 0; i < macro_num_args(e); i++)
                arg_types.push_back(infer_type_core(macro_arg(e, i), infer_only));
            type_checker_context ctx(*this);
            r = macro_def(e).get_type(macro_num_args(e), macro_args(e), arg_types.data(), ctx);
            if (!infer_only && macro_def(e).trust_level() <= m_env.trust_lvl()) {
                optional<expr> m = expand_macro(e);
                if (!m)
                    throw_kernel_exception(m_env, "failed to expand macro", some_expr(e));
                expr t = infer_type_core(*m, infer_only);
                delayed_justification jst([=]() { return mk_macro_jst(e); });
                if (!is_def_eq(r, t, jst))
                    throw_kernel_exception(m_env, g_macro_error_msg, some_expr(e));
            }
            break;
        }
        case expr_kind::Lambda: {
            if (!infer_only) {
                expr t = infer_type_core(binder_domain(e), infer_only);
                ensure_sort(t, binder_domain(e));
            }
            auto b = open_binder_body(e);
            r = mk_pi(binder_name(e), binder_domain(e), abstract_p(infer_type_core(b.first, infer_only), b.second));
            break;
        }
        case expr_kind::Pi: {
            expr t1 = ensure_sort(infer_type_core(binder_domain(e), infer_only), binder_domain(e));
            auto b  = open_binder_body(e);
            expr t2 = ensure_sort(infer_type_core(b.first, infer_only), binder_body(e));
            r = mk_sort(mk_imax(sort_level(t1), sort_level(t2)));
            break;
        }
        case expr_kind::App: {
            expr f_type = ensure_pi(infer_type_core(app_fn(e), infer_only), app_fn(e));
            if (!infer_only) {
                expr a_type = infer_type_core(app_arg(e), infer_only);
                delayed_justification jst([=]() { return mk_app_mismatch_jst(e, f_type, a_type); });
                if (!is_conv(a_type, binder_domain(f_type), jst)) {
                    throw_kernel_exception(m_env, trace_back(e),
                                           [=](formatter const & fmt, options const & o) { return pp_app_type_mismatch(fmt, o, e, binder_domain(f_type), a_type); });
                }
            }
            r = instantiate(binder_body(f_type), app_arg(e));
            break;
        }
        case expr_kind::Let:
            if (!infer_only) {
                ensure_sort(infer_type_core(let_type(e), infer_only), let_type(e));
                expr val_type  = infer_type_core(let_value(e), infer_only);
                delayed_justification jst([=]() { return mk_let_mismatch_jst(e, val_type); });
                if (!is_conv(val_type, let_type(e), jst)) {
                    throw_kernel_exception(m_env, trace_back(e),
                                           [=](formatter const & fmt, options const & o) { return pp_def_type_mismatch(fmt, o, let_name(e), let_type(e), val_type); });
                }
            }
            r = infer_type_core(instantiate_with_trace(let_body(e), let_value(e)), infer_only);
            break;
        }

        if (m_memoize && shared)
            m_infer_type_cache.insert(mk_pair(e, r));

        return r;
    }

    expr infer_type(expr const & e) { return infer_type_core(e, true); }
    expr check(expr const & e) { return infer_type_core(e, false); }
    bool is_conv(expr const & t, expr const & s) {
        delayed_justification j([]() { return justification(); });
        return is_conv(t, s, j);
    }
    bool is_def_eq(expr const & t, expr const & s) {
        delayed_justification j([]() { return justification(); });
        return is_conv(t, s, j);
    }

};

no_constraint_handler g_no_constraint_handler;

type_checker::type_checker(environment const & env, name_generator const & g, constraint_handler & h,
                           optional<module_idx> mod_idx, bool memoize, name_set const & extra_opaque):
    m_ptr(new imp(env, g, h, mod_idx, memoize, extra_opaque)) {}

type_checker::type_checker(environment const & env, name_generator const & g,
                           optional<module_idx> mod_idx, bool memoize, name_set const & extra_opaque):
    type_checker(env, g, g_no_constraint_handler, mod_idx, memoize, extra_opaque) {}

type_checker::~type_checker() {}
expr type_checker::infer(expr const & t) { return m_ptr->infer_type(t); }
expr type_checker::check(expr const & t) { return m_ptr->check(t); }
bool type_checker::is_conv(expr const & t, expr const & s) { return m_ptr->is_conv(t, s); }
bool type_checker::is_def_eq(expr const & t, expr const & s) { return m_ptr->is_def_eq(t, s); }
bool type_checker::is_prop(expr const & t) { return m_ptr->is_prop(t); }
expr type_checker::whnf(expr const & t) { return m_ptr->whnf(t); }
expr type_checker::ensure_pi(expr const & t) { return m_ptr->ensure_pi(t, t); }
expr type_checker::ensure_sort(expr const & t) { return m_ptr->ensure_sort(t, t); }

static void check_no_metavar(environment const & env, expr const & e) {
    if (has_metavar(e))
        throw kernel_exception(env, "failed to add declaration to environment, it contains metavariables");
}

static void check_no_local(environment const & env, expr const & e) {
    if (has_local(e))
        throw kernel_exception(env, "failed to add declaration to environment, it contains local constants");
}

static void check_no_mlocal(environment const & env, expr const & e) {
    check_no_metavar(env, e);
    check_no_local(env, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw_already_declared(env, n);
}

struct simple_constraint_handler : public constraint_handler {
    std::vector<constraint> m_cnstrs;
    virtual void add_cnstr(constraint const & c) { m_cnstrs.push_back(c); }
};

certified_definition check(environment const & env, name_generator const & g, definition const & d, bool memoize, name_set const & extra_opaque) {
    check_no_mlocal(env, d.get_type());
    if (d.is_definition())
        check_no_mlocal(env, d.get_value());
    check_name(env, d.get_name());

    optional<module_idx> midx;
    if (!d.is_definition() || d.is_opaque())
        midx = optional<module_idx>(d.get_module_idx());

    simple_constraint_handler chandler;
    type_checker checker(env, g, chandler, midx, memoize, extra_opaque);

    checker.check(d.get_type());
    if (d.is_definition()) {
        expr val_type = checker.check(d.get_value());
        if (!checker.is_conv(val_type, d.get_type())) {
            throw_kernel_exception(env, d.get_value(),
                                   [=](formatter const & fmt, options const & o) { return pp_def_type_mismatch(fmt, o, d.get_name(), d.get_type(), val_type); });
        }
    }

    // TODO(Leo): solve universe level constraints

    return certified_definition(env.get_id(), d);
}
}
