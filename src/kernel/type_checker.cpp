/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/max_sharing.h"

namespace lean {

/** \brief Auxiliary functional object used to implement type checker. */
struct type_checker::imp {
    environment           m_env;
    name_generator        m_gen;
    constraint_handler &  m_chandler;
    bool                  m_memoize;
    name_set              m_extra_opaque;
    max_sharing_fn        m_sharing;
    expr_map<expr>        m_cache;
    expr_map<expr>        m_whnf_cache;

    imp(environment const & env, name_generator const & g, constraint_handler & h, bool memoize, name_set const & extra_opaque):
        m_env(env), m_gen(g), m_chandler(h), m_memoize(memoize), m_extra_opaque(extra_opaque) {}

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

    bool check_memoized(expr const & e) const {
        return !m_memoize || m_sharing.already_processed(e);
    }

    /** \brief Weak head normal form core procedure. It does not perform delta reduction nor extensions. */
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
            auto it = m_whnf_cache.find(e);
            if (it != m_whnf_cache.end())
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
            m_whnf_cache.insert(mk_pair(e, r));
        return r;
    }

    /** \brief Expand \c e if it is non-opaque constant with weight >= w */
    expr unfold_name_core(expr e, unsigned w) {
        if (is_constant(e)) {
            if (auto d = m_env.find(const_name(e))) {
                if (d->is_definition() && !d->is_opaque() && d->get_weight() >= w && !m_extra_opaque.contains(d->get_name()))
                    return unfold_name_core(instantiate_params(d->get_value(), d->get_params(), const_level_params(e)), w);
            }
        }
        return e;
    }

    /**
       \brief Expand constants and application where the function is a constant.

       The unfolding is only performend if the constant corresponds to
       a non-opaque definition with weight >= w, and it is not in the
       set of extra_opaque constants.
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

};
}
