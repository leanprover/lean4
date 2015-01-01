/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/name_generator.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"

namespace lean {
class normalize_fn {
    type_checker   &                  m_tc;
    name_generator                    m_ngen;
    std::function<bool(expr const &)> m_pred;  // NOLINT
    bool                              m_save_cnstrs;
    constraint_seq                    m_cnstrs;

    expr normalize_binding(expr const & e) {
        expr d = normalize(binding_domain(e));
        expr l = mk_local(m_ngen.next(), binding_name(e), d, binding_info(e));
        expr b = abstract(normalize(instantiate(binding_body(e), l)), l);
        return update_binding(e, d, b);
    }

    expr normalize_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args) {
            expr new_a = normalize(a);
            if (new_a != a)
                modified = true;
            a = new_a;
        }
        if (!modified)
            return e;
        expr r = mk_rev_app(f, args);
        if (is_constant(f) && inductive::is_elim_rule(m_tc.env(), const_name(f))) {
            return normalize(r);
        } else {
            return r;
        }
    }

    expr normalize(expr e) {
        check_system("normalize");
        if (!m_pred(e))
            return e;
        auto w = m_tc.whnf(e);
        e = w.first;
        if (m_save_cnstrs)
            m_cnstrs += w.second;
        switch (e.kind()) {
        case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
        case expr_kind::Meta: case expr_kind::Local: case expr_kind::Macro:
            return e;
        case expr_kind::Lambda: case expr_kind::Pi:
            return normalize_binding(e);
        case expr_kind::App:
            return normalize_app(e);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

public:
    normalize_fn(type_checker & tc, bool save = true):
        m_tc(tc), m_ngen(m_tc.mk_ngen()),
        m_pred([](expr const &) { return true; }),
        m_save_cnstrs(save) {}

    normalize_fn(type_checker & tc, std::function<bool(expr const &)> const & fn): // NOLINT
        m_tc(tc), m_ngen(m_tc.mk_ngen()),
        m_pred(fn), m_save_cnstrs(true) {}

    expr operator()(expr const & e) {
        m_cnstrs = constraint_seq();
        return normalize(e);
    }

    expr operator()(level_param_names const & ls, expr const & e) {
        m_cnstrs = constraint_seq();
        return m_tc.with_params(ls, [&]() {
                return normalize(e);
            });
    }

    constraint_seq get_cnstrs() const { return m_cnstrs; }
};

expr normalize(environment const & env, expr const & e) {
    auto tc          = mk_type_checker(env, true);
    bool save_cnstrs = false;
    return normalize_fn(*tc, save_cnstrs)(e);
}

expr normalize(environment const & env, level_param_names const & ls, expr const & e) {
    auto tc          = mk_type_checker(env, true);
    bool save_cnstrs = false;
    return normalize_fn(*tc, save_cnstrs)(ls, e);
}

expr normalize(type_checker & tc, expr const & e) {
    bool save_cnstrs = false;
    return normalize_fn(tc, save_cnstrs)(e);
}

expr normalize(type_checker & tc, expr const & e, constraint_seq & cs) {
    normalize_fn fn(tc);
    expr r = fn(e);
    cs += fn.get_cnstrs();
    return r;
}

expr normalize(type_checker & tc, expr const & e, std::function<bool(expr const &)> const & pred, // NOLINT
               constraint_seq & cs) {
    normalize_fn fn(tc, pred);
    expr r = fn(e);
    cs += fn.get_cnstrs();
    return r;
}
}
