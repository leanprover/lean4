/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"

namespace lean {
static name g_tmp_prefix = name::mk_internal_unique_name();

class normalize_fn {
    type_checker   m_tc;
    name_generator m_ngen;

    expr normalize_binding(expr const & e) {
        expr d = normalize(binding_domain(e));
        expr l = mk_local(m_ngen.next(), binding_name(e), d);
        expr b = abstract(normalize(instantiate(binding_body(e), l)), l);
        return update_binding(e, d, b);
    }

    expr normalize_app(expr const & e) {
        buffer<expr> args;
        expr f = get_app_rev_args(e, args);
        for (expr & a : args)
            a = normalize(a);
        return mk_rev_app(f, args);
    }

    expr normalize(expr e) {
        e = m_tc.whnf(e);
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
    normalize_fn(environment const & env):m_tc(env), m_ngen(g_tmp_prefix) {}
    expr operator()(expr const & e) { return normalize(e); }
};

expr normalize(environment const & env, expr const & e) { return normalize_fn(env)(e); }
}
