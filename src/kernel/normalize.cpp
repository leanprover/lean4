/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "expr.h"
#include "context.h"
#include "environment.h"
#include "free_vars.h"
#include "list.h"
#include "buffer.h"
#include "trace.h"
#include "exception.h"

namespace lean {

class value;
typedef list<value> local_context;
enum class value_kind { Expr, Closure, BoundedVar };
class value {
    unsigned       m_kind:2;
    unsigned       m_bvar:30;
    expr           m_expr;
    local_context  m_ctx;
public:
    value() {}
    explicit value(expr const & e):m_kind(static_cast<unsigned>(value_kind::Expr)), m_expr(e) {}
    explicit value(unsigned k):m_kind(static_cast<unsigned>(value_kind::BoundedVar)), m_bvar(k) {}
    value(expr const & e, local_context const & c):
        m_kind(static_cast<unsigned>(value_kind::Closure)),
        m_expr(e),
        m_ctx(c) {
        lean_assert(is_lambda(e));
    }

    value_kind kind() const { return static_cast<value_kind>(m_kind); }

    bool is_expr() const        { return kind() == value_kind::Expr; }
    bool is_closure() const     { return kind() == value_kind::Closure; }
    bool is_bounded_var() const { return kind() == value_kind::BoundedVar; }

    expr const & get_expr() const         { lean_assert(is_expr() || is_closure()); return m_expr; }
    local_context const & get_ctx() const { lean_assert(is_closure());              return m_ctx; }
    unsigned get_var_idx() const          { lean_assert(is_bounded_var());          return m_bvar; }
};

value_kind            kind(value const & v)    { return v.kind(); }
expr const &          to_expr(value const & v) { return v.get_expr(); }
local_context const & ctx_of(value const & v)  { return v.get_ctx(); }
unsigned              to_bvar(value const & v) { return v.get_var_idx(); }

local_context extend(local_context const & c, value const & v) { return cons(v, c); }

class normalize_fn {
    environment const & m_env;
    context     const & m_ctx;

    value lookup(local_context const & c, unsigned i) {
        local_context const * it1 = &c;
        while (!is_nil(*it1)) {
            if (i == 0)
                return head(*it1);
            --i;
            it1 = &tail(*it1);
        }

        context const * it2 = &m_ctx;
        while (!is_nil(*it2)) {
            if (i == 0) {
                expr const & b = head(*it2).get_body();
                if (!is_null(b))
                    return value(b);
                else break;
            }
            --i;
            it2 = &tail(*it2);
        }
        throw exception("unknown free variable");
    }

    expr reify_closure(expr const & a, local_context const & c, unsigned k) {
        lean_assert(is_lambda(a));
        expr new_t = reify(normalize(abst_type(a), c, k), k);
        expr new_b = reify(normalize(abst_body(a), extend(c, value(k)), k+1), k+1);
        if (is_app(new_b)) {
            // (lambda (x:T) (app f ... (var 0)))
            // check eta-rule applicability
            unsigned n = num_args(new_b);
            if (is_var(arg(new_b, n - 1), 0) &&
                std::all_of(begin_args(new_b),
                            end_args(new_b) - 1,
                            [](expr const & arg) { return !has_free_var(arg, 0); })) {
                if (n == 2)
                    return lower_free_vars(arg(new_b, 0), 1);
                else
                    return lower_free_vars(app(n - 1, begin_args(new_b)), 1);
            }
            return lambda(abst_name(a), new_t, new_b);
        }
        else {
            return lambda(abst_name(a), new_t, new_b);
        }
    }

    expr reify(value const & v, unsigned k) {
        lean_trace("normalize", tout << "Reify kind: " << static_cast<unsigned>(v.kind()) << "\n";
                   if (v.is_bounded_var()) tout << "#" << to_bvar(v); else tout << to_expr(v); tout << "\n";);
        switch (v.kind()) {
        case value_kind::Expr:       return to_expr(v);
        case value_kind::BoundedVar: return var(k - to_bvar(v) - 1);
        case value_kind::Closure:    return reify_closure(to_expr(v), ctx_of(v), k);
        }
        lean_unreachable();
        return expr();
    }

    value normalize(expr const & a, local_context const & c, unsigned k) {
        lean_trace("normalize", tout << "Normalize, k: " << k << "\n" << a << "\n";);
        switch (a.kind()) {
        case expr_kind::Var:
            return lookup(c, var_idx(a));
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Numeral:
            return value(a);
        case expr_kind::App: {
            value f    = normalize(arg(a, 0), c, k);
            unsigned i = 1;
            unsigned n = num_args(a);
            while (true) {
                if (f.is_closure()) {
                    // beta reduction
                    expr const & fv = to_expr(f);
                    lean_trace("normalize", tout << "beta reduction...\n" << fv << "\n";);
                    local_context new_c = extend(ctx_of(f), normalize(arg(a, i), c, k));
                    f = normalize(abst_body(fv), new_c, k);
                    if (i == n - 1)
                        return f;
                    i++;
                }
                else {
                    // TODO: support for interpreted symbols
                    buffer<expr> new_args;
                    new_args.push_back(reify(f, k));
                    for (; i < n; i++)
                        new_args.push_back(reify(normalize(arg(a, i), c, k), k));
                    return value(app(new_args.size(), new_args.data()));
                }
            }
        }
        case expr_kind::Lambda:
            return value(a, c);
        case expr_kind::Pi: {
            expr new_t = reify(normalize(abst_type(a), c, k), k);
            expr new_b = reify(normalize(abst_body(a), extend(c, value(k)), k+1), k+1);
            return value(pi(abst_name(a), new_t, new_b));
        }}
        lean_unreachable();
        return value(a);
    }

public:
    normalize_fn(environment const & env, context const & ctx):
        m_env(env),
        m_ctx(ctx) {
    }

    expr operator()(expr const & e) {
        return reify(normalize(e, local_context(), 0), 0);
    }
};

expr normalize(expr const & e, environment const & env, context const & ctx) {
    return normalize_fn(env, ctx)(e);
}

}
