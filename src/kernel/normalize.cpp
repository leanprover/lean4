/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "normalize.h"
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
typedef list<value> stack; //!< Normalization stack
enum class value_kind { Expr, Closure, BoundedVar };
class value {
    value_kind m_kind;
    unsigned   m_bvar;
    expr       m_expr;
    stack      m_ctx;
public:
    explicit value(expr const & e):m_kind(value_kind::Expr), m_expr(e) {}
    explicit value(unsigned k):m_kind(value_kind::BoundedVar), m_bvar(k) {}
    value(expr const & e, stack const & c):m_kind(value_kind::Closure), m_expr(e), m_ctx(c) { lean_assert(is_lambda(e)); }

    value_kind kind() const { return m_kind; }

    bool is_expr() const        { return kind() == value_kind::Expr; }
    bool is_closure() const     { return kind() == value_kind::Closure; }
    bool is_bounded_var() const { return kind() == value_kind::BoundedVar; }

    expr  const & get_expr() const { lean_assert(is_expr() || is_closure()); return m_expr; }
    stack const & get_ctx()  const { lean_assert(is_closure());              return m_ctx; }
    unsigned get_var_idx()   const { lean_assert(is_bounded_var());          return m_bvar; }
};

value_kind    kind(value const & v)     { return v.kind(); }
expr const &  to_expr(value const & v)  { return v.get_expr(); }
stack const & stack_of(value const & v) { return v.get_ctx(); }
unsigned      to_bvar(value const & v)  { return v.get_var_idx(); }

stack extend(stack const & s, value const & v) { return cons(v, s); }

class normalize_fn {
    environment const & m_env;
    context     const & m_ctx;

    value lookup(stack const & s, unsigned i, unsigned k) {
        unsigned j = i;
        stack const * it1 = &s;
        while (*it1) {
            if (j == 0)
                return head(*it1);
            --j;
            it1 = &tail(*it1);
        }
        context const & c = ::lean::lookup(m_ctx, j);
        if (c) {
            context_entry const & entry = head(c);
            if (entry.get_body())
                return value(::lean::normalize(entry.get_body(), m_env, tail(c)));
            else
                return value(length(c) - 1);
        }
        throw exception("unknown free variable");
    }

    expr reify_closure(expr const & a, stack const & c, unsigned k) {
        lean_assert(is_lambda(a));
        expr new_t = reify(normalize(abst_type(a), c, k), k);
        expr new_b = reify(normalize(abst_body(a), extend(c, value(k)), k+1), k+1);
        return lambda(abst_name(a), new_t, new_b);
#if 0
        // Eta-reduction + Cumulativity + Set theoretic interpretation is unsound.
        // Example:
        //   f : (Type 2) -> (Type 2)
        //   (lambda (x : (Type 1)) (f x)) : (Type 1) -> (Type 2)
        // The domains of these two terms are different. So, they must have different denotations.
        // However, by eta-reduction, we have:
        //     (lambda (x : (Type 1)) (f x)) == f
        // For now, we will disable it.
        // REMARK: we can workaround this problem by applying only when the domain of f is equal
        // to the domain of the lambda abstraction.
        //
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
        } else {
            return lambda(abst_name(a), new_t, new_b);
        }
#endif
    }

    expr reify(value const & v, unsigned k) {
        lean_trace("normalize", tout << "Reify kind: " << static_cast<unsigned>(v.kind()) << "\n";
                   if (v.is_bounded_var()) tout << "#" << to_bvar(v); else tout << to_expr(v); tout << "\n";);
        switch (v.kind()) {
        case value_kind::Expr:       return to_expr(v);
        case value_kind::BoundedVar: return var(k - to_bvar(v) - 1);
        case value_kind::Closure:    return reify_closure(to_expr(v), stack_of(v), k);
        }
        lean_unreachable();
        return expr();
    }

    value normalize(expr const & a, stack const & c, unsigned k) {
        lean_trace("normalize", tout << "Normalize, k: " << k << "\n" << a << "\n";);
        switch (a.kind()) {
        case expr_kind::Var:
            return lookup(c, var_idx(a), k);
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
                    stack new_c = extend(stack_of(f), normalize(arg(a, i), c, k));
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
        unsigned k = length(m_ctx);
        return reify(normalize(e, stack(), k), k);
    }

    expr operator()(expr const & e, expr const & v) {
        unsigned k = length(m_ctx);
        stack s = extend(stack(), normalize(v, stack(), k));
        return reify(normalize(e, s, k+1), k+1);
    }
};

expr normalize(expr const & e, environment const & env, context const & ctx) {
    return normalize_fn(env, ctx)(e);
}
expr normalize(expr const & e, environment const & env, context const & ctx, expr const & v) {
    return normalize_fn(env, ctx)(e, v);
}
}
