/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "expr.h"
#include "list.h"
#include "buffer.h"
#include "trace.h"

namespace lean {

class value;
typedef list<value> context;
class value {
    expr    m_expr;
    context m_ctx;
public:
    value() {}
    explicit value(expr const & e):m_expr(e) {}
    value(expr const & e, context const & c):m_expr(e), m_ctx(c) {}

    expr const & get_expr() const { return m_expr; }
    context const & get_ctx() const { return m_ctx; }
};

expr const &    to_expr(value const & v) { return v.get_expr(); }
context const & ctx_of(value const & v) { return v.get_ctx(); }

bool lookup(context const & c, unsigned i, value & r) {
    context const * curr = &c;
    while (!is_nil(*curr)) {
        if (i == 0) {
            r = head(*curr);
            return !is_null(to_expr(r));
        }
        --i;
        curr = &tail(*curr);
    }
    return false;
}

context extend(context const & c, value const & v = value()) { return cons(v, c); }

value normalize(expr const & a, context const & c);
expr expand(value const & v);

expr expand(expr const & a, context const & c) {
    if (is_lambda(a)) {
        expr new_t = to_expr(normalize(abst_type(a), c));
        expr new_b = expand(normalize(abst_body(a), extend(c)));
        if (is_app(new_b)) {
            // (lambda (x:T) (app f ... (var 0)))
            // check eta-rule applicability
            unsigned n = num_args(new_b);
            lean_assert(n >= 2);
            expr const & last_arg = arg(new_b, n - 1);
            if (is_var(last_arg) && var_idx(last_arg) == 0) {
                // FIXME: I have to shift the variables in new_b
                if (n == 2)
                    return arg(new_b, 0);
                else
                    return app(n - 1, begin_args(new_b));
            }
        }
        return lambda(abst_name(a), new_t, new_b);
    }
    else {
        return a;
    }
}

expr expand(value const & v) {
    return expand(to_expr(v), ctx_of(v));
}

value normalize(expr const & a, context const & c) {
    lean_trace("normalize", tout << a << "\n";);
    switch (a.kind()) {
    case expr_kind::Var: {
        value r;
        if (lookup(c, var_idx(a), r))
            return r;
        else
            return value(a);
    }
    case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
        return value(a);
    case expr_kind::App: {
        value f    = normalize(arg(a, 0), c);
        unsigned i = 1;
        unsigned n = num_args(a);
        while (true) {
            expr const & fv = to_expr(f);
            lean_trace("normalize", tout << "fv: " << fv << "\ni: " << i << "\n";);
            switch (fv.kind()) {
            case expr_kind::Lambda: {
                // beta reduction
                value a_v = normalize(arg(a, i), c);
                f = normalize(abst_body(fv), extend(ctx_of(f), a_v));
                if (i == n - 1)
                    return f;
                i++;
                break;
            }
            default: {
                // TODO: support for interpreted symbols
                buffer<expr> new_args;
                new_args.push_back(fv);
                for (; i < n; i++)
                    new_args.push_back(expand(normalize(arg(a, i), c)));
                return value(app(new_args.size(), new_args.data()));
            }}
        }
    }
    case expr_kind::Lambda:
        return value(a, c);
    case expr_kind::Pi: {
        expr new_t = to_expr(normalize(abst_type(a), c));
        expr new_b = to_expr(normalize(abst_body(a), extend(c)));
        return value(pi(abst_name(a), new_t, new_b));
    }}
    return value(a);
}

expr normalize(expr const & e) {
    return expand(normalize(e, context()));
}
}
