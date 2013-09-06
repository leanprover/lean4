/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "update_expr.h"
#include "buffer.h"

namespace lean {
expr update_app(expr const & app, unsigned i, expr const & new_arg) {
    if (is_eqp(arg(app, i), new_arg)) {
        return app;
    } else {
        buffer<expr> new_args;
        unsigned num = num_args(app);
        for (unsigned j = 0; j < num; j++) {
            if (i == j)
                new_args.push_back(new_arg);
            else
                new_args.push_back(arg(app, j));
        }
        return mk_app(new_args.size(), new_args.data());
    }
}

expr update_lambda(expr const & lambda, expr const & d, expr const & b) {
    if (is_eqp(abst_domain(lambda), d) && is_eqp(abst_body(lambda), b))
        return lambda;
    else
        return mk_lambda(abst_name(lambda), d, b);
}

expr update_pi(expr const & pi, expr const & d, expr const & b) {
    if (is_eqp(abst_domain(pi), d) && is_eqp(abst_body(pi), b))
        return pi;
    else
        return mk_pi(abst_name(pi), d, b);
}

expr update_let(expr const & let, expr const & t, expr const & v, expr const & b) {
    if (is_eqp(let_type(let), t) && is_eqp(let_value(let), v) && is_eqp(let_body(let), b))
        return let;
    else
        return mk_let(let_name(let), t, v, b);
}

expr update_eq(expr const & eq, expr const & l, expr const & r) {
    if (is_eqp(eq_lhs(eq), l) && is_eqp(eq_rhs(eq), r))
        return eq;
    else
        return mk_eq(l, r);
}
}
