/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_set.h"
#include "kernel/context.h"
#include "kernel/instantiate.h"
#include "kernel/environment.h"
#include "kernel/free_vars.h"
#include "library/update_expr.h"

namespace lean {
bool is_head_beta(expr const & t) {
    return is_app(t) && is_lambda(arg(t, 0));
}
expr head_beta_reduce(expr const & t) {
    if (!is_head_beta(t)) {
        return t;
    } else {
        unsigned num  = num_args(t);
        unsigned num1 = num - 1;
        expr const * f = &arg(t, 0);
        lean_assert(is_lambda(*f));
        unsigned m = 1;
        while (is_lambda(abst_body(*f)) && m < num1) {
            f = &abst_body(*f);
            m++;
        }
        lean_assert(m <= num1);
        expr r = instantiate(abst_body(*f), m, &arg(t, 1));
        if (m == num1) {
            return r;
        } else {
            buffer<expr> args;
            args.push_back(r);
            m++;
            for (; m < num; m++)
                args.push_back(arg(t, m));
            return mk_app(args.size(), args.data());
        }
    }
}

expr head_reduce(expr const & t, environment const & e, context const & c, name_set const * defs) {
    if (is_head_beta(t)) {
        return head_beta_reduce(t);
    } else if (is_app(t)) {
        expr f     = arg(t, 0);
        if (is_head_beta(f) || is_let(f) || is_constant(f) || is_var(f)) {
            expr new_f = head_reduce(f, e, c, defs);
            if (!is_eqp(f, new_f))
                return update_app(t, 0, new_f);
            else
                return t;
        } else {
            return t;
        }
    } else if (is_var(t)) {
        auto p = lookup_ext(c, var_idx(t));
        context_entry const & ce = p.first;
        if (ce.get_body()) {
            return lift_free_vars(ce.get_body(), c.size() - p.second.size());
        } else {
            return t;
        }
    } else if (is_let(t)) {
        return instantiate(let_body(t), let_value(t));
    } else if (is_constant(t)) {
        name const & n = const_name(t);
        if (defs == nullptr || defs->find(n) != defs->end()) {
            object const & obj = e.find_object(n);
            if (obj && obj.is_definition() && !obj.is_opaque())
                return obj.get_value();
        }
    }
    return t;
}
}
