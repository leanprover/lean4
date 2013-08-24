/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "beta.h"
#include "instantiate.h"
#include "environment.h"

namespace lean {
bool is_head_beta(expr const & e) {
    return is_app(e) && is_lambda(arg(e, 0));
}
expr head_beta(expr const & e) {
    if (!is_head_beta(e)) {
        return e;
    } else {
        unsigned num  = num_args(e);
        unsigned num1 = num - 1;
        expr const * f = &arg(e, 0);
        lean_assert(is_lambda(*f));
        unsigned m = 1;
        while (is_lambda(abst_body(*f)) && m < num1) {
            f = &abst_body(*f);
            m++;
        }
        lean_assert(m <= num1);
        expr r = instantiate(abst_body(*f), m, &arg(e, 1));
        if (m == num1) {
            return r;
        } else {
            buffer<expr> args;
            args.push_back(r);
            m++;
            for (; m < num; m++)
                args.push_back(arg(e, m));
            return mk_app(args.size(), args.data());
        }
    }
}

expr head_reduce(expr const & e, environment const & env, name_set const * defs) {
    if (is_head_beta(e)) {
        return head_beta(e);
    } else if (is_let(e)) {
        return instantiate(let_body(e), let_value(e));
    } else if (is_constant(e)) {
        name const & n = const_name(e);
        if (defs == nullptr || defs->find(n) != defs->end()) {
            object const & obj = env.find_object(n);
            if (obj && obj.is_definition() && !obj.is_opaque())
                return obj.get_value();
        }
    }
    return e;
}
}
