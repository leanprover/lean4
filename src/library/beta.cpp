/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "beta.h"
#include "instantiate.h"

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
}
