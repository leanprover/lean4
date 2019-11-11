/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/bin_app.h"

namespace lean {
bool is_bin_app(expr const & t, expr const & f) {
    return is_app(t) && is_app(app_fn(t)) && app_fn(app_fn(t)) == f;
}

bool is_bin_app(expr const & t, expr const & f, expr & lhs, expr & rhs) {
    if (is_bin_app(t, f)) {
        lhs = app_arg(app_fn(t));
        rhs = app_arg(t);
        return true;
    } else {
        return false;
    }
}

expr mk_bin_rop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return unit;
    } else {
        expr r = args[num_args - 1];
        unsigned i = num_args - 1;
        while (i > 0) {
            --i;
            r = mk_app(op, args[i], r);
        }
        return r;
    }
}
expr mk_bin_rop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_rop(op, unit, l.size(), l.begin());
}

expr mk_bin_lop(expr const & op, expr const & unit, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return unit;
    } else {
        expr r = args[0];
        for (unsigned i = 1; i < num_args; i++) {
            r = mk_app(op, r, args[i]);
        }
        return r;
    }
}
expr mk_bin_lop(expr const & op, expr const & unit, std::initializer_list<expr> const & l) {
    return mk_bin_lop(op, unit, l.size(), l.begin());
}
}
