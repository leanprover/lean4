/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/num.h"

namespace lean {
static expr g_num(Const({"num", "num"}));
static expr g_pos_num(Const({"num", "pos_num"}));
static expr g_zero(Const({"num", "zero"}));
static expr g_pos(Const({"num", "pos"}));
static expr g_one(Const({"num", "one"}));
static expr g_bit0(Const({"num", "bit0"}));
static expr g_bit1(Const({"num", "bit1"}));

bool has_num_decls(environment const & env) {
    try {
        type_checker tc(env);
        return
            tc.infer(g_zero) == g_num &&
            tc.infer(g_pos)  == mk_arrow(g_pos_num, g_num) &&
            tc.infer(g_one)  == g_pos_num &&
            tc.infer(g_bit0) == mk_arrow(g_pos_num, g_pos_num) &&
            tc.infer(g_bit1) == mk_arrow(g_pos_num, g_pos_num);
    } catch (...) {
        return false;
    }
}

expr from_pos_num(mpz const & n) {
    lean_assert(n > 0);
    if (n == 1)
        return g_one;
    if (n % mpz(2) == 1)
        return mk_app(g_bit1, from_pos_num(n / 2));
    else
        return mk_app(g_bit0, from_pos_num(n / 2));
}

expr from_num(mpz const & n) {
    expr r;
    lean_assert(n >= 0);
    if (n == 0)
        r = g_zero;
    else
        r = mk_app(g_pos, from_pos_num(n));
    lean_assert(*to_num(r) == n);
    return r;
}

optional<mpz> to_pos_num(expr const & e) {
    if (e == g_one) {
        return some(mpz(1));
    } else if (app_fn(e) == g_bit0) {
        if (auto r = to_pos_num(app_arg(e)))
            return some(2*(*r));
    } else if (app_fn(e) == g_bit1) {
        if (auto r = to_pos_num(app_arg(e)))
            return some(2*(*r) + 1);
    }
    return optional<mpz>();
}

optional<mpz> to_num(expr const & e) {
    if (e == g_zero)
        return some(mpz(0));
    else if (is_app(e) && app_fn(e) == g_pos)
        return to_pos_num(app_arg(e));
    else
        return optional<mpz>();
}
}
