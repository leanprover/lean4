/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/num.h"

namespace lean {
static expr * g_num     = nullptr;
static expr * g_pos_num = nullptr;
static expr * g_zero    = nullptr;
static expr * g_pos     = nullptr;
static expr * g_one     = nullptr;
static expr * g_bit0    = nullptr;
static expr * g_bit1    = nullptr;

void initialize_num() {
    g_num = new expr(Const("num"));
    g_pos_num = new expr(Const("pos_num"));
    g_zero = new expr(Const({"num", "zero"}));
    g_pos = new expr(Const({"num", "pos"}));
    g_one = new expr(Const({"pos_num", "one"}));
    g_bit0 = new expr(Const({"pos_num", "bit0"}));
    g_bit1 = new expr(Const({"pos_num", "bit1"}));
}

void finalize_num() {
    delete g_num;
    delete g_pos_num;
    delete g_zero;
    delete g_pos;
    delete g_one;
    delete g_bit0;
    delete g_bit1;
}

bool has_num_decls(environment const & env) {
    try {
        type_checker tc(env);
        return
            tc.infer(*g_zero).first == *g_num &&
            tc.infer(*g_pos).first  == mk_arrow(*g_pos_num, *g_num) &&
            tc.infer(*g_one).first  == *g_pos_num &&
            tc.infer(*g_bit0).first == mk_arrow(*g_pos_num, *g_pos_num) &&
            tc.infer(*g_bit1).first == mk_arrow(*g_pos_num, *g_pos_num);
    } catch (exception&) {
        return false;
    }
}

expr from_pos_num(mpz const & n) {
    lean_assert(n > 0);
    if (n == 1)
        return *g_one;
    if (n % mpz(2) == 1)
        return mk_app(*g_bit1, from_pos_num(n / 2));
    else
        return mk_app(*g_bit0, from_pos_num(n / 2));
}

expr from_num(mpz const & n) {
    expr r;
    lean_assert(n >= 0);
    if (n == 0)
        r = *g_zero;
    else
        r = mk_app(*g_pos, from_pos_num(n));
    lean_assert(*to_num(r) == n);
    return r;
}

optional<mpz> to_pos_num(expr const & e) {
    if (e == *g_one) {
        return some(mpz(1));
    } else if (is_app(e)) {
        if (app_fn(e) == *g_bit0) {
            if (auto r = to_pos_num(app_arg(e)))
                return some(2*(*r));
        } else if (app_fn(e) == *g_bit1) {
            if (auto r = to_pos_num(app_arg(e)))
                return some(2*(*r) + 1);
        }
    }
    return optional<mpz>();
}

optional<mpz> to_num(expr const & e) {
    if (e == *g_zero)
        return some(mpz(0));
    else if (is_app(e) && app_fn(e) == *g_pos)
        return to_pos_num(app_arg(e));
    else
        return optional<mpz>();
}
}
