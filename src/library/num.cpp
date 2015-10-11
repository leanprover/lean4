/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "library/num.h"
#include "library/constants.h"

namespace lean {
bool has_num_decls(environment const & env) {
    return
        env.find(get_zero_name()) &&
        env.find(get_one_name()) &&
        env.find(get_bit0_name()) &&
        env.find(get_bit1_name());
}

static bool is_const_app(expr const & e, name const & n, unsigned nargs) {
    expr const & f = get_app_fn(e);
    return is_constant(f) && const_name(f) == n && get_app_num_args(e) == nargs;
}

bool is_zero(expr const & e) {
    return is_const_app(e, get_zero_name(), 2);
}

bool is_one(expr const & e) {
    return is_const_app(e, get_one_name(), 2);
}

optional<expr> is_bit0(expr const & e) {
    if (!is_const_app(e, get_bit0_name(), 3))
        return none_expr();
    return some_expr(app_arg(e));
}

optional<expr> is_bit1(expr const & e) {
    if (!is_const_app(e, get_bit1_name(), 4))
        return none_expr();
    return some_expr(app_arg(e));
}

static bool is_num(expr const & e, bool first) {
    if (is_zero(e))
        return first;
    else if (is_one(e))
        return true;
    else if (auto a = is_bit0(e))
        return is_num(*a, false);
    else if (auto a = is_bit1(e))
        return is_num(*a, false);
    else
        return false;
}

bool is_num(expr const & e) {
    return is_num(e, true);
}

static optional<mpz> to_num(expr const & e, bool first) {
    if (is_zero(e)) {
        return first ? some(mpz(0)) : optional<mpz>();
    } else if (is_one(e)) {
        return some(mpz(1));
    } else if (auto a = is_bit0(e)) {
        if (auto r = to_num(*a, false))
            return some(2*(*r));
    } else if (auto a = is_bit1(e)) {
        if (auto r = to_num(*a, false))
            return some(2*(*r)+1);
    }
    return optional<mpz>();
}

optional<mpz> to_num(expr const & e) {
    return to_num(e, true);
}

optional<mpz> to_pos_num(expr const & e) {
    if (is_constant(e, get_pos_num_one_name())) {
         return some(mpz(1));
    } else if (is_const_app(e, get_pos_num_bit0_name(), 1)) {
        if (auto r = to_pos_num(app_arg(e)))
            return some(2*(*r));
    } else if (is_const_app(e, get_pos_num_bit1_name(), 1)) {
        if (auto r = to_pos_num(app_arg(e)))
            return some(2*(*r) + 1);
    }
    return optional<mpz>();
}

optional<mpz> to_num_core(expr const & e) {
    if (is_constant(e, get_num_zero_name()))
        return some(mpz(0));
    else if (is_const_app(e, get_num_pos_name(), 1))
        return to_pos_num(app_arg(e));
    else
        return optional<mpz>();
}
}
