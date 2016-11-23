/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/num.h"
#include "library/util.h"
#include "library/constants.h"

namespace lean {
optional<expr> mk_nat_val_ne_proof(expr const & a, expr const & b) {
    if (a == b) return none_expr();
    if (auto a1 = is_bit0(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_ne_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit0_ne_bit1_name()), *a1, *b1));
        } else if (is_zero(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, b))
                return some_expr(mk_app(mk_constant(get_nat_bit0_ne_zero_name()), *a1, *pr));
        } else if (is_one(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit0_ne_one_name()), *a1));
        }
    } else if (auto a1 = is_bit1(a)) {
        if (auto b1 = is_bit0(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit1_ne_bit0_name()), *a1, *b1));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit1_ne_name()), *a1, *b1, *pr));
        } else if (is_zero(b)) {
            return some_expr(mk_app(mk_constant(get_nat_bit1_ne_zero_name()), *a1));
        } else if (is_one(b)) {
            if (auto pr = mk_nat_val_ne_proof(*a1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_bit1_ne_one_name()), *a1, *pr));
        }
    } else if (is_zero(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, a))
                return some_expr(mk_app(mk_constant(get_nat_zero_ne_bit0_name()), *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            return some_expr(mk_app(mk_constant(get_nat_zero_ne_bit1_name()), *b1));
        } else if (is_one(b)) {
            return some_expr(mk_constant(get_nat_zero_ne_one_name()));
        }
    } else if (is_one(a)) {
        if (auto b1 = is_bit0(b)) {
            return some_expr(mk_app(mk_constant(get_nat_one_ne_bit0_name()), *b1));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_one_ne_bit1_name()), *b1, *pr));
        } else if (is_zero(b)) {
            return some_expr(mk_constant(get_nat_one_ne_zero_name()));
        }
    }
    return none_expr();
}

optional<expr> mk_nat_val_le_proof(expr const & a, expr const & b);

optional<expr> mk_nat_val_lt_proof(expr const & a, expr const & b) {
    if (a == b) return none_expr();
    if (auto a1 = is_bit0(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_lt_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_le_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_lt_bit1_name()), *a1, *b1, *pr));
        }
    } else if (auto a1 = is_bit1(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit1_lt_bit0_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit1_lt_name()), *a1, *b1, *pr));
        }
    } else if (is_zero(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, a))
                return some_expr(mk_app(mk_constant(get_nat_zero_lt_bit0_name()), *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            return some_expr(mk_app(mk_constant(get_nat_zero_lt_bit1_name()), *b1));
        } else if (is_one(b)) {
            return some_expr(mk_constant(get_nat_zero_lt_one_name()));
        }
    } else if (is_one(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_one_lt_bit0_name()), *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_ne_proof(*b1, mk_nat_zero()))
                return some_expr(mk_app(mk_constant(get_nat_one_lt_bit1_name()), *b1, *pr));
        }
    }
    return none_expr();
}

optional<expr> mk_nat_val_le_proof(expr const & a, expr const & b) {
    if (a == b)
        return some_expr(mk_app(mk_constant(get_nat_le_refl_name()), a));
    if (auto pr = mk_nat_val_lt_proof(a, b))
        return some_expr(mk_app(mk_constant(get_nat_le_of_lt_name()), a, b, *pr));
    return none_expr();
}

optional<expr> mk_fin_val_ne_proof(expr const & a, expr const & b) {
    if (!is_app_of(a, get_fin_mk_name(), 3) ||
        !is_app_of(b, get_fin_mk_name(), 3))
        return none_expr();
    expr const & n   = app_arg(app_fn(app_fn(a)));
    expr const & v_a = app_arg(app_fn(a));
    expr const & v_b = app_arg(app_fn(b));
    auto pr = mk_nat_val_lt_proof(v_a, v_b);
    if (!pr) return none_expr();
    return some_expr(mk_app(mk_constant(get_fin_ne_of_vne_name()), n, a, b, *pr));
}

static expr * g_char_sz = nullptr;

optional<expr> mk_char_val_ne_proof(expr const & a, expr const & b) {
    if (is_app_of(a, get_char_of_nat_name(), 1) &&
        is_app_of(a, get_char_of_nat_name(), 1)) {
        expr const & v_a = app_arg(a);
        expr const & v_b = app_arg(b);
        if (auto h_1 = mk_nat_val_ne_proof(v_a, v_b)) {
        if (auto h_2 = mk_nat_val_lt_proof(v_a, *g_char_sz)) {
        if (auto h_3 = mk_nat_val_lt_proof(v_b, *g_char_sz)) {
            return some_expr(mk_app({mk_constant(get_char_of_nat_ne_of_ne_name()), v_a, v_b, *h_1, *h_2, *h_3}));
        }}}
    }
    return mk_fin_val_ne_proof(a, b);
}

void initialize_comp_val() {
    g_char_sz = new expr(to_nat_expr(mpz(255)));
}

void finalize_comp_val() {
    delete g_char_sz;
}
}
