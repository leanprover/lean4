/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/num.h"
#include "library/string.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/comp_val.h"
#include "library/expr_pair.h"
#include "library/trace.h"

/* Remark: we can improve performance by using Lean macros for delaying the
   proof construction. */

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
    auto pr = mk_nat_val_ne_proof(v_a, v_b);
    if (!pr) return none_expr();
    return some_expr(mk_app(mk_constant(get_fin_ne_of_vne_name()), n, a, b, *pr));
}

optional<expr> mk_char_mk_ne_proof(expr const & a, expr const & b) {
    if (!is_app_of(a, get_char_mk_name(), 2) ||
        !is_app_of(a, get_char_mk_name(), 2))
        return none_expr();
    expr const & v_a = app_arg(app_fn(a));
    expr const & v_b = app_arg(app_fn(b));
    auto pr = mk_nat_val_ne_proof(v_a, v_b);
    if (!pr) return none_expr();
    return some_expr(mk_app(mk_constant(get_char_ne_of_vne_name()), a, b, *pr));
}

static expr * g_d800   = nullptr;
static expr * g_dfff   = nullptr;
static expr * g_110000 = nullptr;

optional<expr> mk_is_valid_char_proof(expr const & v) {
    if (auto h = mk_nat_val_lt_proof(v, *g_d800)) {
        return some_expr(mk_app(mk_constant(get_is_valid_char_range_1_name()), v, *h));
    }

    if (auto h_1 = mk_nat_val_lt_proof(*g_dfff, v)) {
    if (auto h_2 = mk_nat_val_lt_proof(v, *g_110000)) {
        return some_expr(mk_app(mk_constant(get_is_valid_char_range_2_name()), v, *h_1, *h_2));
    }}

    return none_expr();
}

optional<expr> mk_char_val_ne_proof(expr const & a, expr const & b) {
    if (is_app_of(a, get_char_of_nat_name(), 1) &&
        is_app_of(a, get_char_of_nat_name(), 1)) {
        expr const & v_a = app_arg(a);
        expr const & v_b = app_arg(b);
        if (auto h_1 = mk_nat_val_ne_proof(v_a, v_b)) {
        if (auto h_2 = mk_is_valid_char_proof(v_a)) {
        if (auto h_3 = mk_is_valid_char_proof(v_b)) {
            return some_expr(mk_app({mk_constant(get_char_of_nat_ne_of_ne_name()), v_a, v_b, *h_1, *h_2, *h_3}));
        }}}
    }
    return mk_char_mk_ne_proof(a, b);
}

/* Remark: this function assumes 'e' has type string */
static bool is_string_str(expr const & e, expr & s, expr & c) {
    if (is_app_of(e, get_string_str_name(), 2)) {
        s = app_arg(app_fn(e));
        c = app_arg(e);
        return true;
    }
    return false;
}

/* Remark: this function assumes 'e' has type string */
static bool is_string_empty(expr const & e) {
    return is_constant(e, get_string_empty_name());
}

optional<expr> mk_string_val_ne_proof(expr a, expr b) {
    if (auto new_a = expand_string_macro(a))
        a = *new_a;
    if (auto new_b = expand_string_macro(b))
        b = *new_b;
    expr c_a, s_a;
    expr c_b, s_b;
    if (is_string_str(a, s_a, c_a)) {
        if (is_string_str(b, s_b, c_b)) {
            if (auto pr = mk_char_val_ne_proof(c_a, c_b)) {
                return some_expr(mk_app({mk_constant(get_string_str_ne_str_left_name()), c_a, c_b, s_a, s_b, *pr}));
            } else if (auto pr = mk_string_val_ne_proof(s_a, s_b)) {
                return some_expr(mk_app({mk_constant(get_string_str_ne_str_right_name()), c_a, c_b, s_a, s_b, *pr}));
            }
        } else if (is_string_empty(b)) {
            return some_expr(mk_app(mk_constant(get_string_str_ne_empty_name()), c_a, s_a));
        }
    } else if (is_string_empty(a)) {
        if (is_string_str(b, s_b, c_b)) {
            return some_expr(mk_app(mk_constant(get_string_empty_ne_str_name()), c_b, s_b));
        }
    }
    return none_expr();
}

optional<expr> mk_val_ne_proof(type_context_old & ctx, expr const & a, expr const & b) {
    expr type = ctx.infer(a);
    if (ctx.is_def_eq(type, mk_nat_type()))
        return mk_nat_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_constant(get_char_name())))
        return mk_char_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_constant(get_string_name())))
        return mk_string_val_ne_proof(a, b);
    return none_expr();
}

void initialize_comp_val() {
    g_d800   = new expr(to_nat_expr(mpz(0xd800)));
    g_dfff   = new expr(to_nat_expr(mpz(0xdfff)));
    g_110000 = new expr(to_nat_expr(mpz(0xd110000)));
}

void finalize_comp_val() {
    delete g_d800;
    delete g_dfff;
    delete g_110000;
}
}
