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

optional<expr> mk_int_val_nonneg_proof(expr const & a) {
    if (auto a1 = is_bit0(a)) {
        if (auto pr = mk_int_val_nonneg_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit0_nonneg_name()), *a1, *pr));
    } else if (auto a1 = is_bit1(a)) {
        if (auto pr = mk_int_val_nonneg_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit1_nonneg_name()), *a1, *pr));
    } else if (is_one(a)) {
        return some_expr(mk_constant(get_int_one_nonneg_name()));
    } else if (is_zero(a)) {
        return some_expr(mk_constant(get_int_zero_nonneg_name()));
    }
    return none_expr();
}

optional<expr> mk_int_val_pos_proof(expr const & a) {
    if (auto a1 = is_bit0(a)) {
        if (auto pr = mk_int_val_pos_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit0_pos_name()), *a1, *pr));
    } else if (auto a1 = is_bit1(a)) {
        if (auto pr = mk_int_val_nonneg_proof(*a1))
            return some_expr(mk_app(mk_constant(get_int_bit1_pos_name()), *a1, *pr));
    } else if (is_one(a)) {
        return some_expr(mk_constant(get_int_one_pos_name()));
    }
    return none_expr();
}

/* Given a nonnegative int numeral a, return a pair (n, H)
   where n is a nat numeral, and (H : nat_abs a = n) */
optional<expr_pair> mk_nat_abs_eq(expr const & a) {
    if (is_zero(a)) {
        return optional<expr_pair>(mk_pair(mk_nat_zero(), mk_constant(get_int_nat_abs_zero_name())));
    } else if (is_one(a)) {
        return optional<expr_pair>(mk_pair(mk_nat_one(), mk_constant(get_int_nat_abs_one_name())));
    } else if (auto a1 = is_bit0(a)) {
        if (auto p = mk_nat_abs_eq(*a1))
            return optional<expr_pair>(mk_pair(mk_nat_bit0(p->first),
                                               mk_app(mk_constant(get_int_nat_abs_bit0_step_name()), *a1, p->first, p->second)));
    } else if (auto a1 = is_bit1(a)) {
        if (auto p = mk_nat_abs_eq(*a1)) {
            expr new_n   = mk_nat_bit1(p->first);
            expr Hnonneg = *mk_int_val_nonneg_proof(*a1);
            expr new_H   = mk_app(mk_constant(get_int_nat_abs_bit1_nonneg_step_name()), *a1, p->first, Hnonneg, p->second);
            return optional<expr_pair>(mk_pair(new_n, new_H));
        }
    }
    return optional<expr_pair>();
}

/* Given nonneg int numerals a and b, create a proof for a != b IF they are not equal. */
optional<expr> mk_int_nonneg_val_ne_proof(expr const & a, expr const & b) {
    auto p1 = mk_nat_abs_eq(a);
    if (!p1) return none_expr();
    auto p2 = mk_nat_abs_eq(b);
    if (!p2) return none_expr();
    auto Ha_nonneg = mk_int_val_nonneg_proof(a);
    if (!Ha_nonneg) return none_expr();
    auto Hb_nonneg = mk_int_val_nonneg_proof(b);
    if (!Hb_nonneg) return none_expr();
    auto H_nat_ne  = mk_nat_val_ne_proof(p1->first, p2->first);
    if (!H_nat_ne) return none_expr();
    expr H = mk_app({mk_constant(get_int_ne_of_nat_ne_nonneg_case_name()), a, b, p1->first, p2->first,
                *Ha_nonneg, *Hb_nonneg, p1->second, p2->second, *H_nat_ne});
    return some_expr(H);
}

optional<expr> mk_int_val_ne_proof(expr const & a, expr const & b) {
    if (auto a1 = is_neg(a)) {
        if (auto b1 = is_neg(b)) {
            auto H = mk_int_nonneg_val_ne_proof(*a1, *b1);
            if (!H) return none_expr();
            return some_expr(mk_app(mk_constant(get_int_ne_neg_of_ne_name()), *a1, *b1, *H));
        } else {
            if (is_zero(b)) {
                auto H = mk_int_nonneg_val_ne_proof(*a1, b);
                if (!H) return none_expr();
                return some_expr(mk_app(mk_constant(get_int_neg_ne_zero_of_ne_name()), *a1, *H));
            } else {
                auto Ha1_nonneg = mk_int_val_pos_proof(*a1);
                if (!Ha1_nonneg) return none_expr();
                auto Hb_nonneg  = mk_int_val_pos_proof(b);
                if (!Hb_nonneg) return none_expr();
                return some_expr(mk_app(mk_constant(get_int_neg_ne_of_pos_name()), *a1, b, *Ha1_nonneg, *Hb_nonneg));
            }
        }
    } else {
        if (auto b1 = is_neg(b)) {
            if (is_zero(a)) {
                auto H = mk_int_nonneg_val_ne_proof(a, *b1);
                if (!H) return none_expr();
                return some_expr(mk_app(mk_constant(get_int_zero_ne_neg_of_ne_name()), *b1, *H));
            } else {
                auto Ha_nonneg = mk_int_val_pos_proof(a);
                if (!Ha_nonneg) return none_expr();
                auto Hb1_nonneg = mk_int_val_pos_proof(*b1);
                return some_expr(mk_app(mk_constant(get_int_ne_neg_of_pos_name()), a, *b1, *Ha_nonneg, *Hb1_nonneg));
            }
        } else {
            return mk_int_nonneg_val_ne_proof(a, b);
        }
    }
}

optional<expr> mk_val_ne_proof(type_context_old & ctx, expr const & a, expr const & b) {
    expr type = ctx.infer(a);
    if (ctx.is_def_eq(type, mk_nat_type()))
        return mk_nat_val_ne_proof(a, b);
    if (ctx.is_def_eq(type, mk_int_type()))
        return mk_int_val_ne_proof(a, b);
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
