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
        } else if (is_zero(b)) {
            return none_expr();
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
        } else if (is_one(b)) {
            return none_expr();
        }
    }
    return none_expr();
}

optional<expr> mk_nat_val_lt_proof(expr const & a, expr const & b) {
    if (a == b) return none_expr();
    if (auto a1 = is_bit0(a)) {
        if (auto b1 = is_bit0(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
                return some_expr(mk_app(mk_constant(get_nat_bit0_lt_name()), *a1, *b1, *pr));
        } else if (auto b1 = is_bit1(b)) {
            if (auto pr = mk_nat_val_lt_proof(*a1, *b1))
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
}
