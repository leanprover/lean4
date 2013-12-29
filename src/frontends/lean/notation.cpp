/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "library/basic_thms.h"
#include "library/arith/arith.h"
#include "frontends/lean/frontend.h"

namespace lean {
void add_alias(environment const & env, name const & n, name const & m) {
    object const & obj = env->get_object(n);
    env->add_definition(m, obj.get_type(), mk_constant(n));
}

/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(environment const & env, io_state & ios, bool kernel_only) {
    env->import_builtin(
        "lean_notation",
        [&]() {
            mark_implicit_arguments(env, mk_if_fn(), 1);


            if (kernel_only)
                return;

            add_infixl(env, ios, "+", 65, mk_nat_add_fn());
            add_infixl(env, ios, "-", 65, mk_nat_sub_fn());
            add_prefix(env, ios, "-", 75, mk_nat_neg_fn());
            add_infixl(env, ios, "*", 70, mk_nat_mul_fn());
            add_infix(env, ios, "<=", 50, mk_nat_le_fn());
            add_infix(env, ios, "\u2264", 50, mk_nat_le_fn());  // ≤
            add_infix(env, ios, ">=", 50, mk_nat_ge_fn());
            add_infix(env, ios, "\u2265", 50, mk_nat_ge_fn());  // ≥
            add_infix(env, ios, "<", 50, mk_nat_lt_fn());
            add_infix(env, ios, ">", 50, mk_nat_gt_fn());
            add_mixfixc(env, ios, {"|", "|"}, 55, mk_nat_id_fn()); // absolute value for naturals is the identity function

            add_infixl(env, ios, "+", 65, mk_int_add_fn());
            add_infixl(env, ios, "-", 65, mk_int_sub_fn());
            add_prefix(env, ios, "-", 75, mk_int_neg_fn());
            add_infixl(env, ios, "*", 70, mk_int_mul_fn());
            add_infixl(env, ios, "div", 70, mk_int_div_fn());
            add_infixl(env, ios, "mod", 70, mk_int_mod_fn());
            add_infix(env, ios, "|", 50, mk_int_divides_fn());
            add_mixfixc(env, ios, {"|", "|"}, 55, mk_int_abs_fn());
            add_infix(env, ios, "<=", 50, mk_int_le_fn());
            add_infix(env, ios, "\u2264", 50, mk_int_le_fn());  // ≤
            add_infix(env, ios, ">=", 50, mk_int_ge_fn());
            add_infix(env, ios, "\u2265", 50, mk_int_ge_fn());  // ≥
            add_infix(env, ios, "<", 50, mk_int_lt_fn());
            add_infix(env, ios, ">", 50, mk_int_gt_fn());

            add_infixl(env, ios, "+", 65, mk_real_add_fn());
            add_infixl(env, ios, "-", 65, mk_real_sub_fn());
            add_prefix(env, ios, "-", 75, mk_real_neg_fn());
            add_infixl(env, ios, "*", 70, mk_real_mul_fn());
            add_infixl(env, ios, "/", 70, mk_real_div_fn());
            add_mixfixc(env, ios, {"|", "|"}, 55, mk_real_abs_fn());
            add_infix(env, ios, "<=", 50, mk_real_le_fn());
            add_infix(env, ios, "\u2264", 50, mk_real_le_fn());  // ≤
            add_infix(env, ios, ">=", 50, mk_real_ge_fn());
            add_infix(env, ios, "\u2265", 50, mk_real_ge_fn());  // ≥
            add_infix(env, ios, "<", 50, mk_real_lt_fn());
            add_infix(env, ios, ">", 50, mk_real_gt_fn());

            add_coercion(env, mk_nat_to_int_fn());
            add_coercion(env, mk_int_to_real_fn());
            add_coercion(env, mk_nat_to_real_fn());
        });
}
}
