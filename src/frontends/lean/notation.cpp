/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "library/basic_thms.h"
#include "library/arith/arith.h"
#include "library/cast/cast.h"
#include "frontends/lean/frontend.h"

namespace lean {
void add_alias(environment const & env, name const & n, name const & m) {
    object const & obj = env->get_object(n);
    env->add_definition(m, obj.get_type(), mk_constant(n));
}

/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(environment const & env, io_state & ios) {
    if (!env->mark_builtin_imported("lean_notation"))
        return;
    add_infix(env, ios, "=",  50, mk_homo_eq_fn());
    mark_implicit_arguments(env, mk_homo_eq_fn(), 1);
    mark_implicit_arguments(env, mk_if_fn(), 1);

    add_prefix(env, ios, "\u00ac", 40, mk_not_fn());     // "¬"
    add_infixr(env, ios, "&&", 35, mk_and_fn());         // "&&"
    add_infixr(env, ios, "/\\", 35, mk_and_fn());        // "/\"
    add_infixr(env, ios, "\u2227", 35, mk_and_fn());     // "∧"
    add_infixr(env, ios, "||", 30, mk_or_fn());          // "||"
    add_infixr(env, ios, "\\/", 30, mk_or_fn());         // "\/"
    add_infixr(env, ios, "\u2228", 30, mk_or_fn());      // "∨"
    add_infixr(env, ios, "=>", 25, mk_implies_fn());     // "=>"
    add_infixr(env, ios, "\u21D2", 25, mk_implies_fn()); // "⇒"
    add_infixr(env, ios, "<=>", 25, mk_iff_fn());        // "<=>"
    add_infixr(env, ios, "\u21D4", 25, mk_iff_fn());     // "⇔"

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

    // implicit arguments for builtin axioms
    mark_implicit_arguments(env, mk_cast_fn(), 2);
    mark_implicit_arguments(env, mk_mp_fn(), 2);
    mark_implicit_arguments(env, mk_discharge_fn(), 2);
    mark_implicit_arguments(env, mk_refl_fn(), 1);
    mark_implicit_arguments(env, mk_subst_fn(), 4);
    add_alias(env, "Subst", "SubstP");
    mark_implicit_arguments(env, "SubstP", 3);
    mark_implicit_arguments(env, mk_trans_ext_fn(), 6);
    mark_implicit_arguments(env, mk_eta_fn(), 2);
    mark_implicit_arguments(env, mk_abst_fn(), 4);
    mark_implicit_arguments(env, mk_imp_antisym_fn(), 2);
    mark_implicit_arguments(env, mk_dom_inj_fn(), 4);
    mark_implicit_arguments(env, mk_ran_inj_fn(), 4);

    // implicit arguments for basic theorems
    mark_implicit_arguments(env, mk_absurd_fn(), 1);
    mark_implicit_arguments(env, mk_double_neg_elim_fn(), 1);
    mark_implicit_arguments(env, mk_mt_fn(), 2);
    mark_implicit_arguments(env, mk_contrapos_fn(), 2);
    mark_implicit_arguments(env, mk_eq_mp_fn(), 2);
    mark_implicit_arguments(env, mk_not_imp1_fn(), 2);
    mark_implicit_arguments(env, mk_not_imp2_fn(), 2);
    mark_implicit_arguments(env, mk_conj_fn(), 2);
    mark_implicit_arguments(env, mk_conjunct1_fn(), 2);
    mark_implicit_arguments(env, mk_conjunct2_fn(), 2);
    mark_implicit_arguments(env, mk_disj1_fn(), 1);
    mark_implicit_arguments(env, mk_disj2_fn(), 1);
    mark_implicit_arguments(env, mk_disj_cases_fn(), 3);
    mark_implicit_arguments(env, mk_refute_fn(), 1);
    mark_implicit_arguments(env, mk_symm_fn(), 3);
    mark_implicit_arguments(env, mk_trans_fn(), 4);
    mark_implicit_arguments(env, mk_eqt_elim_fn(), 1);
    mark_implicit_arguments(env, mk_eqt_intro_fn(), 1);
    mark_implicit_arguments(env, mk_congr1_fn(), 4);
    mark_implicit_arguments(env, mk_congr2_fn(), 4);
    mark_implicit_arguments(env, mk_congr_fn(),  6);
    mark_implicit_arguments(env, mk_forall_elim_fn(), 2);
    mark_implicit_arguments(env, mk_forall_intro_fn(), 2);
    mark_implicit_arguments(env, mk_exists_elim_fn(), 3);
    mark_implicit_arguments(env, mk_exists_intro_fn(), 2);
}
}
