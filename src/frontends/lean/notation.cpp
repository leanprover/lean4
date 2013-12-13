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
void add_alias(frontend & f, name const & n, name const & m) {
    object const & obj = f.get_object(n);
    f.add_definition(m, obj.get_type(), mk_constant(n));
}

/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(frontend & f) {
    if (!f.get_environment()->mark_builtin_imported("lean_notation"))
        return;
    f.add_infix("=",  50, mk_homo_eq_fn());
    f.mark_implicit_arguments(mk_homo_eq_fn(), 1);
    f.mark_implicit_arguments(mk_if_fn(), 1);

    f.add_prefix("\u00ac", 40, mk_not_fn());     // "¬"
    f.add_infixr("&&", 35, mk_and_fn());         // "&&"
    f.add_infixr("/\\", 35, mk_and_fn());        // "/\"
    f.add_infixr("\u2227", 35, mk_and_fn());     // "∧"
    f.add_infixr("||", 30, mk_or_fn());          // "||"
    f.add_infixr("\\/", 30, mk_or_fn());         // "\/"
    f.add_infixr("\u2228", 30, mk_or_fn());      // "∨"
    f.add_infixr("=>", 25, mk_implies_fn());     // "=>"
    f.add_infixr("\u21D2", 25, mk_implies_fn()); // "⇒"
    f.add_infixr("<=>", 25, mk_iff_fn());        // "<=>"
    f.add_infixr("\u21D4", 25, mk_iff_fn());     // "⇔"

    f.add_infixl("+", 65, mk_nat_add_fn());
    f.add_infixl("-", 65, mk_nat_sub_fn());
    f.add_prefix("-", 75, mk_nat_neg_fn());
    f.add_infixl("*", 70, mk_nat_mul_fn());
    f.add_infix("<=", 50, mk_nat_le_fn());
    f.add_infix("\u2264", 50, mk_nat_le_fn());  // ≤
    f.add_infix(">=", 50, mk_nat_ge_fn());
    f.add_infix("\u2265", 50, mk_nat_ge_fn());  // ≥
    f.add_infix("<", 50, mk_nat_lt_fn());
    f.add_infix(">", 50, mk_nat_gt_fn());
    f.add_mixfixc({"|", "|"}, 55, mk_nat_id_fn()); // absolute value for naturals is the identity function

    f.add_infixl("+", 65, mk_int_add_fn());
    f.add_infixl("-", 65, mk_int_sub_fn());
    f.add_prefix("-", 75, mk_int_neg_fn());
    f.add_infixl("*", 70, mk_int_mul_fn());
    f.add_infixl("div", 70, mk_int_div_fn());
    f.add_infixl("mod", 70, mk_int_mod_fn());
    f.add_infix("|", 50, mk_int_divides_fn());
    f.add_mixfixc({"|", "|"}, 55, mk_int_abs_fn());
    f.add_infix("<=", 50, mk_int_le_fn());
    f.add_infix("\u2264", 50, mk_int_le_fn());  // ≤
    f.add_infix(">=", 50, mk_int_ge_fn());
    f.add_infix("\u2265", 50, mk_int_ge_fn());  // ≥
    f.add_infix("<", 50, mk_int_lt_fn());
    f.add_infix(">", 50, mk_int_gt_fn());

    f.add_infixl("+", 65, mk_real_add_fn());
    f.add_infixl("-", 65, mk_real_sub_fn());
    f.add_prefix("-", 75, mk_real_neg_fn());
    f.add_infixl("*", 70, mk_real_mul_fn());
    f.add_infixl("/", 70, mk_real_div_fn());
    f.add_mixfixc({"|", "|"}, 55, mk_real_abs_fn());
    f.add_infix("<=", 50, mk_real_le_fn());
    f.add_infix("\u2264", 50, mk_real_le_fn());  // ≤
    f.add_infix(">=", 50, mk_real_ge_fn());
    f.add_infix("\u2265", 50, mk_real_ge_fn());  // ≥
    f.add_infix("<", 50, mk_real_lt_fn());
    f.add_infix(">", 50, mk_real_gt_fn());

    f.add_coercion(mk_nat_to_int_fn());
    f.add_coercion(mk_int_to_real_fn());
    f.add_coercion(mk_nat_to_real_fn());

    // implicit arguments for builtin axioms
    f.mark_implicit_arguments(mk_cast_fn(), 2);
    f.mark_implicit_arguments(mk_mp_fn(), 2);
    f.mark_implicit_arguments(mk_discharge_fn(), 2);
    f.mark_implicit_arguments(mk_refl_fn(), 1);
    f.mark_implicit_arguments(mk_subst_fn(), 4);
    add_alias(f, "Subst", "SubstP");
    f.mark_implicit_arguments("SubstP", 3);
    f.mark_implicit_arguments(mk_trans_ext_fn(), 6);
    f.mark_implicit_arguments(mk_eta_fn(), 2);
    f.mark_implicit_arguments(mk_abst_fn(), 4);
    f.mark_implicit_arguments(mk_imp_antisym_fn(), 2);
    f.mark_implicit_arguments(mk_dom_inj_fn(), 4);
    f.mark_implicit_arguments(mk_ran_inj_fn(), 4);

    // implicit arguments for basic theorems
    f.mark_implicit_arguments(mk_absurd_fn(), 1);
    f.mark_implicit_arguments(mk_double_neg_elim_fn(), 2);
    f.mark_implicit_arguments(mk_mt_fn(), 2);
    f.mark_implicit_arguments(mk_contrapos_fn(), 2);
    f.mark_implicit_arguments(mk_eq_mp_fn(), 2);
    f.mark_implicit_arguments(mk_not_imp1_fn(), 2);
    f.mark_implicit_arguments(mk_not_imp2_fn(), 2);
    f.mark_implicit_arguments(mk_conj_fn(), 2);
    f.mark_implicit_arguments(mk_conjunct1_fn(), 2);
    f.mark_implicit_arguments(mk_conjunct2_fn(), 2);
    f.mark_implicit_arguments(mk_disj1_fn(), 1);
    f.mark_implicit_arguments(mk_disj2_fn(), 1);
    f.mark_implicit_arguments(mk_disj_cases_fn(), 3);
    f.mark_implicit_arguments(mk_symm_fn(), 3);
    f.mark_implicit_arguments(mk_trans_fn(), 4);
    f.mark_implicit_arguments(mk_eqt_elim_fn(), 1);
    f.mark_implicit_arguments(mk_eqt_intro_fn(), 1);
    f.mark_implicit_arguments(mk_congr1_fn(), 4);
    f.mark_implicit_arguments(mk_congr2_fn(), 4);
    f.mark_implicit_arguments(mk_congr_fn(),  6);
    f.mark_implicit_arguments(mk_forall_elim_fn(), 2);
}
}
