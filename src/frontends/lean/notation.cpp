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
    if (!f.get_environment().mark_builtin_imported("lean_notation"))
        return;
    f.add_infix("=",  50, mk_homo_eq_fn());
    f.mark_implicit_arguments(mk_homo_eq_fn(), {true, false, false});
    f.mark_implicit_arguments(mk_if_fn(), {true, false, false, false});

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
    f.mark_implicit_arguments(mk_cast_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_mp_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_discharge_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_refl_fn(), {true, false});
    f.mark_implicit_arguments(mk_subst_fn(), {true, true, true, true, false, false});
    add_alias(f, "Subst", "SubstP");
    f.mark_implicit_arguments("SubstP", {true, true, true, false, false, false});
    f.mark_implicit_arguments(mk_trans_ext_fn(), {true, true, true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_eta_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_abst_fn(), {true, true, true, true, false});
    f.mark_implicit_arguments(mk_imp_antisym_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_dom_inj_fn(), {true, true, true, true, false});
    f.mark_implicit_arguments(mk_ran_inj_fn(), {true, true, true, true, false, false});

    // implicit arguments for basic theorems
    f.mark_implicit_arguments(mk_absurd_fn(), {true, false, false});
    f.mark_implicit_arguments(mk_double_neg_elim_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_mt_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_contrapos_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_eq_mp_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_not_imp1_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_not_imp2_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_conj_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_conjunct1_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_conjunct2_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_disj1_fn(), {true, false, false});
    f.mark_implicit_arguments(mk_disj2_fn(), {true, false, false});
    f.mark_implicit_arguments(mk_disj_cases_fn(), {true, true, true, false, false, false});
    f.mark_implicit_arguments(mk_symm_fn(), {true, true, true, false});
    f.mark_implicit_arguments(mk_trans_fn(), {true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_eqt_elim_fn(), {true, false});
    f.mark_implicit_arguments(mk_eqt_intro_fn(), {true, false});
    f.mark_implicit_arguments(mk_congr1_fn(), {true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_congr2_fn(), {true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_congr_fn(),  {true, true, true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_forall_elim_fn(), {true, true, false, false});
}
}
