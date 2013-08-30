/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "builtin.h"
#include "basic_thms.h"
#include "lean_frontend.h"

namespace lean {
/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(frontend & f) {
    f.mark_implicit_arguments(mk_homo_eq_fn(), {true, false, false});
    f.add_infix("==", 50, mk_homo_eq_fn());
    f.add_infix("≃",  50, mk_homo_eq_fn());

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

    // implicit arguments for builtin axioms
    f.mark_implicit_arguments(mk_mp_fn(), {true, true, false, false});
    f.mark_implicit_arguments(mk_discharge_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_refl_fn(), {true, false});
    f.mark_implicit_arguments(mk_subst_fn(), {true, true, true, false, false, false});
    f.mark_implicit_arguments(mk_eta_fn(), {true, true, false});
    f.mark_implicit_arguments(mk_imp_antisym_fn(), {true, true, false, false});

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
    f.mark_implicit_arguments(mk_trans_ext_fn(), {true, true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_eqt_elim_fn(), {true, false});
    f.mark_implicit_arguments(mk_eqt_intro_fn(), {true, false});
    f.mark_implicit_arguments(mk_congr1_fn(), {true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_congr2_fn(), {true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_congr_fn(),  {true, true, true, true, true, true, false, false});
    f.mark_implicit_arguments(mk_forall_elim_fn(), {true, true, false, false});
}
}
