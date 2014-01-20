/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_Nat();
bool is_Nat(expr const & e);
expr mk_Nat_ge_fn();
bool is_Nat_ge_fn(expr const & e);
inline bool is_Nat_ge(expr const & e) { return is_app(e) && is_Nat_ge_fn(arg(e, 0)); }
inline expr mk_Nat_ge(expr const & e1, expr const & e2) { return mk_app({mk_Nat_ge_fn(), e1, e2}); }
expr mk_Nat_lt_fn();
bool is_Nat_lt_fn(expr const & e);
inline bool is_Nat_lt(expr const & e) { return is_app(e) && is_Nat_lt_fn(arg(e, 0)); }
inline expr mk_Nat_lt(expr const & e1, expr const & e2) { return mk_app({mk_Nat_lt_fn(), e1, e2}); }
expr mk_Nat_gt_fn();
bool is_Nat_gt_fn(expr const & e);
inline bool is_Nat_gt(expr const & e) { return is_app(e) && is_Nat_gt_fn(arg(e, 0)); }
inline expr mk_Nat_gt(expr const & e1, expr const & e2) { return mk_app({mk_Nat_gt_fn(), e1, e2}); }
expr mk_Nat_id_fn();
bool is_Nat_id_fn(expr const & e);
inline bool is_Nat_id(expr const & e) { return is_app(e) && is_Nat_id_fn(arg(e, 0)); }
inline expr mk_Nat_id(expr const & e1) { return mk_app({mk_Nat_id_fn(), e1}); }
expr mk_Nat_succ_nz_fn();
bool is_Nat_succ_nz_fn(expr const & e);
inline expr mk_Nat_succ_nz_th(expr const & e1) { return mk_app({mk_Nat_succ_nz_fn(), e1}); }
expr mk_Nat_succ_inj_fn();
bool is_Nat_succ_inj_fn(expr const & e);
inline expr mk_Nat_succ_inj_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_succ_inj_fn(), e1, e2, e3}); }
expr mk_Nat_add_zeror_fn();
bool is_Nat_add_zeror_fn(expr const & e);
inline expr mk_Nat_add_zeror_th(expr const & e1) { return mk_app({mk_Nat_add_zeror_fn(), e1}); }
expr mk_Nat_add_succr_fn();
bool is_Nat_add_succr_fn(expr const & e);
inline expr mk_Nat_add_succr_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_add_succr_fn(), e1, e2}); }
expr mk_Nat_mul_zeror_fn();
bool is_Nat_mul_zeror_fn(expr const & e);
inline expr mk_Nat_mul_zeror_th(expr const & e1) { return mk_app({mk_Nat_mul_zeror_fn(), e1}); }
expr mk_Nat_mul_succr_fn();
bool is_Nat_mul_succr_fn(expr const & e);
inline expr mk_Nat_mul_succr_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_mul_succr_fn(), e1, e2}); }
expr mk_Nat_le_def_fn();
bool is_Nat_le_def_fn(expr const & e);
inline expr mk_Nat_le_def_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_le_def_fn(), e1, e2}); }
expr mk_Nat_induction_fn();
bool is_Nat_induction_fn(expr const & e);
inline expr mk_Nat_induction_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_induction_fn(), e1, e2, e3, e4}); }
expr mk_Nat_induction_on_fn();
bool is_Nat_induction_on_fn(expr const & e);
inline expr mk_Nat_induction_on_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_induction_on_fn(), e1, e2, e3, e4}); }
expr mk_Nat_pred_nz_fn();
bool is_Nat_pred_nz_fn(expr const & e);
inline expr mk_Nat_pred_nz_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_pred_nz_fn(), e1, e2}); }
expr mk_Nat_discriminate_fn();
bool is_Nat_discriminate_fn(expr const & e);
inline expr mk_Nat_discriminate_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_discriminate_fn(), e1, e2, e3, e4}); }
expr mk_Nat_add_zerol_fn();
bool is_Nat_add_zerol_fn(expr const & e);
inline expr mk_Nat_add_zerol_th(expr const & e1) { return mk_app({mk_Nat_add_zerol_fn(), e1}); }
expr mk_Nat_add_succl_fn();
bool is_Nat_add_succl_fn(expr const & e);
inline expr mk_Nat_add_succl_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_add_succl_fn(), e1, e2}); }
expr mk_Nat_add_comm_fn();
bool is_Nat_add_comm_fn(expr const & e);
inline expr mk_Nat_add_comm_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_add_comm_fn(), e1, e2}); }
expr mk_Nat_add_assoc_fn();
bool is_Nat_add_assoc_fn(expr const & e);
inline expr mk_Nat_add_assoc_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_add_assoc_fn(), e1, e2, e3}); }
expr mk_Nat_mul_zerol_fn();
bool is_Nat_mul_zerol_fn(expr const & e);
inline expr mk_Nat_mul_zerol_th(expr const & e1) { return mk_app({mk_Nat_mul_zerol_fn(), e1}); }
expr mk_Nat_mul_succl_fn();
bool is_Nat_mul_succl_fn(expr const & e);
inline expr mk_Nat_mul_succl_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_mul_succl_fn(), e1, e2}); }
expr mk_Nat_mul_onel_fn();
bool is_Nat_mul_onel_fn(expr const & e);
inline expr mk_Nat_mul_onel_th(expr const & e1) { return mk_app({mk_Nat_mul_onel_fn(), e1}); }
expr mk_Nat_mul_oner_fn();
bool is_Nat_mul_oner_fn(expr const & e);
inline expr mk_Nat_mul_oner_th(expr const & e1) { return mk_app({mk_Nat_mul_oner_fn(), e1}); }
expr mk_Nat_mul_comm_fn();
bool is_Nat_mul_comm_fn(expr const & e);
inline expr mk_Nat_mul_comm_th(expr const & e1, expr const & e2) { return mk_app({mk_Nat_mul_comm_fn(), e1, e2}); }
expr mk_Nat_distributer_fn();
bool is_Nat_distributer_fn(expr const & e);
inline expr mk_Nat_distributer_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_distributer_fn(), e1, e2, e3}); }
expr mk_Nat_distributel_fn();
bool is_Nat_distributel_fn(expr const & e);
inline expr mk_Nat_distributel_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_distributel_fn(), e1, e2, e3}); }
expr mk_Nat_mul_assoc_fn();
bool is_Nat_mul_assoc_fn(expr const & e);
inline expr mk_Nat_mul_assoc_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_mul_assoc_fn(), e1, e2, e3}); }
expr mk_Nat_add_left_comm_fn();
bool is_Nat_add_left_comm_fn(expr const & e);
inline expr mk_Nat_add_left_comm_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_add_left_comm_fn(), e1, e2, e3}); }
expr mk_Nat_mul_left_comm_fn();
bool is_Nat_mul_left_comm_fn(expr const & e);
inline expr mk_Nat_mul_left_comm_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_mul_left_comm_fn(), e1, e2, e3}); }
expr mk_Nat_add_injr_fn();
bool is_Nat_add_injr_fn(expr const & e);
inline expr mk_Nat_add_injr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_add_injr_fn(), e1, e2, e3, e4}); }
expr mk_Nat_add_injl_fn();
bool is_Nat_add_injl_fn(expr const & e);
inline expr mk_Nat_add_injl_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_add_injl_fn(), e1, e2, e3, e4}); }
expr mk_Nat_add_eqz_fn();
bool is_Nat_add_eqz_fn(expr const & e);
inline expr mk_Nat_add_eqz_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_add_eqz_fn(), e1, e2, e3}); }
expr mk_Nat_le_intro_fn();
bool is_Nat_le_intro_fn(expr const & e);
inline expr mk_Nat_le_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_le_intro_fn(), e1, e2, e3, e4}); }
expr mk_Nat_le_elim_fn();
bool is_Nat_le_elim_fn(expr const & e);
inline expr mk_Nat_le_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_le_elim_fn(), e1, e2, e3}); }
expr mk_Nat_le_refl_fn();
bool is_Nat_le_refl_fn(expr const & e);
inline expr mk_Nat_le_refl_th(expr const & e1) { return mk_app({mk_Nat_le_refl_fn(), e1}); }
expr mk_Nat_le_zero_fn();
bool is_Nat_le_zero_fn(expr const & e);
inline expr mk_Nat_le_zero_th(expr const & e1) { return mk_app({mk_Nat_le_zero_fn(), e1}); }
expr mk_Nat_le_trans_fn();
bool is_Nat_le_trans_fn(expr const & e);
inline expr mk_Nat_le_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_Nat_le_trans_fn(), e1, e2, e3, e4, e5}); }
expr mk_Nat_le_add_fn();
bool is_Nat_le_add_fn(expr const & e);
inline expr mk_Nat_le_add_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_le_add_fn(), e1, e2, e3, e4}); }
expr mk_Nat_le_antisym_fn();
bool is_Nat_le_antisym_fn(expr const & e);
inline expr mk_Nat_le_antisym_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_le_antisym_fn(), e1, e2, e3, e4}); }
expr mk_Nat_not_lt_0_fn();
bool is_Nat_not_lt_0_fn(expr const & e);
inline expr mk_Nat_not_lt_0_th(expr const & e1) { return mk_app({mk_Nat_not_lt_0_fn(), e1}); }
expr mk_Nat_lt_intro_fn();
bool is_Nat_lt_intro_fn(expr const & e);
inline expr mk_Nat_lt_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_lt_intro_fn(), e1, e2, e3, e4}); }
expr mk_Nat_lt_elim_fn();
bool is_Nat_lt_elim_fn(expr const & e);
inline expr mk_Nat_lt_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_lt_elim_fn(), e1, e2, e3}); }
expr mk_Nat_lt_le_fn();
bool is_Nat_lt_le_fn(expr const & e);
inline expr mk_Nat_lt_le_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_lt_le_fn(), e1, e2, e3}); }
expr mk_Nat_lt_ne_fn();
bool is_Nat_lt_ne_fn(expr const & e);
inline expr mk_Nat_lt_ne_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_lt_ne_fn(), e1, e2, e3}); }
expr mk_Nat_lt_nrefl_fn();
bool is_Nat_lt_nrefl_fn(expr const & e);
inline expr mk_Nat_lt_nrefl_th(expr const & e1) { return mk_app({mk_Nat_lt_nrefl_fn(), e1}); }
expr mk_Nat_lt_trans_fn();
bool is_Nat_lt_trans_fn(expr const & e);
inline expr mk_Nat_lt_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_Nat_lt_trans_fn(), e1, e2, e3, e4, e5}); }
expr mk_Nat_lt_le_trans_fn();
bool is_Nat_lt_le_trans_fn(expr const & e);
inline expr mk_Nat_lt_le_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_Nat_lt_le_trans_fn(), e1, e2, e3, e4, e5}); }
expr mk_Nat_le_lt_trans_fn();
bool is_Nat_le_lt_trans_fn(expr const & e);
inline expr mk_Nat_le_lt_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_Nat_le_lt_trans_fn(), e1, e2, e3, e4, e5}); }
expr mk_Nat_ne_lt_succ_fn();
bool is_Nat_ne_lt_succ_fn(expr const & e);
inline expr mk_Nat_ne_lt_succ_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_Nat_ne_lt_succ_fn(), e1, e2, e3, e4}); }
expr mk_Nat_strong_induction_fn();
bool is_Nat_strong_induction_fn(expr const & e);
inline expr mk_Nat_strong_induction_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_Nat_strong_induction_fn(), e1, e2, e3}); }
}
