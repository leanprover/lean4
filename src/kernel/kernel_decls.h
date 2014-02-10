/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_TypeU();
bool is_TypeU(expr const & e);
expr mk_Bool();
bool is_Bool(expr const & e);
expr mk_hrefl_fn();
bool is_hrefl_fn(expr const & e);
inline expr mk_hrefl_th(expr const & e1, expr const & e2) { return mk_app({mk_hrefl_fn(), e1, e2}); }
expr mk_eq_fn();
bool is_eq_fn(expr const & e);
inline bool is_eq(expr const & e) { return is_app(e) && is_eq_fn(arg(e, 0)) && num_args(e) == 4; }
inline expr mk_eq(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_eq_fn(), e1, e2, e3}); }
expr mk_refl_fn();
bool is_refl_fn(expr const & e);
inline expr mk_refl_th(expr const & e1, expr const & e2) { return mk_app({mk_refl_fn(), e1, e2}); }
expr mk_heq_eq_fn();
bool is_heq_eq_fn(expr const & e);
inline expr mk_heq_eq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_heq_eq_fn(), e1, e2, e3}); }
expr mk_true();
bool is_true(expr const & e);
expr mk_trivial();
bool is_trivial(expr const & e);
expr mk_false();
bool is_false(expr const & e);
expr mk_not_fn();
bool is_not_fn(expr const & e);
inline bool is_not(expr const & e) { return is_app(e) && is_not_fn(arg(e, 0)) && num_args(e) == 2; }
inline expr mk_not(expr const & e1) { return mk_app({mk_not_fn(), e1}); }
expr mk_or_fn();
bool is_or_fn(expr const & e);
inline bool is_or(expr const & e) { return is_app(e) && is_or_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_or(expr const & e1, expr const & e2) { return mk_app({mk_or_fn(), e1, e2}); }
expr mk_and_fn();
bool is_and_fn(expr const & e);
inline bool is_and(expr const & e) { return is_app(e) && is_and_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_and(expr const & e1, expr const & e2) { return mk_app({mk_and_fn(), e1, e2}); }
expr mk_implies_fn();
bool is_implies_fn(expr const & e);
inline bool is_implies(expr const & e) { return is_app(e) && is_implies_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_implies(expr const & e1, expr const & e2) { return mk_app({mk_implies_fn(), e1, e2}); }
expr mk_neq_fn();
bool is_neq_fn(expr const & e);
inline bool is_neq(expr const & e) { return is_app(e) && is_neq_fn(arg(e, 0)) && num_args(e) == 4; }
inline expr mk_neq(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_neq_fn(), e1, e2, e3}); }
expr mk_a_neq_a_elim_fn();
bool is_a_neq_a_elim_fn(expr const & e);
inline expr mk_a_neq_a_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_a_neq_a_elim_fn(), e1, e2, e3}); }
expr mk_iff_fn();
bool is_iff_fn(expr const & e);
inline bool is_iff(expr const & e) { return is_app(e) && is_iff_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_iff(expr const & e1, expr const & e2) { return mk_app({mk_iff_fn(), e1, e2}); }
expr mk_em_fn();
bool is_em_fn(expr const & e);
inline expr mk_em_th(expr const & e1) { return mk_app({mk_em_fn(), e1}); }
expr mk_not_intro_fn();
bool is_not_intro_fn(expr const & e);
inline expr mk_not_intro_th(expr const & e1, expr const & e2) { return mk_app({mk_not_intro_fn(), e1, e2}); }
expr mk_absurd_fn();
bool is_absurd_fn(expr const & e);
inline expr mk_absurd_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_absurd_fn(), e1, e2, e3}); }
expr mk_exists_fn();
bool is_exists_fn(expr const & e);
inline bool is_exists(expr const & e) { return is_app(e) && is_exists_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_exists(expr const & e1, expr const & e2) { return mk_app({mk_exists_fn(), e1, e2}); }
expr mk_exists_unique_fn();
bool is_exists_unique_fn(expr const & e);
inline bool is_exists_unique(expr const & e) { return is_app(e) && is_exists_unique_fn(arg(e, 0)) && num_args(e) == 3; }
inline expr mk_exists_unique(expr const & e1, expr const & e2) { return mk_app({mk_exists_unique_fn(), e1, e2}); }
expr mk_case_fn();
bool is_case_fn(expr const & e);
inline expr mk_case_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_case_fn(), e1, e2, e3, e4}); }
expr mk_false_elim_fn();
bool is_false_elim_fn(expr const & e);
inline expr mk_false_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_false_elim_fn(), e1, e2}); }
expr mk_mt_fn();
bool is_mt_fn(expr const & e);
inline expr mk_mt_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_mt_fn(), e1, e2, e3, e4}); }
expr mk_contrapos_fn();
bool is_contrapos_fn(expr const & e);
inline expr mk_contrapos_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_contrapos_fn(), e1, e2, e3, e4}); }
expr mk_absurd_elim_fn();
bool is_absurd_elim_fn(expr const & e);
inline expr mk_absurd_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_absurd_elim_fn(), e1, e2, e3, e4}); }
expr mk_or_introl_fn();
bool is_or_introl_fn(expr const & e);
inline expr mk_or_introl_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_or_introl_fn(), e1, e2, e3}); }
expr mk_or_intror_fn();
bool is_or_intror_fn(expr const & e);
inline expr mk_or_intror_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_or_intror_fn(), e1, e2, e3}); }
expr mk_boolcomplete_fn();
bool is_boolcomplete_fn(expr const & e);
inline expr mk_boolcomplete_th(expr const & e1) { return mk_app({mk_boolcomplete_fn(), e1}); }
expr mk_boolcomplete_swapped_fn();
bool is_boolcomplete_swapped_fn(expr const & e);
inline expr mk_boolcomplete_swapped_th(expr const & e1) { return mk_app({mk_boolcomplete_swapped_fn(), e1}); }
expr mk_resolve1_fn();
bool is_resolve1_fn(expr const & e);
inline expr mk_resolve1_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_resolve1_fn(), e1, e2, e3, e4}); }
expr mk_subst_fn();
bool is_subst_fn(expr const & e);
inline expr mk_subst_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_subst_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_substp_fn();
bool is_substp_fn(expr const & e);
inline expr mk_substp_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_substp_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_symm_fn();
bool is_symm_fn(expr const & e);
inline expr mk_symm_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_symm_fn(), e1, e2, e3, e4}); }
expr mk_trans_fn();
bool is_trans_fn(expr const & e);
inline expr mk_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_hcongr1_fn();
bool is_hcongr1_fn(expr const & e);
inline expr mk_hcongr1_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hcongr1_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_congr1_fn();
bool is_congr1_fn(expr const & e);
inline expr mk_congr1_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_congr1_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_congr2_fn();
bool is_congr2_fn(expr const & e);
inline expr mk_congr2_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_congr2_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_congr_fn();
bool is_congr_fn(expr const & e);
inline expr mk_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_true_ne_false();
bool is_true_ne_false(expr const & e);
expr mk_absurd_not_true_fn();
bool is_absurd_not_true_fn(expr const & e);
inline expr mk_absurd_not_true_th(expr const & e1) { return mk_app({mk_absurd_not_true_fn(), e1}); }
expr mk_not_false_trivial();
bool is_not_false_trivial(expr const & e);
expr mk_eqmp_fn();
bool is_eqmp_fn(expr const & e);
inline expr mk_eqmp_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_eqmp_fn(), e1, e2, e3, e4}); }
expr mk_eqmpr_fn();
bool is_eqmpr_fn(expr const & e);
inline expr mk_eqmpr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_eqmpr_fn(), e1, e2, e3, e4}); }
expr mk_imp_trans_fn();
bool is_imp_trans_fn(expr const & e);
inline expr mk_imp_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_imp_eq_trans_fn();
bool is_imp_eq_trans_fn(expr const & e);
inline expr mk_imp_eq_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_eq_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_eq_imp_trans_fn();
bool is_eq_imp_trans_fn(expr const & e);
inline expr mk_eq_imp_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_eq_imp_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_to_eq_fn();
bool is_to_eq_fn(expr const & e);
inline expr mk_to_eq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_to_eq_fn(), e1, e2, e3, e4}); }
expr mk_to_heq_fn();
bool is_to_heq_fn(expr const & e);
inline expr mk_to_heq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_to_heq_fn(), e1, e2, e3, e4}); }
expr mk_iff_eliml_fn();
bool is_iff_eliml_fn(expr const & e);
inline expr mk_iff_eliml_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_iff_eliml_fn(), e1, e2, e3, e4}); }
expr mk_iff_elimr_fn();
bool is_iff_elimr_fn(expr const & e);
inline expr mk_iff_elimr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_iff_elimr_fn(), e1, e2, e3, e4}); }
expr mk_ne_symm_fn();
bool is_ne_symm_fn(expr const & e);
inline expr mk_ne_symm_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_ne_symm_fn(), e1, e2, e3, e4}); }
expr mk_eq_ne_trans_fn();
bool is_eq_ne_trans_fn(expr const & e);
inline expr mk_eq_ne_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_eq_ne_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_ne_eq_trans_fn();
bool is_ne_eq_trans_fn(expr const & e);
inline expr mk_ne_eq_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_ne_eq_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_eqt_elim_fn();
bool is_eqt_elim_fn(expr const & e);
inline expr mk_eqt_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_eqt_elim_fn(), e1, e2}); }
expr mk_eqf_elim_fn();
bool is_eqf_elim_fn(expr const & e);
inline expr mk_eqf_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_eqf_elim_fn(), e1, e2}); }
expr mk_heqt_elim_fn();
bool is_heqt_elim_fn(expr const & e);
inline expr mk_heqt_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_heqt_elim_fn(), e1, e2}); }
expr mk_not_true();
bool is_not_true(expr const & e);
expr mk_not_false();
bool is_not_false(expr const & e);
expr mk_not_not_eq_fn();
bool is_not_not_eq_fn(expr const & e);
inline expr mk_not_not_eq_th(expr const & e1) { return mk_app({mk_not_not_eq_fn(), e1}); }
expr mk_not_neq_fn();
bool is_not_neq_fn(expr const & e);
inline expr mk_not_neq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_neq_fn(), e1, e2, e3}); }
expr mk_not_neq_elim_fn();
bool is_not_neq_elim_fn(expr const & e);
inline expr mk_not_neq_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_not_neq_elim_fn(), e1, e2, e3, e4}); }
expr mk_not_not_elim_fn();
bool is_not_not_elim_fn(expr const & e);
inline expr mk_not_not_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_not_not_elim_fn(), e1, e2}); }
expr mk_not_imp_eliml_fn();
bool is_not_imp_eliml_fn(expr const & e);
inline expr mk_not_imp_eliml_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_imp_eliml_fn(), e1, e2, e3}); }
expr mk_not_imp_elimr_fn();
bool is_not_imp_elimr_fn(expr const & e);
inline expr mk_not_imp_elimr_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_imp_elimr_fn(), e1, e2, e3}); }
expr mk_and_intro_fn();
bool is_and_intro_fn(expr const & e);
inline expr mk_and_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_and_intro_fn(), e1, e2, e3, e4}); }
expr mk_and_eliml_fn();
bool is_and_eliml_fn(expr const & e);
inline expr mk_and_eliml_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_and_eliml_fn(), e1, e2, e3}); }
expr mk_and_elimr_fn();
bool is_and_elimr_fn(expr const & e);
inline expr mk_and_elimr_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_and_elimr_fn(), e1, e2, e3}); }
expr mk_or_elim_fn();
bool is_or_elim_fn(expr const & e);
inline expr mk_or_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_or_elim_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_refute_fn();
bool is_refute_fn(expr const & e);
inline expr mk_refute_th(expr const & e1, expr const & e2) { return mk_app({mk_refute_fn(), e1, e2}); }
expr mk_boolext_fn();
bool is_boolext_fn(expr const & e);
inline expr mk_boolext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_boolext_fn(), e1, e2, e3, e4}); }
expr mk_iff_intro_fn();
bool is_iff_intro_fn(expr const & e);
inline expr mk_iff_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_iff_intro_fn(), e1, e2, e3, e4}); }
expr mk_eqt_intro_fn();
bool is_eqt_intro_fn(expr const & e);
inline expr mk_eqt_intro_th(expr const & e1, expr const & e2) { return mk_app({mk_eqt_intro_fn(), e1, e2}); }
expr mk_eqf_intro_fn();
bool is_eqf_intro_fn(expr const & e);
inline expr mk_eqf_intro_th(expr const & e1, expr const & e2) { return mk_app({mk_eqf_intro_fn(), e1, e2}); }
expr mk_a_neq_a_fn();
bool is_a_neq_a_fn(expr const & e);
inline expr mk_a_neq_a_th(expr const & e1, expr const & e2) { return mk_app({mk_a_neq_a_fn(), e1, e2}); }
expr mk_eq_id_fn();
bool is_eq_id_fn(expr const & e);
inline expr mk_eq_id_th(expr const & e1, expr const & e2) { return mk_app({mk_eq_id_fn(), e1, e2}); }
expr mk_iff_id_fn();
bool is_iff_id_fn(expr const & e);
inline expr mk_iff_id_th(expr const & e1) { return mk_app({mk_iff_id_fn(), e1}); }
expr mk_heq_id_fn();
bool is_heq_id_fn(expr const & e);
inline expr mk_heq_id_th(expr const & e1, expr const & e2) { return mk_app({mk_heq_id_fn(), e1, e2}); }
expr mk_neq_elim_fn();
bool is_neq_elim_fn(expr const & e);
inline expr mk_neq_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_neq_elim_fn(), e1, e2, e3, e4}); }
expr mk_neq_to_not_eq_fn();
bool is_neq_to_not_eq_fn(expr const & e);
inline expr mk_neq_to_not_eq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_neq_to_not_eq_fn(), e1, e2, e3}); }
expr mk_left_comm_fn();
bool is_left_comm_fn(expr const & e);
inline expr mk_left_comm_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7) { return mk_app({mk_left_comm_fn(), e1, e2, e3, e4, e5, e6, e7}); }
expr mk_or_comm_fn();
bool is_or_comm_fn(expr const & e);
inline expr mk_or_comm_th(expr const & e1, expr const & e2) { return mk_app({mk_or_comm_fn(), e1, e2}); }
expr mk_or_assoc_fn();
bool is_or_assoc_fn(expr const & e);
inline expr mk_or_assoc_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_or_assoc_fn(), e1, e2, e3}); }
expr mk_or_id_fn();
bool is_or_id_fn(expr const & e);
inline expr mk_or_id_th(expr const & e1) { return mk_app({mk_or_id_fn(), e1}); }
expr mk_or_falsel_fn();
bool is_or_falsel_fn(expr const & e);
inline expr mk_or_falsel_th(expr const & e1) { return mk_app({mk_or_falsel_fn(), e1}); }
expr mk_or_falser_fn();
bool is_or_falser_fn(expr const & e);
inline expr mk_or_falser_th(expr const & e1) { return mk_app({mk_or_falser_fn(), e1}); }
expr mk_or_truel_fn();
bool is_or_truel_fn(expr const & e);
inline expr mk_or_truel_th(expr const & e1) { return mk_app({mk_or_truel_fn(), e1}); }
expr mk_or_truer_fn();
bool is_or_truer_fn(expr const & e);
inline expr mk_or_truer_th(expr const & e1) { return mk_app({mk_or_truer_fn(), e1}); }
expr mk_or_tauto_fn();
bool is_or_tauto_fn(expr const & e);
inline expr mk_or_tauto_th(expr const & e1) { return mk_app({mk_or_tauto_fn(), e1}); }
expr mk_or_left_comm_fn();
bool is_or_left_comm_fn(expr const & e);
inline expr mk_or_left_comm_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_or_left_comm_fn(), e1, e2, e3}); }
expr mk_resolve2_fn();
bool is_resolve2_fn(expr const & e);
inline expr mk_resolve2_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_resolve2_fn(), e1, e2, e3, e4}); }
expr mk_and_comm_fn();
bool is_and_comm_fn(expr const & e);
inline expr mk_and_comm_th(expr const & e1, expr const & e2) { return mk_app({mk_and_comm_fn(), e1, e2}); }
expr mk_and_id_fn();
bool is_and_id_fn(expr const & e);
inline expr mk_and_id_th(expr const & e1) { return mk_app({mk_and_id_fn(), e1}); }
expr mk_and_assoc_fn();
bool is_and_assoc_fn(expr const & e);
inline expr mk_and_assoc_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_and_assoc_fn(), e1, e2, e3}); }
expr mk_and_truer_fn();
bool is_and_truer_fn(expr const & e);
inline expr mk_and_truer_th(expr const & e1) { return mk_app({mk_and_truer_fn(), e1}); }
expr mk_and_truel_fn();
bool is_and_truel_fn(expr const & e);
inline expr mk_and_truel_th(expr const & e1) { return mk_app({mk_and_truel_fn(), e1}); }
expr mk_and_falsel_fn();
bool is_and_falsel_fn(expr const & e);
inline expr mk_and_falsel_th(expr const & e1) { return mk_app({mk_and_falsel_fn(), e1}); }
expr mk_and_falser_fn();
bool is_and_falser_fn(expr const & e);
inline expr mk_and_falser_th(expr const & e1) { return mk_app({mk_and_falser_fn(), e1}); }
expr mk_and_absurd_fn();
bool is_and_absurd_fn(expr const & e);
inline expr mk_and_absurd_th(expr const & e1) { return mk_app({mk_and_absurd_fn(), e1}); }
expr mk_and_left_comm_fn();
bool is_and_left_comm_fn(expr const & e);
inline expr mk_and_left_comm_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_and_left_comm_fn(), e1, e2, e3}); }
expr mk_imp_truer_fn();
bool is_imp_truer_fn(expr const & e);
inline expr mk_imp_truer_th(expr const & e1) { return mk_app({mk_imp_truer_fn(), e1}); }
expr mk_imp_truel_fn();
bool is_imp_truel_fn(expr const & e);
inline expr mk_imp_truel_th(expr const & e1) { return mk_app({mk_imp_truel_fn(), e1}); }
expr mk_imp_falser_fn();
bool is_imp_falser_fn(expr const & e);
inline expr mk_imp_falser_th(expr const & e1) { return mk_app({mk_imp_falser_fn(), e1}); }
expr mk_imp_falsel_fn();
bool is_imp_falsel_fn(expr const & e);
inline expr mk_imp_falsel_th(expr const & e1) { return mk_app({mk_imp_falsel_fn(), e1}); }
expr mk_imp_id_fn();
bool is_imp_id_fn(expr const & e);
inline expr mk_imp_id_th(expr const & e1) { return mk_app({mk_imp_id_fn(), e1}); }
expr mk_imp_or_fn();
bool is_imp_or_fn(expr const & e);
inline expr mk_imp_or_th(expr const & e1, expr const & e2) { return mk_app({mk_imp_or_fn(), e1, e2}); }
expr mk_not_congr_fn();
bool is_not_congr_fn(expr const & e);
inline expr mk_not_congr_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_congr_fn(), e1, e2, e3}); }
expr mk_exists_elim_fn();
bool is_exists_elim_fn(expr const & e);
inline expr mk_exists_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_exists_elim_fn(), e1, e2, e3, e4, e5}); }
expr mk_exists_intro_fn();
bool is_exists_intro_fn(expr const & e);
inline expr mk_exists_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_exists_intro_fn(), e1, e2, e3, e4}); }
expr mk_not_exists_fn();
bool is_not_exists_fn(expr const & e);
inline expr mk_not_exists_th(expr const & e1, expr const & e2) { return mk_app({mk_not_exists_fn(), e1, e2}); }
expr mk_not_exists_elim_fn();
bool is_not_exists_elim_fn(expr const & e);
inline expr mk_not_exists_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_not_exists_elim_fn(), e1, e2, e3, e4}); }
expr mk_exists_unfold1_fn();
bool is_exists_unfold1_fn(expr const & e);
inline expr mk_exists_unfold1_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_exists_unfold1_fn(), e1, e2, e3, e4}); }
expr mk_exists_unfold2_fn();
bool is_exists_unfold2_fn(expr const & e);
inline expr mk_exists_unfold2_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_exists_unfold2_fn(), e1, e2, e3, e4}); }
expr mk_exists_unfold_fn();
bool is_exists_unfold_fn(expr const & e);
inline expr mk_exists_unfold_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_unfold_fn(), e1, e2, e3}); }
expr mk_inhabited_fn();
bool is_inhabited_fn(expr const & e);
inline bool is_inhabited(expr const & e) { return is_app(e) && is_inhabited_fn(arg(e, 0)) && num_args(e) == 2; }
inline expr mk_inhabited(expr const & e1) { return mk_app({mk_inhabited_fn(), e1}); }
expr mk_inhabited_intro_fn();
bool is_inhabited_intro_fn(expr const & e);
inline expr mk_inhabited_intro_th(expr const & e1, expr const & e2) { return mk_app({mk_inhabited_intro_fn(), e1, e2}); }
expr mk_inhabited_elim_fn();
bool is_inhabited_elim_fn(expr const & e);
inline expr mk_inhabited_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_inhabited_elim_fn(), e1, e2, e3, e4}); }
expr mk_inhabited_ex_intro_fn();
bool is_inhabited_ex_intro_fn(expr const & e);
inline expr mk_inhabited_ex_intro_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_inhabited_ex_intro_fn(), e1, e2, e3}); }
expr mk_inhabited_range_fn();
bool is_inhabited_range_fn(expr const & e);
inline expr mk_inhabited_range_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_inhabited_range_fn(), e1, e2, e3, e4}); }
expr mk_exists_rem_fn();
bool is_exists_rem_fn(expr const & e);
inline expr mk_exists_rem_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_rem_fn(), e1, e2, e3}); }
expr mk_forall_rem_fn();
bool is_forall_rem_fn(expr const & e);
inline expr mk_forall_rem_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_forall_rem_fn(), e1, e2, e3}); }
expr mk_imp_congrr_fn();
bool is_imp_congrr_fn(expr const & e);
inline expr mk_imp_congrr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_congrr_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_imp_congrl_fn();
bool is_imp_congrl_fn(expr const & e);
inline expr mk_imp_congrl_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_congrl_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_imp_congr_fn();
bool is_imp_congr_fn(expr const & e);
inline expr mk_imp_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_congr_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_or_congrr_fn();
bool is_or_congrr_fn(expr const & e);
inline expr mk_or_congrr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_or_congrr_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_or_congrl_fn();
bool is_or_congrl_fn(expr const & e);
inline expr mk_or_congrl_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_or_congrl_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_or_congr_fn();
bool is_or_congr_fn(expr const & e);
inline expr mk_or_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_or_congr_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_and_congrr_fn();
bool is_and_congrr_fn(expr const & e);
inline expr mk_and_congrr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_and_congrr_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_and_congrl_fn();
bool is_and_congrl_fn(expr const & e);
inline expr mk_and_congrl_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_and_congrl_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_and_congr_fn();
bool is_and_congr_fn(expr const & e);
inline expr mk_and_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_and_congr_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_not_and_fn();
bool is_not_and_fn(expr const & e);
inline expr mk_not_and_th(expr const & e1, expr const & e2) { return mk_app({mk_not_and_fn(), e1, e2}); }
expr mk_not_and_elim_fn();
bool is_not_and_elim_fn(expr const & e);
inline expr mk_not_and_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_and_elim_fn(), e1, e2, e3}); }
expr mk_not_or_fn();
bool is_not_or_fn(expr const & e);
inline expr mk_not_or_th(expr const & e1, expr const & e2) { return mk_app({mk_not_or_fn(), e1, e2}); }
expr mk_not_or_elim_fn();
bool is_not_or_elim_fn(expr const & e);
inline expr mk_not_or_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_or_elim_fn(), e1, e2, e3}); }
expr mk_not_implies_fn();
bool is_not_implies_fn(expr const & e);
inline expr mk_not_implies_th(expr const & e1, expr const & e2) { return mk_app({mk_not_implies_fn(), e1, e2}); }
expr mk_not_implies_elim_fn();
bool is_not_implies_elim_fn(expr const & e);
inline expr mk_not_implies_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_implies_elim_fn(), e1, e2, e3}); }
expr mk_a_eq_not_a_fn();
bool is_a_eq_not_a_fn(expr const & e);
inline expr mk_a_eq_not_a_th(expr const & e1) { return mk_app({mk_a_eq_not_a_fn(), e1}); }
expr mk_a_iff_not_a_fn();
bool is_a_iff_not_a_fn(expr const & e);
inline expr mk_a_iff_not_a_th(expr const & e1) { return mk_app({mk_a_iff_not_a_fn(), e1}); }
expr mk_true_eq_false();
bool is_true_eq_false(expr const & e);
expr mk_true_iff_false();
bool is_true_iff_false(expr const & e);
expr mk_false_eq_true();
bool is_false_eq_true(expr const & e);
expr mk_false_iff_true();
bool is_false_iff_true(expr const & e);
expr mk_a_iff_true_fn();
bool is_a_iff_true_fn(expr const & e);
inline expr mk_a_iff_true_th(expr const & e1) { return mk_app({mk_a_iff_true_fn(), e1}); }
expr mk_a_iff_false_fn();
bool is_a_iff_false_fn(expr const & e);
inline expr mk_a_iff_false_th(expr const & e1) { return mk_app({mk_a_iff_false_fn(), e1}); }
expr mk_not_iff_fn();
bool is_not_iff_fn(expr const & e);
inline expr mk_not_iff_th(expr const & e1, expr const & e2) { return mk_app({mk_not_iff_fn(), e1, e2}); }
expr mk_not_iff_elim_fn();
bool is_not_iff_elim_fn(expr const & e);
inline expr mk_not_iff_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_iff_elim_fn(), e1, e2, e3}); }
expr mk_forall_or_distributer_fn();
bool is_forall_or_distributer_fn(expr const & e);
inline expr mk_forall_or_distributer_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_forall_or_distributer_fn(), e1, e2, e3}); }
expr mk_forall_or_distributel_fn();
bool is_forall_or_distributel_fn(expr const & e);
inline expr mk_forall_or_distributel_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_forall_or_distributel_fn(), e1, e2, e3}); }
expr mk_forall_and_distribute_fn();
bool is_forall_and_distribute_fn(expr const & e);
inline expr mk_forall_and_distribute_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_forall_and_distribute_fn(), e1, e2, e3}); }
expr mk_exists_and_distributer_fn();
bool is_exists_and_distributer_fn(expr const & e);
inline expr mk_exists_and_distributer_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_and_distributer_fn(), e1, e2, e3}); }
expr mk_exists_or_distribute_fn();
bool is_exists_or_distribute_fn(expr const & e);
inline expr mk_exists_or_distribute_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_or_distribute_fn(), e1, e2, e3}); }
expr mk_eq_exists_intro_fn();
bool is_eq_exists_intro_fn(expr const & e);
inline expr mk_eq_exists_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_eq_exists_intro_fn(), e1, e2, e3, e4}); }
expr mk_not_forall_fn();
bool is_not_forall_fn(expr const & e);
inline expr mk_not_forall_th(expr const & e1, expr const & e2) { return mk_app({mk_not_forall_fn(), e1, e2}); }
expr mk_not_forall_elim_fn();
bool is_not_forall_elim_fn(expr const & e);
inline expr mk_not_forall_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_forall_elim_fn(), e1, e2, e3}); }
expr mk_exists_and_distributel_fn();
bool is_exists_and_distributel_fn(expr const & e);
inline expr mk_exists_and_distributel_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_and_distributel_fn(), e1, e2, e3}); }
expr mk_exists_imp_distribute_fn();
bool is_exists_imp_distribute_fn(expr const & e);
inline expr mk_exists_imp_distribute_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_imp_distribute_fn(), e1, e2, e3}); }
expr mk_forall_uninhabited_fn();
bool is_forall_uninhabited_fn(expr const & e);
inline expr mk_forall_uninhabited_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_forall_uninhabited_fn(), e1, e2, e3, e4}); }
expr mk_allext_fn();
bool is_allext_fn(expr const & e);
inline expr mk_allext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_allext_fn(), e1, e2, e3, e4}); }
expr mk_proj1_congr_fn();
bool is_proj1_congr_fn(expr const & e);
inline expr mk_proj1_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_proj1_congr_fn(), e1, e2, e3, e4, e5}); }
expr mk_proj2_congr_fn();
bool is_proj2_congr_fn(expr const & e);
inline expr mk_proj2_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_proj2_congr_fn(), e1, e2, e3, e4, e5}); }
expr mk_hproj2_congr_fn();
bool is_hproj2_congr_fn(expr const & e);
inline expr mk_hproj2_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_hproj2_congr_fn(), e1, e2, e3, e4, e5}); }
expr mk_pair_fn();
bool is_pair_fn(expr const & e);
inline bool is_pair(expr const & e) { return is_app(e) && is_pair_fn(arg(e, 0)) && num_args(e) == 5; }
inline expr mk_pair(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_pair_fn(), e1, e2, e3, e4}); }
expr mk_funext_fn();
bool is_funext_fn(expr const & e);
inline expr mk_funext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_funext_fn(), e1, e2, e3, e4, e5}); }
expr mk_eta_fn();
bool is_eta_fn(expr const & e);
inline expr mk_eta_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_eta_fn(), e1, e2, e3}); }
expr mk_eps_fn();
bool is_eps_fn(expr const & e);
inline bool is_eps(expr const & e) { return is_app(e) && is_eps_fn(arg(e, 0)) && num_args(e) == 4; }
inline expr mk_eps(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_eps_fn(), e1, e2, e3}); }
expr mk_eps_ax_fn();
bool is_eps_ax_fn(expr const & e);
inline expr mk_eps_ax_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_eps_ax_fn(), e1, e2, e3, e4, e5}); }
expr mk_eps_th_fn();
bool is_eps_th_fn(expr const & e);
inline expr mk_eps_th_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_eps_th_fn(), e1, e2, e3, e4}); }
expr mk_eps_singleton_fn();
bool is_eps_singleton_fn(expr const & e);
inline expr mk_eps_singleton_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_eps_singleton_fn(), e1, e2, e3}); }
expr mk_inhabited_dfun_fn();
bool is_inhabited_dfun_fn(expr const & e);
inline expr mk_inhabited_dfun_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_inhabited_dfun_fn(), e1, e2, e3}); }
expr mk_inhabited_fun_fn();
bool is_inhabited_fun_fn(expr const & e);
inline expr mk_inhabited_fun_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_inhabited_fun_fn(), e1, e2, e3}); }
expr mk_exists_to_eps_fn();
bool is_exists_to_eps_fn(expr const & e);
inline expr mk_exists_to_eps_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_exists_to_eps_fn(), e1, e2, e3}); }
expr mk_axiom_of_choice_fn();
bool is_axiom_of_choice_fn(expr const & e);
inline expr mk_axiom_of_choice_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_axiom_of_choice_fn(), e1, e2, e3, e4}); }
expr mk_skolem_th_fn();
bool is_skolem_th_fn(expr const & e);
inline expr mk_skolem_th_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_skolem_th_fn(), e1, e2, e3}); }
expr mk_ite_fn();
bool is_ite_fn(expr const & e);
inline bool is_ite(expr const & e) { return is_app(e) && is_ite_fn(arg(e, 0)) && num_args(e) == 5; }
inline expr mk_ite(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_ite_fn(), e1, e2, e3, e4}); }
expr mk_if_true_fn();
bool is_if_true_fn(expr const & e);
inline expr mk_if_true_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_if_true_fn(), e1, e2, e3}); }
expr mk_if_false_fn();
bool is_if_false_fn(expr const & e);
inline expr mk_if_false_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_if_false_fn(), e1, e2, e3}); }
expr mk_if_a_a_fn();
bool is_if_a_a_fn(expr const & e);
inline expr mk_if_a_a_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_if_a_a_fn(), e1, e2, e3}); }
expr mk_if_congr_fn();
bool is_if_congr_fn(expr const & e);
inline expr mk_if_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8, expr const & e9, expr const & e10) { return mk_app({mk_if_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8, e9, e10}); }
expr mk_if_imp_then_fn();
bool is_if_imp_then_fn(expr const & e);
inline expr mk_if_imp_then_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_if_imp_then_fn(), e1, e2, e3, e4, e5}); }
expr mk_if_imp_else_fn();
bool is_if_imp_else_fn(expr const & e);
inline expr mk_if_imp_else_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_if_imp_else_fn(), e1, e2, e3, e4, e5}); }
expr mk_app_if_distribute_fn();
bool is_app_if_distribute_fn(expr const & e);
inline expr mk_app_if_distribute_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_app_if_distribute_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_eq_if_distributer_fn();
bool is_eq_if_distributer_fn(expr const & e);
inline expr mk_eq_if_distributer_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_eq_if_distributer_fn(), e1, e2, e3, e4, e5}); }
expr mk_eq_if_distributel_fn();
bool is_eq_if_distributel_fn(expr const & e);
inline expr mk_eq_if_distributel_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_eq_if_distributel_fn(), e1, e2, e3, e4, e5}); }
expr mk_injective_fn();
bool is_injective_fn(expr const & e);
inline bool is_injective(expr const & e) { return is_app(e) && is_injective_fn(arg(e, 0)) && num_args(e) == 4; }
inline expr mk_injective(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_injective_fn(), e1, e2, e3}); }
expr mk_non_surjective_fn();
bool is_non_surjective_fn(expr const & e);
inline bool is_non_surjective(expr const & e) { return is_app(e) && is_non_surjective_fn(arg(e, 0)) && num_args(e) == 4; }
inline expr mk_non_surjective(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_non_surjective_fn(), e1, e2, e3}); }
expr mk_ind();
bool is_ind(expr const & e);
expr mk_infinity();
bool is_infinity(expr const & e);
expr mk_pairext_fn();
bool is_pairext_fn(expr const & e);
inline expr mk_pairext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_pairext_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_pair_proj_eq_fn();
bool is_pair_proj_eq_fn(expr const & e);
inline expr mk_pair_proj_eq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_pair_proj_eq_fn(), e1, e2, e3}); }
expr mk_pair_congr_fn();
bool is_pair_congr_fn(expr const & e);
inline expr mk_pair_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_pair_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_pairext_proj_fn();
bool is_pairext_proj_fn(expr const & e);
inline expr mk_pairext_proj_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7) { return mk_app({mk_pairext_proj_fn(), e1, e2, e3, e4, e5, e6, e7}); }
expr mk_hpairext_proj_fn();
bool is_hpairext_proj_fn(expr const & e);
inline expr mk_hpairext_proj_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7) { return mk_app({mk_hpairext_proj_fn(), e1, e2, e3, e4, e5, e6, e7}); }
expr mk_cast_fn();
bool is_cast_fn(expr const & e);
inline bool is_cast(expr const & e) { return is_app(e) && is_cast_fn(arg(e, 0)) && num_args(e) == 5; }
inline expr mk_cast(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_cast_fn(), e1, e2, e3, e4}); }
expr mk_cast_heq_fn();
bool is_cast_heq_fn(expr const & e);
inline expr mk_cast_heq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_cast_heq_fn(), e1, e2, e3, e4}); }
expr mk_hsubst_fn();
bool is_hsubst_fn(expr const & e);
inline expr mk_hsubst_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7) { return mk_app({mk_hsubst_fn(), e1, e2, e3, e4, e5, e6, e7}); }
expr mk_hsymm_fn();
bool is_hsymm_fn(expr const & e);
inline expr mk_hsymm_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_hsymm_fn(), e1, e2, e3, e4, e5}); }
expr mk_htrans_fn();
bool is_htrans_fn(expr const & e);
inline expr mk_htrans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_htrans_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_hcongr_fn();
bool is_hcongr_fn(expr const & e);
inline expr mk_hcongr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8, expr const & e9, expr const & e10) { return mk_app({mk_hcongr_fn(), e1, e2, e3, e4, e5, e6, e7, e8, e9, e10}); }
expr mk_hfunext_fn();
bool is_hfunext_fn(expr const & e);
inline expr mk_hfunext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_hfunext_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_hpiext_fn();
bool is_hpiext_fn(expr const & e);
inline expr mk_hpiext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hpiext_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_hsigext_fn();
bool is_hsigext_fn(expr const & e);
inline expr mk_hsigext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hsigext_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_hallext_fn();
bool is_hallext_fn(expr const & e);
inline expr mk_hallext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hallext_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_hsfunext_fn();
bool is_hsfunext_fn(expr const & e);
inline expr mk_hsfunext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_hsfunext_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_heq_congr_fn();
bool is_heq_congr_fn(expr const & e);
inline expr mk_heq_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_heq_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_hheq_congr_fn();
bool is_hheq_congr_fn(expr const & e);
inline expr mk_hheq_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8, expr const & e9, expr const & e10) { return mk_app({mk_hheq_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8, e9, e10}); }
expr mk_type_eq_fn();
bool is_type_eq_fn(expr const & e);
inline expr mk_type_eq_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_type_eq_fn(), e1, e2, e3, e4, e5}); }
expr mk_cast_eq_fn();
bool is_cast_eq_fn(expr const & e);
inline expr mk_cast_eq_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_cast_eq_fn(), e1, e2, e3}); }
expr mk_cast_trans_fn();
bool is_cast_trans_fn(expr const & e);
inline expr mk_cast_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_cast_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_cast_pull_fn();
bool is_cast_pull_fn(expr const & e);
inline expr mk_cast_pull_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7) { return mk_app({mk_cast_pull_fn(), e1, e2, e3, e4, e5, e6, e7}); }
expr mk_proof_irrel_fn();
bool is_proof_irrel_fn(expr const & e);
inline expr mk_proof_irrel_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_proof_irrel_fn(), e1, e2, e3}); }
expr mk_hproof_irrel_fn();
bool is_hproof_irrel_fn(expr const & e);
inline expr mk_hproof_irrel_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_hproof_irrel_fn(), e1, e2, e3, e4}); }
}
