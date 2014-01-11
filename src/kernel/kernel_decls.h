/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
// Automatically generated file, DO NOT EDIT
#include "kernel/expr.h"
namespace lean {
expr mk_Bool();
bool is_Bool(expr const & e);
expr mk_TypeU();
bool is_TypeU(expr const & e);
expr mk_not_fn();
bool is_not_fn(expr const & e);
inline bool is_not(expr const & e) { return is_app(e) && is_not_fn(arg(e, 0)); }
inline expr mk_not(expr const & e1) { return mk_app({mk_not_fn(), e1}); }
expr mk_or_fn();
bool is_or_fn(expr const & e);
inline bool is_or(expr const & e) { return is_app(e) && is_or_fn(arg(e, 0)); }
inline expr mk_or(expr const & e1, expr const & e2) { return mk_app({mk_or_fn(), e1, e2}); }
expr mk_and_fn();
bool is_and_fn(expr const & e);
inline bool is_and(expr const & e) { return is_app(e) && is_and_fn(arg(e, 0)); }
inline expr mk_and(expr const & e1, expr const & e2) { return mk_app({mk_and_fn(), e1, e2}); }
expr mk_implies_fn();
bool is_implies_fn(expr const & e);
inline bool is_implies(expr const & e) { return is_app(e) && is_implies_fn(arg(e, 0)); }
inline expr mk_implies(expr const & e1, expr const & e2) { return mk_app({mk_implies_fn(), e1, e2}); }
expr mk_exists_fn();
bool is_exists_fn(expr const & e);
inline bool is_exists(expr const & e) { return is_app(e) && is_exists_fn(arg(e, 0)); }
inline expr mk_exists(expr const & e1, expr const & e2) { return mk_app({mk_exists_fn(), e1, e2}); }
expr mk_eq_fn();
bool is_eq_fn(expr const & e);
inline bool is_eq(expr const & e) { return is_app(e) && is_eq_fn(arg(e, 0)); }
inline expr mk_eq(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_eq_fn(), e1, e2, e3}); }
expr mk_neq_fn();
bool is_neq_fn(expr const & e);
inline bool is_neq(expr const & e) { return is_app(e) && is_neq_fn(arg(e, 0)); }
inline expr mk_neq(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_neq_fn(), e1, e2, e3}); }
expr mk_em_fn();
bool is_em_fn(expr const & e);
inline expr mk_em_th(expr const & e1) { return mk_app({mk_em_fn(), e1}); }
expr mk_case_fn();
bool is_case_fn(expr const & e);
inline expr mk_case_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_case_fn(), e1, e2, e3, e4}); }
expr mk_refl_fn();
bool is_refl_fn(expr const & e);
inline expr mk_refl_th(expr const & e1, expr const & e2) { return mk_app({mk_refl_fn(), e1, e2}); }
expr mk_subst_fn();
bool is_subst_fn(expr const & e);
inline expr mk_subst_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_subst_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_funext_fn();
bool is_funext_fn(expr const & e);
inline expr mk_funext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_funext_fn(), e1, e2, e3, e4, e5}); }
expr mk_allext_fn();
bool is_allext_fn(expr const & e);
inline expr mk_allext_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_allext_fn(), e1, e2, e3, e4}); }
expr mk_substp_fn();
bool is_substp_fn(expr const & e);
inline expr mk_substp_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_substp_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_not_intro_fn();
bool is_not_intro_fn(expr const & e);
inline expr mk_not_intro_th(expr const & e1, expr const & e2) { return mk_app({mk_not_intro_fn(), e1, e2}); }
expr mk_eta_fn();
bool is_eta_fn(expr const & e);
inline expr mk_eta_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_eta_fn(), e1, e2, e3}); }
expr mk_trivial();
bool is_trivial(expr const & e);
expr mk_absurd_fn();
bool is_absurd_fn(expr const & e);
inline expr mk_absurd_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_absurd_fn(), e1, e2, e3}); }
expr mk_eqmp_fn();
bool is_eqmp_fn(expr const & e);
inline expr mk_eqmp_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_eqmp_fn(), e1, e2, e3, e4}); }
expr mk_boolcomplete_fn();
bool is_boolcomplete_fn(expr const & e);
inline expr mk_boolcomplete_th(expr const & e1) { return mk_app({mk_boolcomplete_fn(), e1}); }
expr mk_false_elim_fn();
bool is_false_elim_fn(expr const & e);
inline expr mk_false_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_false_elim_fn(), e1, e2}); }
expr mk_imp_trans_fn();
bool is_imp_trans_fn(expr const & e);
inline expr mk_imp_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_imp_eq_trans_fn();
bool is_imp_eq_trans_fn(expr const & e);
inline expr mk_imp_eq_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_imp_eq_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_eq_imp_trans_fn();
bool is_eq_imp_trans_fn(expr const & e);
inline expr mk_eq_imp_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_eq_imp_trans_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_not_not_eq_fn();
bool is_not_not_eq_fn(expr const & e);
inline expr mk_not_not_eq_th(expr const & e1) { return mk_app({mk_not_not_eq_fn(), e1}); }
expr mk_not_not_elim_fn();
bool is_not_not_elim_fn(expr const & e);
inline expr mk_not_not_elim_th(expr const & e1, expr const & e2) { return mk_app({mk_not_not_elim_fn(), e1, e2}); }
expr mk_mt_fn();
bool is_mt_fn(expr const & e);
inline expr mk_mt_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_mt_fn(), e1, e2, e3, e4}); }
expr mk_contrapos_fn();
bool is_contrapos_fn(expr const & e);
inline expr mk_contrapos_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_contrapos_fn(), e1, e2, e3, e4}); }
expr mk_absurd_elim_fn();
bool is_absurd_elim_fn(expr const & e);
inline expr mk_absurd_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_absurd_elim_fn(), e1, e2, e3, e4}); }
expr mk_not_imp_eliml_fn();
bool is_not_imp_eliml_fn(expr const & e);
inline expr mk_not_imp_eliml_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_imp_eliml_fn(), e1, e2, e3}); }
expr mk_not_imp_elimr_fn();
bool is_not_imp_elimr_fn(expr const & e);
inline expr mk_not_imp_elimr_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_imp_elimr_fn(), e1, e2, e3}); }
expr mk_resolve1_fn();
bool is_resolve1_fn(expr const & e);
inline expr mk_resolve1_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_resolve1_fn(), e1, e2, e3, e4}); }
expr mk_and_intro_fn();
bool is_and_intro_fn(expr const & e);
inline expr mk_and_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_and_intro_fn(), e1, e2, e3, e4}); }
expr mk_and_eliml_fn();
bool is_and_eliml_fn(expr const & e);
inline expr mk_and_eliml_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_and_eliml_fn(), e1, e2, e3}); }
expr mk_and_elimr_fn();
bool is_and_elimr_fn(expr const & e);
inline expr mk_and_elimr_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_and_elimr_fn(), e1, e2, e3}); }
expr mk_or_introl_fn();
bool is_or_introl_fn(expr const & e);
inline expr mk_or_introl_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_or_introl_fn(), e1, e2, e3}); }
expr mk_or_intror_fn();
bool is_or_intror_fn(expr const & e);
inline expr mk_or_intror_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_or_intror_fn(), e1, e2, e3}); }
expr mk_or_elim_fn();
bool is_or_elim_fn(expr const & e);
inline expr mk_or_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_or_elim_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_refute_fn();
bool is_refute_fn(expr const & e);
inline expr mk_refute_th(expr const & e1, expr const & e2) { return mk_app({mk_refute_fn(), e1, e2}); }
expr mk_symm_fn();
bool is_symm_fn(expr const & e);
inline expr mk_symm_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_symm_fn(), e1, e2, e3, e4}); }
expr mk_trans_fn();
bool is_trans_fn(expr const & e);
inline expr mk_trans_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_trans_fn(), e1, e2, e3, e4, e5, e6}); }
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
expr mk_congr1_fn();
bool is_congr1_fn(expr const & e);
inline expr mk_congr1_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_congr1_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_congr2_fn();
bool is_congr2_fn(expr const & e);
inline expr mk_congr2_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6) { return mk_app({mk_congr2_fn(), e1, e2, e3, e4, e5, e6}); }
expr mk_congr_fn();
bool is_congr_fn(expr const & e);
inline expr mk_congr_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5, expr const & e6, expr const & e7, expr const & e8) { return mk_app({mk_congr_fn(), e1, e2, e3, e4, e5, e6, e7, e8}); }
expr mk_exists_elim_fn();
bool is_exists_elim_fn(expr const & e);
inline expr mk_exists_elim_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4, expr const & e5) { return mk_app({mk_exists_elim_fn(), e1, e2, e3, e4, e5}); }
expr mk_exists_intro_fn();
bool is_exists_intro_fn(expr const & e);
inline expr mk_exists_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_exists_intro_fn(), e1, e2, e3, e4}); }
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
expr mk_not_iff_fn();
bool is_not_iff_fn(expr const & e);
inline expr mk_not_iff_th(expr const & e1, expr const & e2) { return mk_app({mk_not_iff_fn(), e1, e2}); }
expr mk_not_iff_elim_fn();
bool is_not_iff_elim_fn(expr const & e);
inline expr mk_not_iff_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_iff_elim_fn(), e1, e2, e3}); }
expr mk_not_implies_fn();
bool is_not_implies_fn(expr const & e);
inline expr mk_not_implies_th(expr const & e1, expr const & e2) { return mk_app({mk_not_implies_fn(), e1, e2}); }
expr mk_not_implies_elim_fn();
bool is_not_implies_elim_fn(expr const & e);
inline expr mk_not_implies_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_implies_elim_fn(), e1, e2, e3}); }
expr mk_not_congr_fn();
bool is_not_congr_fn(expr const & e);
inline expr mk_not_congr_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_congr_fn(), e1, e2, e3}); }
expr mk_eq_exists_intro_fn();
bool is_eq_exists_intro_fn(expr const & e);
inline expr mk_eq_exists_intro_th(expr const & e1, expr const & e2, expr const & e3, expr const & e4) { return mk_app({mk_eq_exists_intro_fn(), e1, e2, e3, e4}); }
expr mk_not_forall_fn();
bool is_not_forall_fn(expr const & e);
inline expr mk_not_forall_th(expr const & e1, expr const & e2) { return mk_app({mk_not_forall_fn(), e1, e2}); }
expr mk_not_forall_elim_fn();
bool is_not_forall_elim_fn(expr const & e);
inline expr mk_not_forall_elim_th(expr const & e1, expr const & e2, expr const & e3) { return mk_app({mk_not_forall_elim_fn(), e1, e2, e3}); }
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
}
