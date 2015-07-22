// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// DO NOT EDIT, automatically generated file, generator scripts/gen_constants_cpp.py
#include "util/name.h"
namespace lean{
name const * g_absurd = nullptr;
name const * g_and = nullptr;
name const * g_and_elim_left = nullptr;
name const * g_and_elim_right = nullptr;
name const * g_and_intro = nullptr;
name const * g_bool = nullptr;
name const * g_bool_ff = nullptr;
name const * g_bool_tt = nullptr;
name const * g_char = nullptr;
name const * g_char_mk = nullptr;
name const * g_congr = nullptr;
name const * g_dite = nullptr;
name const * g_empty = nullptr;
name const * g_empty_rec = nullptr;
name const * g_eq = nullptr;
name const * g_eq_elim_inv_inv = nullptr;
name const * g_eq_intro = nullptr;
name const * g_eq_rec = nullptr;
name const * g_eq_drec = nullptr;
name const * g_eq_rec_eq = nullptr;
name const * g_eq_refl = nullptr;
name const * g_eq_symm = nullptr;
name const * g_eq_trans = nullptr;
name const * g_eq_subst = nullptr;
name const * g_exists_elim = nullptr;
name const * g_false = nullptr;
name const * g_false_rec = nullptr;
name const * g_funext = nullptr;
name const * g_heq = nullptr;
name const * g_heq_refl = nullptr;
name const * g_heq_to_eq = nullptr;
name const * g_iff = nullptr;
name const * g_iff_refl = nullptr;
name const * g_iff_false_intro = nullptr;
name const * g_iff_true_intro = nullptr;
name const * g_implies = nullptr;
name const * g_implies_of_if_pos = nullptr;
name const * g_implies_of_if_neg = nullptr;
name const * g_is_trunc_is_hprop_elim = nullptr;
name const * g_ite = nullptr;
name const * g_lift = nullptr;
name const * g_lift_down = nullptr;
name const * g_lift_up = nullptr;
name const * g_nat = nullptr;
name const * g_nat_of_num = nullptr;
name const * g_nat_succ = nullptr;
name const * g_nat_zero = nullptr;
name const * g_not = nullptr;
name const * g_num = nullptr;
name const * g_num_zero = nullptr;
name const * g_num_pos = nullptr;
name const * g_option = nullptr;
name const * g_option_some = nullptr;
name const * g_option_none = nullptr;
name const * g_or = nullptr;
name const * g_or_elim = nullptr;
name const * g_or_intro_left = nullptr;
name const * g_or_intro_right = nullptr;
name const * g_poly_unit = nullptr;
name const * g_poly_unit_star = nullptr;
name const * g_pos_num = nullptr;
name const * g_pos_num_one = nullptr;
name const * g_pos_num_bit0 = nullptr;
name const * g_pos_num_bit1 = nullptr;
name const * g_prod = nullptr;
name const * g_prod_mk = nullptr;
name const * g_prod_pr1 = nullptr;
name const * g_prod_pr2 = nullptr;
name const * g_propext = nullptr;
name const * g_sigma = nullptr;
name const * g_sigma_mk = nullptr;
name const * g_string = nullptr;
name const * g_string_empty = nullptr;
name const * g_string_str = nullptr;
name const * g_subsingleton = nullptr;
name const * g_subsingleton_elim = nullptr;
name const * g_tactic = nullptr;
name const * g_tactic_all_goals = nullptr;
name const * g_tactic_apply = nullptr;
name const * g_tactic_assert_hypothesis = nullptr;
name const * g_tactic_eapply = nullptr;
name const * g_tactic_fapply = nullptr;
name const * g_tactic_eassumption = nullptr;
name const * g_tactic_and_then = nullptr;
name const * g_tactic_append = nullptr;
name const * g_tactic_assumption = nullptr;
name const * g_tactic_at_most = nullptr;
name const * g_tactic_beta = nullptr;
name const * g_tactic_builtin = nullptr;
name const * g_tactic_cases = nullptr;
name const * g_tactic_change = nullptr;
name const * g_tactic_check_expr = nullptr;
name const * g_tactic_clear = nullptr;
name const * g_tactic_clears = nullptr;
name const * g_tactic_determ = nullptr;
name const * g_tactic_discard = nullptr;
name const * g_tactic_intro = nullptr;
name const * g_tactic_intros = nullptr;
name const * g_tactic_exact = nullptr;
name const * g_tactic_expr = nullptr;
name const * g_tactic_expr_builtin = nullptr;
name const * g_tactic_expr_list = nullptr;
name const * g_tactic_expr_list_cons = nullptr;
name const * g_tactic_expr_list_nil = nullptr;
name const * g_tactic_using_expr = nullptr;
name const * g_tactic_none_expr = nullptr;
name const * g_tactic_identifier = nullptr;
name const * g_tactic_identifier_list = nullptr;
name const * g_tactic_opt_expr = nullptr;
name const * g_tactic_opt_identifier_list = nullptr;
name const * g_tactic_fail = nullptr;
name const * g_tactic_fixpoint = nullptr;
name const * g_tactic_focus_at = nullptr;
name const * g_tactic_generalize_tac = nullptr;
name const * g_tactic_generalizes = nullptr;
name const * g_tactic_id = nullptr;
name const * g_tactic_interleave = nullptr;
name const * g_tactic_lettac = nullptr;
name const * g_tactic_now = nullptr;
name const * g_tactic_opt_expr_list = nullptr;
name const * g_tactic_or_else = nullptr;
name const * g_tactic_par = nullptr;
name const * g_tactic_refine = nullptr;
name const * g_tactic_rename = nullptr;
name const * g_tactic_repeat = nullptr;
name const * g_tactic_revert = nullptr;
name const * g_tactic_reverts = nullptr;
name const * g_tactic_rexact = nullptr;
name const * g_tactic_rotate_left = nullptr;
name const * g_tactic_rotate_right = nullptr;
name const * g_tactic_state = nullptr;
name const * g_tactic_trace = nullptr;
name const * g_tactic_try_for = nullptr;
name const * g_tactic_whnf = nullptr;
name const * g_trans_rel_left = nullptr;
name const * g_trans_rel_right = nullptr;
name const * g_true = nullptr;
name const * g_true_intro = nullptr;
name const * g_is_trunc_is_hset = nullptr;
name const * g_is_trunc_is_hprop = nullptr;
name const * g_well_founded = nullptr;
void initialize_constants() {
    g_absurd = new name{"absurd"};
    g_and = new name{"and"};
    g_and_elim_left = new name{"and", "elim_left"};
    g_and_elim_right = new name{"and", "elim_right"};
    g_and_intro = new name{"and", "intro"};
    g_bool = new name{"bool"};
    g_bool_ff = new name{"bool", "ff"};
    g_bool_tt = new name{"bool", "tt"};
    g_char = new name{"char"};
    g_char_mk = new name{"char", "mk"};
    g_congr = new name{"congr"};
    g_dite = new name{"dite"};
    g_empty = new name{"empty"};
    g_empty_rec = new name{"empty", "rec"};
    g_eq = new name{"eq"};
    g_eq_elim_inv_inv = new name{"eq", "elim_inv_inv"};
    g_eq_intro = new name{"eq", "intro"};
    g_eq_rec = new name{"eq", "rec"};
    g_eq_drec = new name{"eq", "drec"};
    g_eq_rec_eq = new name{"eq_rec_eq"};
    g_eq_refl = new name{"eq", "refl"};
    g_eq_symm = new name{"eq", "symm"};
    g_eq_trans = new name{"eq", "trans"};
    g_eq_subst = new name{"eq", "subst"};
    g_exists_elim = new name{"exists", "elim"};
    g_false = new name{"false"};
    g_false_rec = new name{"false", "rec"};
    g_funext = new name{"funext"};
    g_heq = new name{"heq"};
    g_heq_refl = new name{"heq", "refl"};
    g_heq_to_eq = new name{"heq", "to_eq"};
    g_iff = new name{"iff"};
    g_iff_refl = new name{"iff", "refl"};
    g_iff_false_intro = new name{"iff_false_intro"};
    g_iff_true_intro = new name{"iff_true_intro"};
    g_implies = new name{"implies"};
    g_implies_of_if_pos = new name{"implies_of_if_pos"};
    g_implies_of_if_neg = new name{"implies_of_if_neg"};
    g_is_trunc_is_hprop_elim = new name{"is_trunc", "is_hprop", "elim"};
    g_ite = new name{"ite"};
    g_lift = new name{"lift"};
    g_lift_down = new name{"lift", "down"};
    g_lift_up = new name{"lift", "up"};
    g_nat = new name{"nat"};
    g_nat_of_num = new name{"nat", "of_num"};
    g_nat_succ = new name{"nat", "succ"};
    g_nat_zero = new name{"nat", "zero"};
    g_not = new name{"not"};
    g_num = new name{"num"};
    g_num_zero = new name{"num", "zero"};
    g_num_pos = new name{"num", "pos"};
    g_option = new name{"option"};
    g_option_some = new name{"option", "some"};
    g_option_none = new name{"option", "none"};
    g_or = new name{"or"};
    g_or_elim = new name{"or", "elim"};
    g_or_intro_left = new name{"or", "intro_left"};
    g_or_intro_right = new name{"or", "intro_right"};
    g_poly_unit = new name{"poly_unit"};
    g_poly_unit_star = new name{"poly_unit", "star"};
    g_pos_num = new name{"pos_num"};
    g_pos_num_one = new name{"pos_num", "one"};
    g_pos_num_bit0 = new name{"pos_num", "bit0"};
    g_pos_num_bit1 = new name{"pos_num", "bit1"};
    g_prod = new name{"prod"};
    g_prod_mk = new name{"prod", "mk"};
    g_prod_pr1 = new name{"prod", "pr1"};
    g_prod_pr2 = new name{"prod", "pr2"};
    g_propext = new name{"propext"};
    g_sigma = new name{"sigma"};
    g_sigma_mk = new name{"sigma", "mk"};
    g_string = new name{"string"};
    g_string_empty = new name{"string", "empty"};
    g_string_str = new name{"string", "str"};
    g_subsingleton = new name{"subsingleton"};
    g_subsingleton_elim = new name{"subsingleton", "elim"};
    g_tactic = new name{"tactic"};
    g_tactic_all_goals = new name{"tactic", "all_goals"};
    g_tactic_apply = new name{"tactic", "apply"};
    g_tactic_assert_hypothesis = new name{"tactic", "assert_hypothesis"};
    g_tactic_eapply = new name{"tactic", "eapply"};
    g_tactic_fapply = new name{"tactic", "fapply"};
    g_tactic_eassumption = new name{"tactic", "eassumption"};
    g_tactic_and_then = new name{"tactic", "and_then"};
    g_tactic_append = new name{"tactic", "append"};
    g_tactic_assumption = new name{"tactic", "assumption"};
    g_tactic_at_most = new name{"tactic", "at_most"};
    g_tactic_beta = new name{"tactic", "beta"};
    g_tactic_builtin = new name{"tactic", "builtin"};
    g_tactic_cases = new name{"tactic", "cases"};
    g_tactic_change = new name{"tactic", "change"};
    g_tactic_check_expr = new name{"tactic", "check_expr"};
    g_tactic_clear = new name{"tactic", "clear"};
    g_tactic_clears = new name{"tactic", "clears"};
    g_tactic_determ = new name{"tactic", "determ"};
    g_tactic_discard = new name{"tactic", "discard"};
    g_tactic_intro = new name{"tactic", "intro"};
    g_tactic_intros = new name{"tactic", "intros"};
    g_tactic_exact = new name{"tactic", "exact"};
    g_tactic_expr = new name{"tactic", "expr"};
    g_tactic_expr_builtin = new name{"tactic", "expr", "builtin"};
    g_tactic_expr_list = new name{"tactic", "expr_list"};
    g_tactic_expr_list_cons = new name{"tactic", "expr_list", "cons"};
    g_tactic_expr_list_nil = new name{"tactic", "expr_list", "nil"};
    g_tactic_using_expr = new name{"tactic", "using_expr"};
    g_tactic_none_expr = new name{"tactic", "none_expr"};
    g_tactic_identifier = new name{"tactic", "identifier"};
    g_tactic_identifier_list = new name{"tactic", "identifier_list"};
    g_tactic_opt_expr = new name{"tactic", "opt_expr"};
    g_tactic_opt_identifier_list = new name{"tactic", "opt_identifier_list"};
    g_tactic_fail = new name{"tactic", "fail"};
    g_tactic_fixpoint = new name{"tactic", "fixpoint"};
    g_tactic_focus_at = new name{"tactic", "focus_at"};
    g_tactic_generalize_tac = new name{"tactic", "generalize_tac"};
    g_tactic_generalizes = new name{"tactic", "generalizes"};
    g_tactic_id = new name{"tactic", "id"};
    g_tactic_interleave = new name{"tactic", "interleave"};
    g_tactic_lettac = new name{"tactic", "lettac"};
    g_tactic_now = new name{"tactic", "now"};
    g_tactic_opt_expr_list = new name{"tactic", "opt_expr_list"};
    g_tactic_or_else = new name{"tactic", "or_else"};
    g_tactic_par = new name{"tactic", "par"};
    g_tactic_refine = new name{"tactic", "refine"};
    g_tactic_rename = new name{"tactic", "rename"};
    g_tactic_repeat = new name{"tactic", "repeat"};
    g_tactic_revert = new name{"tactic", "revert"};
    g_tactic_reverts = new name{"tactic", "reverts"};
    g_tactic_rexact = new name{"tactic", "rexact"};
    g_tactic_rotate_left = new name{"tactic", "rotate_left"};
    g_tactic_rotate_right = new name{"tactic", "rotate_right"};
    g_tactic_state = new name{"tactic", "state"};
    g_tactic_trace = new name{"tactic", "trace"};
    g_tactic_try_for = new name{"tactic", "try_for"};
    g_tactic_whnf = new name{"tactic", "whnf"};
    g_trans_rel_left = new name{"trans_rel_left"};
    g_trans_rel_right = new name{"trans_rel_right"};
    g_true = new name{"true"};
    g_true_intro = new name{"true", "intro"};
    g_is_trunc_is_hset = new name{"is_trunc", "is_hset"};
    g_is_trunc_is_hprop = new name{"is_trunc", "is_hprop"};
    g_well_founded = new name{"well_founded"};
}
void finalize_constants() {
    delete g_absurd;
    delete g_and;
    delete g_and_elim_left;
    delete g_and_elim_right;
    delete g_and_intro;
    delete g_bool;
    delete g_bool_ff;
    delete g_bool_tt;
    delete g_char;
    delete g_char_mk;
    delete g_congr;
    delete g_dite;
    delete g_empty;
    delete g_empty_rec;
    delete g_eq;
    delete g_eq_elim_inv_inv;
    delete g_eq_intro;
    delete g_eq_rec;
    delete g_eq_drec;
    delete g_eq_rec_eq;
    delete g_eq_refl;
    delete g_eq_symm;
    delete g_eq_trans;
    delete g_eq_subst;
    delete g_exists_elim;
    delete g_false;
    delete g_false_rec;
    delete g_funext;
    delete g_heq;
    delete g_heq_refl;
    delete g_heq_to_eq;
    delete g_iff;
    delete g_iff_refl;
    delete g_iff_false_intro;
    delete g_iff_true_intro;
    delete g_implies;
    delete g_implies_of_if_pos;
    delete g_implies_of_if_neg;
    delete g_is_trunc_is_hprop_elim;
    delete g_ite;
    delete g_lift;
    delete g_lift_down;
    delete g_lift_up;
    delete g_nat;
    delete g_nat_of_num;
    delete g_nat_succ;
    delete g_nat_zero;
    delete g_not;
    delete g_num;
    delete g_num_zero;
    delete g_num_pos;
    delete g_option;
    delete g_option_some;
    delete g_option_none;
    delete g_or;
    delete g_or_elim;
    delete g_or_intro_left;
    delete g_or_intro_right;
    delete g_poly_unit;
    delete g_poly_unit_star;
    delete g_pos_num;
    delete g_pos_num_one;
    delete g_pos_num_bit0;
    delete g_pos_num_bit1;
    delete g_prod;
    delete g_prod_mk;
    delete g_prod_pr1;
    delete g_prod_pr2;
    delete g_propext;
    delete g_sigma;
    delete g_sigma_mk;
    delete g_string;
    delete g_string_empty;
    delete g_string_str;
    delete g_subsingleton;
    delete g_subsingleton_elim;
    delete g_tactic;
    delete g_tactic_all_goals;
    delete g_tactic_apply;
    delete g_tactic_assert_hypothesis;
    delete g_tactic_eapply;
    delete g_tactic_fapply;
    delete g_tactic_eassumption;
    delete g_tactic_and_then;
    delete g_tactic_append;
    delete g_tactic_assumption;
    delete g_tactic_at_most;
    delete g_tactic_beta;
    delete g_tactic_builtin;
    delete g_tactic_cases;
    delete g_tactic_change;
    delete g_tactic_check_expr;
    delete g_tactic_clear;
    delete g_tactic_clears;
    delete g_tactic_determ;
    delete g_tactic_discard;
    delete g_tactic_intro;
    delete g_tactic_intros;
    delete g_tactic_exact;
    delete g_tactic_expr;
    delete g_tactic_expr_builtin;
    delete g_tactic_expr_list;
    delete g_tactic_expr_list_cons;
    delete g_tactic_expr_list_nil;
    delete g_tactic_using_expr;
    delete g_tactic_none_expr;
    delete g_tactic_identifier;
    delete g_tactic_identifier_list;
    delete g_tactic_opt_expr;
    delete g_tactic_opt_identifier_list;
    delete g_tactic_fail;
    delete g_tactic_fixpoint;
    delete g_tactic_focus_at;
    delete g_tactic_generalize_tac;
    delete g_tactic_generalizes;
    delete g_tactic_id;
    delete g_tactic_interleave;
    delete g_tactic_lettac;
    delete g_tactic_now;
    delete g_tactic_opt_expr_list;
    delete g_tactic_or_else;
    delete g_tactic_par;
    delete g_tactic_refine;
    delete g_tactic_rename;
    delete g_tactic_repeat;
    delete g_tactic_revert;
    delete g_tactic_reverts;
    delete g_tactic_rexact;
    delete g_tactic_rotate_left;
    delete g_tactic_rotate_right;
    delete g_tactic_state;
    delete g_tactic_trace;
    delete g_tactic_try_for;
    delete g_tactic_whnf;
    delete g_trans_rel_left;
    delete g_trans_rel_right;
    delete g_true;
    delete g_true_intro;
    delete g_is_trunc_is_hset;
    delete g_is_trunc_is_hprop;
    delete g_well_founded;
}
name const & get_absurd_name() { return *g_absurd; }
name const & get_and_name() { return *g_and; }
name const & get_and_elim_left_name() { return *g_and_elim_left; }
name const & get_and_elim_right_name() { return *g_and_elim_right; }
name const & get_and_intro_name() { return *g_and_intro; }
name const & get_bool_name() { return *g_bool; }
name const & get_bool_ff_name() { return *g_bool_ff; }
name const & get_bool_tt_name() { return *g_bool_tt; }
name const & get_char_name() { return *g_char; }
name const & get_char_mk_name() { return *g_char_mk; }
name const & get_congr_name() { return *g_congr; }
name const & get_dite_name() { return *g_dite; }
name const & get_empty_name() { return *g_empty; }
name const & get_empty_rec_name() { return *g_empty_rec; }
name const & get_eq_name() { return *g_eq; }
name const & get_eq_elim_inv_inv_name() { return *g_eq_elim_inv_inv; }
name const & get_eq_intro_name() { return *g_eq_intro; }
name const & get_eq_rec_name() { return *g_eq_rec; }
name const & get_eq_drec_name() { return *g_eq_drec; }
name const & get_eq_rec_eq_name() { return *g_eq_rec_eq; }
name const & get_eq_refl_name() { return *g_eq_refl; }
name const & get_eq_symm_name() { return *g_eq_symm; }
name const & get_eq_trans_name() { return *g_eq_trans; }
name const & get_eq_subst_name() { return *g_eq_subst; }
name const & get_exists_elim_name() { return *g_exists_elim; }
name const & get_false_name() { return *g_false; }
name const & get_false_rec_name() { return *g_false_rec; }
name const & get_funext_name() { return *g_funext; }
name const & get_heq_name() { return *g_heq; }
name const & get_heq_refl_name() { return *g_heq_refl; }
name const & get_heq_to_eq_name() { return *g_heq_to_eq; }
name const & get_iff_name() { return *g_iff; }
name const & get_iff_refl_name() { return *g_iff_refl; }
name const & get_iff_false_intro_name() { return *g_iff_false_intro; }
name const & get_iff_true_intro_name() { return *g_iff_true_intro; }
name const & get_implies_name() { return *g_implies; }
name const & get_implies_of_if_pos_name() { return *g_implies_of_if_pos; }
name const & get_implies_of_if_neg_name() { return *g_implies_of_if_neg; }
name const & get_is_trunc_is_hprop_elim_name() { return *g_is_trunc_is_hprop_elim; }
name const & get_ite_name() { return *g_ite; }
name const & get_lift_name() { return *g_lift; }
name const & get_lift_down_name() { return *g_lift_down; }
name const & get_lift_up_name() { return *g_lift_up; }
name const & get_nat_name() { return *g_nat; }
name const & get_nat_of_num_name() { return *g_nat_of_num; }
name const & get_nat_succ_name() { return *g_nat_succ; }
name const & get_nat_zero_name() { return *g_nat_zero; }
name const & get_not_name() { return *g_not; }
name const & get_num_name() { return *g_num; }
name const & get_num_zero_name() { return *g_num_zero; }
name const & get_num_pos_name() { return *g_num_pos; }
name const & get_option_name() { return *g_option; }
name const & get_option_some_name() { return *g_option_some; }
name const & get_option_none_name() { return *g_option_none; }
name const & get_or_name() { return *g_or; }
name const & get_or_elim_name() { return *g_or_elim; }
name const & get_or_intro_left_name() { return *g_or_intro_left; }
name const & get_or_intro_right_name() { return *g_or_intro_right; }
name const & get_poly_unit_name() { return *g_poly_unit; }
name const & get_poly_unit_star_name() { return *g_poly_unit_star; }
name const & get_pos_num_name() { return *g_pos_num; }
name const & get_pos_num_one_name() { return *g_pos_num_one; }
name const & get_pos_num_bit0_name() { return *g_pos_num_bit0; }
name const & get_pos_num_bit1_name() { return *g_pos_num_bit1; }
name const & get_prod_name() { return *g_prod; }
name const & get_prod_mk_name() { return *g_prod_mk; }
name const & get_prod_pr1_name() { return *g_prod_pr1; }
name const & get_prod_pr2_name() { return *g_prod_pr2; }
name const & get_propext_name() { return *g_propext; }
name const & get_sigma_name() { return *g_sigma; }
name const & get_sigma_mk_name() { return *g_sigma_mk; }
name const & get_string_name() { return *g_string; }
name const & get_string_empty_name() { return *g_string_empty; }
name const & get_string_str_name() { return *g_string_str; }
name const & get_subsingleton_name() { return *g_subsingleton; }
name const & get_subsingleton_elim_name() { return *g_subsingleton_elim; }
name const & get_tactic_name() { return *g_tactic; }
name const & get_tactic_all_goals_name() { return *g_tactic_all_goals; }
name const & get_tactic_apply_name() { return *g_tactic_apply; }
name const & get_tactic_assert_hypothesis_name() { return *g_tactic_assert_hypothesis; }
name const & get_tactic_eapply_name() { return *g_tactic_eapply; }
name const & get_tactic_fapply_name() { return *g_tactic_fapply; }
name const & get_tactic_eassumption_name() { return *g_tactic_eassumption; }
name const & get_tactic_and_then_name() { return *g_tactic_and_then; }
name const & get_tactic_append_name() { return *g_tactic_append; }
name const & get_tactic_assumption_name() { return *g_tactic_assumption; }
name const & get_tactic_at_most_name() { return *g_tactic_at_most; }
name const & get_tactic_beta_name() { return *g_tactic_beta; }
name const & get_tactic_builtin_name() { return *g_tactic_builtin; }
name const & get_tactic_cases_name() { return *g_tactic_cases; }
name const & get_tactic_change_name() { return *g_tactic_change; }
name const & get_tactic_check_expr_name() { return *g_tactic_check_expr; }
name const & get_tactic_clear_name() { return *g_tactic_clear; }
name const & get_tactic_clears_name() { return *g_tactic_clears; }
name const & get_tactic_determ_name() { return *g_tactic_determ; }
name const & get_tactic_discard_name() { return *g_tactic_discard; }
name const & get_tactic_intro_name() { return *g_tactic_intro; }
name const & get_tactic_intros_name() { return *g_tactic_intros; }
name const & get_tactic_exact_name() { return *g_tactic_exact; }
name const & get_tactic_expr_name() { return *g_tactic_expr; }
name const & get_tactic_expr_builtin_name() { return *g_tactic_expr_builtin; }
name const & get_tactic_expr_list_name() { return *g_tactic_expr_list; }
name const & get_tactic_expr_list_cons_name() { return *g_tactic_expr_list_cons; }
name const & get_tactic_expr_list_nil_name() { return *g_tactic_expr_list_nil; }
name const & get_tactic_using_expr_name() { return *g_tactic_using_expr; }
name const & get_tactic_none_expr_name() { return *g_tactic_none_expr; }
name const & get_tactic_identifier_name() { return *g_tactic_identifier; }
name const & get_tactic_identifier_list_name() { return *g_tactic_identifier_list; }
name const & get_tactic_opt_expr_name() { return *g_tactic_opt_expr; }
name const & get_tactic_opt_identifier_list_name() { return *g_tactic_opt_identifier_list; }
name const & get_tactic_fail_name() { return *g_tactic_fail; }
name const & get_tactic_fixpoint_name() { return *g_tactic_fixpoint; }
name const & get_tactic_focus_at_name() { return *g_tactic_focus_at; }
name const & get_tactic_generalize_tac_name() { return *g_tactic_generalize_tac; }
name const & get_tactic_generalizes_name() { return *g_tactic_generalizes; }
name const & get_tactic_id_name() { return *g_tactic_id; }
name const & get_tactic_interleave_name() { return *g_tactic_interleave; }
name const & get_tactic_lettac_name() { return *g_tactic_lettac; }
name const & get_tactic_now_name() { return *g_tactic_now; }
name const & get_tactic_opt_expr_list_name() { return *g_tactic_opt_expr_list; }
name const & get_tactic_or_else_name() { return *g_tactic_or_else; }
name const & get_tactic_par_name() { return *g_tactic_par; }
name const & get_tactic_refine_name() { return *g_tactic_refine; }
name const & get_tactic_rename_name() { return *g_tactic_rename; }
name const & get_tactic_repeat_name() { return *g_tactic_repeat; }
name const & get_tactic_revert_name() { return *g_tactic_revert; }
name const & get_tactic_reverts_name() { return *g_tactic_reverts; }
name const & get_tactic_rexact_name() { return *g_tactic_rexact; }
name const & get_tactic_rotate_left_name() { return *g_tactic_rotate_left; }
name const & get_tactic_rotate_right_name() { return *g_tactic_rotate_right; }
name const & get_tactic_state_name() { return *g_tactic_state; }
name const & get_tactic_trace_name() { return *g_tactic_trace; }
name const & get_tactic_try_for_name() { return *g_tactic_try_for; }
name const & get_tactic_whnf_name() { return *g_tactic_whnf; }
name const & get_trans_rel_left_name() { return *g_trans_rel_left; }
name const & get_trans_rel_right_name() { return *g_trans_rel_right; }
name const & get_true_name() { return *g_true; }
name const & get_true_intro_name() { return *g_true_intro; }
name const & get_is_trunc_is_hset_name() { return *g_is_trunc_is_hset; }
name const & get_is_trunc_is_hprop_name() { return *g_is_trunc_is_hprop; }
name const & get_well_founded_name() { return *g_well_founded; }
}
