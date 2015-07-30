// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// DO NOT EDIT, automatically generated file, generator scripts/gen_tokens_cpp.py
#include "util/name.h"
namespace lean{
static name const * g_period_tk = nullptr;
static name const * g_placeholder_tk = nullptr;
static name const * g_colon_tk = nullptr;
static name const * g_semicolon_tk = nullptr;
static name const * g_dcolon_tk = nullptr;
static name const * g_lparen_tk = nullptr;
static name const * g_rparen_tk = nullptr;
static name const * g_llevel_curly_tk = nullptr;
static name const * g_lcurly_tk = nullptr;
static name const * g_rcurly_tk = nullptr;
static name const * g_ldcurly_tk = nullptr;
static name const * g_rdcurly_tk = nullptr;
static name const * g_lcurlybar_tk = nullptr;
static name const * g_rcurlybar_tk = nullptr;
static name const * g_lbracket_tk = nullptr;
static name const * g_rbracket_tk = nullptr;
static name const * g_langle_tk = nullptr;
static name const * g_rangle_tk = nullptr;
static name const * g_triangle_tk = nullptr;
static name const * g_caret_tk = nullptr;
static name const * g_up_tk = nullptr;
static name const * g_down_tk = nullptr;
static name const * g_bar_tk = nullptr;
static name const * g_comma_tk = nullptr;
static name const * g_add_tk = nullptr;
static name const * g_sub_tk = nullptr;
static name const * g_greater_tk = nullptr;
static name const * g_question_tk = nullptr;
static name const * g_question_lp_tk = nullptr;
static name const * g_bang_tk = nullptr;
static name const * g_slash_tk = nullptr;
static name const * g_plus_tk = nullptr;
static name const * g_star_tk = nullptr;
static name const * g_turnstile_tk = nullptr;
static name const * g_explicit_tk = nullptr;
static name const * g_max_tk = nullptr;
static name const * g_imax_tk = nullptr;
static name const * g_cup_tk = nullptr;
static name const * g_import_tk = nullptr;
static name const * g_prelude_tk = nullptr;
static name const * g_show_tk = nullptr;
static name const * g_have_tk = nullptr;
static name const * g_assert_tk = nullptr;
static name const * g_assume_tk = nullptr;
static name const * g_suppose_tk = nullptr;
static name const * g_take_tk = nullptr;
static name const * g_fun_tk = nullptr;
static name const * g_match_tk = nullptr;
static name const * g_ellipsis_tk = nullptr;
static name const * g_raw_tk = nullptr;
static name const * g_true_tk = nullptr;
static name const * g_false_tk = nullptr;
static name const * g_options_tk = nullptr;
static name const * g_commands_tk = nullptr;
static name const * g_instances_tk = nullptr;
static name const * g_classes_tk = nullptr;
static name const * g_coercions_tk = nullptr;
static name const * g_arrow_tk = nullptr;
static name const * g_declarations_tk = nullptr;
static name const * g_decls_tk = nullptr;
static name const * g_hiding_tk = nullptr;
static name const * g_exposing_tk = nullptr;
static name const * g_renaming_tk = nullptr;
static name const * g_replacing_tk = nullptr;
static name const * g_extends_tk = nullptr;
static name const * g_as_tk = nullptr;
static name const * g_none_tk = nullptr;
static name const * g_whnf_tk = nullptr;
static name const * g_wf_tk = nullptr;
static name const * g_in_tk = nullptr;
static name const * g_at_tk = nullptr;
static name const * g_assign_tk = nullptr;
static name const * g_visible_tk = nullptr;
static name const * g_from_tk = nullptr;
static name const * g_using_tk = nullptr;
static name const * g_then_tk = nullptr;
static name const * g_else_tk = nullptr;
static name const * g_by_tk = nullptr;
static name const * g_rewrite_tk = nullptr;
static name const * g_proof_tk = nullptr;
static name const * g_qed_tk = nullptr;
static name const * g_begin_tk = nullptr;
static name const * g_begin_plus_tk = nullptr;
static name const * g_end_tk = nullptr;
static name const * g_private_tk = nullptr;
static name const * g_protected_tk = nullptr;
static name const * g_definition_tk = nullptr;
static name const * g_theorem_tk = nullptr;
static name const * g_abbreviation_tk = nullptr;
static name const * g_axiom_tk = nullptr;
static name const * g_axioms_tk = nullptr;
static name const * g_constant_tk = nullptr;
static name const * g_constants_tk = nullptr;
static name const * g_variable_tk = nullptr;
static name const * g_variables_tk = nullptr;
static name const * g_instance_tk = nullptr;
static name const * g_trans_inst_tk = nullptr;
static name const * g_priority_tk = nullptr;
static name const * g_unfold_tk = nullptr;
static name const * g_unfold_full_tk = nullptr;
static name const * g_unfold_hints_bracket_tk = nullptr;
static name const * g_unfold_hints_tk = nullptr;
static name const * g_constructor_tk = nullptr;
static name const * g_coercion_tk = nullptr;
static name const * g_reducible_tk = nullptr;
static name const * g_quasireducible_tk = nullptr;
static name const * g_semireducible_tk = nullptr;
static name const * g_irreducible_tk = nullptr;
static name const * g_parsing_only_tk = nullptr;
static name const * g_symm_tk = nullptr;
static name const * g_trans_tk = nullptr;
static name const * g_refl_tk = nullptr;
static name const * g_subst_tk = nullptr;
static name const * g_simp_attr_tk = nullptr;
static name const * g_congr_attr_tk = nullptr;
static name const * g_recursor_tk = nullptr;
static name const * g_attribute_tk = nullptr;
static name const * g_with_tk = nullptr;
static name const * g_class_tk = nullptr;
static name const * g_multiple_instances_tk = nullptr;
static name const * g_prev_tk = nullptr;
static name const * g_scoped_tk = nullptr;
static name const * g_foldr_tk = nullptr;
static name const * g_foldl_tk = nullptr;
static name const * g_binder_tk = nullptr;
static name const * g_binders_tk = nullptr;
static name const * g_precedence_tk = nullptr;
static name const * g_infix_tk = nullptr;
static name const * g_infixl_tk = nullptr;
static name const * g_infixr_tk = nullptr;
static name const * g_postfix_tk = nullptr;
static name const * g_prefix_tk = nullptr;
static name const * g_notation_tk = nullptr;
static name const * g_tactic_infix_tk = nullptr;
static name const * g_tactic_infixl_tk = nullptr;
static name const * g_tactic_infixr_tk = nullptr;
static name const * g_tactic_postfix_tk = nullptr;
static name const * g_tactic_prefix_tk = nullptr;
static name const * g_tactic_notation_tk = nullptr;
static name const * g_call_tk = nullptr;
static name const * g_calc_tk = nullptr;
static name const * g_obtain_tk = nullptr;
static name const * g_persistent_tk = nullptr;
static name const * g_root_tk = nullptr;
static name const * g_fields_tk = nullptr;
static name const * g_trust_tk = nullptr;
static name const * g_metaclasses_tk = nullptr;
static name const * g_inductive_tk = nullptr;
static name const * g_this_tk = nullptr;
static name const * g_noncomputable_tk = nullptr;
static name const * g_theory_tk = nullptr;
void initialize_tokens() {
    g_period_tk = new name{"."};
    g_placeholder_tk = new name{"_"};
    g_colon_tk = new name{":"};
    g_semicolon_tk = new name{";"};
    g_dcolon_tk = new name{"::"};
    g_lparen_tk = new name{"("};
    g_rparen_tk = new name{")"};
    g_llevel_curly_tk = new name{".{"};
    g_lcurly_tk = new name{"{"};
    g_rcurly_tk = new name{"}"};
    g_ldcurly_tk = new name{"⦃"};
    g_rdcurly_tk = new name{"⦄"};
    g_lcurlybar_tk = new name{"{|"};
    g_rcurlybar_tk = new name{"|}"};
    g_lbracket_tk = new name{"["};
    g_rbracket_tk = new name{"]"};
    g_langle_tk = new name{"⟨"};
    g_rangle_tk = new name{"⟩"};
    g_triangle_tk = new name{"▸"};
    g_caret_tk = new name{"^"};
    g_up_tk = new name{"↑"};
    g_down_tk = new name{"<d"};
    g_bar_tk = new name{"|"};
    g_comma_tk = new name{","};
    g_add_tk = new name{"+"};
    g_sub_tk = new name{"-"};
    g_greater_tk = new name{">"};
    g_question_tk = new name{"?"};
    g_question_lp_tk = new name{"?("};
    g_bang_tk = new name{"!"};
    g_slash_tk = new name{"/"};
    g_plus_tk = new name{"+"};
    g_star_tk = new name{"*"};
    g_turnstile_tk = new name{"⊢"};
    g_explicit_tk = new name{"@"};
    g_max_tk = new name{"max"};
    g_imax_tk = new name{"imax"};
    g_cup_tk = new name{"\u2294"};
    g_import_tk = new name{"import"};
    g_prelude_tk = new name{"prelude"};
    g_show_tk = new name{"show"};
    g_have_tk = new name{"have"};
    g_assert_tk = new name{"assert"};
    g_assume_tk = new name{"assume"};
    g_suppose_tk = new name{"suppose"};
    g_take_tk = new name{"take"};
    g_fun_tk = new name{"fun"};
    g_match_tk = new name{"match"};
    g_ellipsis_tk = new name{"..."};
    g_raw_tk = new name{"raw"};
    g_true_tk = new name{"true"};
    g_false_tk = new name{"false"};
    g_options_tk = new name{"options"};
    g_commands_tk = new name{"commands"};
    g_instances_tk = new name{"instances"};
    g_classes_tk = new name{"classes"};
    g_coercions_tk = new name{"coercions"};
    g_arrow_tk = new name{"->"};
    g_declarations_tk = new name{"declarations"};
    g_decls_tk = new name{"decls"};
    g_hiding_tk = new name{"hiding"};
    g_exposing_tk = new name{"exposing"};
    g_renaming_tk = new name{"renaming"};
    g_replacing_tk = new name{"replacing"};
    g_extends_tk = new name{"extends"};
    g_as_tk = new name{"as"};
    g_none_tk = new name{"[none]"};
    g_whnf_tk = new name{"[whnf]"};
    g_wf_tk = new name{"[wf]"};
    g_in_tk = new name{"in"};
    g_at_tk = new name{"at"};
    g_assign_tk = new name{":="};
    g_visible_tk = new name{"[visible]"};
    g_from_tk = new name{"from"};
    g_using_tk = new name{"using"};
    g_then_tk = new name{"then"};
    g_else_tk = new name{"else"};
    g_by_tk = new name{"by"};
    g_rewrite_tk = new name{"rewrite"};
    g_proof_tk = new name{"proof"};
    g_qed_tk = new name{"qed"};
    g_begin_tk = new name{"begin"};
    g_begin_plus_tk = new name{"begin+"};
    g_end_tk = new name{"end"};
    g_private_tk = new name{"private"};
    g_protected_tk = new name{"protected"};
    g_definition_tk = new name{"definition"};
    g_theorem_tk = new name{"theorem"};
    g_abbreviation_tk = new name{"abbreviation"};
    g_axiom_tk = new name{"axiom"};
    g_axioms_tk = new name{"axioms"};
    g_constant_tk = new name{"constant"};
    g_constants_tk = new name{"constants"};
    g_variable_tk = new name{"variable"};
    g_variables_tk = new name{"variables"};
    g_instance_tk = new name{"[instance]"};
    g_trans_inst_tk = new name{"[trans-instance]"};
    g_priority_tk = new name{"[priority"};
    g_unfold_tk = new name{"[unfold"};
    g_unfold_full_tk = new name{"[unfold-full]"};
    g_unfold_hints_bracket_tk = new name{"[unfold-hints]"};
    g_unfold_hints_tk = new name{"unfold-hints"};
    g_constructor_tk = new name{"[constructor]"};
    g_coercion_tk = new name{"[coercion]"};
    g_reducible_tk = new name{"[reducible]"};
    g_quasireducible_tk = new name{"[quasireducible]"};
    g_semireducible_tk = new name{"[semireducible]"};
    g_irreducible_tk = new name{"[irreducible]"};
    g_parsing_only_tk = new name{"[parsing-only]"};
    g_symm_tk = new name{"[symm]"};
    g_trans_tk = new name{"[trans]"};
    g_refl_tk = new name{"[refl]"};
    g_subst_tk = new name{"[subst]"};
    g_simp_attr_tk = new name{"[simp]"};
    g_congr_attr_tk = new name{"[congr]"};
    g_recursor_tk = new name{"[recursor"};
    g_attribute_tk = new name{"attribute"};
    g_with_tk = new name{"with"};
    g_class_tk = new name{"[class]"};
    g_multiple_instances_tk = new name{"[multiple-instances]"};
    g_prev_tk = new name{"prev"};
    g_scoped_tk = new name{"scoped"};
    g_foldr_tk = new name{"foldr"};
    g_foldl_tk = new name{"foldl"};
    g_binder_tk = new name{"binder"};
    g_binders_tk = new name{"binders"};
    g_precedence_tk = new name{"precedence"};
    g_infix_tk = new name{"infix"};
    g_infixl_tk = new name{"infixl"};
    g_infixr_tk = new name{"infixr"};
    g_postfix_tk = new name{"postfix"};
    g_prefix_tk = new name{"prefix"};
    g_notation_tk = new name{"notation"};
    g_tactic_infix_tk = new name{"tactic_infix"};
    g_tactic_infixl_tk = new name{"tactic_infixl"};
    g_tactic_infixr_tk = new name{"tactic_infixr"};
    g_tactic_postfix_tk = new name{"tactic_postfix"};
    g_tactic_prefix_tk = new name{"tactic_prefix"};
    g_tactic_notation_tk = new name{"tactic_notation"};
    g_call_tk = new name{"call"};
    g_calc_tk = new name{"calc"};
    g_obtain_tk = new name{"obtain"};
    g_persistent_tk = new name{"[persistent]"};
    g_root_tk = new name{"_root_"};
    g_fields_tk = new name{"fields"};
    g_trust_tk = new name{"trust"};
    g_metaclasses_tk = new name{"metaclasses"};
    g_inductive_tk = new name{"inductive"};
    g_this_tk = new name{"this"};
    g_noncomputable_tk = new name{"noncomputable"};
    g_theory_tk = new name{"theory"};
}
void finalize_tokens() {
    delete g_period_tk;
    delete g_placeholder_tk;
    delete g_colon_tk;
    delete g_semicolon_tk;
    delete g_dcolon_tk;
    delete g_lparen_tk;
    delete g_rparen_tk;
    delete g_llevel_curly_tk;
    delete g_lcurly_tk;
    delete g_rcurly_tk;
    delete g_ldcurly_tk;
    delete g_rdcurly_tk;
    delete g_lcurlybar_tk;
    delete g_rcurlybar_tk;
    delete g_lbracket_tk;
    delete g_rbracket_tk;
    delete g_langle_tk;
    delete g_rangle_tk;
    delete g_triangle_tk;
    delete g_caret_tk;
    delete g_up_tk;
    delete g_down_tk;
    delete g_bar_tk;
    delete g_comma_tk;
    delete g_add_tk;
    delete g_sub_tk;
    delete g_greater_tk;
    delete g_question_tk;
    delete g_question_lp_tk;
    delete g_bang_tk;
    delete g_slash_tk;
    delete g_plus_tk;
    delete g_star_tk;
    delete g_turnstile_tk;
    delete g_explicit_tk;
    delete g_max_tk;
    delete g_imax_tk;
    delete g_cup_tk;
    delete g_import_tk;
    delete g_prelude_tk;
    delete g_show_tk;
    delete g_have_tk;
    delete g_assert_tk;
    delete g_assume_tk;
    delete g_suppose_tk;
    delete g_take_tk;
    delete g_fun_tk;
    delete g_match_tk;
    delete g_ellipsis_tk;
    delete g_raw_tk;
    delete g_true_tk;
    delete g_false_tk;
    delete g_options_tk;
    delete g_commands_tk;
    delete g_instances_tk;
    delete g_classes_tk;
    delete g_coercions_tk;
    delete g_arrow_tk;
    delete g_declarations_tk;
    delete g_decls_tk;
    delete g_hiding_tk;
    delete g_exposing_tk;
    delete g_renaming_tk;
    delete g_replacing_tk;
    delete g_extends_tk;
    delete g_as_tk;
    delete g_none_tk;
    delete g_whnf_tk;
    delete g_wf_tk;
    delete g_in_tk;
    delete g_at_tk;
    delete g_assign_tk;
    delete g_visible_tk;
    delete g_from_tk;
    delete g_using_tk;
    delete g_then_tk;
    delete g_else_tk;
    delete g_by_tk;
    delete g_rewrite_tk;
    delete g_proof_tk;
    delete g_qed_tk;
    delete g_begin_tk;
    delete g_begin_plus_tk;
    delete g_end_tk;
    delete g_private_tk;
    delete g_protected_tk;
    delete g_definition_tk;
    delete g_theorem_tk;
    delete g_abbreviation_tk;
    delete g_axiom_tk;
    delete g_axioms_tk;
    delete g_constant_tk;
    delete g_constants_tk;
    delete g_variable_tk;
    delete g_variables_tk;
    delete g_instance_tk;
    delete g_trans_inst_tk;
    delete g_priority_tk;
    delete g_unfold_tk;
    delete g_unfold_full_tk;
    delete g_unfold_hints_bracket_tk;
    delete g_unfold_hints_tk;
    delete g_constructor_tk;
    delete g_coercion_tk;
    delete g_reducible_tk;
    delete g_quasireducible_tk;
    delete g_semireducible_tk;
    delete g_irreducible_tk;
    delete g_parsing_only_tk;
    delete g_symm_tk;
    delete g_trans_tk;
    delete g_refl_tk;
    delete g_subst_tk;
    delete g_simp_attr_tk;
    delete g_congr_attr_tk;
    delete g_recursor_tk;
    delete g_attribute_tk;
    delete g_with_tk;
    delete g_class_tk;
    delete g_multiple_instances_tk;
    delete g_prev_tk;
    delete g_scoped_tk;
    delete g_foldr_tk;
    delete g_foldl_tk;
    delete g_binder_tk;
    delete g_binders_tk;
    delete g_precedence_tk;
    delete g_infix_tk;
    delete g_infixl_tk;
    delete g_infixr_tk;
    delete g_postfix_tk;
    delete g_prefix_tk;
    delete g_notation_tk;
    delete g_tactic_infix_tk;
    delete g_tactic_infixl_tk;
    delete g_tactic_infixr_tk;
    delete g_tactic_postfix_tk;
    delete g_tactic_prefix_tk;
    delete g_tactic_notation_tk;
    delete g_call_tk;
    delete g_calc_tk;
    delete g_obtain_tk;
    delete g_persistent_tk;
    delete g_root_tk;
    delete g_fields_tk;
    delete g_trust_tk;
    delete g_metaclasses_tk;
    delete g_inductive_tk;
    delete g_this_tk;
    delete g_noncomputable_tk;
    delete g_theory_tk;
}
name const & get_period_tk() { return *g_period_tk; }
name const & get_placeholder_tk() { return *g_placeholder_tk; }
name const & get_colon_tk() { return *g_colon_tk; }
name const & get_semicolon_tk() { return *g_semicolon_tk; }
name const & get_dcolon_tk() { return *g_dcolon_tk; }
name const & get_lparen_tk() { return *g_lparen_tk; }
name const & get_rparen_tk() { return *g_rparen_tk; }
name const & get_llevel_curly_tk() { return *g_llevel_curly_tk; }
name const & get_lcurly_tk() { return *g_lcurly_tk; }
name const & get_rcurly_tk() { return *g_rcurly_tk; }
name const & get_ldcurly_tk() { return *g_ldcurly_tk; }
name const & get_rdcurly_tk() { return *g_rdcurly_tk; }
name const & get_lcurlybar_tk() { return *g_lcurlybar_tk; }
name const & get_rcurlybar_tk() { return *g_rcurlybar_tk; }
name const & get_lbracket_tk() { return *g_lbracket_tk; }
name const & get_rbracket_tk() { return *g_rbracket_tk; }
name const & get_langle_tk() { return *g_langle_tk; }
name const & get_rangle_tk() { return *g_rangle_tk; }
name const & get_triangle_tk() { return *g_triangle_tk; }
name const & get_caret_tk() { return *g_caret_tk; }
name const & get_up_tk() { return *g_up_tk; }
name const & get_down_tk() { return *g_down_tk; }
name const & get_bar_tk() { return *g_bar_tk; }
name const & get_comma_tk() { return *g_comma_tk; }
name const & get_add_tk() { return *g_add_tk; }
name const & get_sub_tk() { return *g_sub_tk; }
name const & get_greater_tk() { return *g_greater_tk; }
name const & get_question_tk() { return *g_question_tk; }
name const & get_question_lp_tk() { return *g_question_lp_tk; }
name const & get_bang_tk() { return *g_bang_tk; }
name const & get_slash_tk() { return *g_slash_tk; }
name const & get_plus_tk() { return *g_plus_tk; }
name const & get_star_tk() { return *g_star_tk; }
name const & get_turnstile_tk() { return *g_turnstile_tk; }
name const & get_explicit_tk() { return *g_explicit_tk; }
name const & get_max_tk() { return *g_max_tk; }
name const & get_imax_tk() { return *g_imax_tk; }
name const & get_cup_tk() { return *g_cup_tk; }
name const & get_import_tk() { return *g_import_tk; }
name const & get_prelude_tk() { return *g_prelude_tk; }
name const & get_show_tk() { return *g_show_tk; }
name const & get_have_tk() { return *g_have_tk; }
name const & get_assert_tk() { return *g_assert_tk; }
name const & get_assume_tk() { return *g_assume_tk; }
name const & get_suppose_tk() { return *g_suppose_tk; }
name const & get_take_tk() { return *g_take_tk; }
name const & get_fun_tk() { return *g_fun_tk; }
name const & get_match_tk() { return *g_match_tk; }
name const & get_ellipsis_tk() { return *g_ellipsis_tk; }
name const & get_raw_tk() { return *g_raw_tk; }
name const & get_true_tk() { return *g_true_tk; }
name const & get_false_tk() { return *g_false_tk; }
name const & get_options_tk() { return *g_options_tk; }
name const & get_commands_tk() { return *g_commands_tk; }
name const & get_instances_tk() { return *g_instances_tk; }
name const & get_classes_tk() { return *g_classes_tk; }
name const & get_coercions_tk() { return *g_coercions_tk; }
name const & get_arrow_tk() { return *g_arrow_tk; }
name const & get_declarations_tk() { return *g_declarations_tk; }
name const & get_decls_tk() { return *g_decls_tk; }
name const & get_hiding_tk() { return *g_hiding_tk; }
name const & get_exposing_tk() { return *g_exposing_tk; }
name const & get_renaming_tk() { return *g_renaming_tk; }
name const & get_replacing_tk() { return *g_replacing_tk; }
name const & get_extends_tk() { return *g_extends_tk; }
name const & get_as_tk() { return *g_as_tk; }
name const & get_none_tk() { return *g_none_tk; }
name const & get_whnf_tk() { return *g_whnf_tk; }
name const & get_wf_tk() { return *g_wf_tk; }
name const & get_in_tk() { return *g_in_tk; }
name const & get_at_tk() { return *g_at_tk; }
name const & get_assign_tk() { return *g_assign_tk; }
name const & get_visible_tk() { return *g_visible_tk; }
name const & get_from_tk() { return *g_from_tk; }
name const & get_using_tk() { return *g_using_tk; }
name const & get_then_tk() { return *g_then_tk; }
name const & get_else_tk() { return *g_else_tk; }
name const & get_by_tk() { return *g_by_tk; }
name const & get_rewrite_tk() { return *g_rewrite_tk; }
name const & get_proof_tk() { return *g_proof_tk; }
name const & get_qed_tk() { return *g_qed_tk; }
name const & get_begin_tk() { return *g_begin_tk; }
name const & get_begin_plus_tk() { return *g_begin_plus_tk; }
name const & get_end_tk() { return *g_end_tk; }
name const & get_private_tk() { return *g_private_tk; }
name const & get_protected_tk() { return *g_protected_tk; }
name const & get_definition_tk() { return *g_definition_tk; }
name const & get_theorem_tk() { return *g_theorem_tk; }
name const & get_abbreviation_tk() { return *g_abbreviation_tk; }
name const & get_axiom_tk() { return *g_axiom_tk; }
name const & get_axioms_tk() { return *g_axioms_tk; }
name const & get_constant_tk() { return *g_constant_tk; }
name const & get_constants_tk() { return *g_constants_tk; }
name const & get_variable_tk() { return *g_variable_tk; }
name const & get_variables_tk() { return *g_variables_tk; }
name const & get_instance_tk() { return *g_instance_tk; }
name const & get_trans_inst_tk() { return *g_trans_inst_tk; }
name const & get_priority_tk() { return *g_priority_tk; }
name const & get_unfold_tk() { return *g_unfold_tk; }
name const & get_unfold_full_tk() { return *g_unfold_full_tk; }
name const & get_unfold_hints_bracket_tk() { return *g_unfold_hints_bracket_tk; }
name const & get_unfold_hints_tk() { return *g_unfold_hints_tk; }
name const & get_constructor_tk() { return *g_constructor_tk; }
name const & get_coercion_tk() { return *g_coercion_tk; }
name const & get_reducible_tk() { return *g_reducible_tk; }
name const & get_quasireducible_tk() { return *g_quasireducible_tk; }
name const & get_semireducible_tk() { return *g_semireducible_tk; }
name const & get_irreducible_tk() { return *g_irreducible_tk; }
name const & get_parsing_only_tk() { return *g_parsing_only_tk; }
name const & get_symm_tk() { return *g_symm_tk; }
name const & get_trans_tk() { return *g_trans_tk; }
name const & get_refl_tk() { return *g_refl_tk; }
name const & get_subst_tk() { return *g_subst_tk; }
name const & get_simp_attr_tk() { return *g_simp_attr_tk; }
name const & get_congr_attr_tk() { return *g_congr_attr_tk; }
name const & get_recursor_tk() { return *g_recursor_tk; }
name const & get_attribute_tk() { return *g_attribute_tk; }
name const & get_with_tk() { return *g_with_tk; }
name const & get_class_tk() { return *g_class_tk; }
name const & get_multiple_instances_tk() { return *g_multiple_instances_tk; }
name const & get_prev_tk() { return *g_prev_tk; }
name const & get_scoped_tk() { return *g_scoped_tk; }
name const & get_foldr_tk() { return *g_foldr_tk; }
name const & get_foldl_tk() { return *g_foldl_tk; }
name const & get_binder_tk() { return *g_binder_tk; }
name const & get_binders_tk() { return *g_binders_tk; }
name const & get_precedence_tk() { return *g_precedence_tk; }
name const & get_infix_tk() { return *g_infix_tk; }
name const & get_infixl_tk() { return *g_infixl_tk; }
name const & get_infixr_tk() { return *g_infixr_tk; }
name const & get_postfix_tk() { return *g_postfix_tk; }
name const & get_prefix_tk() { return *g_prefix_tk; }
name const & get_notation_tk() { return *g_notation_tk; }
name const & get_tactic_infix_tk() { return *g_tactic_infix_tk; }
name const & get_tactic_infixl_tk() { return *g_tactic_infixl_tk; }
name const & get_tactic_infixr_tk() { return *g_tactic_infixr_tk; }
name const & get_tactic_postfix_tk() { return *g_tactic_postfix_tk; }
name const & get_tactic_prefix_tk() { return *g_tactic_prefix_tk; }
name const & get_tactic_notation_tk() { return *g_tactic_notation_tk; }
name const & get_call_tk() { return *g_call_tk; }
name const & get_calc_tk() { return *g_calc_tk; }
name const & get_obtain_tk() { return *g_obtain_tk; }
name const & get_persistent_tk() { return *g_persistent_tk; }
name const & get_root_tk() { return *g_root_tk; }
name const & get_fields_tk() { return *g_fields_tk; }
name const & get_trust_tk() { return *g_trust_tk; }
name const & get_metaclasses_tk() { return *g_metaclasses_tk; }
name const & get_inductive_tk() { return *g_inductive_tk; }
name const & get_this_tk() { return *g_this_tk; }
name const & get_noncomputable_tk() { return *g_noncomputable_tk; }
name const & get_theory_tk() { return *g_theory_tk; }
}
