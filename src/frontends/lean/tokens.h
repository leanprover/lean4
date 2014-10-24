/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name.h"

namespace lean {
void initialize_tokens();
void finalize_tokens();
name const & get_period_tk();
name const & get_placeholder_tk();
name const & get_colon_tk();
name const & get_dcolon_tk();
name const & get_lparen_tk();
name const & get_rparen_tk();
name const & get_llevel_curly_tk();
name const & get_lcurly_tk();
name const & get_rcurly_tk();
name const & get_ldcurly_tk();
name const & get_rdcurly_tk();
name const & get_lbracket_tk();
name const & get_rbracket_tk();
name const & get_bar_tk();
name const & get_comma_tk();
name const & get_add_tk();
name const & get_max_tk();
name const & get_imax_tk();
name const & get_cup_tk();
name const & get_import_tk();
name const & get_show_tk();
name const & get_have_tk();
name const & get_assume_tk();
name const & get_take_tk();
name const & get_fun_tk();
name const & get_ellipsis_tk();
name const & get_raw_tk();
name const & get_true_tk();
name const & get_false_tk();
name const & get_options_tk();
name const & get_instances_tk();
name const & get_classes_tk();
name const & get_coercions_tk();
name const & get_arrow_tk();
name const & get_declarations_tk();
name const & get_decls_tk();
name const & get_hiding_tk();
name const & get_exposing_tk();
name const & get_renaming_tk();
name const & get_extends_tk();
name const & get_as_tk();
name const & get_on_tk();
name const & get_off_tk();
name const & get_none_tk();
name const & get_in_tk();
name const & get_assign_tk();
name const & get_visible_tk();
name const & get_from_tk();
name const & get_using_tk();
name const & get_then_tk();
name const & get_by_tk();
name const & get_proof_tk();
name const & get_begin_tk();
name const & get_qed_tk();
name const & get_end_tk();
name const & get_definition_tk();
name const & get_theorem_tk();
name const & get_axiom_tk();
name const & get_axioms_tk();
name const & get_variable_tk();
name const & get_variables_tk();
name const & get_opaque_tk();
name const & get_instance_tk();
name const & get_priority_tk();
name const & get_coercion_tk();
name const & get_reducible_tk();
name const & get_class_tk();
name const & get_with_tk();
name const & get_prev_tk();
name const & get_scoped_tk();
name const & get_foldr_tk();
name const & get_foldl_tk();
name const & get_binder_tk();
name const & get_binders_tk();
name const & get_infix_tk();
name const & get_infixl_tk();
name const & get_infixr_tk();
name const & get_postfix_tk();
name const & get_prefix_tk();
name const & get_notation_tk();
name const & get_call_tk();
name const & get_persistent_tk();
name const & get_root_tk();
}
