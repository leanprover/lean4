/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name.h"

namespace lean {
static name * g_period       = nullptr;
static name * g_placeholder  = nullptr;
static name * g_colon        = nullptr;
static name * g_semicolon    = nullptr;
static name * g_dcolon       = nullptr;
static name * g_lparen       = nullptr;
static name * g_rparen       = nullptr;
static name * g_llevel_curly = nullptr;
static name * g_lcurly       = nullptr;
static name * g_rcurly       = nullptr;
static name * g_ldcurly      = nullptr;
static name * g_rdcurly      = nullptr;
static name * g_lcurlybar    = nullptr;
static name * g_rcurlybar    = nullptr;
static name * g_lbracket     = nullptr;
static name * g_rbracket     = nullptr;
static name * g_langle       = nullptr;
static name * g_rangle       = nullptr;
static name * g_triangle     = nullptr;
static name * g_caret        = nullptr;
static name * g_up           = nullptr;
static name * g_down         = nullptr;
static name * g_bar          = nullptr;
static name * g_comma        = nullptr;
static name * g_add          = nullptr;
static name * g_sub          = nullptr;
static name * g_greater      = nullptr;
static name * g_question     = nullptr;
static name * g_question_lp  = nullptr;
static name * g_bang         = nullptr;
static name * g_slash        = nullptr;
static name * g_star         = nullptr;
static name * g_plus         = nullptr;
static name * g_turnstile    = nullptr;
static name * g_explicit     = nullptr;
static name * g_max          = nullptr;
static name * g_imax         = nullptr;
static name * g_cup          = nullptr;
static name * g_import       = nullptr;
static name * g_prelude      = nullptr;
static name * g_show         = nullptr;
static name * g_have         = nullptr;
static name * g_assert       = nullptr;
static name * g_assume       = nullptr;
static name * g_take         = nullptr;
static name * g_fun          = nullptr;
static name * g_match        = nullptr;
static name * g_ellipsis     = nullptr;
static name * g_raw          = nullptr;
static name * g_true         = nullptr;
static name * g_false        = nullptr;
static name * g_options      = nullptr;
static name * g_commands     = nullptr;
static name * g_instances    = nullptr;
static name * g_classes      = nullptr;
static name * g_coercions    = nullptr;
static name * g_arrow        = nullptr;
static name * g_declarations = nullptr;
static name * g_decls        = nullptr;
static name * g_hiding       = nullptr;
static name * g_exposing     = nullptr;
static name * g_renaming     = nullptr;
static name * g_replacing    = nullptr;
static name * g_extends      = nullptr;
static name * g_as           = nullptr;
static name * g_none         = nullptr;
static name * g_whnf         = nullptr;
static name * g_wf           = nullptr;
static name * g_all_transparent = nullptr;
static name * g_in           = nullptr;
static name * g_at           = nullptr;
static name * g_assign       = nullptr;
static name * g_visible      = nullptr;
static name * g_from         = nullptr;
static name * g_using        = nullptr;
static name * g_then         = nullptr;
static name * g_else         = nullptr;
static name * g_by           = nullptr;
static name * g_rewrite      = nullptr;
static name * g_proof        = nullptr;
static name * g_qed          = nullptr;
static name * g_begin        = nullptr;
static name * g_end          = nullptr;
static name * g_private      = nullptr;
static name * g_definition   = nullptr;
static name * g_theorem      = nullptr;
static name * g_abbreviation = nullptr;
static name * g_axiom        = nullptr;
static name * g_axioms       = nullptr;
static name * g_variable     = nullptr;
static name * g_variables    = nullptr;
static name * g_opaque       = nullptr;
static name * g_instance     = nullptr;
static name * g_priority     = nullptr;
static name * g_unfold_c     = nullptr;
static name * g_coercion     = nullptr;
static name * g_reducible    = nullptr;
static name * g_quasireducible = nullptr;
static name * g_semireducible = nullptr;
static name * g_irreducible  = nullptr;
static name * g_parsing_only = nullptr;
static name * g_with         = nullptr;
static name * g_class        = nullptr;
static name * g_multiple_instances = nullptr;
static name * g_attribute    = nullptr;
static name * g_prev         = nullptr;
static name * g_scoped       = nullptr;
static name * g_foldr        = nullptr;
static name * g_foldl        = nullptr;
static name * g_binder       = nullptr;
static name * g_binders      = nullptr;
static name * g_infix        = nullptr;
static name * g_infixl       = nullptr;
static name * g_infixr       = nullptr;
static name * g_postfix      = nullptr;
static name * g_prefix       = nullptr;
static name * g_notation     = nullptr;
static name * g_call         = nullptr;
static name * g_persistent   = nullptr;
static name * g_root         = nullptr;
static name * g_fields       = nullptr;
static name * g_trust        = nullptr;
static name * g_metaclasses  = nullptr;

void initialize_tokens() {
    g_period       = new name(".");
    g_placeholder  = new name("_");
    g_colon        = new name(":");
    g_semicolon    = new name(";");
    g_dcolon       = new name("::");
    g_lparen       = new name("(");
    g_rparen       = new name(")");
    g_llevel_curly = new name(".{");
    g_lcurly       = new name("{");
    g_rcurly       = new name("}");
    g_ldcurly      = new name("⦃");
    g_rdcurly      = new name("⦄");
    g_lcurlybar    = new name("{|");
    g_rcurlybar    = new name("|}");
    g_lbracket     = new name("[");
    g_rbracket     = new name("]");
    g_langle       = new name("⟨");
    g_rangle       = new name("⟩");
    g_triangle     = new name("▸");
    g_caret        = new name("^");
    g_up           = new name("↑");
    g_down         = new name("<d");
    g_bar          = new name("|");
    g_comma        = new name(",");
    g_add          = new name("+");
    g_sub          = new name("-");
    g_greater      = new name(">");
    g_question     = new name("?");
    g_question_lp  = new name("?(");
    g_bang         = new name("!");
    g_slash        = new name("/");
    g_plus         = new name("+");
    g_star         = new name("*");
    g_turnstile    = new name("⊢");
    g_explicit     = new name("@");
    g_max          = new name("max");
    g_imax         = new name("imax");
    g_cup          = new name("\u2294");
    g_import       = new name("import");
    g_prelude      = new name("prelude");
    g_show         = new name("show");
    g_have         = new name("have");
    g_assert       = new name("assert");
    g_assume       = new name("assume");
    g_take         = new name("take");
    g_fun          = new name("fun");
    g_match        = new name("match");
    g_ellipsis     = new name("...");
    g_raw          = new name("raw");
    g_true         = new name("true");
    g_false        = new name("false");
    g_options      = new name("options");
    g_commands     = new name("commands");
    g_instances    = new name("instances");
    g_classes      = new name("classes");
    g_coercions    = new name("coercions");
    g_arrow        = new name("->");
    g_declarations = new name("declarations");
    g_decls        = new name("decls");
    g_hiding       = new name("hiding");
    g_exposing     = new name("exposing");
    g_renaming     = new name("renaming");
    g_replacing    = new name("replacing");
    g_extends      = new name("extends");
    g_as           = new name("as");
    g_none         = new name("[none]");
    g_whnf         = new name("[whnf]");
    g_wf           = new name("[wf]");
    g_all_transparent = new name("[all-transparent]");
    g_in           = new name("in");
    g_at           = new name("at");
    g_assign       = new name(":=");
    g_visible      = new name("[visible]");
    g_from         = new name("from");
    g_using        = new name("using");
    g_then         = new name("then");
    g_else         = new name("else");
    g_by           = new name("by");
    g_rewrite      = new name("rewrite");
    g_proof        = new name("proof");
    g_qed          = new name("qed");
    g_begin        = new name("begin");
    g_end          = new name("end");
    g_private      = new name("private");
    g_definition   = new name("definition");
    g_theorem      = new name("theorem");
    g_abbreviation = new name("abbreviation");
    g_opaque       = new name("opaque");
    g_axiom        = new name("axiom");
    g_axioms       = new name("axioms");
    g_variable     = new name("variable");
    g_variables    = new name("variables");
    g_instance     = new name("[instance]");
    g_priority     = new name("[priority");
    g_unfold_c     = new name("[unfold-c");
    g_coercion     = new name("[coercion]");
    g_reducible    = new name("[reducible]");
    g_quasireducible = new name("[quasireducible]");
    g_semireducible = new name("[semireducible]");
    g_irreducible  = new name("[irreducible]");
    g_parsing_only = new name("[parsing-only]");
    g_attribute    = new name("attribute");
    g_with         = new name("with");
    g_class        = new name("[class]");
    g_multiple_instances = new name("[multiple-instances]");
    g_prev         = new name("prev");
    g_scoped       = new name("scoped");
    g_foldr        = new name("foldr");
    g_foldl        = new name("foldl");
    g_binder       = new name("binder");
    g_binders      = new name("binders");
    g_infix        = new name("infix");
    g_infixl       = new name("infixl");
    g_infixr       = new name("infixr");
    g_postfix      = new name("postfix");
    g_prefix       = new name("prefix");
    g_notation     = new name("notation");
    g_call         = new name("call");
    g_persistent   = new name("[persistent]");
    g_root         = new name("_root_");
    g_fields       = new name("fields");
    g_trust        = new name("trust");
    g_metaclasses  = new name("metaclasses");
}

void finalize_tokens() {
    delete g_metaclasses;
    delete g_persistent;
    delete g_root;
    delete g_fields;
    delete g_trust;
    delete g_prev;
    delete g_scoped;
    delete g_foldr;
    delete g_foldl;
    delete g_binder;
    delete g_binders;
    delete g_infix;
    delete g_infixl;
    delete g_infixr;
    delete g_postfix;
    delete g_prefix;
    delete g_notation;
    delete g_call;
    delete g_with;
    delete g_class;
    delete g_private;
    delete g_definition;
    delete g_theorem;
    delete g_abbreviation;
    delete g_opaque;
    delete g_axiom;
    delete g_axioms;
    delete g_variables;
    delete g_variable;
    delete g_instance;
    delete g_priority;
    delete g_unfold_c;
    delete g_coercion;
    delete g_reducible;
    delete g_quasireducible;
    delete g_semireducible;
    delete g_irreducible;
    delete g_multiple_instances;
    delete g_attribute;
    delete g_parsing_only;
    delete g_in;
    delete g_at;
    delete g_assign;
    delete g_visible;
    delete g_from;
    delete g_using;
    delete g_then;
    delete g_else;
    delete g_by;
    delete g_rewrite;
    delete g_proof;
    delete g_qed;
    delete g_begin;
    delete g_end;
    delete g_raw;
    delete g_true;
    delete g_false;
    delete g_options;
    delete g_commands;
    delete g_instances;
    delete g_classes;
    delete g_coercions;
    delete g_arrow;
    delete g_declarations;
    delete g_decls;
    delete g_hiding;
    delete g_exposing;
    delete g_renaming;
    delete g_replacing;
    delete g_extends;
    delete g_as;
    delete g_none;
    delete g_whnf;
    delete g_wf;
    delete g_all_transparent;
    delete g_ellipsis;
    delete g_match;
    delete g_fun;
    delete g_take;
    delete g_assume;
    delete g_have;
    delete g_assert;
    delete g_show;
    delete g_import;
    delete g_prelude;
    delete g_cup;
    delete g_imax;
    delete g_max;
    delete g_add;
    delete g_sub;
    delete g_greater;
    delete g_question;
    delete g_question_lp;
    delete g_bang;
    delete g_slash;
    delete g_plus;
    delete g_star;
    delete g_turnstile;
    delete g_explicit;
    delete g_comma;
    delete g_bar;
    delete g_langle;
    delete g_rangle;
    delete g_triangle;
    delete g_caret;
    delete g_up;
    delete g_down;
    delete g_rbracket;
    delete g_lbracket;
    delete g_rdcurly;
    delete g_ldcurly;
    delete g_rcurlybar;
    delete g_lcurlybar;
    delete g_lcurly;
    delete g_rcurly;
    delete g_llevel_curly;
    delete g_rparen;
    delete g_lparen;
    delete g_colon;
    delete g_semicolon;
    delete g_dcolon;
    delete g_placeholder;
    delete g_period;
}

name const & get_metaclasses_tk() { return *g_metaclasses; }
name const & get_period_tk() { return *g_period; }
name const & get_placeholder_tk() { return *g_placeholder; }
name const & get_colon_tk() { return *g_colon; }
name const & get_semicolon_tk() { return *g_semicolon; }
name const & get_dcolon_tk() { return *g_dcolon; }
name const & get_langle_tk() { return *g_langle; }
name const & get_rangle_tk() { return *g_rangle; }
name const & get_triangle_tk() { return *g_triangle; }
name const & get_caret_tk() { return *g_caret; }
name const & get_up_tk() { return *g_up; }
name const & get_down_tk() { return *g_down; }
name const & get_lparen_tk() { return *g_lparen; }
name const & get_rparen_tk() { return *g_rparen; }
name const & get_llevel_curly_tk() { return *g_llevel_curly; }
name const & get_lcurly_tk() { return *g_lcurly; }
name const & get_rcurly_tk() { return *g_rcurly; }
name const & get_ldcurly_tk() { return *g_ldcurly; }
name const & get_rdcurly_tk() { return *g_rdcurly; }
name const & get_lcurlybar_tk() { return *g_lcurlybar; }
name const & get_rcurlybar_tk() { return *g_rcurlybar; }
name const & get_lbracket_tk() { return *g_lbracket; }
name const & get_rbracket_tk() { return *g_rbracket; }
name const & get_bar_tk() { return *g_bar; }
name const & get_comma_tk() { return *g_comma; }
name const & get_add_tk() { return *g_add; }
name const & get_sub_tk() { return *g_sub; }
name const & get_greater_tk() { return *g_greater; }
name const & get_question_tk() { return *g_question; }
name const & get_question_lp_tk() { return *g_question_lp; }
name const & get_bang_tk() { return *g_bang; }
name const & get_slash_tk() { return *g_slash; }
name const & get_star_tk() { return *g_star; }
name const & get_plus_tk() { return *g_plus; }
name const & get_turnstile_tk() { return *g_turnstile; }
name const & get_explicit_tk() { return *g_explicit; }
name const & get_max_tk() { return *g_max; }
name const & get_imax_tk() { return *g_imax; }
name const & get_cup_tk() { return *g_cup; }
name const & get_import_tk() { return *g_import; }
name const & get_prelude_tk() { return *g_prelude; }
name const & get_show_tk() { return *g_show; }
name const & get_have_tk() { return *g_have; }
name const & get_assert_tk() { return *g_assert; }
name const & get_assume_tk() { return *g_assume; }
name const & get_take_tk() { return *g_take; }
name const & get_fun_tk() { return *g_fun; }
name const & get_match_tk() { return *g_match; }
name const & get_ellipsis_tk() { return *g_ellipsis; }
name const & get_raw_tk() { return *g_raw; }
name const & get_true_tk() { return *g_true; }
name const & get_false_tk() { return *g_false; }
name const & get_options_tk() { return *g_options; }
name const & get_commands_tk() { return *g_commands; }
name const & get_instances_tk() { return *g_instances; }
name const & get_classes_tk() { return *g_classes; }
name const & get_coercions_tk() { return *g_coercions; }
name const & get_arrow_tk() { return *g_arrow; }
name const & get_declarations_tk() { return *g_declarations; }
name const & get_decls_tk() { return *g_decls; }
name const & get_hiding_tk() { return *g_hiding; }
name const & get_exposing_tk() { return *g_exposing; }
name const & get_renaming_tk() { return *g_renaming; }
name const & get_replacing_tk() { return *g_replacing; }
name const & get_extends_tk() { return *g_extends; }
name const & get_as_tk() { return *g_as; }
name const & get_none_tk() { return *g_none; }
name const & get_whnf_tk() { return *g_whnf; }
name const & get_wf_tk() { return *g_wf; }
name const & get_all_transparent_tk() { return *g_all_transparent; }
name const & get_in_tk() { return *g_in; }
name const & get_at_tk() { return *g_at; }
name const & get_assign_tk() { return *g_assign; }
name const & get_visible_tk() { return *g_visible; }
name const & get_from_tk() { return *g_from; }
name const & get_using_tk() { return *g_using; }
name const & get_then_tk() { return *g_then; }
name const & get_else_tk() { return *g_else; }
name const & get_by_tk() { return *g_by; }
name const & get_rewrite_tk() { return *g_rewrite; }
name const & get_proof_tk() { return *g_proof; }
name const & get_qed_tk() { return *g_qed; }
name const & get_begin_tk() { return *g_begin; }
name const & get_end_tk() { return *g_end; }
name const & get_private_tk() { return *g_private; }
name const & get_definition_tk() { return *g_definition; }
name const & get_theorem_tk() { return *g_theorem; }
name const & get_abbreviation_tk() { return *g_abbreviation; }
name const & get_axiom_tk() { return *g_axiom; }
name const & get_axioms_tk() { return *g_axioms; }
name const & get_variable_tk() { return *g_variable; }
name const & get_variables_tk() { return *g_variables; }
name const & get_opaque_tk() { return *g_opaque; }
name const & get_instance_tk() { return *g_instance; }
name const & get_priority_tk() { return *g_priority; }
name const & get_unfold_c_tk() { return *g_unfold_c; }
name const & get_coercion_tk() { return *g_coercion; }
name const & get_reducible_tk() { return *g_reducible; }
name const & get_quasireducible_tk() { return *g_quasireducible; }
name const & get_semireducible_tk() { return *g_semireducible; }
name const & get_irreducible_tk() { return *g_irreducible; }
name const & get_multiple_instances_tk() { return *g_multiple_instances; }
name const & get_attribute_tk() { return *g_attribute; }
name const & get_parsing_only_tk() { return *g_parsing_only; }
name const & get_class_tk() { return *g_class; }
name const & get_with_tk() { return *g_with; }
name const & get_prev_tk() { return *g_prev; }
name const & get_scoped_tk() { return *g_scoped; }
name const & get_foldr_tk() { return *g_foldr; }
name const & get_foldl_tk() { return *g_foldl; }
name const & get_binder_tk() { return *g_binder; }
name const & get_binders_tk() { return *g_binders; }
name const & get_infix_tk() { return *g_infix; }
name const & get_infixl_tk() { return *g_infixl; }
name const & get_infixr_tk() { return *g_infixr; }
name const & get_postfix_tk() { return *g_postfix; }
name const & get_prefix_tk() { return *g_prefix; }
name const & get_notation_tk() { return *g_notation; }
name const & get_call_tk() { return *g_call; }
name const & get_persistent_tk() { return *g_persistent; }
name const & get_root_tk() { return *g_root; }
name const & get_fields_tk() { return *g_fields; }
name const & get_trust_tk() { return *g_trust; }
}
