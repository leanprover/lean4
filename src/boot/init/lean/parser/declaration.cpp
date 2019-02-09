// Lean compiler output
// Module: init.lean.parser.declaration
// Imports: init.lean.parser.term
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_parser_command_infer__modifier_parser_lean_parser_has__view;
obj* l_lean_parser_command_declaration_inner_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_visibility_has__view;
obj* l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__2;
obj* l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_structure__kw_has__view_x_27;
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__7(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__val_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
obj* l_list_map___main___rarg(obj*, obj*);
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_infer__modifier_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_decl__attributes_has__view_x_27;
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_command_old__univ__params_parser___closed__1;
obj* l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1(obj*);
extern uint8 l_true_decidable;
extern obj* l_lean_parser_command_notation__like_has__view;
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__2(obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_term_bracketed__binders_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_structure__field__block_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_equation_has__view_x_27___lambda__1(obj*);
obj* l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_constant_has__view;
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_command_inductive_has__view;
obj* l_lean_parser_command_struct__explicit__binder__content_has__view;
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_structure_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_declaration;
obj* l_lean_parser_command_doc__comment_parser_lean_parser_has__view;
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__sig_has__view_x_27;
obj* l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_equation_parser___closed__1;
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_equation;
obj* l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_infer__modifier_has__view_x_27;
obj* l_lean_parser_command_doc__comment_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_simple__decl__val_has__view_x_27;
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_command_declaration_has__view_x_27;
obj* l_lean_parser_command_strict__implicit__binder;
obj* l_lean_parser_command_decl__modifiers;
obj* l_lean_parser_command_def__like_kind_has__view;
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_visibility;
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__6;
obj* l_lean_parser_command_doc__comment_parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens;
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_command_structure__field__block;
obj* l_lean_parser_monad__parsec_error___at___private_409789351__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_sep__by1_tokens___rarg(obj*, obj*);
obj* l_lean_parser_command_declaration_parser___closed__1;
obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_structure_has__view;
obj* l_lean_parser_command_decl__modifiers_parser(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_command_extends_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27;
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_struct__explicit__binder;
obj* l_lean_parser_command_structure__ctor;
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_opt__decl__sig_parser___closed__1;
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_old__univ__params_parser_lean_parser_has__view;
obj* l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27;
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
obj* l_list_reverse___rarg(obj*);
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__5;
extern obj* l_lean_parser_command__parser__m_monad__except___closed__1;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_infer__modifier_parser___closed__1;
obj* l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_constant__keyword;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_structure_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_def__like_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_struct__binder__content_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_simple__decl__val;
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_term_binder__default_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_constant__keyword_has__view_x_27;
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__2;
obj* l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_old__univ__params_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_example;
obj* l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_struct__implicit__binder_has__view;
obj* l_lean_parser_command_instance;
extern obj* l_lean_parser_command__parser__m_monad___closed__1;
obj* l_lean_parser_command_struct__explicit__binder__content;
obj* l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_equation_parser_lean_parser_has__view;
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__2___closed__1;
obj* l_list_map___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_declaration_parser_lean_parser_has__view;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_instance_has__view_x_27;
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_decl__attributes_has__view;
obj* l_lean_parser_command_intro__rule_parser_lean_parser_has__view;
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__2(obj*);
obj* l___private_2873386687__str__aux___main(obj*, obj*, obj*);
obj* l___private_1386096941__many1__aux___main___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_old__univ__params_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__attributes_parser_lean_parser_has__view;
uint8 l_string_is__empty(obj*);
extern obj* l_lean_parser_command_notation__like_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_intro__rule_has__view;
obj* l_lean_parser_command_structure_has__view_x_27;
obj* l_lean_parser_command_structure_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_strict__implicit__binder_has__view_x_27;
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_command_declaration_inner;
obj* l_lean_parser_command_extends_has__view;
extern obj* l_lean_parser_term_binder__content_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_command__parser__m_alternative___closed__1;
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_constant_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
obj* l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6(obj*);
obj* l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_doc__comment;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_command_structure__ctor_has__view;
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_extends;
obj* l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_attr__instance_parser_lean_parser_has__view;
obj* l_lean_parser_command_instance_has__view_x_27___lambda__1(obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__2(obj*);
obj* l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2(obj*, obj*, uint8, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_command_notation__spec_symbol__quote_parser_lean_parser_has__view___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_doc__comment_parser_lean_parser_has__tokens;
extern obj* l_lean_parser_command_mixfix_kind_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_struct__binder__content_parser___closed__1;
obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__3(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_structure__kw;
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
extern obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_command_decl__val_has__view_x_27;
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_def__like_has__view_x_27;
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_attr__instance_has__view_x_27;
extern obj* l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
obj* l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
extern obj* l___private_1386096941__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__4;
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_command_old__univ__params;
obj* l_lean_parser_command_decl__modifiers_has__view_x_27;
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_opt__decl__sig_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_simple__decl__val_has__view;
obj* l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_relaxed__infer__modifier_has__view;
obj* l_lean_parser_command_decl__sig_has__view;
obj* l_lean_parser_command_decl__val_has__view;
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_structure__field__block_has__view_x_27;
obj* l_lean_parser_command_struct__binder__content_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_ident__univ__params_parser___closed__1;
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2;
extern obj* l_lean_parser_term_bracketed__binders_has__view;
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_decl__attributes_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_instance_has__view;
obj* l_lean_parser_command_equation_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_doc__comment_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
extern obj* l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_mk__raw__res(obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_command_declaration_inner_has__view;
obj* l_lean_parser_command_decl__modifiers_parser_lean_parser_has__view;
obj* l_lean_parser_command_opt__decl__sig_has__view;
obj* l_lean_parser_command_extends_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_univ__params_has__view_x_27;
obj* l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_decl__val_parser___closed__1;
obj* l_lean_parser_command_intro__rule_has__view_x_27;
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_ident__univ__params_has__view_x_27;
obj* l_lean_parser_command_extends_has__view_x_27;
obj* l_lean_parser_command_equation_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_struct__explicit__binder_has__view;
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__2;
obj* l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9(obj*, obj*);
extern obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_command_constant__keyword_has__view;
obj* l_lean_parser_command_ident__univ__params_has__view;
extern obj* l_string_join___closed__1;
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
obj* l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_infer__modifier;
extern obj* l_lean_parser_max__prec;
obj* l_lean_parser_command_def__like;
obj* l_lean_parser_command_ident__univ__params_parser_lean_parser_has__view;
obj* l_lean_parser_command_intro__rule_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_ident__univ__params_parser_lean_parser_has__tokens;
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_opt__decl__sig;
obj* l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_old__univ__params_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_doc__comment_has__view_x_27;
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__5(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_instance_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_lean_parser_command_opt__decl__sig_has__view_x_27;
obj* l_lean_parser_command_def__like_has__view;
extern obj* l___private_409789351__finish__comment__block__aux___main___closed__1;
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_inst__implicit__binder;
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_command_infer__modifier_parser(obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_command_doc__comment_parser___spec__5(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27;
obj* l_lean_parser_command_intro__rule;
extern obj* l_lean_parser_term_bracketed__binders_parser_lean_parser_has__tokens;
extern obj* l_lean_parser_term_type__spec_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_visibility_has__view_x_27;
obj* l_lean_parser_command_univ__params_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_term_parser(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_example_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_decl__attributes_parser___closed__1;
extern obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_command_univ__params_has__view;
obj* l_lean_parser_command_structure__ctor_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_term_opt__type_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_ident__univ__params;
obj* l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_structure_parser___closed__1;
obj* l_lean_parser_command_structure__field__block_has__view_x_27___lambda__2(obj*);
obj* l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_decl__val_parser_lean_parser_has__view;
obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__2(obj*);
obj* l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_structure;
obj* l_lean_parser_command_structure__field__block_has__view;
extern obj* l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__2(obj*);
extern obj* l_lean_parser_term_binder__default_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_structure__field__block_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__modifiers_parser___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4(obj*);
obj* l_lean_parser_command_extends_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__view;
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_constant_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_attr__instance_has__view;
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_structure_has__view_x_27___lambda__2___closed__1;
obj* l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_equation_has__view_x_27;
obj* l_lean_parser_command_decl__val;
extern obj* l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_attr__instance;
obj* l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1(obj*);
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__5(obj*);
obj* l_lean_parser_command_constant_has__view_x_27;
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27;
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_term__parser__command__parser__coe(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_inst__implicit__binder_has__view_x_27;
obj* l_lean_parser_command_equation_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_inductive_has__view_x_27;
obj* l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_decl__sig_parser_lean_parser_has__view;
obj* l_lean_parser_command_old__univ__params_has__view_x_27;
extern obj* l___private_409789351__finish__comment__block__aux___main___closed__2;
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
obj* l_string_trim(obj*);
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_command_structure__kw_has__view;
obj* l_lean_parser_command_structure__field__block_parser___closed__1;
obj* l_lean_parser_command_declaration_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_def__like_kind_has__view_x_27;
obj* l_lean_parser_command_constant;
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__1(obj*);
extern obj* l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
extern obj* l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_attr__instance_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_command_doc__comment_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_equation_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__attributes;
obj* l_lean_parser_command_ident__univ__params_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_intro__rule_parser___closed__1;
extern obj* l_lean_parser_term_opt__type_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_term__parser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_struct__binder__content_parser_lean_parser_has__view;
obj* l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_example_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__1;
obj* l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_declaration_has__view;
obj* l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_structure__ctor_has__view_x_27;
obj* l_lean_parser_command_struct__binder__content;
obj* l_lean_parser_command_univ__params;
obj* l_lean_parser_command_declaration_inner_has__view_x_27;
obj* l_lean_parser_command_struct__binder__content_has__view_x_27;
obj* l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_command_structure_parser_lean_parser_has__view;
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_univ__params_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_doc__comment_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_inst__implicit__binder_has__view;
obj* l_lean_parser_command_strict__infer__modifier_has__view;
obj* l_lean_parser_command_def__like_kind;
obj* l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_relaxed__infer__modifier;
obj* l_lean_parser_command_declaration_parser(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_binder__default_has__view;
extern obj* l_lean_parser_term_type__spec_has__view;
obj* l_lean_parser_command_attr__instance_parser___closed__1;
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_univ__params_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_notation__like_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__val_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_decl__sig_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
obj* l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_doc__comment_parser(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_decl__sig_parser___closed__1;
obj* l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_equation_has__view;
obj* l_lean_parser_command_strict__implicit__binder_has__view;
obj* l_lean_parser_command_structure__field__block_parser_lean_parser_has__view;
obj* l_lean_parser_command_decl__sig_parser_lean_parser_has__tokens;
obj* l_lean_parser_command_def__like_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__3(obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_command_doc__comment_parser___closed__1;
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1(obj*);
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__4(obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_old__univ__params_has__view;
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_command_struct__implicit__binder;
obj* l_lean_parser_command_example_has__view_x_27;
obj* l_lean_parser_command_doc__comment_has__view;
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_struct__binder__content_has__view;
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__2(obj*);
obj* l___private_3601861905__ident_x_27(obj*, obj*, obj*);
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_term_tuple_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_intro__rule_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command_decl__sig;
obj* l_char_quote__core(uint32);
obj* l_lean_parser_command_infer__modifier_has__view;
obj* l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_command_inductive;
obj* l_lean_parser_command_strict__infer__modifier;
obj* l_lean_parser_command_example_has__view;
obj* l_lean_parser_term_type__spec_parser(obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_3809070873__whitespace__aux___main___closed__1;
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_parser_command_example_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_command_decl__modifiers_has__view;
obj* l_lean_parser_term__parser__command__parser__coe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_term__parser_run(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_doc__comment() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("doc_comment");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_doc__comment_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_doc__comment_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_doc__comment_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_doc__comment_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_doc__comment_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_38; 
x_38 = lean::box(3);
x_35 = x_1;
x_36 = x_38;
goto lbl_37;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_1, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 1);
lean::inc(x_41);
lean::dec(x_1);
x_35 = x_41;
x_36 = x_39;
goto lbl_37;
}
lbl_34:
{
switch (lean::obj_tag(x_33)) {
case 0:
{
obj* x_44; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_33, 0);
lean::inc(x_44);
lean::dec(x_33);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_44);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_20);
lean::cnstr_set(x_48, 1, x_32);
lean::cnstr_set(x_48, 2, x_47);
return x_48;
}
case 1:
{
obj* x_50; obj* x_51; 
lean::dec(x_33);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_20);
lean::cnstr_set(x_51, 1, x_32);
lean::cnstr_set(x_51, 2, x_50);
return x_51;
}
case 2:
{
obj* x_53; obj* x_54; 
lean::dec(x_33);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_20);
lean::cnstr_set(x_54, 1, x_32);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
default:
{
obj* x_56; obj* x_57; 
lean::dec(x_33);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_20);
lean::cnstr_set(x_57, 1, x_32);
lean::cnstr_set(x_57, 2, x_56);
return x_57;
}
}
}
lbl_37:
{
switch (lean::obj_tag(x_36)) {
case 0:
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_36, 0);
lean::inc(x_58);
lean::dec(x_36);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_58);
if (lean::obj_tag(x_35) == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_35);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_20);
lean::cnstr_set(x_64, 1, x_61);
lean::cnstr_set(x_64, 2, x_63);
return x_64;
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_35, 0);
lean::inc(x_65);
lean::dec(x_35);
x_32 = x_61;
x_33 = x_65;
goto lbl_34;
}
}
case 1:
{
obj* x_69; 
lean::dec(x_36);
x_69 = lean::box(0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_72; 
lean::dec(x_35);
lean::inc(x_69);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_20);
lean::cnstr_set(x_72, 1, x_69);
lean::cnstr_set(x_72, 2, x_69);
return x_72;
}
else
{
obj* x_73; 
x_73 = lean::cnstr_get(x_35, 0);
lean::inc(x_73);
lean::dec(x_35);
x_32 = x_69;
x_33 = x_73;
goto lbl_34;
}
}
case 2:
{
obj* x_77; 
lean::dec(x_36);
x_77 = lean::box(0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_80; 
lean::dec(x_35);
lean::inc(x_77);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_20);
lean::cnstr_set(x_80, 1, x_77);
lean::cnstr_set(x_80, 2, x_77);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_35, 0);
lean::inc(x_81);
lean::dec(x_35);
x_32 = x_77;
x_33 = x_81;
goto lbl_34;
}
}
default:
{
obj* x_85; 
lean::dec(x_36);
x_85 = lean::box(0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_88; 
lean::dec(x_35);
lean::inc(x_85);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_20);
lean::cnstr_set(x_88, 1, x_85);
lean::cnstr_set(x_88, 2, x_85);
return x_88;
}
else
{
obj* x_89; 
x_89 = lean::cnstr_get(x_35, 0);
lean::inc(x_89);
lean::dec(x_35);
x_32 = x_85;
x_33 = x_89;
goto lbl_34;
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_doc__comment_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_23; 
x_23 = lean::box(3);
x_20 = x_0;
x_21 = x_23;
goto lbl_22;
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
lean::dec(x_0);
x_20 = x_26;
x_21 = x_24;
goto lbl_22;
}
lbl_19:
{
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_18, 0);
lean::inc(x_29);
lean::dec(x_18);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_5);
lean::cnstr_set(x_33, 1, x_17);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
case 1:
{
obj* x_35; obj* x_36; 
lean::dec(x_18);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_5);
lean::cnstr_set(x_36, 1, x_17);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
case 2:
{
obj* x_38; obj* x_39; 
lean::dec(x_18);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_5);
lean::cnstr_set(x_39, 1, x_17);
lean::cnstr_set(x_39, 2, x_38);
return x_39;
}
default:
{
obj* x_41; obj* x_42; 
lean::dec(x_18);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_17);
lean::cnstr_set(x_42, 2, x_41);
return x_42;
}
}
}
lbl_22:
{
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_43; obj* x_46; 
x_43 = lean::cnstr_get(x_21, 0);
lean::inc(x_43);
lean::dec(x_21);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_43);
if (lean::obj_tag(x_20) == 0)
{
obj* x_48; obj* x_49; 
lean::dec(x_20);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_46);
lean::cnstr_set(x_49, 2, x_48);
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_20, 0);
lean::inc(x_50);
lean::dec(x_20);
x_17 = x_46;
x_18 = x_50;
goto lbl_19;
}
}
case 1:
{
obj* x_54; 
lean::dec(x_21);
x_54 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_57; 
lean::dec(x_20);
lean::inc(x_54);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_20, 0);
lean::inc(x_58);
lean::dec(x_20);
x_17 = x_54;
x_18 = x_58;
goto lbl_19;
}
}
case 2:
{
obj* x_62; 
lean::dec(x_21);
x_62 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_65; 
lean::dec(x_20);
lean::inc(x_62);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_5);
lean::cnstr_set(x_65, 1, x_62);
lean::cnstr_set(x_65, 2, x_62);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_20, 0);
lean::inc(x_66);
lean::dec(x_20);
x_17 = x_62;
x_18 = x_66;
goto lbl_19;
}
}
default:
{
obj* x_70; 
lean::dec(x_21);
x_70 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_73; 
lean::dec(x_20);
lean::inc(x_70);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_5);
lean::cnstr_set(x_73, 1, x_70);
lean::cnstr_set(x_73, 2, x_70);
return x_73;
}
else
{
obj* x_74; 
x_74 = lean::cnstr_get(x_20, 0);
lean::inc(x_74);
lean::dec(x_20);
x_17 = x_70;
x_18 = x_74;
goto lbl_19;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_doc__comment_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
lean::inc(x_8);
x_15 = l_option_map___rarg(x_8, x_3);
lean::inc(x_11);
x_17 = l_option_get__or__else___main___rarg(x_15, x_11);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_doc__comment;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_doc__comment_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_doc__comment_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; 
lean::dec(x_4);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_5);
lean::inc(x_9);
x_14 = l_lean_parser_token(x_9, x_5, x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
lean::inc(x_0);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_0);
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_15, 2);
lean::inc(x_26);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_28 = x_15;
}
switch (lean::obj_tag(x_22)) {
case 0:
{
obj* x_32; obj* x_34; uint8 x_37; 
lean::dec(x_19);
x_32 = lean::cnstr_get(x_22, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
lean::dec(x_32);
x_37 = lean::string_dec_eq(x_0, x_34);
lean::dec(x_0);
if (x_37 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; 
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_5);
x_40 = lean::box(0);
x_41 = l_lean_parser_monad__parsec_error___at___private_409789351__finish__comment__block__aux___main___spec__1___rarg(x_34, x_2, x_39, x_40, x_9, x_24, x_17);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_46 = x_41;
}
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_42, 2);
lean::inc(x_49);
lean::dec(x_42);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
if (lean::is_scalar(x_28)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_28;
}
lean::cnstr_set(x_54, 0, x_22);
lean::cnstr_set(x_54, 1, x_47);
lean::cnstr_set(x_54, 2, x_52);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_55);
lean::inc(x_52);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_56);
x_59 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_21);
x_60 = l_lean_parser_parsec__t_try__mk__res___rarg(x_59);
if (lean::is_scalar(x_46)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_46;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_44);
return x_61;
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_22);
lean::dec(x_28);
x_64 = lean::cnstr_get(x_42, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_67 = x_42;
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_69);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_70);
x_74 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_73, x_21);
x_75 = l_lean_parser_parsec__t_try__mk__res___rarg(x_74);
if (lean::is_scalar(x_46)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_46;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_44);
return x_76;
}
}
else
{
obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_34);
x_81 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_81);
if (lean::is_scalar(x_28)) {
 x_83 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_83 = x_28;
}
lean::cnstr_set(x_83, 0, x_22);
lean::cnstr_set(x_83, 1, x_24);
lean::cnstr_set(x_83, 2, x_81);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_83);
x_85 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_85);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_84);
x_88 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_87, x_21);
x_89 = l_lean_parser_parsec__t_try__mk__res___rarg(x_88);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_17);
return x_90;
}
}
case 1:
{
obj* x_94; 
lean::dec(x_0);
lean::dec(x_22);
lean::dec(x_28);
x_94 = lean::box(0);
x_29 = x_94;
goto lbl_30;
}
case 2:
{
obj* x_98; 
lean::dec(x_0);
lean::dec(x_22);
lean::dec(x_28);
x_98 = lean::box(0);
x_29 = x_98;
goto lbl_30;
}
default:
{
obj* x_102; 
lean::dec(x_0);
lean::dec(x_22);
lean::dec(x_28);
x_102 = lean::box(0);
x_29 = x_102;
goto lbl_30;
}
}
lbl_30:
{
obj* x_104; obj* x_105; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_114; obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_29);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_5);
x_105 = lean::box(0);
x_106 = l_string_join___closed__1;
lean::inc(x_106);
x_108 = l_lean_parser_monad__parsec_error___at___private_409789351__finish__comment__block__aux___main___spec__1___rarg(x_106, x_2, x_104, x_105, x_9, x_24, x_17);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_109);
x_115 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_115);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_114);
x_118 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_117, x_21);
x_119 = l_lean_parser_parsec__t_try__mk__res___rarg(x_118);
if (lean::is_scalar(x_19)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_19;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_111);
return x_120;
}
}
else
{
obj* x_125; uint8 x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_125 = lean::cnstr_get(x_15, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_128 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_128 = x_15;
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_125);
lean::cnstr_set_scalar(x_129, sizeof(void*)*1, x_127);
x_130 = x_129;
x_131 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_131, x_130);
x_134 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_133, x_21);
x_135 = l_lean_parser_parsec__t_try__mk__res___rarg(x_134);
if (lean::is_scalar(x_19)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_19;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_17);
return x_136;
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_9; 
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_0);
x_9 = l_string_is__empty(x_0);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; 
x_10 = lean::string_length(x_0);
lean::inc(x_0);
x_12 = lean::string_mk_iterator(x_0);
lean::inc(x_4);
x_14 = l___private_2873386687__str__aux___main(x_10, x_12, x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_0);
x_17 = lean::box(0);
x_18 = l_string_join___closed__1;
lean::inc(x_18);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 2, x_1);
lean::cnstr_set(x_20, 3, x_17);
x_21 = 0;
x_22 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*1, x_21);
x_23 = x_22;
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_5);
return x_24;
}
else
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_4);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_14, 0);
lean::inc(x_27);
lean::dec(x_14);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_0);
lean::cnstr_set(x_31, 1, x_27);
lean::cnstr_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_5);
return x_32;
}
}
else
{
obj* x_35; obj* x_36; obj* x_39; obj* x_40; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = l_string_join___closed__1;
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_36);
lean::inc(x_35);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set(x_39, 1, x_4);
lean::cnstr_set(x_39, 2, x_36);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_5);
return x_40;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
x_4 = l___private_409789351__finish__comment__block__aux___main___closed__1;
x_5 = l___private_409789351__finish__comment__block__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 2);
lean::inc(x_17);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_19 = x_10;
}
x_20 = 0;
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = lean::box(x_20);
lean::inc(x_21);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_15);
lean::cnstr_set(x_24, 2, x_21);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_24);
if (lean::obj_tag(x_25) == 0)
{
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 lean::cnstr_release(x_25, 2);
 x_28 = x_25;
}
lean::inc(x_21);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_21);
if (lean::is_scalar(x_14)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_14;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_12);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_2);
if (lean::is_scalar(x_14)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_14;
}
lean::cnstr_set(x_33, 0, x_25);
lean::cnstr_set(x_33, 1, x_12);
return x_33;
}
}
else
{
uint8 x_35; obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_25);
x_35 = 1;
x_36 = lean::box(x_35);
lean::inc(x_21);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_2);
lean::cnstr_set(x_38, 2, x_21);
if (lean::is_scalar(x_14)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_14;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
return x_39;
}
}
else
{
uint8 x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_10);
x_41 = 1;
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_43 = lean::box(x_41);
lean::inc(x_42);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_2);
lean::cnstr_set(x_45, 2, x_42);
if (lean::is_scalar(x_14)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_14;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_12);
return x_46;
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_4);
x_10 = l_option_get__or__else___main___rarg(x_2, x_6);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
lean::cnstr_set(x_11, 2, x_1);
lean::cnstr_set(x_11, 3, x_3);
x_12 = 0;
x_13 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*1, x_12);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_iterator_has_next(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_5 = lean::box(0);
x_6 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_6, x_7, x_5, x_5, x_0, x_1, x_2, x_3);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_14);
return x_20;
}
else
{
uint32 x_21; uint8 x_22; 
x_21 = lean::string_iterator_curr(x_2);
x_22 = l_true_decidable;
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
x_23 = l_char_quote__core(x_21);
x_24 = l_char_has__repr___closed__1;
lean::inc(x_24);
x_26 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_28 = lean::string_append(x_26, x_24);
x_29 = lean::box(0);
x_30 = l_mjoin___rarg___closed__1;
lean::inc(x_29);
lean::inc(x_30);
x_33 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_28, x_30, x_29, x_29, x_0, x_1, x_2, x_3);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_38 = x_33;
}
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_39);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_34);
if (lean::is_scalar(x_38)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_38;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_36);
return x_42;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_0);
x_45 = lean::string_iterator_next(x_2);
x_46 = lean::box(0);
x_47 = lean::box_uint32(x_21);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_46);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_3);
return x_49;
}
}
}
}
obj* l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
}
obj* l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_0, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_21 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__3(x_1, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; uint8 x_34; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_22, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 2);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_33 = x_22;
}
x_34 = lean::unbox(x_27);
lean::dec(x_27);
if (x_34 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_33);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_3);
x_38 = lean::box(0);
x_39 = l___private_3809070873__whitespace__aux___main___closed__1;
x_40 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_40);
lean::inc(x_39);
x_45 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_39, x_40, x_37, x_38, x_1, x_2, x_29, x_24);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_62; obj* x_63; obj* x_65; obj* x_68; 
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
lean::dec(x_54);
lean::inc(x_2);
lean::inc(x_1);
x_62 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_55, x_48);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_63);
x_15 = x_68;
x_16 = x_65;
goto lbl_17;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_54, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_72 = x_54;
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_15 = x_74;
x_16 = x_48;
goto lbl_17;
}
}
else
{
obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; 
lean::dec(x_3);
x_76 = lean::box(0);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_77);
if (lean::is_scalar(x_33)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_33;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_29);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_79);
lean::inc(x_77);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_80);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_90; obj* x_91; obj* x_93; obj* x_96; 
x_83 = lean::cnstr_get(x_82, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
lean::inc(x_2);
lean::inc(x_1);
x_90 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_83, x_24);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
x_15 = x_96;
x_16 = x_93;
goto lbl_17;
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_82, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_100 = x_82;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_15 = x_102;
x_16 = x_24;
goto lbl_17;
}
}
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_22, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_107 = x_22;
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_104);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_106);
x_109 = x_108;
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_115; obj* x_120; obj* x_121; obj* x_123; obj* x_126; 
x_113 = lean::cnstr_get(x_112, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 2);
lean::inc(x_115);
lean::dec(x_112);
lean::inc(x_2);
lean::inc(x_1);
x_120 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_113, x_24);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_121);
x_15 = x_126;
x_16 = x_123;
goto lbl_17;
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; 
x_127 = lean::cnstr_get(x_112, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_shared(x_112)) {
 lean::dec(x_112);
 x_130 = lean::box(0);
} else {
 lean::cnstr_release(x_112, 0);
 x_130 = x_112;
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_129);
x_132 = x_131;
x_15 = x_132;
x_16 = x_24;
goto lbl_17;
}
}
lbl_17:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; 
x_133 = lean::cnstr_get(x_15, 1);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_15, 2);
lean::inc(x_135);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_137 = x_15;
}
lean::inc(x_133);
x_139 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__8(x_12, x_1, x_2, x_133, x_16);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
if (lean::is_shared(x_139)) {
 lean::dec(x_139);
 x_144 = lean::box(0);
} else {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_144 = x_139;
}
if (lean::obj_tag(x_140) == 0)
{
obj* x_147; obj* x_148; 
lean::dec(x_137);
lean::dec(x_133);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_144;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_142);
return x_148;
}
else
{
obj* x_149; uint8 x_151; 
x_149 = lean::cnstr_get(x_140, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_140, sizeof(void*)*1);
if (x_151 == 0)
{
obj* x_153; obj* x_156; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_140);
x_153 = lean::cnstr_get(x_149, 2);
lean::inc(x_153);
lean::dec(x_149);
x_156 = l_mjoin___rarg___closed__1;
lean::inc(x_156);
x_158 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_158, 0, x_153);
lean::closure_set(x_158, 1, x_156);
x_159 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_159, 0, x_158);
x_160 = lean::box(0);
if (lean::is_scalar(x_137)) {
 x_161 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_161 = x_137;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_133);
lean::cnstr_set(x_161, 2, x_159);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_161);
if (lean::is_scalar(x_144)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_144;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_142);
return x_163;
}
else
{
obj* x_167; obj* x_168; 
lean::dec(x_137);
lean::dec(x_133);
lean::dec(x_149);
x_167 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_144;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_142);
return x_168;
}
}
}
else
{
obj* x_172; uint8 x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_2);
x_172 = lean::cnstr_get(x_15, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_175 = x_15;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_172);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_174);
x_177 = x_176;
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_16);
return x_178;
}
}
}
else
{
obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_183 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__3(x_1, x_2, x_3, x_4);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_189; obj* x_191; obj* x_193; obj* x_195; uint8 x_196; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_184, 1);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_184, 2);
lean::inc(x_193);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 x_195 = x_184;
}
x_196 = lean::unbox(x_189);
lean::dec(x_189);
if (x_196 == 0)
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_207; obj* x_208; obj* x_210; obj* x_213; obj* x_214; obj* x_216; 
lean::dec(x_195);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_3);
x_200 = lean::box(0);
x_201 = l___private_3809070873__whitespace__aux___main___closed__1;
x_202 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_202);
lean::inc(x_201);
x_207 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_201, x_202, x_199, x_200, x_1, x_2, x_191, x_186);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
lean::dec(x_207);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_208);
x_214 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_213);
if (lean::obj_tag(x_216) == 0)
{
obj* x_217; obj* x_219; obj* x_222; obj* x_223; obj* x_225; obj* x_228; 
x_217 = lean::cnstr_get(x_216, 1);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 2);
lean::inc(x_219);
lean::dec(x_216);
x_222 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_217, x_210);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_222, 1);
lean::inc(x_225);
lean::dec(x_222);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_219, x_223);
x_5 = x_228;
x_6 = x_225;
goto lbl_7;
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_1);
lean::dec(x_2);
x_231 = lean::cnstr_get(x_216, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<uint8>(x_216, sizeof(void*)*1);
if (lean::is_shared(x_216)) {
 lean::dec(x_216);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_216, 0);
 x_234 = x_216;
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_5 = x_236;
x_6 = x_210;
goto lbl_7;
}
}
else
{
obj* x_238; obj* x_239; obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_3);
x_238 = lean::box(0);
x_239 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_239);
if (lean::is_scalar(x_195)) {
 x_241 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_241 = x_195;
}
lean::cnstr_set(x_241, 0, x_238);
lean::cnstr_set(x_241, 1, x_191);
lean::cnstr_set(x_241, 2, x_239);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_241);
lean::inc(x_239);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_242);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_247; obj* x_250; obj* x_251; obj* x_253; obj* x_256; 
x_245 = lean::cnstr_get(x_244, 1);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 2);
lean::inc(x_247);
lean::dec(x_244);
x_250 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_245, x_186);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_251);
x_5 = x_256;
x_6 = x_253;
goto lbl_7;
}
else
{
obj* x_259; uint8 x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_1);
lean::dec(x_2);
x_259 = lean::cnstr_get(x_244, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get_scalar<uint8>(x_244, sizeof(void*)*1);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_262 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 x_262 = x_244;
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_259);
lean::cnstr_set_scalar(x_263, sizeof(void*)*1, x_261);
x_264 = x_263;
x_5 = x_264;
x_6 = x_186;
goto lbl_7;
}
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_274; 
lean::dec(x_3);
x_266 = lean::cnstr_get(x_184, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_269 = x_184;
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_266);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_268);
x_271 = x_270;
x_272 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_272);
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_271);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; obj* x_277; obj* x_280; obj* x_281; obj* x_283; obj* x_286; 
x_275 = lean::cnstr_get(x_274, 1);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 2);
lean::inc(x_277);
lean::dec(x_274);
x_280 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_275, x_186);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
lean::dec(x_280);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_281);
x_5 = x_286;
x_6 = x_283;
goto lbl_7;
}
else
{
obj* x_289; uint8 x_291; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_1);
lean::dec(x_2);
x_289 = lean::cnstr_get(x_274, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get_scalar<uint8>(x_274, sizeof(void*)*1);
if (lean::is_shared(x_274)) {
 lean::dec(x_274);
 x_292 = lean::box(0);
} else {
 lean::cnstr_release(x_274, 0);
 x_292 = x_274;
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_289);
lean::cnstr_set_scalar(x_293, sizeof(void*)*1, x_291);
x_294 = x_293;
x_5 = x_294;
x_6 = x_186;
goto lbl_7;
}
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
x_295 = lean::cnstr_get(x_5, 1);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_5, 2);
lean::inc(x_297);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_299 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_299 = x_5;
}
x_300 = lean::box(0);
x_301 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_301);
if (lean::is_scalar(x_299)) {
 x_303 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_303 = x_299;
}
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_295);
lean::cnstr_set(x_303, 2, x_301);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_297, x_303);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_6);
return x_305;
}
else
{
obj* x_306; uint8 x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_306 = lean::cnstr_get(x_5, 0);
lean::inc(x_306);
x_308 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_309 = x_5;
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_306);
lean::cnstr_set_scalar(x_310, sizeof(void*)*1, x_308);
x_311 = x_310;
x_312 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_6);
return x_312;
}
}
}
}
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_4 = lean::string_iterator_remaining(x_2);
lean::inc(x_2);
x_6 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__8(x_4, x_0, x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_12);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_7);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; 
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_17; uint8 x_19; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_14);
x_21 = lean::cnstr_get(x_17, 2);
lean::inc(x_21);
lean::dec(x_17);
x_24 = l_mjoin___rarg___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_21);
lean::closure_set(x_26, 1, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_27);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_9);
return x_30;
}
else
{
obj* x_33; 
lean::dec(x_17);
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_14);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
}
}
obj* l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_3);
lean::inc(x_2);
x_8 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::apply_5(x_1, x_14, x_2, x_3, x_16, x_11);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_22);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_35 = x_9;
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
if (lean::is_scalar(x_13)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_13;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
return x_38;
}
}
}
obj* l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9___rarg), 6, 0);
return x_4;
}
}
obj* _init_l_lean_parser_command_doc__comment_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_33; 
x_0 = lean::mk_string("/--");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_notation__spec_symbol__quote_parser_lean_parser_has__view___spec__1___rarg), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6___rarg), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_doc__comment_parser_lean_parser_has__view___lambda__1), 5, 0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9___rarg), 6, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::mk_string("-/");
x_13 = l_string_trim(x_12);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_4);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_command__parser__m_monad___closed__1;
x_22 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_23 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_24 = l_lean_parser_command__parser__m_alternative___closed__1;
x_25 = l_lean_parser_command_doc__comment;
x_26 = l_lean_parser_command_doc__comment_has__view;
lean::inc(x_26);
lean::inc(x_25);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
x_33 = l_lean_parser_combinators_node_view___rarg(x_21, x_22, x_23, x_24, x_25, x_20, x_26);
return x_33;
}
}
obj* l_lean_parser_command_doc__comment_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_5 = l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__7(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_15 = x_6;
}
lean::inc(x_11);
x_17 = l_lean_parser_mk__raw__res(x_0, x_11);
x_18 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_18);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_11);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_20);
if (lean::is_scalar(x_10)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_10;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_8);
return x_22;
}
else
{
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_24 = lean::cnstr_get(x_6, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_27 = x_6;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_26);
x_29 = x_28;
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_10;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_8);
return x_30;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
x_4 = l___private_409789351__finish__comment__block__aux___main___closed__1;
x_5 = l___private_409789351__finish__comment__block__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 2);
lean::inc(x_17);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_19 = x_10;
}
x_20 = 0;
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = lean::box(x_20);
lean::inc(x_21);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_15);
lean::cnstr_set(x_24, 2, x_21);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_24);
if (lean::obj_tag(x_25) == 0)
{
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 lean::cnstr_release(x_25, 2);
 x_28 = x_25;
}
lean::inc(x_21);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_21);
if (lean::is_scalar(x_14)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_14;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_12);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_2);
if (lean::is_scalar(x_14)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_14;
}
lean::cnstr_set(x_33, 0, x_25);
lean::cnstr_set(x_33, 1, x_12);
return x_33;
}
}
else
{
uint8 x_35; obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_25);
x_35 = 1;
x_36 = lean::box(x_35);
lean::inc(x_21);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_2);
lean::cnstr_set(x_38, 2, x_21);
if (lean::is_scalar(x_14)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_14;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
return x_39;
}
}
else
{
uint8 x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_10);
x_41 = 1;
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_43 = lean::box(x_41);
lean::inc(x_42);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_2);
lean::cnstr_set(x_45, 2, x_42);
if (lean::is_scalar(x_14)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_14;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_12);
return x_46;
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_0, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_21 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(x_1, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; uint8 x_34; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_22, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 2);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_33 = x_22;
}
x_34 = lean::unbox(x_27);
lean::dec(x_27);
if (x_34 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_33);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_3);
x_38 = lean::box(0);
x_39 = l___private_3809070873__whitespace__aux___main___closed__1;
x_40 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_40);
lean::inc(x_39);
x_45 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_39, x_40, x_37, x_38, x_1, x_2, x_29, x_24);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_62; obj* x_63; obj* x_65; obj* x_68; 
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
lean::dec(x_54);
lean::inc(x_2);
lean::inc(x_1);
x_62 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_55, x_48);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_63);
x_15 = x_68;
x_16 = x_65;
goto lbl_17;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_54, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_72 = x_54;
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_15 = x_74;
x_16 = x_48;
goto lbl_17;
}
}
else
{
obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; 
lean::dec(x_3);
x_76 = lean::box(0);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_77);
if (lean::is_scalar(x_33)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_33;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_29);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_79);
lean::inc(x_77);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_80);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_90; obj* x_91; obj* x_93; obj* x_96; 
x_83 = lean::cnstr_get(x_82, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
lean::inc(x_2);
lean::inc(x_1);
x_90 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_83, x_24);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
x_15 = x_96;
x_16 = x_93;
goto lbl_17;
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_82, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_100 = x_82;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_15 = x_102;
x_16 = x_24;
goto lbl_17;
}
}
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_22, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_107 = x_22;
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_104);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_106);
x_109 = x_108;
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_115; obj* x_120; obj* x_121; obj* x_123; obj* x_126; 
x_113 = lean::cnstr_get(x_112, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 2);
lean::inc(x_115);
lean::dec(x_112);
lean::inc(x_2);
lean::inc(x_1);
x_120 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_113, x_24);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_121);
x_15 = x_126;
x_16 = x_123;
goto lbl_17;
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; 
x_127 = lean::cnstr_get(x_112, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_shared(x_112)) {
 lean::dec(x_112);
 x_130 = lean::box(0);
} else {
 lean::cnstr_release(x_112, 0);
 x_130 = x_112;
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_129);
x_132 = x_131;
x_15 = x_132;
x_16 = x_24;
goto lbl_17;
}
}
lbl_17:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; 
x_133 = lean::cnstr_get(x_15, 1);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_15, 2);
lean::inc(x_135);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_137 = x_15;
}
lean::inc(x_133);
x_139 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__3(x_12, x_1, x_2, x_133, x_16);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
if (lean::is_shared(x_139)) {
 lean::dec(x_139);
 x_144 = lean::box(0);
} else {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_144 = x_139;
}
if (lean::obj_tag(x_140) == 0)
{
obj* x_147; obj* x_148; 
lean::dec(x_137);
lean::dec(x_133);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_144;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_142);
return x_148;
}
else
{
obj* x_149; uint8 x_151; 
x_149 = lean::cnstr_get(x_140, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_140, sizeof(void*)*1);
if (x_151 == 0)
{
obj* x_153; obj* x_156; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_140);
x_153 = lean::cnstr_get(x_149, 2);
lean::inc(x_153);
lean::dec(x_149);
x_156 = l_mjoin___rarg___closed__1;
lean::inc(x_156);
x_158 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_158, 0, x_153);
lean::closure_set(x_158, 1, x_156);
x_159 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_159, 0, x_158);
x_160 = lean::box(0);
if (lean::is_scalar(x_137)) {
 x_161 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_161 = x_137;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_133);
lean::cnstr_set(x_161, 2, x_159);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_161);
if (lean::is_scalar(x_144)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_144;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_142);
return x_163;
}
else
{
obj* x_167; obj* x_168; 
lean::dec(x_137);
lean::dec(x_133);
lean::dec(x_149);
x_167 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_144;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_142);
return x_168;
}
}
}
else
{
obj* x_172; uint8 x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_2);
x_172 = lean::cnstr_get(x_15, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_175 = x_15;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_172);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_174);
x_177 = x_176;
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_16);
return x_178;
}
}
}
else
{
obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_183 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(x_1, x_2, x_3, x_4);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_189; obj* x_191; obj* x_193; obj* x_195; uint8 x_196; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_184, 1);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_184, 2);
lean::inc(x_193);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 x_195 = x_184;
}
x_196 = lean::unbox(x_189);
lean::dec(x_189);
if (x_196 == 0)
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_207; obj* x_208; obj* x_210; obj* x_213; obj* x_214; obj* x_216; 
lean::dec(x_195);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_3);
x_200 = lean::box(0);
x_201 = l___private_3809070873__whitespace__aux___main___closed__1;
x_202 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_202);
lean::inc(x_201);
x_207 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_201, x_202, x_199, x_200, x_1, x_2, x_191, x_186);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
lean::dec(x_207);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_208);
x_214 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_213);
if (lean::obj_tag(x_216) == 0)
{
obj* x_217; obj* x_219; obj* x_222; obj* x_223; obj* x_225; obj* x_228; 
x_217 = lean::cnstr_get(x_216, 1);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 2);
lean::inc(x_219);
lean::dec(x_216);
x_222 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_217, x_210);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_222, 1);
lean::inc(x_225);
lean::dec(x_222);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_219, x_223);
x_5 = x_228;
x_6 = x_225;
goto lbl_7;
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_1);
lean::dec(x_2);
x_231 = lean::cnstr_get(x_216, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<uint8>(x_216, sizeof(void*)*1);
if (lean::is_shared(x_216)) {
 lean::dec(x_216);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_216, 0);
 x_234 = x_216;
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_5 = x_236;
x_6 = x_210;
goto lbl_7;
}
}
else
{
obj* x_238; obj* x_239; obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_3);
x_238 = lean::box(0);
x_239 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_239);
if (lean::is_scalar(x_195)) {
 x_241 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_241 = x_195;
}
lean::cnstr_set(x_241, 0, x_238);
lean::cnstr_set(x_241, 1, x_191);
lean::cnstr_set(x_241, 2, x_239);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_241);
lean::inc(x_239);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_242);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_247; obj* x_250; obj* x_251; obj* x_253; obj* x_256; 
x_245 = lean::cnstr_get(x_244, 1);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 2);
lean::inc(x_247);
lean::dec(x_244);
x_250 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_245, x_186);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_251);
x_5 = x_256;
x_6 = x_253;
goto lbl_7;
}
else
{
obj* x_259; uint8 x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_1);
lean::dec(x_2);
x_259 = lean::cnstr_get(x_244, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get_scalar<uint8>(x_244, sizeof(void*)*1);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_262 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 x_262 = x_244;
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_259);
lean::cnstr_set_scalar(x_263, sizeof(void*)*1, x_261);
x_264 = x_263;
x_5 = x_264;
x_6 = x_186;
goto lbl_7;
}
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_274; 
lean::dec(x_3);
x_266 = lean::cnstr_get(x_184, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_269 = x_184;
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_266);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_268);
x_271 = x_270;
x_272 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_272);
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_271);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; obj* x_277; obj* x_280; obj* x_281; obj* x_283; obj* x_286; 
x_275 = lean::cnstr_get(x_274, 1);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 2);
lean::inc(x_277);
lean::dec(x_274);
x_280 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_275, x_186);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
lean::dec(x_280);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_281);
x_5 = x_286;
x_6 = x_283;
goto lbl_7;
}
else
{
obj* x_289; uint8 x_291; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_1);
lean::dec(x_2);
x_289 = lean::cnstr_get(x_274, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get_scalar<uint8>(x_274, sizeof(void*)*1);
if (lean::is_shared(x_274)) {
 lean::dec(x_274);
 x_292 = lean::box(0);
} else {
 lean::cnstr_release(x_274, 0);
 x_292 = x_274;
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_289);
lean::cnstr_set_scalar(x_293, sizeof(void*)*1, x_291);
x_294 = x_293;
x_5 = x_294;
x_6 = x_186;
goto lbl_7;
}
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
x_295 = lean::cnstr_get(x_5, 1);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_5, 2);
lean::inc(x_297);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_299 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_299 = x_5;
}
x_300 = lean::box(0);
x_301 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_301);
if (lean::is_scalar(x_299)) {
 x_303 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_303 = x_299;
}
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_295);
lean::cnstr_set(x_303, 2, x_301);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_297, x_303);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_6);
return x_305;
}
else
{
obj* x_306; uint8 x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_306 = lean::cnstr_get(x_5, 0);
lean::inc(x_306);
x_308 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_309 = x_5;
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_306);
lean::cnstr_set_scalar(x_310, sizeof(void*)*1, x_308);
x_311 = x_310;
x_312 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_6);
return x_312;
}
}
}
}
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_4 = lean::string_iterator_remaining(x_2);
lean::inc(x_2);
x_6 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__3(x_4, x_0, x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_12);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_7);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; 
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_17; uint8 x_19; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_14);
x_21 = lean::cnstr_get(x_17, 2);
lean::inc(x_21);
lean::dec(x_17);
x_24 = l_mjoin___rarg___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_21);
lean::closure_set(x_26, 1, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_27);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_9);
return x_30;
}
else
{
obj* x_33; 
lean::dec(x_17);
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_14);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_0, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_21 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(x_1, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; uint8 x_34; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_22, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 2);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_33 = x_22;
}
x_34 = lean::unbox(x_27);
lean::dec(x_27);
if (x_34 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_33);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_3);
x_38 = lean::box(0);
x_39 = l___private_3809070873__whitespace__aux___main___closed__1;
x_40 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_40);
lean::inc(x_39);
x_45 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_39, x_40, x_37, x_38, x_1, x_2, x_29, x_24);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_62; obj* x_63; obj* x_65; obj* x_68; 
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
lean::dec(x_54);
lean::inc(x_2);
lean::inc(x_1);
x_62 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_55, x_48);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_63);
x_15 = x_68;
x_16 = x_65;
goto lbl_17;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_54, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_72 = x_54;
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_15 = x_74;
x_16 = x_48;
goto lbl_17;
}
}
else
{
obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; 
lean::dec(x_3);
x_76 = lean::box(0);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_77);
if (lean::is_scalar(x_33)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_33;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_29);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_79);
lean::inc(x_77);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_80);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_90; obj* x_91; obj* x_93; obj* x_96; 
x_83 = lean::cnstr_get(x_82, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
lean::inc(x_2);
lean::inc(x_1);
x_90 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_83, x_24);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
x_15 = x_96;
x_16 = x_93;
goto lbl_17;
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_82, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_100 = x_82;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_15 = x_102;
x_16 = x_24;
goto lbl_17;
}
}
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_22, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_107 = x_22;
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_104);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_106);
x_109 = x_108;
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_115; obj* x_120; obj* x_121; obj* x_123; obj* x_126; 
x_113 = lean::cnstr_get(x_112, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 2);
lean::inc(x_115);
lean::dec(x_112);
lean::inc(x_2);
lean::inc(x_1);
x_120 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_113, x_24);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_121);
x_15 = x_126;
x_16 = x_123;
goto lbl_17;
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; 
x_127 = lean::cnstr_get(x_112, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_shared(x_112)) {
 lean::dec(x_112);
 x_130 = lean::box(0);
} else {
 lean::cnstr_release(x_112, 0);
 x_130 = x_112;
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_129);
x_132 = x_131;
x_15 = x_132;
x_16 = x_24;
goto lbl_17;
}
}
lbl_17:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; 
x_133 = lean::cnstr_get(x_15, 1);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_15, 2);
lean::inc(x_135);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_137 = x_15;
}
lean::inc(x_133);
x_139 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__5(x_12, x_1, x_2, x_133, x_16);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
if (lean::is_shared(x_139)) {
 lean::dec(x_139);
 x_144 = lean::box(0);
} else {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_144 = x_139;
}
if (lean::obj_tag(x_140) == 0)
{
obj* x_147; obj* x_148; 
lean::dec(x_137);
lean::dec(x_133);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_144;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_142);
return x_148;
}
else
{
obj* x_149; uint8 x_151; 
x_149 = lean::cnstr_get(x_140, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_140, sizeof(void*)*1);
if (x_151 == 0)
{
obj* x_153; obj* x_156; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_140);
x_153 = lean::cnstr_get(x_149, 2);
lean::inc(x_153);
lean::dec(x_149);
x_156 = l_mjoin___rarg___closed__1;
lean::inc(x_156);
x_158 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_158, 0, x_153);
lean::closure_set(x_158, 1, x_156);
x_159 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_159, 0, x_158);
x_160 = lean::box(0);
if (lean::is_scalar(x_137)) {
 x_161 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_161 = x_137;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_133);
lean::cnstr_set(x_161, 2, x_159);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_161);
if (lean::is_scalar(x_144)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_144;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_142);
return x_163;
}
else
{
obj* x_167; obj* x_168; 
lean::dec(x_137);
lean::dec(x_133);
lean::dec(x_149);
x_167 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_144;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_142);
return x_168;
}
}
}
else
{
obj* x_172; uint8 x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_2);
x_172 = lean::cnstr_get(x_15, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_175 = x_15;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_172);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_174);
x_177 = x_176;
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_16);
return x_178;
}
}
}
else
{
obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_183 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__1(x_1, x_2, x_3, x_4);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_189; obj* x_191; obj* x_193; obj* x_195; uint8 x_196; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_184, 1);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_184, 2);
lean::inc(x_193);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 x_195 = x_184;
}
x_196 = lean::unbox(x_189);
lean::dec(x_189);
if (x_196 == 0)
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_207; obj* x_208; obj* x_210; obj* x_213; obj* x_214; obj* x_216; 
lean::dec(x_195);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_3);
x_200 = lean::box(0);
x_201 = l___private_3809070873__whitespace__aux___main___closed__1;
x_202 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_202);
lean::inc(x_201);
x_207 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_201, x_202, x_199, x_200, x_1, x_2, x_191, x_186);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
lean::dec(x_207);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_208);
x_214 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_213);
if (lean::obj_tag(x_216) == 0)
{
obj* x_217; obj* x_219; obj* x_222; obj* x_223; obj* x_225; obj* x_228; 
x_217 = lean::cnstr_get(x_216, 1);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 2);
lean::inc(x_219);
lean::dec(x_216);
x_222 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_217, x_210);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_222, 1);
lean::inc(x_225);
lean::dec(x_222);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_219, x_223);
x_5 = x_228;
x_6 = x_225;
goto lbl_7;
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_1);
lean::dec(x_2);
x_231 = lean::cnstr_get(x_216, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<uint8>(x_216, sizeof(void*)*1);
if (lean::is_shared(x_216)) {
 lean::dec(x_216);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_216, 0);
 x_234 = x_216;
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_5 = x_236;
x_6 = x_210;
goto lbl_7;
}
}
else
{
obj* x_238; obj* x_239; obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_3);
x_238 = lean::box(0);
x_239 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_239);
if (lean::is_scalar(x_195)) {
 x_241 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_241 = x_195;
}
lean::cnstr_set(x_241, 0, x_238);
lean::cnstr_set(x_241, 1, x_191);
lean::cnstr_set(x_241, 2, x_239);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_241);
lean::inc(x_239);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_242);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_247; obj* x_250; obj* x_251; obj* x_253; obj* x_256; 
x_245 = lean::cnstr_get(x_244, 1);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 2);
lean::inc(x_247);
lean::dec(x_244);
x_250 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_245, x_186);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_251);
x_5 = x_256;
x_6 = x_253;
goto lbl_7;
}
else
{
obj* x_259; uint8 x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_1);
lean::dec(x_2);
x_259 = lean::cnstr_get(x_244, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get_scalar<uint8>(x_244, sizeof(void*)*1);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_262 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 x_262 = x_244;
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_259);
lean::cnstr_set_scalar(x_263, sizeof(void*)*1, x_261);
x_264 = x_263;
x_5 = x_264;
x_6 = x_186;
goto lbl_7;
}
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_274; 
lean::dec(x_3);
x_266 = lean::cnstr_get(x_184, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_269 = x_184;
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_266);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_268);
x_271 = x_270;
x_272 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_272);
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_271);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; obj* x_277; obj* x_280; obj* x_281; obj* x_283; obj* x_286; 
x_275 = lean::cnstr_get(x_274, 1);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 2);
lean::inc(x_277);
lean::dec(x_274);
x_280 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_275, x_186);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
lean::dec(x_280);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_281);
x_5 = x_286;
x_6 = x_283;
goto lbl_7;
}
else
{
obj* x_289; uint8 x_291; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_1);
lean::dec(x_2);
x_289 = lean::cnstr_get(x_274, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get_scalar<uint8>(x_274, sizeof(void*)*1);
if (lean::is_shared(x_274)) {
 lean::dec(x_274);
 x_292 = lean::box(0);
} else {
 lean::cnstr_release(x_274, 0);
 x_292 = x_274;
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_289);
lean::cnstr_set_scalar(x_293, sizeof(void*)*1, x_291);
x_294 = x_293;
x_5 = x_294;
x_6 = x_186;
goto lbl_7;
}
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
x_295 = lean::cnstr_get(x_5, 1);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_5, 2);
lean::inc(x_297);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_299 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_299 = x_5;
}
x_300 = lean::box(0);
x_301 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_301);
if (lean::is_scalar(x_299)) {
 x_303 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_303 = x_299;
}
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_295);
lean::cnstr_set(x_303, 2, x_301);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_297, x_303);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_6);
return x_305;
}
else
{
obj* x_306; uint8 x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_306 = lean::cnstr_get(x_5, 0);
lean::inc(x_306);
x_308 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_309 = x_5;
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_306);
lean::cnstr_set_scalar(x_310, sizeof(void*)*1, x_308);
x_311 = x_310;
x_312 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_6);
return x_312;
}
}
}
}
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_4 = lean::string_iterator_remaining(x_2);
lean::inc(x_2);
x_6 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser_lean_parser_has__tokens___spec__5(x_4, x_0, x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_12);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_7);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; 
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_17; uint8 x_19; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_14);
x_21 = lean::cnstr_get(x_17, 2);
lean::inc(x_21);
lean::dec(x_17);
x_24 = l_mjoin___rarg___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_21);
lean::closure_set(x_26, 1, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_27);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_9);
return x_30;
}
else
{
obj* x_33; 
lean::dec(x_17);
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_14);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
}
}
obj* _init_l_lean_parser_command_doc__comment_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::mk_string("/--");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::box(0);
x_5 = lean::mk_string("-/");
x_6 = l_lean_parser_symbol_tokens___rarg(x_5, x_1);
lean::inc(x_4);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_6, x_4);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_4, x_8);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_3, x_9);
x_11 = l_lean_parser_tokens___rarg(x_10);
return x_11;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
x_4 = l___private_409789351__finish__comment__block__aux___main___closed__1;
x_5 = l___private_409789351__finish__comment__block__aux___main___closed__2;
lean::inc(x_2);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_str__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 2);
lean::inc(x_17);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_19 = x_10;
}
x_20 = 0;
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = lean::box(x_20);
lean::inc(x_21);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_15);
lean::cnstr_set(x_24, 2, x_21);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_24);
if (lean::obj_tag(x_25) == 0)
{
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 lean::cnstr_release(x_25, 2);
 x_28 = x_25;
}
lean::inc(x_21);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_21);
if (lean::is_scalar(x_14)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_14;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_12);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_2);
if (lean::is_scalar(x_14)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_14;
}
lean::cnstr_set(x_33, 0, x_25);
lean::cnstr_set(x_33, 1, x_12);
return x_33;
}
}
else
{
uint8 x_35; obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_25);
x_35 = 1;
x_36 = lean::box(x_35);
lean::inc(x_21);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_2);
lean::cnstr_set(x_38, 2, x_21);
if (lean::is_scalar(x_14)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_14;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
return x_39;
}
}
else
{
uint8 x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_10);
x_41 = 1;
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_43 = lean::box(x_41);
lean::inc(x_42);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_2);
lean::cnstr_set(x_45, 2, x_42);
if (lean::is_scalar(x_14)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_14;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_12);
return x_46;
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_0, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_21 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser___spec__1(x_1, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; uint8 x_34; 
x_27 = lean::cnstr_get(x_22, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_22, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 2);
lean::inc(x_31);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_33 = x_22;
}
x_34 = lean::unbox(x_27);
lean::dec(x_27);
if (x_34 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_33);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_3);
x_38 = lean::box(0);
x_39 = l___private_3809070873__whitespace__aux___main___closed__1;
x_40 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_40);
lean::inc(x_39);
x_45 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_39, x_40, x_37, x_38, x_1, x_2, x_29, x_24);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_62; obj* x_63; obj* x_65; obj* x_68; 
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
lean::dec(x_54);
lean::inc(x_2);
lean::inc(x_1);
x_62 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_55, x_48);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_63);
x_15 = x_68;
x_16 = x_65;
goto lbl_17;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_54, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_72 = x_54;
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_15 = x_74;
x_16 = x_48;
goto lbl_17;
}
}
else
{
obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; 
lean::dec(x_3);
x_76 = lean::box(0);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_77);
if (lean::is_scalar(x_33)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_33;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set(x_79, 1, x_29);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_79);
lean::inc(x_77);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_80);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_85; obj* x_90; obj* x_91; obj* x_93; obj* x_96; 
x_83 = lean::cnstr_get(x_82, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 2);
lean::inc(x_85);
lean::dec(x_82);
lean::inc(x_2);
lean::inc(x_1);
x_90 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_83, x_24);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
x_15 = x_96;
x_16 = x_93;
goto lbl_17;
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_82, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_100 = x_82;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_15 = x_102;
x_16 = x_24;
goto lbl_17;
}
}
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_22, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_107 = x_22;
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_104);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_106);
x_109 = x_108;
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
if (lean::obj_tag(x_112) == 0)
{
obj* x_113; obj* x_115; obj* x_120; obj* x_121; obj* x_123; obj* x_126; 
x_113 = lean::cnstr_get(x_112, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 2);
lean::inc(x_115);
lean::dec(x_112);
lean::inc(x_2);
lean::inc(x_1);
x_120 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_113, x_24);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_121);
x_15 = x_126;
x_16 = x_123;
goto lbl_17;
}
else
{
obj* x_127; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; 
x_127 = lean::cnstr_get(x_112, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_shared(x_112)) {
 lean::dec(x_112);
 x_130 = lean::box(0);
} else {
 lean::cnstr_release(x_112, 0);
 x_130 = x_112;
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_127);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_129);
x_132 = x_131;
x_15 = x_132;
x_16 = x_24;
goto lbl_17;
}
}
lbl_17:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; 
x_133 = lean::cnstr_get(x_15, 1);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_15, 2);
lean::inc(x_135);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_137 = x_15;
}
lean::inc(x_133);
x_139 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser___spec__3(x_12, x_1, x_2, x_133, x_16);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
if (lean::is_shared(x_139)) {
 lean::dec(x_139);
 x_144 = lean::box(0);
} else {
 lean::cnstr_release(x_139, 0);
 lean::cnstr_release(x_139, 1);
 x_144 = x_139;
}
if (lean::obj_tag(x_140) == 0)
{
obj* x_147; obj* x_148; 
lean::dec(x_137);
lean::dec(x_133);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_144;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_142);
return x_148;
}
else
{
obj* x_149; uint8 x_151; 
x_149 = lean::cnstr_get(x_140, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_140, sizeof(void*)*1);
if (x_151 == 0)
{
obj* x_153; obj* x_156; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_140);
x_153 = lean::cnstr_get(x_149, 2);
lean::inc(x_153);
lean::dec(x_149);
x_156 = l_mjoin___rarg___closed__1;
lean::inc(x_156);
x_158 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_158, 0, x_153);
lean::closure_set(x_158, 1, x_156);
x_159 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_159, 0, x_158);
x_160 = lean::box(0);
if (lean::is_scalar(x_137)) {
 x_161 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_161 = x_137;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_133);
lean::cnstr_set(x_161, 2, x_159);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_161);
if (lean::is_scalar(x_144)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_144;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_142);
return x_163;
}
else
{
obj* x_167; obj* x_168; 
lean::dec(x_137);
lean::dec(x_133);
lean::dec(x_149);
x_167 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_140);
if (lean::is_scalar(x_144)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_144;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_142);
return x_168;
}
}
}
else
{
obj* x_172; uint8 x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_2);
x_172 = lean::cnstr_get(x_15, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_175 = x_15;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_172);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_174);
x_177 = x_176;
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_16);
return x_178;
}
}
}
else
{
obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_0);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_183 = l_lean_parser_parsec__t_lookahead___at_lean_parser_command_doc__comment_parser___spec__1(x_1, x_2, x_3, x_4);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_189; obj* x_191; obj* x_193; obj* x_195; uint8 x_196; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_184, 1);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_184, 2);
lean::inc(x_193);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 x_195 = x_184;
}
x_196 = lean::unbox(x_189);
lean::dec(x_189);
if (x_196 == 0)
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_207; obj* x_208; obj* x_210; obj* x_213; obj* x_214; obj* x_216; 
lean::dec(x_195);
x_199 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_199, 0, x_3);
x_200 = lean::box(0);
x_201 = l___private_3809070873__whitespace__aux___main___closed__1;
x_202 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_202);
lean::inc(x_201);
x_207 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_201, x_202, x_199, x_200, x_1, x_2, x_191, x_186);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
lean::dec(x_207);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_208);
x_214 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_213);
if (lean::obj_tag(x_216) == 0)
{
obj* x_217; obj* x_219; obj* x_222; obj* x_223; obj* x_225; obj* x_228; 
x_217 = lean::cnstr_get(x_216, 1);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 2);
lean::inc(x_219);
lean::dec(x_216);
x_222 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_217, x_210);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_222, 1);
lean::inc(x_225);
lean::dec(x_222);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_219, x_223);
x_5 = x_228;
x_6 = x_225;
goto lbl_7;
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_1);
lean::dec(x_2);
x_231 = lean::cnstr_get(x_216, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<uint8>(x_216, sizeof(void*)*1);
if (lean::is_shared(x_216)) {
 lean::dec(x_216);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_216, 0);
 x_234 = x_216;
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_5 = x_236;
x_6 = x_210;
goto lbl_7;
}
}
else
{
obj* x_238; obj* x_239; obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_3);
x_238 = lean::box(0);
x_239 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_239);
if (lean::is_scalar(x_195)) {
 x_241 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_241 = x_195;
}
lean::cnstr_set(x_241, 0, x_238);
lean::cnstr_set(x_241, 1, x_191);
lean::cnstr_set(x_241, 2, x_239);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_193, x_241);
lean::inc(x_239);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_242);
if (lean::obj_tag(x_244) == 0)
{
obj* x_245; obj* x_247; obj* x_250; obj* x_251; obj* x_253; obj* x_256; 
x_245 = lean::cnstr_get(x_244, 1);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 2);
lean::inc(x_247);
lean::dec(x_244);
x_250 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_245, x_186);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_251);
x_5 = x_256;
x_6 = x_253;
goto lbl_7;
}
else
{
obj* x_259; uint8 x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_1);
lean::dec(x_2);
x_259 = lean::cnstr_get(x_244, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get_scalar<uint8>(x_244, sizeof(void*)*1);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_262 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 x_262 = x_244;
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_259);
lean::cnstr_set_scalar(x_263, sizeof(void*)*1, x_261);
x_264 = x_263;
x_5 = x_264;
x_6 = x_186;
goto lbl_7;
}
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_274; 
lean::dec(x_3);
x_266 = lean::cnstr_get(x_184, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_269 = x_184;
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_266);
lean::cnstr_set_scalar(x_270, sizeof(void*)*1, x_268);
x_271 = x_270;
x_272 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_272);
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_272, x_271);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; obj* x_277; obj* x_280; obj* x_281; obj* x_283; obj* x_286; 
x_275 = lean::cnstr_get(x_274, 1);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 2);
lean::inc(x_277);
lean::dec(x_274);
x_280 = l_lean_parser_monad__parsec_any___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__5(x_1, x_2, x_275, x_186);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
lean::dec(x_280);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_281);
x_5 = x_286;
x_6 = x_283;
goto lbl_7;
}
else
{
obj* x_289; uint8 x_291; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_1);
lean::dec(x_2);
x_289 = lean::cnstr_get(x_274, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get_scalar<uint8>(x_274, sizeof(void*)*1);
if (lean::is_shared(x_274)) {
 lean::dec(x_274);
 x_292 = lean::box(0);
} else {
 lean::cnstr_release(x_274, 0);
 x_292 = x_274;
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_289);
lean::cnstr_set_scalar(x_293, sizeof(void*)*1, x_291);
x_294 = x_293;
x_5 = x_294;
x_6 = x_186;
goto lbl_7;
}
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
x_295 = lean::cnstr_get(x_5, 1);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_5, 2);
lean::inc(x_297);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_299 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_299 = x_5;
}
x_300 = lean::box(0);
x_301 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_301);
if (lean::is_scalar(x_299)) {
 x_303 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_303 = x_299;
}
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_295);
lean::cnstr_set(x_303, 2, x_301);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_297, x_303);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_6);
return x_305;
}
else
{
obj* x_306; uint8 x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
x_306 = lean::cnstr_get(x_5, 0);
lean::inc(x_306);
x_308 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_309 = x_5;
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_306);
lean::cnstr_set_scalar(x_310, sizeof(void*)*1, x_308);
x_311 = x_310;
x_312 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_6);
return x_312;
}
}
}
}
obj* l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_4 = lean::string_iterator_remaining(x_2);
lean::inc(x_2);
x_6 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_command_doc__comment_parser___spec__3(x_4, x_0, x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_12);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_7);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; 
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_17; uint8 x_19; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_14);
x_21 = lean::cnstr_get(x_17, 2);
lean::inc(x_21);
lean::dec(x_17);
x_24 = l_mjoin___rarg___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_26, 0, x_21);
lean::closure_set(x_26, 1, x_24);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_2);
lean::cnstr_set(x_29, 2, x_27);
if (lean::is_scalar(x_11)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_11;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_9);
return x_30;
}
else
{
obj* x_33; 
lean::dec(x_17);
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_14);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
}
}
obj* l_list_mfoldl___main___at_lean_parser_command_doc__comment_parser___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_11 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_5);
lean::cnstr_set(x_13, 2, x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_6);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_28; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 1);
lean::inc(x_17);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_19 = x_2;
}
lean::inc(x_4);
lean::inc(x_3);
x_25 = lean::apply_4(x_15, x_3, x_4, x_5, x_6);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
x_20 = x_26;
x_21 = x_28;
goto lbl_22;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_34 = x_26;
}
if (lean::obj_tag(x_1) == 0)
{
if (x_33 == 0)
{
uint8 x_35; obj* x_36; obj* x_37; 
x_35 = 0;
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
x_37 = x_36;
x_20 = x_37;
x_21 = x_28;
goto lbl_22;
}
else
{
obj* x_38; obj* x_39; 
if (lean::is_scalar(x_34)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_34;
}
lean::cnstr_set(x_38, 0, x_31);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_33);
x_39 = x_38;
x_20 = x_39;
x_21 = x_28;
goto lbl_22;
}
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
x_40 = lean::cnstr_get(x_31, 3);
lean::inc(x_40);
x_42 = l_option_get___main___at_lean_parser_run___spec__2(x_40);
lean::inc(x_1);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_1);
x_45 = lean::cnstr_get(x_31, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_31, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_31, 2);
lean::inc(x_49);
lean::dec(x_31);
x_52 = l_list_reverse___rarg(x_44);
lean::inc(x_0);
x_54 = l_lean_parser_syntax_mk__node(x_0, x_52);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_45);
lean::cnstr_set(x_56, 1, x_47);
lean::cnstr_set(x_56, 2, x_49);
lean::cnstr_set(x_56, 3, x_55);
if (x_33 == 0)
{
uint8 x_57; obj* x_58; obj* x_59; 
x_57 = 0;
if (lean::is_scalar(x_34)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_34;
}
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_57);
x_59 = x_58;
x_20 = x_59;
x_21 = x_28;
goto lbl_22;
}
else
{
obj* x_60; obj* x_61; 
if (lean::is_scalar(x_34)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_34;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_33);
x_61 = x_60;
x_20 = x_61;
x_21 = x_28;
goto lbl_22;
}
}
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; 
x_62 = lean::cnstr_get(x_20, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_20, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_20, 2);
lean::inc(x_66);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 lean::cnstr_release(x_20, 2);
 x_68 = x_20;
}
if (lean::is_scalar(x_19)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_19;
}
lean::cnstr_set(x_69, 0, x_62);
lean::cnstr_set(x_69, 1, x_1);
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_70);
if (lean::is_scalar(x_68)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_68;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_64);
lean::cnstr_set(x_72, 2, x_70);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_73, 2);
lean::inc(x_78);
lean::dec(x_73);
x_81 = l_list_mfoldl___main___at_lean_parser_command_doc__comment_parser___spec__5(x_0, x_74, x_17, x_3, x_4, x_76, x_21);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
if (lean::is_shared(x_81)) {
 lean::dec(x_81);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_86 = x_81;
}
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_82);
if (lean::is_scalar(x_86)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_86;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_84);
return x_88;
}
else
{
obj* x_93; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_93 = lean::cnstr_get(x_73, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_96 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_96 = x_73;
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_21);
return x_99;
}
}
else
{
obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
x_106 = lean::cnstr_get(x_20, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_109 = x_20;
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
x_111 = x_110;
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_21);
return x_112;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_command_doc__comment_parser___spec__5(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_20 = x_9;
}
x_21 = l_list_reverse___rarg(x_14);
x_22 = l_lean_parser_syntax_mk__node(x_0, x_21);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_23);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_16);
lean::cnstr_set(x_25, 2, x_23);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_25);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_11);
return x_27;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_0);
x_29 = lean::cnstr_get(x_9, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_32 = x_9;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_13)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_13;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_11);
return x_35;
}
}
}
obj* l_lean_parser_command_doc__comment_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_doc__comment;
x_5 = l_lean_parser_command_doc__comment_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_doc__comment_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::mk_string("/--");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_notation__spec_symbol__quote_parser_lean_parser_has__view___spec__1___rarg), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__6___rarg), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_doc__comment_parser___lambda__1), 5, 0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__9___rarg), 6, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::mk_string("-/");
x_13 = l_string_trim(x_12);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_15, 0, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_4);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
obj* l_lean_parser_command_doc__comment_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_5 = l_lean_parser_monad__parsec_many_x_27___at_lean_parser_command_doc__comment_parser___spec__2(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_15 = x_6;
}
lean::inc(x_11);
x_17 = l_lean_parser_mk__raw__res(x_0, x_11);
x_18 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_18);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_11);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_20);
if (lean::is_scalar(x_10)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_10;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_8);
return x_22;
}
else
{
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_24 = lean::cnstr_get(x_6, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_27 = x_6;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_26);
x_29 = x_28;
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_10;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_8);
return x_30;
}
}
}
obj* _init_l_lean_parser_command_attr__instance() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("attr_instance");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__3(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__3(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__4(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__4(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__5(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__5(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* _init_l_lean_parser_command_attr__instance_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_23; 
lean::dec(x_2);
x_23 = lean::box(0);
x_20 = x_23;
goto lbl_21;
}
case 1:
{
obj* x_24; 
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_1);
x_28 = lean::box(3);
x_29 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_33; 
lean::dec(x_29);
x_31 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_40; obj* x_41; 
x_34 = lean::cnstr_get(x_29, 0);
lean::inc(x_34);
lean::dec(x_29);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__3(x_37);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_24);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
else
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
lean::dec(x_1);
x_45 = l_lean_parser_syntax_as__node___main(x_42);
if (lean::obj_tag(x_45) == 0)
{
obj* x_47; obj* x_49; 
lean::dec(x_45);
x_47 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_24);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_56; obj* x_57; 
x_50 = lean::cnstr_get(x_45, 0);
lean::inc(x_50);
lean::dec(x_45);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__4(x_53);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_24);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
case 2:
{
obj* x_59; 
lean::dec(x_2);
x_59 = lean::box(0);
x_20 = x_59;
goto lbl_21;
}
default:
{
obj* x_61; 
lean::dec(x_2);
x_61 = lean::box(0);
x_20 = x_61;
goto lbl_21;
}
}
lbl_21:
{
lean::dec(x_20);
if (lean::obj_tag(x_1) == 0)
{
obj* x_64; 
lean::dec(x_1);
x_64 = l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_64);
return x_64;
}
else
{
obj* x_66; obj* x_69; 
x_66 = lean::cnstr_get(x_1, 0);
lean::inc(x_66);
lean::dec(x_1);
x_69 = l_lean_parser_syntax_as__node___main(x_66);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; 
lean::dec(x_69);
x_71 = l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_71);
return x_71;
}
else
{
obj* x_73; obj* x_76; obj* x_79; obj* x_80; obj* x_82; 
x_73 = lean::cnstr_get(x_69, 0);
lean::inc(x_73);
lean::dec(x_69);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__2(x_76);
x_80 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_79);
return x_82;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
lean::inc(x_0);
x_5 = lean::name_mk_string(x_0, x_1);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set(x_9, 2, x_5);
lean::cnstr_set(x_9, 3, x_0);
lean::cnstr_set(x_9, 4, x_0);
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* _init_l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__1(x_8);
x_12 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
}
}
obj* _init_l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::box(0);
x_5 = x_8;
goto lbl_6;
}
case 1:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_0);
x_13 = lean::box(3);
x_14 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_18; 
lean::dec(x_14);
x_16 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
lean::dec(x_14);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__3(x_22);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
lean::dec(x_0);
x_30 = l_lean_parser_syntax_as__node___main(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_32; obj* x_34; 
lean::dec(x_30);
x_32 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_32);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_30, 0);
lean::inc(x_35);
lean::dec(x_30);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
x_41 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__4(x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
case 2:
{
obj* x_44; 
lean::dec(x_1);
x_44 = lean::box(0);
x_5 = x_44;
goto lbl_6;
}
default:
{
obj* x_46; 
lean::dec(x_1);
x_46 = lean::box(0);
x_5 = x_46;
goto lbl_6;
}
}
lbl_6:
{
lean::dec(x_5);
if (lean::obj_tag(x_0) == 0)
{
obj* x_49; 
lean::dec(x_0);
x_49 = l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_49);
return x_49;
}
else
{
obj* x_51; obj* x_54; 
x_51 = lean::cnstr_get(x_0, 0);
lean::inc(x_51);
lean::dec(x_0);
x_54 = l_lean_parser_syntax_as__node___main(x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; 
lean::dec(x_54);
x_56 = l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
return x_56;
}
else
{
obj* x_58; obj* x_61; obj* x_64; obj* x_65; obj* x_67; 
x_58 = lean::cnstr_get(x_54, 0);
lean::inc(x_58);
lean::dec(x_54);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__2(x_61);
x_65 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_64);
return x_67;
}
}
}
}
}
}
obj* l_lean_parser_command_attr__instance_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
x_7 = l_list_map___main___at_lean_parser_command_attr__instance_has__view_x_27___spec__5(x_3);
x_8 = l_lean_parser_no__kind;
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mk__node(x_8, x_7);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_command_attr__instance;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
}
obj* _init_l_lean_parser_command_attr__instance_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_attr__instance_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_raw__ident_parser___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_5);
x_9 = l___private_3601861905__ident_x_27(x_5, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_28; obj* x_29; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
lean::dec(x_10);
x_22 = l_lean_parser_with__trailing___at_lean_parser_token___spec__3(x_15, x_5, x_17, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_23);
if (lean::is_scalar(x_14)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_14;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_25);
return x_29;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_5);
x_31 = lean::cnstr_get(x_10, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_34 = x_10;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_14)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_14;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_12);
return x_37;
}
}
}
obj* l___private_1386096941__many1__aux___main___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_2, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_20; obj* x_21; obj* x_23; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_0);
x_20 = lean::apply_4(x_0, x_3, x_4, x_5, x_6);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
x_14 = x_21;
x_15 = x_23;
goto lbl_16;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_29 = x_21;
}
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_26, 3);
lean::inc(x_36);
lean::dec(x_26);
x_39 = l_option_get___main___at_lean_parser_run___spec__2(x_36);
lean::inc(x_1);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_1);
x_42 = lean::box(3);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_list_reverse___rarg(x_43);
x_45 = l_lean_parser_no__kind;
lean::inc(x_45);
x_47 = l_lean_parser_syntax_mk__node(x_45, x_44);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
if (x_28 == 0)
{
uint8 x_50; obj* x_51; obj* x_52; 
x_50 = 0;
if (lean::is_scalar(x_29)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_29;
}
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_50);
x_52 = x_51;
x_14 = x_52;
x_15 = x_23;
goto lbl_16;
}
else
{
obj* x_53; obj* x_54; 
if (lean::is_scalar(x_29)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_29;
}
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_28);
x_54 = x_53;
x_14 = x_54;
x_15 = x_23;
goto lbl_16;
}
}
lbl_16:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_65; obj* x_66; obj* x_68; obj* x_70; 
x_55 = lean::cnstr_get(x_14, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_14, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_14, 2);
lean::inc(x_59);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_61 = x_14;
}
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_55);
lean::cnstr_set(x_62, 1, x_1);
lean::inc(x_57);
lean::inc(x_62);
x_65 = l___private_1386096941__many1__aux___main___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__4(x_0, x_62, x_11, x_3, x_4, x_57, x_15);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_70 = x_65;
}
if (lean::obj_tag(x_66) == 0)
{
obj* x_74; obj* x_75; 
lean::dec(x_62);
lean::dec(x_61);
lean::dec(x_57);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_66);
if (lean::is_scalar(x_70)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_70;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_68);
return x_75;
}
else
{
obj* x_76; uint8 x_78; 
x_76 = lean::cnstr_get(x_66, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (x_78 == 0)
{
obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_66);
x_80 = l_list_reverse___rarg(x_62);
x_81 = l_lean_parser_no__kind;
lean::inc(x_81);
x_83 = l_lean_parser_syntax_mk__node(x_81, x_80);
x_84 = lean::cnstr_get(x_76, 2);
lean::inc(x_84);
lean::dec(x_76);
x_87 = l_mjoin___rarg___closed__1;
lean::inc(x_87);
x_89 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_89, 0, x_84);
lean::closure_set(x_89, 1, x_87);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_89);
if (lean::is_scalar(x_61)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_61;
}
lean::cnstr_set(x_91, 0, x_83);
lean::cnstr_set(x_91, 1, x_57);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_91);
if (lean::is_scalar(x_70)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_70;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_68);
return x_93;
}
else
{
obj* x_98; obj* x_99; 
lean::dec(x_76);
lean::dec(x_62);
lean::dec(x_61);
lean::dec(x_57);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_66);
if (lean::is_scalar(x_70)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_70;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_68);
return x_99;
}
}
}
else
{
obj* x_105; uint8 x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_105 = lean::cnstr_get(x_14, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_108 = x_14;
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_105);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_107);
x_110 = x_109;
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_15);
return x_111;
}
}
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_121; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::box(0);
x_116 = l___private_1386096941__many1__aux___main___rarg___closed__1;
x_117 = l_mjoin___rarg___closed__1;
lean::inc(x_115);
lean::inc(x_117);
lean::inc(x_116);
x_121 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_116, x_117, x_115, x_115, x_3, x_4, x_5, x_6);
return x_121;
}
}
}
obj* l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_5 = lean::string_iterator_remaining(x_3);
x_6 = lean::box(0);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
x_11 = l___private_1386096941__many1__aux___main___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__4(x_0, x_6, x_8, x_1, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_14);
return x_20;
}
}
obj* l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_3);
x_6 = l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3(x_0, x_1, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_13; 
lean::dec(x_3);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
else
{
obj* x_14; uint8 x_16; 
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_16 == 0)
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_7);
x_18 = lean::cnstr_get(x_14, 2);
lean::inc(x_18);
lean::dec(x_14);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_23, 0, x_18);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_3);
lean::cnstr_set(x_27, 2, x_24);
if (lean::is_scalar(x_11)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_11;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
return x_28;
}
else
{
obj* x_31; 
lean::dec(x_14);
lean::dec(x_3);
if (lean::is_scalar(x_11)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_11;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_9);
return x_31;
}
}
}
}
obj* _init_l_lean_parser_command_attr__instance_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_21; 
x_0 = l_lean_parser_max__prec;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__ident_parser___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__1), 4, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = l_lean_parser_command__parser__m_monad___closed__1;
x_10 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_11 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_12 = l_lean_parser_command__parser__m_alternative___closed__1;
x_13 = l_lean_parser_command_attr__instance;
x_14 = l_lean_parser_command_attr__instance_has__view;
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
x_21 = l_lean_parser_combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
return x_21;
}
}
obj* _init_l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_1);
x_3 = l_lean_parser_tokens___rarg(x_1);
x_4 = l_lean_parser_tokens___rarg(x_3);
lean::inc(x_0);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_4, x_0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_0, x_6);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* l_lean_parser_command_attr__instance_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_attr__instance;
x_5 = l_lean_parser_command_attr__instance_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_attr__instance_parser___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = l_lean_parser_max__prec;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__ident_parser___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__1), 4, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__attributes() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("decl_attributes");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_5);
x_9 = l_lean_parser_command_attr__instance_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_3);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_parser_command_attr__instance_has__view;
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::apply_1(x_23, x_3);
x_26 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__1(x_19);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
lean::dec(x_17);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_31);
if (lean::is_scalar(x_7)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_7;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
case 1:
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_17);
x_35 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_25);
lean::cnstr_set(x_37, 1, x_35);
if (lean::is_scalar(x_7)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_7;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_26);
return x_38;
}
case 2:
{
obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_17);
x_40 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_25);
lean::cnstr_set(x_42, 1, x_40);
if (lean::is_scalar(x_7)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_7;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_26);
return x_43;
}
default:
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_17);
x_45 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_25);
lean::cnstr_set(x_47, 1, x_45);
if (lean::is_scalar(x_7)) {
 x_48 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_48 = x_7;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_26);
return x_48;
}
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_list_map___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__2(x_5);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_10);
x_15 = l_lean_parser_command_attr__instance_has__view;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_18 = lean::apply_1(x_16, x_8);
x_19 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_22 = lean::cnstr_get(x_10, 0);
lean::inc(x_22);
lean::dec(x_10);
x_25 = l_lean_parser_command_attr__instance_has__view;
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
x_28 = lean::apply_1(x_26, x_8);
x_29 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_29);
x_31 = l_option_map___rarg(x_29, x_22);
x_32 = lean::box(3);
x_33 = l_option_get__or__else___main___rarg(x_31, x_32);
x_34 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_7;
}
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_28);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_13);
return x_37;
}
}
}
}
obj* _init_l_lean_parser_command_decl__attributes_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__attributes_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_1;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
lean::dec(x_1);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_33);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; 
lean::dec(x_41);
x_43 = lean::box(0);
if (lean::obj_tag(x_32) == 0)
{
obj* x_45; obj* x_47; 
lean::dec(x_32);
x_45 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 2, x_43);
return x_47;
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_32, 0);
lean::inc(x_48);
lean::dec(x_32);
switch (lean::obj_tag(x_48)) {
case 0:
{
obj* x_52; obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_43);
x_52 = lean::cnstr_get(x_48, 0);
lean::inc(x_52);
lean::dec(x_48);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_52);
x_56 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_58, 0, x_20);
lean::cnstr_set(x_58, 1, x_56);
lean::cnstr_set(x_58, 2, x_55);
return x_58;
}
case 1:
{
obj* x_60; obj* x_62; 
lean::dec(x_48);
x_60 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_20);
lean::cnstr_set(x_62, 1, x_60);
lean::cnstr_set(x_62, 2, x_43);
return x_62;
}
case 2:
{
obj* x_64; obj* x_66; 
lean::dec(x_48);
x_64 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_20);
lean::cnstr_set(x_66, 1, x_64);
lean::cnstr_set(x_66, 2, x_43);
return x_66;
}
default:
{
obj* x_68; obj* x_70; 
lean::dec(x_48);
x_68 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_68);
x_70 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_70, 0, x_20);
lean::cnstr_set(x_70, 1, x_68);
lean::cnstr_set(x_70, 2, x_43);
return x_70;
}
}
}
}
else
{
obj* x_71; obj* x_73; obj* x_74; obj* x_77; 
x_71 = lean::cnstr_get(x_41, 0);
lean::inc(x_71);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_73 = x_41;
}
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
x_77 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__1(x_74);
if (lean::obj_tag(x_32) == 0)
{
obj* x_80; obj* x_81; 
lean::dec(x_73);
lean::dec(x_32);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_20);
lean::cnstr_set(x_81, 1, x_77);
lean::cnstr_set(x_81, 2, x_80);
return x_81;
}
else
{
obj* x_82; 
x_82 = lean::cnstr_get(x_32, 0);
lean::inc(x_82);
lean::dec(x_32);
switch (lean::obj_tag(x_82)) {
case 0:
{
obj* x_85; obj* x_88; obj* x_89; 
x_85 = lean::cnstr_get(x_82, 0);
lean::inc(x_85);
lean::dec(x_82);
if (lean::is_scalar(x_73)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_73;
}
lean::cnstr_set(x_88, 0, x_85);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_20);
lean::cnstr_set(x_89, 1, x_77);
lean::cnstr_set(x_89, 2, x_88);
return x_89;
}
case 1:
{
obj* x_92; obj* x_93; 
lean::dec(x_73);
lean::dec(x_82);
x_92 = lean::box(0);
x_93 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_93, 0, x_20);
lean::cnstr_set(x_93, 1, x_77);
lean::cnstr_set(x_93, 2, x_92);
return x_93;
}
case 2:
{
obj* x_96; obj* x_97; 
lean::dec(x_73);
lean::dec(x_82);
x_96 = lean::box(0);
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_20);
lean::cnstr_set(x_97, 1, x_77);
lean::cnstr_set(x_97, 2, x_96);
return x_97;
}
default:
{
obj* x_100; obj* x_101; 
lean::dec(x_73);
lean::dec(x_82);
x_100 = lean::box(0);
x_101 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_101, 0, x_20);
lean::cnstr_set(x_101, 1, x_77);
lean::cnstr_set(x_101, 2, x_100);
return x_101;
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_0 = l_lean_parser_command_attr__instance_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = lean::box(3);
x_17 = x_0;
x_18 = x_20;
goto lbl_19;
}
else
{
obj* x_21; obj* x_23; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
x_17 = x_23;
x_18 = x_21;
goto lbl_19;
}
lbl_19:
{
obj* x_26; 
x_26 = l_lean_parser_syntax_as__node___main(x_18);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; 
lean::dec(x_26);
x_28 = lean::box(0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_30; obj* x_32; 
lean::dec(x_17);
x_30 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_28);
return x_32;
}
else
{
obj* x_33; 
x_33 = lean::cnstr_get(x_17, 0);
lean::inc(x_33);
lean::dec(x_17);
switch (lean::obj_tag(x_33)) {
case 0:
{
obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_28);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
x_41 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_5);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set(x_43, 2, x_40);
return x_43;
}
case 1:
{
obj* x_45; obj* x_47; 
lean::dec(x_33);
x_45 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_5);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 2, x_28);
return x_47;
}
case 2:
{
obj* x_49; obj* x_51; 
lean::dec(x_33);
x_49 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_5);
lean::cnstr_set(x_51, 1, x_49);
lean::cnstr_set(x_51, 2, x_28);
return x_51;
}
default:
{
obj* x_53; obj* x_55; 
lean::dec(x_33);
x_53 = l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_55, 0, x_5);
lean::cnstr_set(x_55, 1, x_53);
lean::cnstr_set(x_55, 2, x_28);
return x_55;
}
}
}
}
else
{
obj* x_56; obj* x_58; obj* x_59; obj* x_62; 
x_56 = lean::cnstr_get(x_26, 0);
lean::inc(x_56);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_58 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_58 = x_26;
}
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
x_62 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__1(x_59);
if (lean::obj_tag(x_17) == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_17);
lean::dec(x_58);
x_65 = lean::box(0);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_5);
lean::cnstr_set(x_66, 1, x_62);
lean::cnstr_set(x_66, 2, x_65);
return x_66;
}
else
{
obj* x_67; 
x_67 = lean::cnstr_get(x_17, 0);
lean::inc(x_67);
lean::dec(x_17);
switch (lean::obj_tag(x_67)) {
case 0:
{
obj* x_70; obj* x_73; obj* x_74; 
x_70 = lean::cnstr_get(x_67, 0);
lean::inc(x_70);
lean::dec(x_67);
if (lean::is_scalar(x_58)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_58;
}
lean::cnstr_set(x_73, 0, x_70);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_5);
lean::cnstr_set(x_74, 1, x_62);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
case 1:
{
obj* x_77; obj* x_78; 
lean::dec(x_58);
lean::dec(x_67);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_5);
lean::cnstr_set(x_78, 1, x_62);
lean::cnstr_set(x_78, 2, x_77);
return x_78;
}
case 2:
{
obj* x_81; obj* x_82; 
lean::dec(x_58);
lean::dec(x_67);
x_81 = lean::box(0);
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_5);
lean::cnstr_set(x_82, 1, x_62);
lean::cnstr_set(x_82, 2, x_81);
return x_82;
}
default:
{
obj* x_85; obj* x_86; 
lean::dec(x_58);
lean::dec(x_67);
x_85 = lean::box(0);
x_86 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_86, 0, x_5);
lean::cnstr_set(x_86, 1, x_62);
lean::cnstr_set(x_86, 2, x_85);
return x_86;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_decl__attributes_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_list_map___main___at_lean_parser_command_decl__attributes_has__view_x_27___spec__2(x_3);
x_15 = l_list_join___main___rarg(x_14);
x_16 = l_lean_parser_no__kind;
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mk__node(x_16, x_15);
lean::inc(x_8);
x_20 = l_option_map___rarg(x_8, x_5);
x_21 = l_option_get__or__else___main___rarg(x_20, x_11);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_18);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_lean_parser_command_decl__attributes;
lean::inc(x_26);
x_28 = l_lean_parser_syntax_mk__node(x_26, x_25);
return x_28;
}
}
obj* _init_l_lean_parser_command_decl__attributes_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_decl__attributes_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2(obj* x_0, obj* x_1, uint8 x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_5, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_5, x_13);
lean::dec(x_13);
lean::dec(x_5);
if (x_3 == 0)
{
obj* x_26; obj* x_27; obj* x_29; 
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_0);
x_26 = lean::apply_4(x_0, x_6, x_7, x_8, x_9);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_32 = lean::cnstr_get(x_27, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_27, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_27, 2);
lean::inc(x_36);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 lean::cnstr_release(x_27, 1);
 lean::cnstr_release(x_27, 2);
 x_38 = x_27;
}
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_32);
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_40);
if (lean::is_scalar(x_38)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_38;
}
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_34);
lean::cnstr_set(x_42, 2, x_40);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_42);
if (lean::obj_tag(x_43) == 0)
{
x_17 = x_43;
x_18 = x_29;
goto lbl_19;
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 x_47 = x_43;
}
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_44, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_44, 2);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_44, 3);
lean::inc(x_54);
lean::dec(x_44);
x_57 = l_option_get___main___at_lean_parser_run___spec__2(x_54);
lean::inc(x_4);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_4);
x_60 = lean::box(3);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_59);
x_62 = l_list_reverse___rarg(x_61);
x_63 = l_lean_parser_no__kind;
lean::inc(x_63);
x_65 = l_lean_parser_syntax_mk__node(x_63, x_62);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_67, 0, x_48);
lean::cnstr_set(x_67, 1, x_50);
lean::cnstr_set(x_67, 2, x_52);
lean::cnstr_set(x_67, 3, x_66);
if (x_46 == 0)
{
uint8 x_68; obj* x_69; obj* x_70; 
x_68 = 0;
if (lean::is_scalar(x_47)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_47;
}
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_68);
x_70 = x_69;
x_17 = x_70;
x_18 = x_29;
goto lbl_19;
}
else
{
obj* x_71; obj* x_72; 
if (lean::is_scalar(x_47)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_47;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_46);
x_72 = x_71;
x_17 = x_72;
x_18 = x_29;
goto lbl_19;
}
}
}
else
{
obj* x_73; uint8 x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_94; obj* x_95; obj* x_96; 
x_73 = lean::cnstr_get(x_27, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 x_76 = x_27;
}
x_77 = lean::cnstr_get(x_73, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_73, 1);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_73, 2);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_73, 3);
lean::inc(x_83);
lean::dec(x_73);
x_86 = l_option_get___main___at_lean_parser_run___spec__2(x_83);
lean::inc(x_4);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_4);
x_89 = lean::box(3);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_88);
x_91 = l_list_reverse___rarg(x_90);
x_92 = l_lean_parser_no__kind;
lean::inc(x_92);
x_94 = l_lean_parser_syntax_mk__node(x_92, x_91);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_96 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_96, 0, x_77);
lean::cnstr_set(x_96, 1, x_79);
lean::cnstr_set(x_96, 2, x_81);
lean::cnstr_set(x_96, 3, x_95);
if (x_75 == 0)
{
uint8 x_97; obj* x_98; obj* x_99; 
x_97 = 0;
if (lean::is_scalar(x_76)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_76;
}
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_97);
x_99 = x_98;
x_17 = x_99;
x_18 = x_29;
goto lbl_19;
}
else
{
obj* x_100; obj* x_101; 
if (lean::is_scalar(x_76)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_76;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_75);
x_101 = x_100;
x_17 = x_101;
x_18 = x_29;
goto lbl_19;
}
}
}
else
{
obj* x_106; obj* x_107; obj* x_109; obj* x_112; 
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_0);
x_106 = lean::apply_4(x_0, x_6, x_7, x_8, x_9);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
x_112 = lean::box(0);
if (lean::obj_tag(x_107) == 0)
{
obj* x_113; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_121; obj* x_123; obj* x_124; 
x_113 = lean::cnstr_get(x_107, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_107, 1);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_107, 2);
lean::inc(x_117);
if (lean::is_shared(x_107)) {
 lean::dec(x_107);
 x_119 = lean::box(0);
} else {
 lean::cnstr_release(x_107, 0);
 lean::cnstr_release(x_107, 1);
 lean::cnstr_release(x_107, 2);
 x_119 = x_107;
}
x_120 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_120, 0, x_113);
x_121 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_121);
if (lean::is_scalar(x_119)) {
 x_123 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_123 = x_119;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_115);
lean::cnstr_set(x_123, 2, x_121);
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_117, x_123);
if (lean::obj_tag(x_124) == 0)
{
lean::dec(x_8);
lean::dec(x_112);
x_20 = x_124;
x_21 = x_109;
goto lbl_22;
}
else
{
obj* x_127; uint8 x_129; 
x_127 = lean::cnstr_get(x_124, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get_scalar<uint8>(x_124, sizeof(void*)*1);
if (x_129 == 0)
{
obj* x_131; obj* x_134; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_124);
x_131 = lean::cnstr_get(x_127, 2);
lean::inc(x_131);
lean::dec(x_127);
x_134 = l_mjoin___rarg___closed__1;
lean::inc(x_134);
x_136 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_136, 0, x_131);
lean::closure_set(x_136, 1, x_134);
x_137 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_137, 0, x_136);
x_138 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_138, 0, x_112);
lean::cnstr_set(x_138, 1, x_8);
lean::cnstr_set(x_138, 2, x_137);
x_20 = x_138;
x_21 = x_109;
goto lbl_22;
}
else
{
lean::dec(x_8);
lean::dec(x_112);
lean::dec(x_127);
x_20 = x_124;
x_21 = x_109;
goto lbl_22;
}
}
}
else
{
obj* x_142; uint8 x_144; obj* x_145; 
x_142 = lean::cnstr_get(x_107, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get_scalar<uint8>(x_107, sizeof(void*)*1);
if (lean::is_shared(x_107)) {
 lean::dec(x_107);
 x_145 = lean::box(0);
} else {
 lean::cnstr_release(x_107, 0);
 x_145 = x_107;
}
if (x_144 == 0)
{
obj* x_147; obj* x_150; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_145);
x_147 = lean::cnstr_get(x_142, 2);
lean::inc(x_147);
lean::dec(x_142);
x_150 = l_mjoin___rarg___closed__1;
lean::inc(x_150);
x_152 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_152, 0, x_147);
lean::closure_set(x_152, 1, x_150);
x_153 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_153, 0, x_152);
x_154 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_154, 0, x_112);
lean::cnstr_set(x_154, 1, x_8);
lean::cnstr_set(x_154, 2, x_153);
x_20 = x_154;
x_21 = x_109;
goto lbl_22;
}
else
{
obj* x_157; obj* x_158; 
lean::dec(x_8);
lean::dec(x_112);
if (lean::is_scalar(x_145)) {
 x_157 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_157 = x_145;
}
lean::cnstr_set(x_157, 0, x_142);
lean::cnstr_set_scalar(x_157, sizeof(void*)*1, x_144);
x_158 = x_157;
x_20 = x_158;
x_21 = x_109;
goto lbl_22;
}
}
}
lbl_19:
{
if (lean::obj_tag(x_17) == 0)
{
obj* x_159; obj* x_161; obj* x_163; obj* x_165; 
x_159 = lean::cnstr_get(x_17, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_17, 1);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_17, 2);
lean::inc(x_163);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_165 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 lean::cnstr_release(x_17, 2);
 x_165 = x_17;
}
if (lean::obj_tag(x_159) == 0)
{
obj* x_172; obj* x_173; obj* x_175; obj* x_176; obj* x_178; obj* x_179; obj* x_180; 
lean::dec(x_159);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_14);
x_172 = l_list_reverse___rarg(x_4);
x_173 = l_lean_parser_no__kind;
lean::inc(x_173);
x_175 = l_lean_parser_syntax_mk__node(x_173, x_172);
x_176 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_176);
if (lean::is_scalar(x_165)) {
 x_178 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_178 = x_165;
}
lean::cnstr_set(x_178, 0, x_175);
lean::cnstr_set(x_178, 1, x_161);
lean::cnstr_set(x_178, 2, x_176);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_178);
x_180 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_180, 0, x_179);
lean::cnstr_set(x_180, 1, x_18);
return x_180;
}
else
{
obj* x_181; obj* x_183; obj* x_184; obj* x_185; obj* x_191; obj* x_192; obj* x_194; obj* x_197; obj* x_198; 
x_181 = lean::cnstr_get(x_159, 0);
lean::inc(x_181);
if (lean::is_shared(x_159)) {
 lean::dec(x_159);
 x_183 = lean::box(0);
} else {
 lean::cnstr_release(x_159, 0);
 x_183 = x_159;
}
lean::inc(x_161);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_1);
x_191 = lean::apply_4(x_1, x_6, x_7, x_161, x_18);
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_191, 1);
lean::inc(x_194);
lean::dec(x_191);
x_197 = lean::box(0);
x_198 = l_lean_parser_parsec__t_try__mk__res___rarg(x_192);
if (lean::obj_tag(x_198) == 0)
{
obj* x_199; obj* x_201; obj* x_203; obj* x_205; obj* x_206; obj* x_207; obj* x_209; obj* x_210; 
x_199 = lean::cnstr_get(x_198, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_198, 1);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_198, 2);
lean::inc(x_203);
if (lean::is_shared(x_198)) {
 lean::dec(x_198);
 x_205 = lean::box(0);
} else {
 lean::cnstr_release(x_198, 0);
 lean::cnstr_release(x_198, 1);
 lean::cnstr_release(x_198, 2);
 x_205 = x_198;
}
if (lean::is_scalar(x_183)) {
 x_206 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_206 = x_183;
}
lean::cnstr_set(x_206, 0, x_199);
x_207 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_207);
if (lean::is_scalar(x_205)) {
 x_209 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_209 = x_205;
}
lean::cnstr_set(x_209, 0, x_206);
lean::cnstr_set(x_209, 1, x_201);
lean::cnstr_set(x_209, 2, x_207);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_209);
if (lean::obj_tag(x_210) == 0)
{
lean::dec(x_161);
lean::dec(x_197);
x_184 = x_210;
x_185 = x_194;
goto lbl_186;
}
else
{
obj* x_213; uint8 x_215; 
x_213 = lean::cnstr_get(x_210, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get_scalar<uint8>(x_210, sizeof(void*)*1);
if (x_215 == 0)
{
obj* x_217; obj* x_220; obj* x_222; obj* x_223; obj* x_224; 
lean::dec(x_210);
x_217 = lean::cnstr_get(x_213, 2);
lean::inc(x_217);
lean::dec(x_213);
x_220 = l_mjoin___rarg___closed__1;
lean::inc(x_220);
x_222 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_222, 0, x_217);
lean::closure_set(x_222, 1, x_220);
x_223 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_223, 0, x_222);
x_224 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_224, 0, x_197);
lean::cnstr_set(x_224, 1, x_161);
lean::cnstr_set(x_224, 2, x_223);
x_184 = x_224;
x_185 = x_194;
goto lbl_186;
}
else
{
lean::dec(x_213);
lean::dec(x_161);
lean::dec(x_197);
x_184 = x_210;
x_185 = x_194;
goto lbl_186;
}
}
}
else
{
obj* x_228; uint8 x_230; obj* x_231; 
x_228 = lean::cnstr_get(x_198, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get_scalar<uint8>(x_198, sizeof(void*)*1);
if (lean::is_shared(x_198)) {
 lean::dec(x_198);
 x_231 = lean::box(0);
} else {
 lean::cnstr_release(x_198, 0);
 x_231 = x_198;
}
if (x_230 == 0)
{
obj* x_233; obj* x_236; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_231);
x_233 = lean::cnstr_get(x_228, 2);
lean::inc(x_233);
lean::dec(x_228);
x_236 = l_mjoin___rarg___closed__1;
lean::inc(x_236);
x_238 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_238, 0, x_233);
lean::closure_set(x_238, 1, x_236);
if (lean::is_scalar(x_183)) {
 x_239 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_239 = x_183;
}
lean::cnstr_set(x_239, 0, x_238);
x_240 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_240, 0, x_197);
lean::cnstr_set(x_240, 1, x_161);
lean::cnstr_set(x_240, 2, x_239);
x_184 = x_240;
x_185 = x_194;
goto lbl_186;
}
else
{
obj* x_244; obj* x_245; 
lean::dec(x_183);
lean::dec(x_161);
lean::dec(x_197);
if (lean::is_scalar(x_231)) {
 x_244 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_244 = x_231;
}
lean::cnstr_set(x_244, 0, x_228);
lean::cnstr_set_scalar(x_244, sizeof(void*)*1, x_230);
x_245 = x_244;
x_184 = x_245;
x_185 = x_194;
goto lbl_186;
}
}
lbl_186:
{
if (lean::obj_tag(x_184) == 0)
{
obj* x_246; obj* x_248; obj* x_250; 
x_246 = lean::cnstr_get(x_184, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_184, 1);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_184, 2);
lean::inc(x_250);
lean::dec(x_184);
if (lean::obj_tag(x_246) == 0)
{
obj* x_259; obj* x_260; obj* x_261; obj* x_263; obj* x_264; obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
lean::dec(x_246);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_14);
x_259 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_259, 0, x_181);
lean::cnstr_set(x_259, 1, x_4);
x_260 = l_list_reverse___rarg(x_259);
x_261 = l_lean_parser_no__kind;
lean::inc(x_261);
x_263 = l_lean_parser_syntax_mk__node(x_261, x_260);
x_264 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_264);
if (lean::is_scalar(x_165)) {
 x_266 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_266 = x_165;
}
lean::cnstr_set(x_266, 0, x_263);
lean::cnstr_set(x_266, 1, x_248);
lean::cnstr_set(x_266, 2, x_264);
x_267 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_250, x_266);
x_268 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_267);
x_269 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_185);
return x_269;
}
else
{
obj* x_271; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_279; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_165);
x_271 = lean::cnstr_get(x_246, 0);
lean::inc(x_271);
lean::dec(x_246);
x_274 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_274, 0, x_181);
lean::cnstr_set(x_274, 1, x_4);
x_275 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_275, 0, x_271);
lean::cnstr_set(x_275, 1, x_274);
x_276 = l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2(x_0, x_1, x_2, x_2, x_275, x_14, x_6, x_7, x_248, x_185);
x_277 = lean::cnstr_get(x_276, 0);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_276, 1);
lean::inc(x_279);
if (lean::is_shared(x_276)) {
 lean::dec(x_276);
 x_281 = lean::box(0);
} else {
 lean::cnstr_release(x_276, 0);
 lean::cnstr_release(x_276, 1);
 x_281 = x_276;
}
x_282 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_250, x_277);
x_283 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_282);
if (lean::is_scalar(x_281)) {
 x_284 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_284 = x_281;
}
lean::cnstr_set(x_284, 0, x_283);
lean::cnstr_set(x_284, 1, x_279);
return x_284;
}
}
else
{
obj* x_293; uint8 x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
lean::dec(x_181);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_14);
lean::dec(x_165);
x_293 = lean::cnstr_get(x_184, 0);
lean::inc(x_293);
x_295 = lean::cnstr_get_scalar<uint8>(x_184, sizeof(void*)*1);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_296 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_296 = x_184;
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_293);
lean::cnstr_set_scalar(x_297, sizeof(void*)*1, x_295);
x_298 = x_297;
x_299 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_163, x_298);
x_300 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_185);
return x_300;
}
}
}
}
else
{
obj* x_307; uint8 x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_14);
x_307 = lean::cnstr_get(x_17, 0);
lean::inc(x_307);
x_309 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_310 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_310 = x_17;
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_307);
lean::cnstr_set_scalar(x_311, sizeof(void*)*1, x_309);
x_312 = x_311;
x_313 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_313, 0, x_312);
lean::cnstr_set(x_313, 1, x_18);
return x_313;
}
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
x_17 = x_20;
x_18 = x_21;
goto lbl_19;
}
else
{
obj* x_314; uint8 x_316; obj* x_317; obj* x_318; obj* x_320; obj* x_322; obj* x_324; obj* x_327; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_335; obj* x_336; obj* x_337; 
x_314 = lean::cnstr_get(x_20, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_317 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_317 = x_20;
}
x_318 = lean::cnstr_get(x_314, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_314, 1);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_314, 2);
lean::inc(x_322);
x_324 = lean::cnstr_get(x_314, 3);
lean::inc(x_324);
lean::dec(x_314);
x_327 = l_option_get___main___at_lean_parser_run___spec__2(x_324);
lean::inc(x_4);
x_329 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_329, 0, x_327);
lean::cnstr_set(x_329, 1, x_4);
x_330 = lean::box(3);
x_331 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_329);
x_332 = l_list_reverse___rarg(x_331);
x_333 = l_lean_parser_no__kind;
lean::inc(x_333);
x_335 = l_lean_parser_syntax_mk__node(x_333, x_332);
x_336 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_336, 0, x_335);
x_337 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_337, 0, x_318);
lean::cnstr_set(x_337, 1, x_320);
lean::cnstr_set(x_337, 2, x_322);
lean::cnstr_set(x_337, 3, x_336);
if (x_316 == 0)
{
uint8 x_338; obj* x_339; obj* x_340; 
x_338 = 0;
if (lean::is_scalar(x_317)) {
 x_339 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_339 = x_317;
}
lean::cnstr_set(x_339, 0, x_337);
lean::cnstr_set_scalar(x_339, sizeof(void*)*1, x_338);
x_340 = x_339;
x_17 = x_340;
x_18 = x_21;
goto lbl_19;
}
else
{
obj* x_341; obj* x_342; 
if (lean::is_scalar(x_317)) {
 x_341 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_341 = x_317;
}
lean::cnstr_set(x_341, 0, x_337);
lean::cnstr_set_scalar(x_341, sizeof(void*)*1, x_316);
x_342 = x_341;
x_17 = x_342;
x_18 = x_21;
goto lbl_19;
}
}
}
}
else
{
obj* x_347; obj* x_348; obj* x_349; obj* x_353; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
x_347 = lean::box(0);
x_348 = l___private_1386096941__many1__aux___main___rarg___closed__1;
x_349 = l_mjoin___rarg___closed__1;
lean::inc(x_347);
lean::inc(x_349);
lean::inc(x_348);
x_353 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_348, x_349, x_347, x_347, x_6, x_7, x_8, x_9);
return x_353;
}
}
}
obj* l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
x_7 = lean::string_iterator_remaining(x_5);
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_7, x_9);
lean::dec(x_9);
lean::dec(x_7);
x_13 = 0;
x_14 = l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2(x_0, x_1, x_2, x_13, x_8, x_10, x_3, x_4, x_5, x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
x_20 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_15);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_17);
return x_23;
}
}
obj* _init_l_lean_parser_command_decl__attributes_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_38; 
x_0 = lean::mk_string("@[");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string(",");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_parser), 4, 0);
x_14 = 1;
x_15 = lean::box(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_12);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::mk_string("]");
x_18 = l_string_trim(x_17);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_4);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_6);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_lean_parser_command__parser__m_monad___closed__1;
x_27 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_28 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_29 = l_lean_parser_command__parser__m_alternative___closed__1;
x_30 = l_lean_parser_command_decl__attributes;
x_31 = l_lean_parser_command_decl__attributes_has__view;
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
x_38 = l_lean_parser_combinators_node_view___rarg(x_26, x_27, x_28, x_29, x_30, x_25, x_31);
return x_38;
}
}
obj* l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; obj* x_12; 
x_10 = lean::unbox(x_2);
x_11 = lean::unbox(x_3);
x_12 = l___private_1209639495__sep__by__aux___main___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__2(x_0, x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
obj* l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
x_8 = l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1(x_0, x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::mk_string("@[");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::mk_string(",");
lean::inc(x_1);
x_6 = l_lean_parser_symbol_tokens___rarg(x_4, x_1);
x_7 = l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens;
lean::inc(x_7);
x_9 = l_lean_parser_combinators_sep__by1_tokens___rarg(x_7, x_6);
x_10 = lean::mk_string("]");
x_11 = l_lean_parser_symbol_tokens___rarg(x_10, x_1);
x_12 = lean::box(0);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_11, x_12);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_9, x_13);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_3, x_14);
x_16 = l_lean_parser_tokens___rarg(x_15);
return x_16;
}
}
obj* l_lean_parser_command_decl__attributes_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_decl__attributes;
x_5 = l_lean_parser_command_decl__attributes_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__attributes_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::mk_string("@[");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string(",");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_attr__instance_parser), 4, 0);
x_14 = 1;
x_15 = lean::box(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1___boxed), 7, 3);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_12);
lean::closure_set(x_16, 2, x_15);
x_17 = lean::mk_string("]");
x_18 = l_string_trim(x_17);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_4);
lean::closure_set(x_21, 2, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_6);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* _init_l_lean_parser_command_visibility() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("visibility");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_visibility_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_visibility_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_visibility_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__4;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
lean::dec(x_2);
if (x_84 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
lean::dec(x_1);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
case 1:
{
obj* x_93; 
lean::dec(x_1);
x_93 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
lean::inc(x_93);
return x_93;
}
case 2:
{
obj* x_96; 
lean::dec(x_1);
x_96 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
return x_96;
}
default:
{
obj* x_99; 
lean::dec(x_1);
x_99 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
return x_99;
}
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_101; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_1, 0);
lean::inc(x_101);
lean::dec(x_1);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_101);
x_105 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
case 1:
{
obj* x_107; 
lean::dec(x_1);
x_107 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
lean::inc(x_107);
return x_107;
}
case 2:
{
obj* x_110; 
lean::dec(x_1);
x_110 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
lean::inc(x_110);
return x_110;
}
default:
{
obj* x_113; 
lean::dec(x_1);
x_113 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
lean::inc(x_113);
return x_113;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_9; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
case 1:
{
obj* x_15; 
lean::dec(x_0);
x_15 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
lean::inc(x_15);
return x_15;
}
case 2:
{
obj* x_18; 
lean::dec(x_0);
x_18 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
return x_18;
}
default:
{
obj* x_21; 
lean::dec(x_0);
x_21 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
case 1:
{
obj* x_29; 
lean::dec(x_0);
x_29 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
lean::inc(x_29);
return x_29;
}
case 2:
{
obj* x_32; 
lean::dec(x_0);
x_32 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
lean::inc(x_32);
return x_32;
}
default:
{
obj* x_35; 
lean::dec(x_0);
x_35 = l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2;
lean::inc(x_35);
return x_35;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("visibility");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_visibility_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_5);
x_7 = l_option_map___rarg(x_5, x_2);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_1);
x_12 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = l_lean_parser_command_visibility;
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mk__node(x_16, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_22);
x_24 = l_option_map___rarg(x_22, x_19);
x_25 = lean::box(3);
x_26 = l_option_get__or__else___main___rarg(x_24, x_25);
lean::inc(x_1);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_command_visibility;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
}
}
obj* _init_l_lean_parser_command_visibility_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_visibility_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_decl__modifiers() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("decl_modifiers");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__modifiers_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__4;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_22; 
x_22 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; 
lean::dec(x_22);
x_24 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3;
lean::inc(x_24);
x_20 = x_24;
goto lbl_21;
}
else
{
obj* x_26; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_28 = x_22;
}
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_34; 
lean::dec(x_28);
lean::dec(x_29);
x_34 = lean::box(0);
x_20 = x_34;
goto lbl_21;
}
else
{
obj* x_35; obj* x_37; 
x_35 = lean::cnstr_get(x_29, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_29, 1);
lean::inc(x_37);
lean::dec(x_29);
if (lean::obj_tag(x_37) == 0)
{
obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_37);
x_41 = l_lean_parser_command_doc__comment_has__view;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::apply_1(x_42, x_35);
if (lean::is_scalar(x_28)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_28;
}
lean::cnstr_set(x_45, 0, x_44);
x_20 = x_45;
goto lbl_21;
}
else
{
obj* x_49; 
lean::dec(x_28);
lean::dec(x_35);
lean::dec(x_37);
x_49 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3;
lean::inc(x_49);
x_20 = x_49;
goto lbl_21;
}
}
}
lbl_21:
{
obj* x_51; obj* x_52; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_54; 
x_54 = lean::box(3);
x_51 = x_1;
x_52 = x_54;
goto lbl_53;
}
else
{
obj* x_55; obj* x_57; 
x_55 = lean::cnstr_get(x_1, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_1, 1);
lean::inc(x_57);
lean::dec(x_1);
x_51 = x_57;
x_52 = x_55;
goto lbl_53;
}
lbl_53:
{
obj* x_60; obj* x_62; 
x_62 = l_lean_parser_syntax_as__node___main(x_52);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; 
lean::dec(x_62);
x_64 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2;
lean::inc(x_64);
x_60 = x_64;
goto lbl_61;
}
else
{
obj* x_66; obj* x_68; obj* x_69; 
x_66 = lean::cnstr_get(x_62, 0);
lean::inc(x_66);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_68 = x_62;
}
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
if (lean::obj_tag(x_69) == 0)
{
obj* x_74; 
lean::dec(x_68);
lean::dec(x_69);
x_74 = lean::box(0);
x_60 = x_74;
goto lbl_61;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_69, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_69, 1);
lean::inc(x_77);
lean::dec(x_69);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_77);
x_81 = l_lean_parser_command_decl__attributes_has__view;
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::apply_1(x_82, x_75);
if (lean::is_scalar(x_68)) {
 x_85 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_85 = x_68;
}
lean::cnstr_set(x_85, 0, x_84);
x_60 = x_85;
goto lbl_61;
}
else
{
obj* x_89; 
lean::dec(x_68);
lean::dec(x_75);
lean::dec(x_77);
x_89 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2;
lean::inc(x_89);
x_60 = x_89;
goto lbl_61;
}
}
}
lbl_61:
{
obj* x_91; obj* x_92; 
if (lean::obj_tag(x_51) == 0)
{
obj* x_94; 
x_94 = lean::box(3);
x_91 = x_51;
x_92 = x_94;
goto lbl_93;
}
else
{
obj* x_95; obj* x_97; 
x_95 = lean::cnstr_get(x_51, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_51, 1);
lean::inc(x_97);
lean::dec(x_51);
x_91 = x_97;
x_92 = x_95;
goto lbl_93;
}
lbl_93:
{
obj* x_100; obj* x_102; 
x_102 = l_lean_parser_syntax_as__node___main(x_92);
if (lean::obj_tag(x_102) == 0)
{
obj* x_104; 
lean::dec(x_102);
x_104 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1;
lean::inc(x_104);
x_100 = x_104;
goto lbl_101;
}
else
{
obj* x_106; obj* x_108; obj* x_109; 
x_106 = lean::cnstr_get(x_102, 0);
lean::inc(x_106);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 x_108 = x_102;
}
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
if (lean::obj_tag(x_109) == 0)
{
obj* x_114; 
lean::dec(x_108);
lean::dec(x_109);
x_114 = lean::box(0);
x_100 = x_114;
goto lbl_101;
}
else
{
obj* x_115; obj* x_117; 
x_115 = lean::cnstr_get(x_109, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_109, 1);
lean::inc(x_117);
lean::dec(x_109);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_117);
x_121 = l_lean_parser_command_visibility_has__view;
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::apply_1(x_122, x_115);
if (lean::is_scalar(x_108)) {
 x_125 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_125 = x_108;
}
lean::cnstr_set(x_125, 0, x_124);
x_100 = x_125;
goto lbl_101;
}
else
{
obj* x_129; 
lean::dec(x_117);
lean::dec(x_115);
lean::dec(x_108);
x_129 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1;
lean::inc(x_129);
x_100 = x_129;
goto lbl_101;
}
}
}
lbl_101:
{
obj* x_131; obj* x_132; 
if (lean::obj_tag(x_91) == 0)
{
obj* x_134; 
x_134 = lean::box(3);
x_131 = x_91;
x_132 = x_134;
goto lbl_133;
}
else
{
obj* x_135; obj* x_137; 
x_135 = lean::cnstr_get(x_91, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_91, 1);
lean::inc(x_137);
lean::dec(x_91);
x_131 = x_137;
x_132 = x_135;
goto lbl_133;
}
lbl_133:
{
obj* x_140; obj* x_142; 
x_142 = l_lean_parser_syntax_as__node___main(x_132);
if (lean::obj_tag(x_142) == 0)
{
obj* x_144; 
lean::dec(x_142);
x_144 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_144);
x_140 = x_144;
goto lbl_141;
}
else
{
obj* x_146; obj* x_148; obj* x_149; 
x_146 = lean::cnstr_get(x_142, 0);
lean::inc(x_146);
if (lean::is_shared(x_142)) {
 lean::dec(x_142);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_142, 0);
 x_148 = x_142;
}
x_149 = lean::cnstr_get(x_146, 1);
lean::inc(x_149);
lean::dec(x_146);
if (lean::obj_tag(x_149) == 0)
{
obj* x_154; 
lean::dec(x_148);
lean::dec(x_149);
x_154 = lean::box(0);
x_140 = x_154;
goto lbl_141;
}
else
{
obj* x_155; obj* x_157; 
x_155 = lean::cnstr_get(x_149, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_149, 1);
lean::inc(x_157);
lean::dec(x_149);
if (lean::obj_tag(x_157) == 0)
{
lean::dec(x_157);
switch (lean::obj_tag(x_155)) {
case 0:
{
obj* x_161; obj* x_164; obj* x_165; 
x_161 = lean::cnstr_get(x_155, 0);
lean::inc(x_161);
lean::dec(x_155);
if (lean::is_scalar(x_148)) {
 x_164 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_164 = x_148;
}
lean::cnstr_set(x_164, 0, x_161);
x_165 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_165, 0, x_164);
x_140 = x_165;
goto lbl_141;
}
case 1:
{
obj* x_168; 
lean::dec(x_148);
lean::dec(x_155);
x_168 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_168);
x_140 = x_168;
goto lbl_141;
}
case 2:
{
obj* x_172; 
lean::dec(x_148);
lean::dec(x_155);
x_172 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_172);
x_140 = x_172;
goto lbl_141;
}
default:
{
obj* x_176; 
lean::dec(x_148);
lean::dec(x_155);
x_176 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_176);
x_140 = x_176;
goto lbl_141;
}
}
}
else
{
obj* x_181; 
lean::dec(x_148);
lean::dec(x_155);
lean::dec(x_157);
x_181 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_181);
x_140 = x_181;
goto lbl_141;
}
}
}
lbl_141:
{
obj* x_183; 
if (lean::obj_tag(x_131) == 0)
{
obj* x_186; 
lean::dec(x_131);
x_186 = lean::box(3);
x_183 = x_186;
goto lbl_184;
}
else
{
obj* x_187; 
x_187 = lean::cnstr_get(x_131, 0);
lean::inc(x_187);
lean::dec(x_131);
x_183 = x_187;
goto lbl_184;
}
lbl_184:
{
obj* x_190; 
x_190 = l_lean_parser_syntax_as__node___main(x_183);
if (lean::obj_tag(x_190) == 0)
{
obj* x_192; obj* x_194; 
lean::dec(x_190);
x_192 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_192);
x_194 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_194, 0, x_20);
lean::cnstr_set(x_194, 1, x_60);
lean::cnstr_set(x_194, 2, x_100);
lean::cnstr_set(x_194, 3, x_140);
lean::cnstr_set(x_194, 4, x_192);
return x_194;
}
else
{
obj* x_195; obj* x_197; obj* x_198; 
x_195 = lean::cnstr_get(x_190, 0);
lean::inc(x_195);
if (lean::is_shared(x_190)) {
 lean::dec(x_190);
 x_197 = lean::box(0);
} else {
 lean::cnstr_release(x_190, 0);
 x_197 = x_190;
}
x_198 = lean::cnstr_get(x_195, 1);
lean::inc(x_198);
lean::dec(x_195);
if (lean::obj_tag(x_198) == 0)
{
obj* x_203; obj* x_204; 
lean::dec(x_197);
lean::dec(x_198);
x_203 = lean::box(0);
x_204 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_204, 0, x_20);
lean::cnstr_set(x_204, 1, x_60);
lean::cnstr_set(x_204, 2, x_100);
lean::cnstr_set(x_204, 3, x_140);
lean::cnstr_set(x_204, 4, x_203);
return x_204;
}
else
{
obj* x_205; obj* x_207; 
x_205 = lean::cnstr_get(x_198, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_198, 1);
lean::inc(x_207);
lean::dec(x_198);
if (lean::obj_tag(x_207) == 0)
{
lean::dec(x_207);
switch (lean::obj_tag(x_205)) {
case 0:
{
obj* x_211; obj* x_214; obj* x_215; obj* x_216; 
x_211 = lean::cnstr_get(x_205, 0);
lean::inc(x_211);
lean::dec(x_205);
if (lean::is_scalar(x_197)) {
 x_214 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_214 = x_197;
}
lean::cnstr_set(x_214, 0, x_211);
x_215 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_215, 0, x_214);
x_216 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_216, 0, x_20);
lean::cnstr_set(x_216, 1, x_60);
lean::cnstr_set(x_216, 2, x_100);
lean::cnstr_set(x_216, 3, x_140);
lean::cnstr_set(x_216, 4, x_215);
return x_216;
}
case 1:
{
obj* x_219; obj* x_221; 
lean::dec(x_197);
lean::dec(x_205);
x_219 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_219);
x_221 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_221, 0, x_20);
lean::cnstr_set(x_221, 1, x_60);
lean::cnstr_set(x_221, 2, x_100);
lean::cnstr_set(x_221, 3, x_140);
lean::cnstr_set(x_221, 4, x_219);
return x_221;
}
case 2:
{
obj* x_224; obj* x_226; 
lean::dec(x_197);
lean::dec(x_205);
x_224 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_224);
x_226 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_226, 0, x_20);
lean::cnstr_set(x_226, 1, x_60);
lean::cnstr_set(x_226, 2, x_100);
lean::cnstr_set(x_226, 3, x_140);
lean::cnstr_set(x_226, 4, x_224);
return x_226;
}
default:
{
obj* x_229; obj* x_231; 
lean::dec(x_197);
lean::dec(x_205);
x_229 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_229);
x_231 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_231, 0, x_20);
lean::cnstr_set(x_231, 1, x_60);
lean::cnstr_set(x_231, 2, x_100);
lean::cnstr_set(x_231, 3, x_140);
lean::cnstr_set(x_231, 4, x_229);
return x_231;
}
}
}
else
{
obj* x_235; obj* x_237; 
lean::dec(x_197);
lean::dec(x_205);
lean::dec(x_207);
x_235 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_235);
x_237 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_237, 0, x_20);
lean::cnstr_set(x_237, 1, x_60);
lean::cnstr_set(x_237, 2, x_100);
lean::cnstr_set(x_237, 3, x_140);
lean::cnstr_set(x_237, 4, x_235);
return x_237;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_visibility_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_decl__attributes_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_doc__comment_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_7; 
x_7 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3;
lean::inc(x_9);
x_5 = x_9;
goto lbl_6;
}
else
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_13 = x_7;
}
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; 
lean::dec(x_14);
lean::dec(x_13);
x_19 = lean::box(0);
x_5 = x_19;
goto lbl_6;
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_14, 1);
lean::inc(x_22);
lean::dec(x_14);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_22);
x_26 = l_lean_parser_command_doc__comment_has__view;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_20);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
x_5 = x_30;
goto lbl_6;
}
else
{
obj* x_34; 
lean::dec(x_22);
lean::dec(x_13);
lean::dec(x_20);
x_34 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3;
lean::inc(x_34);
x_5 = x_34;
goto lbl_6;
}
}
}
lbl_6:
{
obj* x_36; obj* x_37; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_39; 
x_39 = lean::box(3);
x_36 = x_0;
x_37 = x_39;
goto lbl_38;
}
else
{
obj* x_40; obj* x_42; 
x_40 = lean::cnstr_get(x_0, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_0, 1);
lean::inc(x_42);
lean::dec(x_0);
x_36 = x_42;
x_37 = x_40;
goto lbl_38;
}
lbl_38:
{
obj* x_45; obj* x_47; 
x_47 = l_lean_parser_syntax_as__node___main(x_37);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; 
lean::dec(x_47);
x_49 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2;
lean::inc(x_49);
x_45 = x_49;
goto lbl_46;
}
else
{
obj* x_51; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_47, 0);
lean::inc(x_51);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_53 = x_47;
}
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_59; 
lean::dec(x_53);
lean::dec(x_54);
x_59 = lean::box(0);
x_45 = x_59;
goto lbl_46;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_54, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_54, 1);
lean::inc(x_62);
lean::dec(x_54);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_62);
x_66 = l_lean_parser_command_decl__attributes_has__view;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::apply_1(x_67, x_60);
if (lean::is_scalar(x_53)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_53;
}
lean::cnstr_set(x_70, 0, x_69);
x_45 = x_70;
goto lbl_46;
}
else
{
obj* x_74; 
lean::dec(x_62);
lean::dec(x_53);
lean::dec(x_60);
x_74 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2;
lean::inc(x_74);
x_45 = x_74;
goto lbl_46;
}
}
}
lbl_46:
{
obj* x_76; obj* x_77; 
if (lean::obj_tag(x_36) == 0)
{
obj* x_79; 
x_79 = lean::box(3);
x_76 = x_36;
x_77 = x_79;
goto lbl_78;
}
else
{
obj* x_80; obj* x_82; 
x_80 = lean::cnstr_get(x_36, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_36, 1);
lean::inc(x_82);
lean::dec(x_36);
x_76 = x_82;
x_77 = x_80;
goto lbl_78;
}
lbl_78:
{
obj* x_85; obj* x_87; 
x_87 = l_lean_parser_syntax_as__node___main(x_77);
if (lean::obj_tag(x_87) == 0)
{
obj* x_89; 
lean::dec(x_87);
x_89 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1;
lean::inc(x_89);
x_85 = x_89;
goto lbl_86;
}
else
{
obj* x_91; obj* x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_87, 0);
lean::inc(x_91);
if (lean::is_shared(x_87)) {
 lean::dec(x_87);
 x_93 = lean::box(0);
} else {
 lean::cnstr_release(x_87, 0);
 x_93 = x_87;
}
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_94) == 0)
{
obj* x_99; 
lean::dec(x_93);
lean::dec(x_94);
x_99 = lean::box(0);
x_85 = x_99;
goto lbl_86;
}
else
{
obj* x_100; obj* x_102; 
x_100 = lean::cnstr_get(x_94, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_94, 1);
lean::inc(x_102);
lean::dec(x_94);
if (lean::obj_tag(x_102) == 0)
{
obj* x_106; obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_102);
x_106 = l_lean_parser_command_visibility_has__view;
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::apply_1(x_107, x_100);
if (lean::is_scalar(x_93)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_93;
}
lean::cnstr_set(x_110, 0, x_109);
x_85 = x_110;
goto lbl_86;
}
else
{
obj* x_114; 
lean::dec(x_100);
lean::dec(x_93);
lean::dec(x_102);
x_114 = l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1;
lean::inc(x_114);
x_85 = x_114;
goto lbl_86;
}
}
}
lbl_86:
{
obj* x_116; obj* x_117; 
if (lean::obj_tag(x_76) == 0)
{
obj* x_119; 
x_119 = lean::box(3);
x_116 = x_76;
x_117 = x_119;
goto lbl_118;
}
else
{
obj* x_120; obj* x_122; 
x_120 = lean::cnstr_get(x_76, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_76, 1);
lean::inc(x_122);
lean::dec(x_76);
x_116 = x_122;
x_117 = x_120;
goto lbl_118;
}
lbl_118:
{
obj* x_125; obj* x_127; 
x_127 = l_lean_parser_syntax_as__node___main(x_117);
if (lean::obj_tag(x_127) == 0)
{
obj* x_129; 
lean::dec(x_127);
x_129 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_129);
x_125 = x_129;
goto lbl_126;
}
else
{
obj* x_131; obj* x_133; obj* x_134; 
x_131 = lean::cnstr_get(x_127, 0);
lean::inc(x_131);
if (lean::is_shared(x_127)) {
 lean::dec(x_127);
 x_133 = lean::box(0);
} else {
 lean::cnstr_release(x_127, 0);
 x_133 = x_127;
}
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
lean::dec(x_131);
if (lean::obj_tag(x_134) == 0)
{
obj* x_139; 
lean::dec(x_134);
lean::dec(x_133);
x_139 = lean::box(0);
x_125 = x_139;
goto lbl_126;
}
else
{
obj* x_140; obj* x_142; 
x_140 = lean::cnstr_get(x_134, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_134, 1);
lean::inc(x_142);
lean::dec(x_134);
if (lean::obj_tag(x_142) == 0)
{
lean::dec(x_142);
switch (lean::obj_tag(x_140)) {
case 0:
{
obj* x_146; obj* x_149; obj* x_150; 
x_146 = lean::cnstr_get(x_140, 0);
lean::inc(x_146);
lean::dec(x_140);
if (lean::is_scalar(x_133)) {
 x_149 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_149 = x_133;
}
lean::cnstr_set(x_149, 0, x_146);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_149);
x_125 = x_150;
goto lbl_126;
}
case 1:
{
obj* x_153; 
lean::dec(x_140);
lean::dec(x_133);
x_153 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_153);
x_125 = x_153;
goto lbl_126;
}
case 2:
{
obj* x_157; 
lean::dec(x_140);
lean::dec(x_133);
x_157 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_157);
x_125 = x_157;
goto lbl_126;
}
default:
{
obj* x_161; 
lean::dec(x_140);
lean::dec(x_133);
x_161 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_161);
x_125 = x_161;
goto lbl_126;
}
}
}
else
{
obj* x_166; 
lean::dec(x_140);
lean::dec(x_142);
lean::dec(x_133);
x_166 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_166);
x_125 = x_166;
goto lbl_126;
}
}
}
lbl_126:
{
obj* x_168; 
if (lean::obj_tag(x_116) == 0)
{
obj* x_171; 
lean::dec(x_116);
x_171 = lean::box(3);
x_168 = x_171;
goto lbl_169;
}
else
{
obj* x_172; 
x_172 = lean::cnstr_get(x_116, 0);
lean::inc(x_172);
lean::dec(x_116);
x_168 = x_172;
goto lbl_169;
}
lbl_169:
{
obj* x_175; 
x_175 = l_lean_parser_syntax_as__node___main(x_168);
if (lean::obj_tag(x_175) == 0)
{
obj* x_177; obj* x_179; 
lean::dec(x_175);
x_177 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_177);
x_179 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_179, 0, x_5);
lean::cnstr_set(x_179, 1, x_45);
lean::cnstr_set(x_179, 2, x_85);
lean::cnstr_set(x_179, 3, x_125);
lean::cnstr_set(x_179, 4, x_177);
return x_179;
}
else
{
obj* x_180; obj* x_182; obj* x_183; 
x_180 = lean::cnstr_get(x_175, 0);
lean::inc(x_180);
if (lean::is_shared(x_175)) {
 lean::dec(x_175);
 x_182 = lean::box(0);
} else {
 lean::cnstr_release(x_175, 0);
 x_182 = x_175;
}
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
lean::dec(x_180);
if (lean::obj_tag(x_183) == 0)
{
obj* x_188; obj* x_189; 
lean::dec(x_182);
lean::dec(x_183);
x_188 = lean::box(0);
x_189 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_189, 0, x_5);
lean::cnstr_set(x_189, 1, x_45);
lean::cnstr_set(x_189, 2, x_85);
lean::cnstr_set(x_189, 3, x_125);
lean::cnstr_set(x_189, 4, x_188);
return x_189;
}
else
{
obj* x_190; obj* x_192; 
x_190 = lean::cnstr_get(x_183, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_183, 1);
lean::inc(x_192);
lean::dec(x_183);
if (lean::obj_tag(x_192) == 0)
{
lean::dec(x_192);
switch (lean::obj_tag(x_190)) {
case 0:
{
obj* x_196; obj* x_199; obj* x_200; obj* x_201; 
x_196 = lean::cnstr_get(x_190, 0);
lean::inc(x_196);
lean::dec(x_190);
if (lean::is_scalar(x_182)) {
 x_199 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_199 = x_182;
}
lean::cnstr_set(x_199, 0, x_196);
x_200 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_200, 0, x_199);
x_201 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_201, 0, x_5);
lean::cnstr_set(x_201, 1, x_45);
lean::cnstr_set(x_201, 2, x_85);
lean::cnstr_set(x_201, 3, x_125);
lean::cnstr_set(x_201, 4, x_200);
return x_201;
}
case 1:
{
obj* x_204; obj* x_206; 
lean::dec(x_182);
lean::dec(x_190);
x_204 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_204);
x_206 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_206, 0, x_5);
lean::cnstr_set(x_206, 1, x_45);
lean::cnstr_set(x_206, 2, x_85);
lean::cnstr_set(x_206, 3, x_125);
lean::cnstr_set(x_206, 4, x_204);
return x_206;
}
case 2:
{
obj* x_209; obj* x_211; 
lean::dec(x_182);
lean::dec(x_190);
x_209 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_209);
x_211 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_211, 0, x_5);
lean::cnstr_set(x_211, 1, x_45);
lean::cnstr_set(x_211, 2, x_85);
lean::cnstr_set(x_211, 3, x_125);
lean::cnstr_set(x_211, 4, x_209);
return x_211;
}
default:
{
obj* x_214; obj* x_216; 
lean::dec(x_182);
lean::dec(x_190);
x_214 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_214);
x_216 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_216, 0, x_5);
lean::cnstr_set(x_216, 1, x_45);
lean::cnstr_set(x_216, 2, x_85);
lean::cnstr_set(x_216, 3, x_125);
lean::cnstr_set(x_216, 4, x_214);
return x_216;
}
}
}
else
{
obj* x_220; obj* x_222; 
lean::dec(x_192);
lean::dec(x_182);
lean::dec(x_190);
x_220 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_220);
x_222 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_222, 0, x_5);
lean::cnstr_set(x_222, 1, x_45);
lean::cnstr_set(x_222, 2, x_85);
lean::cnstr_set(x_222, 3, x_125);
lean::cnstr_set(x_222, 4, x_220);
return x_222;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_16; 
lean::dec(x_1);
x_16 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_16);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = l_lean_parser_command_doc__comment_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_12);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_12);
x_27 = l_lean_parser_no__kind;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_13 = x_29;
goto lbl_14;
}
lbl_14:
{
obj* x_30; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_33; 
lean::dec(x_3);
x_33 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_33);
x_30 = x_33;
goto lbl_31;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_46; 
x_35 = lean::cnstr_get(x_3, 0);
lean::inc(x_35);
lean::dec(x_3);
x_38 = l_lean_parser_command_decl__attributes_has__view;
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
x_41 = lean::apply_1(x_39, x_35);
lean::inc(x_12);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_12);
x_44 = l_lean_parser_no__kind;
lean::inc(x_44);
x_46 = l_lean_parser_syntax_mk__node(x_44, x_43);
x_30 = x_46;
goto lbl_31;
}
lbl_31:
{
obj* x_47; obj* x_49; obj* x_50; 
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
obj* x_54; 
lean::dec(x_7);
x_54 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_54);
x_47 = x_54;
goto lbl_48;
}
else
{
obj* x_56; obj* x_59; 
x_56 = lean::cnstr_get(x_7, 0);
lean::inc(x_56);
lean::dec(x_7);
x_59 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_59);
x_49 = x_59;
x_50 = x_56;
goto lbl_51;
}
}
else
{
obj* x_61; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
x_61 = lean::cnstr_get(x_5, 0);
lean::inc(x_61);
lean::dec(x_5);
x_64 = l_lean_parser_command_visibility_has__view;
x_65 = lean::cnstr_get(x_64, 1);
lean::inc(x_65);
x_67 = lean::apply_1(x_65, x_61);
lean::inc(x_12);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_12);
x_70 = l_lean_parser_no__kind;
lean::inc(x_70);
x_72 = l_lean_parser_syntax_mk__node(x_70, x_69);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_7);
x_47 = x_72;
goto lbl_48;
}
else
{
obj* x_74; 
x_74 = lean::cnstr_get(x_7, 0);
lean::inc(x_74);
lean::dec(x_7);
x_49 = x_72;
x_50 = x_74;
goto lbl_51;
}
}
lbl_48:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; 
lean::dec(x_9);
lean::dec(x_12);
x_79 = l_lean_parser_term_binder__content_has__view_x_27___lambda__2___closed__2;
lean::inc(x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_47);
lean::cnstr_set(x_81, 1, x_79);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_30);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_13);
lean::cnstr_set(x_83, 1, x_82);
x_84 = l_lean_parser_command_decl__modifiers;
lean::inc(x_84);
x_86 = l_lean_parser_syntax_mk__node(x_84, x_83);
return x_86;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_109; 
x_87 = lean::cnstr_get(x_9, 0);
lean::inc(x_87);
lean::dec(x_9);
x_90 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_90);
x_92 = l_option_map___rarg(x_90, x_87);
x_93 = lean::box(3);
x_94 = l_option_get__or__else___main___rarg(x_92, x_93);
lean::inc(x_12);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_12);
x_97 = l_lean_parser_no__kind;
lean::inc(x_97);
x_99 = l_lean_parser_syntax_mk__node(x_97, x_96);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_12);
x_101 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_101);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_101);
lean::cnstr_set(x_103, 1, x_100);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_47);
lean::cnstr_set(x_104, 1, x_103);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_30);
lean::cnstr_set(x_105, 1, x_104);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_13);
lean::cnstr_set(x_106, 1, x_105);
x_107 = l_lean_parser_command_decl__modifiers;
lean::inc(x_107);
x_109 = l_lean_parser_syntax_mk__node(x_107, x_106);
return x_109;
}
}
lbl_51:
{
obj* x_110; obj* x_112; obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_120; 
x_110 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_110);
x_112 = l_option_map___rarg(x_110, x_50);
x_113 = lean::box(3);
lean::inc(x_113);
x_115 = l_option_get__or__else___main___rarg(x_112, x_113);
lean::inc(x_12);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set(x_117, 1, x_12);
x_118 = l_lean_parser_no__kind;
lean::inc(x_118);
x_120 = l_lean_parser_syntax_mk__node(x_118, x_117);
if (lean::obj_tag(x_9) == 0)
{
obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_132; 
lean::dec(x_9);
lean::dec(x_12);
lean::dec(x_113);
x_124 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_124);
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_120);
lean::cnstr_set(x_126, 1, x_124);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_49);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_30);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_13);
lean::cnstr_set(x_129, 1, x_128);
x_130 = l_lean_parser_command_decl__modifiers;
lean::inc(x_130);
x_132 = l_lean_parser_syntax_mk__node(x_130, x_129);
return x_132;
}
else
{
obj* x_133; obj* x_137; obj* x_138; obj* x_140; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_150; 
x_133 = lean::cnstr_get(x_9, 0);
lean::inc(x_133);
lean::dec(x_9);
lean::inc(x_110);
x_137 = l_option_map___rarg(x_110, x_133);
x_138 = l_option_get__or__else___main___rarg(x_137, x_113);
lean::inc(x_12);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_12);
lean::inc(x_118);
x_142 = l_lean_parser_syntax_mk__node(x_118, x_140);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_12);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_120);
lean::cnstr_set(x_144, 1, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_49);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_30);
lean::cnstr_set(x_146, 1, x_145);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_13);
lean::cnstr_set(x_147, 1, x_146);
x_148 = l_lean_parser_command_decl__modifiers;
lean::inc(x_148);
x_150 = l_lean_parser_syntax_mk__node(x_148, x_147);
return x_150;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_decl__modifiers_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_decl__modifiers_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_16; 
x_8 = lean::box(0);
lean::inc(x_3);
x_13 = lean::apply_4(x_0, x_1, x_2, x_3, x_4);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 2);
lean::inc(x_23);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_25 = x_14;
}
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_19);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_27);
if (lean::is_scalar(x_25)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_25;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_21);
lean::cnstr_set(x_29, 2, x_27);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_29);
x_9 = x_30;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_14, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_34 = x_14;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_9 = x_36;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_37; uint8 x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_37 = lean::cnstr_get(x_14, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_40 = x_14;
}
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_37, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_37, 3);
lean::inc(x_47);
lean::dec(x_37);
x_50 = l_option_get___main___at_lean_parser_run___spec__2(x_47);
lean::inc(x_8);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_8);
x_53 = l_lean_parser_no__kind;
lean::inc(x_53);
x_55 = l_lean_parser_syntax_mk__node(x_53, x_52);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_57, 0, x_41);
lean::cnstr_set(x_57, 1, x_43);
lean::cnstr_set(x_57, 2, x_45);
lean::cnstr_set(x_57, 3, x_56);
if (x_39 == 0)
{
uint8 x_58; obj* x_59; obj* x_60; 
x_58 = 0;
if (lean::is_scalar(x_40)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_40;
}
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_58);
x_60 = x_59;
x_9 = x_60;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_61; obj* x_62; 
if (lean::is_scalar(x_40)) {
 x_61 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_61 = x_40;
}
lean::cnstr_set(x_61, 0, x_57);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_39);
x_62 = x_61;
x_9 = x_62;
x_10 = x_16;
goto lbl_11;
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_69; 
x_63 = lean::cnstr_get(x_5, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_5, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_5, 2);
lean::inc(x_67);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_69 = x_5;
}
if (lean::obj_tag(x_63) == 0)
{
obj* x_71; obj* x_72; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_63);
x_71 = l_lean_parser_combinators_many___rarg___closed__1;
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
lean::inc(x_71);
if (lean::is_scalar(x_69)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_69;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set(x_75, 1, x_65);
lean::cnstr_set(x_75, 2, x_72);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_75);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_6);
return x_77;
}
else
{
obj* x_78; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
x_78 = lean::cnstr_get(x_63, 0);
lean::inc(x_78);
lean::dec(x_63);
x_81 = lean::box(0);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set(x_82, 1, x_81);
x_83 = l_lean_parser_no__kind;
lean::inc(x_83);
x_85 = l_lean_parser_syntax_mk__node(x_83, x_82);
x_86 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_86);
if (lean::is_scalar(x_69)) {
 x_88 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_88 = x_69;
}
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set(x_88, 1, x_65);
lean::cnstr_set(x_88, 2, x_86);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_88);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_6);
return x_90;
}
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_5, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_94 = x_5;
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_6);
return x_97;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_8);
lean::dec(x_3);
x_5 = x_9;
x_6 = x_10;
goto lbl_7;
}
else
{
obj* x_100; uint8 x_102; 
x_100 = lean::cnstr_get(x_9, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_102 == 0)
{
obj* x_104; obj* x_107; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_9);
x_104 = lean::cnstr_get(x_100, 2);
lean::inc(x_104);
lean::dec(x_100);
x_107 = l_mjoin___rarg___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_109, 0, x_104);
lean::closure_set(x_109, 1, x_107);
x_110 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_110, 0, x_109);
x_111 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_111, 0, x_8);
lean::cnstr_set(x_111, 1, x_3);
lean::cnstr_set(x_111, 2, x_110);
x_5 = x_111;
x_6 = x_10;
goto lbl_7;
}
else
{
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_100);
x_5 = x_9;
x_6 = x_10;
goto lbl_7;
}
}
}
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::box(0);
x_9 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__4___rarg(x_9, x_10, x_8, x_8, x_2, x_3, x_4, x_5);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_19 = x_0;
}
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_23 = lean::apply_4(x_15, x_2, x_3, x_4, x_5);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 x_28 = x_23;
}
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_1, x_29);
lean::dec(x_29);
if (lean::obj_tag(x_24) == 0)
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; 
x_32 = lean::cnstr_get(x_24, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_24, 2);
lean::inc(x_36);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 lean::cnstr_release(x_24, 2);
 x_38 = x_24;
}
x_39 = lean::box(0);
lean::inc(x_39);
x_41 = lean::name_mk_numeral(x_39, x_1);
if (lean::is_scalar(x_19)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_19;
}
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_39);
x_43 = l_lean_parser_syntax_mk__node(x_41, x_42);
x_44 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_44);
if (lean::is_scalar(x_38)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_38;
}
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_34);
lean::cnstr_set(x_46, 2, x_44);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_53; 
lean::dec(x_17);
lean::dec(x_30);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_28)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_28;
}
lean::cnstr_set(x_53, 0, x_47);
lean::cnstr_set(x_53, 1, x_26);
return x_53;
}
else
{
obj* x_54; uint8 x_56; 
x_54 = lean::cnstr_get(x_47, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_47);
x_58 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2(x_17, x_30, x_2, x_3, x_4, x_26);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_59);
if (lean::is_scalar(x_28)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_28;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
return x_65;
}
else
{
obj* x_72; 
lean::dec(x_17);
lean::dec(x_30);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_54);
if (lean::is_scalar(x_28)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_28;
}
lean::cnstr_set(x_72, 0, x_47);
lean::cnstr_set(x_72, 1, x_26);
return x_72;
}
}
}
else
{
obj* x_75; uint8 x_77; obj* x_78; 
lean::dec(x_19);
lean::dec(x_1);
x_75 = lean::cnstr_get(x_24, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_78 = x_24;
}
if (x_77 == 0)
{
obj* x_80; obj* x_81; obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_78);
x_80 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2(x_17, x_30, x_2, x_3, x_4, x_26);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
x_86 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_75, x_81);
if (lean::is_scalar(x_28)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_28;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_83);
return x_87;
}
else
{
obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_17);
lean::dec(x_30);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_78)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_78;
}
lean::cnstr_set(x_93, 0, x_75);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_77);
x_94 = x_93;
if (lean::is_scalar(x_28)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_28;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_26);
return x_95;
}
}
}
}
}
obj* _init_l_lean_parser_command_decl__modifiers_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_59; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_doc__comment_parser), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__attributes_parser), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("private");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_7);
x_11 = lean::mk_string("protected");
x_12 = l_string_trim(x_11);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_14, 0, x_12);
lean::inc(x_8);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_8);
lean::closure_set(x_16, 2, x_14);
x_17 = lean::box(0);
lean::inc(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_8);
lean::inc(x_17);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_17);
x_25 = l_lean_parser_command_visibility;
lean::inc(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_27, 0, x_25);
lean::closure_set(x_27, 1, x_24);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::mk_string("noncomputable");
x_30 = l_string_trim(x_29);
lean::inc(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_32, 0, x_30);
lean::inc(x_8);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_34, 0, x_30);
lean::closure_set(x_34, 1, x_8);
lean::closure_set(x_34, 2, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_35, 0, x_34);
x_36 = lean::mk_string("meta");
x_37 = l_string_trim(x_36);
lean::inc(x_37);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_39, 0, x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_40, 0, x_37);
lean::closure_set(x_40, 1, x_8);
lean::closure_set(x_40, 2, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_17);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_35);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_28);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_3);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_1);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_parser_command__parser__m_monad___closed__1;
x_48 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_49 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_50 = l_lean_parser_command__parser__m_alternative___closed__1;
x_51 = l_lean_parser_command_decl__modifiers;
x_52 = l_lean_parser_command_decl__modifiers_has__view;
lean::inc(x_52);
lean::inc(x_51);
lean::inc(x_50);
lean::inc(x_49);
lean::inc(x_48);
lean::inc(x_47);
x_59 = l_lean_parser_combinators_node_view___rarg(x_47, x_48, x_49, x_50, x_51, x_46, x_52);
return x_59;
}
}
obj* _init_l_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_0 = l_lean_parser_command_doc__comment_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::mk_string("private");
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_9 = l_lean_parser_symbol_tokens___rarg(x_6, x_7);
x_10 = lean::mk_string("protected");
lean::inc(x_7);
x_12 = l_lean_parser_symbol_tokens___rarg(x_10, x_7);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_12, x_13);
x_16 = l_lean_parser_list_cons_tokens___rarg(x_9, x_15);
x_17 = l_lean_parser_tokens___rarg(x_16);
lean::inc(x_13);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_17, x_13);
x_20 = l_lean_parser_tokens___rarg(x_19);
x_21 = l_lean_parser_tokens___rarg(x_20);
x_22 = lean::mk_string("noncomputable");
lean::inc(x_7);
x_24 = l_lean_parser_symbol_tokens___rarg(x_22, x_7);
x_25 = l_lean_parser_tokens___rarg(x_24);
x_26 = lean::mk_string("meta");
x_27 = l_lean_parser_symbol_tokens___rarg(x_26, x_7);
x_28 = l_lean_parser_tokens___rarg(x_27);
x_29 = l_lean_parser_list_cons_tokens___rarg(x_28, x_13);
x_30 = l_lean_parser_list_cons_tokens___rarg(x_25, x_29);
x_31 = l_lean_parser_list_cons_tokens___rarg(x_21, x_30);
x_32 = l_lean_parser_list_cons_tokens___rarg(x_5, x_31);
x_33 = l_lean_parser_list_cons_tokens___rarg(x_2, x_32);
x_34 = l_lean_parser_tokens___rarg(x_33);
return x_34;
}
}
obj* l_lean_parser_command_decl__modifiers_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_decl__modifiers;
x_5 = l_lean_parser_command_decl__modifiers_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__modifiers_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_doc__comment_parser), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__attributes_parser), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("private");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_7);
x_11 = lean::mk_string("protected");
x_12 = l_string_trim(x_11);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_14, 0, x_12);
lean::inc(x_8);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_16, 0, x_12);
lean::closure_set(x_16, 1, x_8);
lean::closure_set(x_16, 2, x_14);
x_17 = lean::box(0);
lean::inc(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_8);
lean::inc(x_17);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_17);
x_25 = l_lean_parser_command_visibility;
lean::inc(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_27, 0, x_25);
lean::closure_set(x_27, 1, x_24);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::mk_string("noncomputable");
x_30 = l_string_trim(x_29);
lean::inc(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_32, 0, x_30);
lean::inc(x_8);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_34, 0, x_30);
lean::closure_set(x_34, 1, x_8);
lean::closure_set(x_34, 2, x_32);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_35, 0, x_34);
x_36 = lean::mk_string("meta");
x_37 = l_string_trim(x_36);
lean::inc(x_37);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_39, 0, x_37);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_40, 0, x_37);
lean::closure_set(x_40, 1, x_8);
lean::closure_set(x_40, 2, x_39);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_17);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_35);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_28);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_3);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_1);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
obj* _init_l_lean_parser_command_decl__sig() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("decl_sig");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__sig_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__sig_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__sig_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_8);
x_12 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__1;
lean::inc(x_12);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_17 = l_lean_parser_term_type__spec_has__view;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::apply_1(x_18, x_14);
x_21 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_20);
return x_23;
}
}
else
{
obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_32; 
x_24 = lean::cnstr_get(x_8, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_8, 1);
lean::inc(x_26);
lean::dec(x_8);
x_29 = l_lean_parser_term_bracketed__binders_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_24);
if (lean::obj_tag(x_26) == 0)
{
obj* x_34; obj* x_36; 
lean::dec(x_26);
x_34 = l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__3;
lean::inc(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_26, 0);
lean::inc(x_37);
lean::dec(x_26);
x_40 = l_lean_parser_term_type__spec_has__view;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_37);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_32);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
obj* _init_l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_0 = l_lean_parser_term_bracketed__binders_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
lean::inc(x_3);
x_5 = lean::apply_1(x_1, x_3);
x_6 = l_lean_parser_term_type__spec_has__view;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::apply_1(x_7, x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_term_bracketed__binders_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_term_type__spec_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_command_decl__sig_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_term_bracketed__binders_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_7, x_1);
x_10 = l_lean_parser_term_type__spec_has__view;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_13 = lean::apply_1(x_11, x_3);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_lean_parser_command_decl__sig;
lean::inc(x_17);
x_19 = l_lean_parser_syntax_mk__node(x_17, x_16);
return x_19;
}
}
obj* _init_l_lean_parser_command_decl__sig_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_decl__sig_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_decl__sig_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_bracketed__binders_parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_type__spec_parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_lean_parser_command__parser__m_monad___closed__1;
x_8 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_9 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_10 = l_lean_parser_command__parser__m_alternative___closed__1;
x_11 = l_lean_parser_command_decl__sig;
x_12 = l_lean_parser_command_decl__sig_has__view;
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
x_19 = l_lean_parser_combinators_node_view___rarg(x_7, x_8, x_9, x_10, x_11, x_6, x_12);
return x_19;
}
}
obj* _init_l_lean_parser_command_decl__sig_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = l_lean_parser_term_bracketed__binders_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_term_type__spec_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* l_lean_parser_command_decl__sig_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_decl__sig;
x_5 = l_lean_parser_command_decl__sig_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__sig_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_bracketed__binders_parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_type__spec_parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_opt__decl__sig() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("opt_decl_sig");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_opt__decl__sig_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_21; obj* x_23; 
x_20 = l_lean_parser_term_bracketed__binders_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_1);
x_25 = lean::box(3);
x_26 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_30; 
lean::dec(x_26);
x_28 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_23);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_33 = x_26;
}
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::obj_tag(x_34) == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_33);
lean::dec(x_34);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_23);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_34, 1);
lean::inc(x_43);
lean::dec(x_34);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_43);
x_47 = l_lean_parser_term_type__spec_has__view;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::apply_1(x_48, x_41);
if (lean::is_scalar(x_33)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_33;
}
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_23);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
else
{
obj* x_56; obj* x_58; 
lean::dec(x_33);
lean::dec(x_41);
lean::dec(x_43);
x_56 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_23);
lean::cnstr_set(x_58, 1, x_56);
return x_58;
}
}
}
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_1, 0);
lean::inc(x_59);
lean::dec(x_1);
x_62 = l_lean_parser_syntax_as__node___main(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; 
lean::dec(x_62);
x_64 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_23);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_69 = x_62;
}
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_76; 
lean::dec(x_70);
lean::dec(x_69);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_23);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_70, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_70, 1);
lean::inc(x_79);
lean::dec(x_70);
if (lean::obj_tag(x_79) == 0)
{
obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_79);
x_83 = l_lean_parser_term_type__spec_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::apply_1(x_84, x_77);
if (lean::is_scalar(x_69)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_69;
}
lean::cnstr_set(x_87, 0, x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_23);
lean::cnstr_set(x_88, 1, x_87);
return x_88;
}
else
{
obj* x_92; obj* x_94; 
lean::dec(x_77);
lean::dec(x_69);
lean::dec(x_79);
x_92 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_23);
lean::cnstr_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_6; obj* x_8; 
x_5 = l_lean_parser_term_bracketed__binders_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_0);
x_10 = lean::box(3);
x_11 = l_lean_parser_syntax_as__node___main(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; 
lean::dec(x_11);
x_13 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
}
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_18);
lean::dec(x_19);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_8);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_19, 1);
lean::inc(x_28);
lean::dec(x_19);
if (lean::obj_tag(x_28) == 0)
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_28);
x_32 = l_lean_parser_term_type__spec_has__view;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::apply_1(x_33, x_26);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_8);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
else
{
obj* x_41; obj* x_43; 
lean::dec(x_18);
lean::dec(x_26);
lean::dec(x_28);
x_41 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_8);
lean::cnstr_set(x_43, 1, x_41);
return x_43;
}
}
}
}
else
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
x_47 = l_lean_parser_syntax_as__node___main(x_44);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_51; 
lean::dec(x_47);
x_49 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_8);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_54 = x_47;
}
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; obj* x_61; 
lean::dec(x_54);
lean::dec(x_55);
x_60 = lean::box(0);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_8);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_55, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_55, 1);
lean::inc(x_64);
lean::dec(x_55);
if (lean::obj_tag(x_64) == 0)
{
obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_64);
x_68 = l_lean_parser_term_type__spec_has__view;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::apply_1(x_69, x_62);
if (lean::is_scalar(x_54)) {
 x_72 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_72 = x_54;
}
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_8);
lean::cnstr_set(x_73, 1, x_72);
return x_73;
}
else
{
obj* x_77; obj* x_79; 
lean::dec(x_54);
lean::dec(x_62);
lean::dec(x_64);
x_77 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_8);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
}
}
}
}
}
obj* l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_term_bracketed__binders_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_7, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
lean::dec(x_3);
x_11 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_command_opt__decl__sig;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
lean::dec(x_3);
x_20 = lean::box(0);
x_21 = l_lean_parser_term_type__spec_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_17);
lean::inc(x_20);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_20);
x_27 = l_lean_parser_no__kind;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_20);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_lean_parser_command_opt__decl__sig;
lean::inc(x_32);
x_34 = l_lean_parser_syntax_mk__node(x_32, x_31);
return x_34;
}
}
}
obj* _init_l_lean_parser_command_opt__decl__sig_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_opt__decl__sig_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_bracketed__binders_parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_opt__type_parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_lean_parser_command__parser__m_monad___closed__1;
x_8 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_9 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_10 = l_lean_parser_command__parser__m_alternative___closed__1;
x_11 = l_lean_parser_command_opt__decl__sig;
x_12 = l_lean_parser_command_opt__decl__sig_has__view;
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
x_19 = l_lean_parser_combinators_node_view___rarg(x_7, x_8, x_9, x_10, x_11, x_6, x_12);
return x_19;
}
}
obj* _init_l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = l_lean_parser_term_bracketed__binders_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_term_opt__type_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* l_lean_parser_command_opt__decl__sig_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_opt__decl__sig;
x_5 = l_lean_parser_command_opt__decl__sig_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_opt__decl__sig_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_bracketed__binders_parser), 5, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_opt__type_parser), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_equation() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("equation");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* _init_l_lean_parser_command_equation_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_equation_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_equation_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_equation_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_equation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_1;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
lean::dec(x_1);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_33);
if (lean::obj_tag(x_41) == 0)
{
lean::dec(x_41);
if (lean::obj_tag(x_32) == 0)
{
obj* x_43; 
x_43 = lean::box(0);
if (lean::obj_tag(x_32) == 0)
{
obj* x_45; obj* x_46; obj* x_48; 
lean::dec(x_32);
x_45 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_46 = lean::box(3);
lean::inc(x_45);
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_20);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_43);
lean::cnstr_set(x_48, 3, x_46);
return x_48;
}
else
{
obj* x_49; obj* x_52; obj* x_54; 
x_49 = lean::cnstr_get(x_32, 0);
lean::inc(x_49);
lean::dec(x_32);
x_52 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_52);
x_54 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_54, 0, x_20);
lean::cnstr_set(x_54, 1, x_52);
lean::cnstr_set(x_54, 2, x_43);
lean::cnstr_set(x_54, 3, x_49);
return x_54;
}
}
else
{
obj* x_55; obj* x_57; 
x_55 = lean::cnstr_get(x_32, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_32, 1);
lean::inc(x_57);
lean::dec(x_32);
switch (lean::obj_tag(x_55)) {
case 0:
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_55, 0);
lean::inc(x_60);
lean::dec(x_55);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_60);
if (lean::obj_tag(x_57) == 0)
{
obj* x_65; obj* x_66; obj* x_68; 
lean::dec(x_57);
x_65 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_66 = lean::box(3);
lean::inc(x_65);
x_68 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_68, 0, x_20);
lean::cnstr_set(x_68, 1, x_65);
lean::cnstr_set(x_68, 2, x_63);
lean::cnstr_set(x_68, 3, x_66);
return x_68;
}
else
{
obj* x_69; obj* x_72; obj* x_74; 
x_69 = lean::cnstr_get(x_57, 0);
lean::inc(x_69);
lean::dec(x_57);
x_72 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_72);
x_74 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_74, 0, x_20);
lean::cnstr_set(x_74, 1, x_72);
lean::cnstr_set(x_74, 2, x_63);
lean::cnstr_set(x_74, 3, x_69);
return x_74;
}
}
case 1:
{
obj* x_76; 
lean::dec(x_55);
x_76 = lean::box(0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_78; obj* x_79; obj* x_81; 
lean::dec(x_57);
x_78 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_79 = lean::box(3);
lean::inc(x_78);
x_81 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_81, 0, x_20);
lean::cnstr_set(x_81, 1, x_78);
lean::cnstr_set(x_81, 2, x_76);
lean::cnstr_set(x_81, 3, x_79);
return x_81;
}
else
{
obj* x_82; obj* x_85; obj* x_87; 
x_82 = lean::cnstr_get(x_57, 0);
lean::inc(x_82);
lean::dec(x_57);
x_85 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_85);
x_87 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_87, 0, x_20);
lean::cnstr_set(x_87, 1, x_85);
lean::cnstr_set(x_87, 2, x_76);
lean::cnstr_set(x_87, 3, x_82);
return x_87;
}
}
case 2:
{
obj* x_89; 
lean::dec(x_55);
x_89 = lean::box(0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_57);
x_91 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_92 = lean::box(3);
lean::inc(x_91);
x_94 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_94, 0, x_20);
lean::cnstr_set(x_94, 1, x_91);
lean::cnstr_set(x_94, 2, x_89);
lean::cnstr_set(x_94, 3, x_92);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_100; 
x_95 = lean::cnstr_get(x_57, 0);
lean::inc(x_95);
lean::dec(x_57);
x_98 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_98);
x_100 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_100, 0, x_20);
lean::cnstr_set(x_100, 1, x_98);
lean::cnstr_set(x_100, 2, x_89);
lean::cnstr_set(x_100, 3, x_95);
return x_100;
}
}
default:
{
obj* x_102; 
lean::dec(x_55);
x_102 = lean::box(0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_57);
x_104 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_105 = lean::box(3);
lean::inc(x_104);
x_107 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_107, 0, x_20);
lean::cnstr_set(x_107, 1, x_104);
lean::cnstr_set(x_107, 2, x_102);
lean::cnstr_set(x_107, 3, x_105);
return x_107;
}
else
{
obj* x_108; obj* x_111; obj* x_113; 
x_108 = lean::cnstr_get(x_57, 0);
lean::inc(x_108);
lean::dec(x_57);
x_111 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_111);
x_113 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_113, 0, x_20);
lean::cnstr_set(x_113, 1, x_111);
lean::cnstr_set(x_113, 2, x_102);
lean::cnstr_set(x_113, 3, x_108);
return x_113;
}
}
}
}
}
else
{
obj* x_114; obj* x_116; obj* x_117; obj* x_120; 
x_114 = lean::cnstr_get(x_41, 0);
lean::inc(x_114);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_116 = x_41;
}
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_120 = l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__1(x_117);
if (lean::obj_tag(x_32) == 0)
{
obj* x_122; 
lean::dec(x_116);
x_122 = lean::box(0);
if (lean::obj_tag(x_32) == 0)
{
obj* x_124; obj* x_125; 
lean::dec(x_32);
x_124 = lean::box(3);
x_125 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_125, 0, x_20);
lean::cnstr_set(x_125, 1, x_120);
lean::cnstr_set(x_125, 2, x_122);
lean::cnstr_set(x_125, 3, x_124);
return x_125;
}
else
{
obj* x_126; obj* x_129; 
x_126 = lean::cnstr_get(x_32, 0);
lean::inc(x_126);
lean::dec(x_32);
x_129 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_129, 0, x_20);
lean::cnstr_set(x_129, 1, x_120);
lean::cnstr_set(x_129, 2, x_122);
lean::cnstr_set(x_129, 3, x_126);
return x_129;
}
}
else
{
obj* x_130; obj* x_132; 
x_130 = lean::cnstr_get(x_32, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_32, 1);
lean::inc(x_132);
lean::dec(x_32);
switch (lean::obj_tag(x_130)) {
case 0:
{
obj* x_135; obj* x_138; 
x_135 = lean::cnstr_get(x_130, 0);
lean::inc(x_135);
lean::dec(x_130);
if (lean::is_scalar(x_116)) {
 x_138 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_138 = x_116;
}
lean::cnstr_set(x_138, 0, x_135);
if (lean::obj_tag(x_132) == 0)
{
obj* x_140; obj* x_141; 
lean::dec(x_132);
x_140 = lean::box(3);
x_141 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_141, 0, x_20);
lean::cnstr_set(x_141, 1, x_120);
lean::cnstr_set(x_141, 2, x_138);
lean::cnstr_set(x_141, 3, x_140);
return x_141;
}
else
{
obj* x_142; obj* x_145; 
x_142 = lean::cnstr_get(x_132, 0);
lean::inc(x_142);
lean::dec(x_132);
x_145 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_145, 0, x_20);
lean::cnstr_set(x_145, 1, x_120);
lean::cnstr_set(x_145, 2, x_138);
lean::cnstr_set(x_145, 3, x_142);
return x_145;
}
}
case 1:
{
obj* x_148; 
lean::dec(x_130);
lean::dec(x_116);
x_148 = lean::box(0);
if (lean::obj_tag(x_132) == 0)
{
obj* x_150; obj* x_151; 
lean::dec(x_132);
x_150 = lean::box(3);
x_151 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_151, 0, x_20);
lean::cnstr_set(x_151, 1, x_120);
lean::cnstr_set(x_151, 2, x_148);
lean::cnstr_set(x_151, 3, x_150);
return x_151;
}
else
{
obj* x_152; obj* x_155; 
x_152 = lean::cnstr_get(x_132, 0);
lean::inc(x_152);
lean::dec(x_132);
x_155 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_155, 0, x_20);
lean::cnstr_set(x_155, 1, x_120);
lean::cnstr_set(x_155, 2, x_148);
lean::cnstr_set(x_155, 3, x_152);
return x_155;
}
}
case 2:
{
obj* x_158; 
lean::dec(x_130);
lean::dec(x_116);
x_158 = lean::box(0);
if (lean::obj_tag(x_132) == 0)
{
obj* x_160; obj* x_161; 
lean::dec(x_132);
x_160 = lean::box(3);
x_161 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_161, 0, x_20);
lean::cnstr_set(x_161, 1, x_120);
lean::cnstr_set(x_161, 2, x_158);
lean::cnstr_set(x_161, 3, x_160);
return x_161;
}
else
{
obj* x_162; obj* x_165; 
x_162 = lean::cnstr_get(x_132, 0);
lean::inc(x_162);
lean::dec(x_132);
x_165 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_165, 0, x_20);
lean::cnstr_set(x_165, 1, x_120);
lean::cnstr_set(x_165, 2, x_158);
lean::cnstr_set(x_165, 3, x_162);
return x_165;
}
}
default:
{
obj* x_168; 
lean::dec(x_130);
lean::dec(x_116);
x_168 = lean::box(0);
if (lean::obj_tag(x_132) == 0)
{
obj* x_170; obj* x_171; 
lean::dec(x_132);
x_170 = lean::box(3);
x_171 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_171, 0, x_20);
lean::cnstr_set(x_171, 1, x_120);
lean::cnstr_set(x_171, 2, x_168);
lean::cnstr_set(x_171, 3, x_170);
return x_171;
}
else
{
obj* x_172; obj* x_175; 
x_172 = lean::cnstr_get(x_132, 0);
lean::inc(x_172);
lean::dec(x_132);
x_175 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_175, 0, x_20);
lean::cnstr_set(x_175, 1, x_120);
lean::cnstr_set(x_175, 2, x_168);
lean::cnstr_set(x_175, 3, x_172);
return x_175;
}
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_equation_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = lean::box(3);
x_17 = x_0;
x_18 = x_20;
goto lbl_19;
}
else
{
obj* x_21; obj* x_23; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
x_17 = x_23;
x_18 = x_21;
goto lbl_19;
}
lbl_19:
{
obj* x_26; 
x_26 = l_lean_parser_syntax_as__node___main(x_18);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_26);
if (lean::obj_tag(x_17) == 0)
{
obj* x_28; 
x_28 = lean::box(0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_30; obj* x_31; obj* x_33; 
lean::dec(x_17);
x_30 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_31 = lean::box(3);
lean::inc(x_30);
x_33 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_33, 0, x_5);
lean::cnstr_set(x_33, 1, x_30);
lean::cnstr_set(x_33, 2, x_28);
lean::cnstr_set(x_33, 3, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_39; 
x_34 = lean::cnstr_get(x_17, 0);
lean::inc(x_34);
lean::dec(x_17);
x_37 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_39, 0, x_5);
lean::cnstr_set(x_39, 1, x_37);
lean::cnstr_set(x_39, 2, x_28);
lean::cnstr_set(x_39, 3, x_34);
return x_39;
}
}
else
{
obj* x_40; obj* x_42; 
x_40 = lean::cnstr_get(x_17, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_17, 1);
lean::inc(x_42);
lean::dec(x_17);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_40, 0);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_45);
if (lean::obj_tag(x_42) == 0)
{
obj* x_50; obj* x_51; obj* x_53; 
lean::dec(x_42);
x_50 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_51 = lean::box(3);
lean::inc(x_50);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_5);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set(x_53, 2, x_48);
lean::cnstr_set(x_53, 3, x_51);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_59; 
x_54 = lean::cnstr_get(x_42, 0);
lean::inc(x_54);
lean::dec(x_42);
x_57 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_5);
lean::cnstr_set(x_59, 1, x_57);
lean::cnstr_set(x_59, 2, x_48);
lean::cnstr_set(x_59, 3, x_54);
return x_59;
}
}
case 1:
{
obj* x_61; 
lean::dec(x_40);
x_61 = lean::box(0);
if (lean::obj_tag(x_42) == 0)
{
obj* x_63; obj* x_64; obj* x_66; 
lean::dec(x_42);
x_63 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_64 = lean::box(3);
lean::inc(x_63);
x_66 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_66, 0, x_5);
lean::cnstr_set(x_66, 1, x_63);
lean::cnstr_set(x_66, 2, x_61);
lean::cnstr_set(x_66, 3, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_72; 
x_67 = lean::cnstr_get(x_42, 0);
lean::inc(x_67);
lean::dec(x_42);
x_70 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_72, 0, x_5);
lean::cnstr_set(x_72, 1, x_70);
lean::cnstr_set(x_72, 2, x_61);
lean::cnstr_set(x_72, 3, x_67);
return x_72;
}
}
case 2:
{
obj* x_74; 
lean::dec(x_40);
x_74 = lean::box(0);
if (lean::obj_tag(x_42) == 0)
{
obj* x_76; obj* x_77; obj* x_79; 
lean::dec(x_42);
x_76 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_77 = lean::box(3);
lean::inc(x_76);
x_79 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_79, 0, x_5);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_74);
lean::cnstr_set(x_79, 3, x_77);
return x_79;
}
else
{
obj* x_80; obj* x_83; obj* x_85; 
x_80 = lean::cnstr_get(x_42, 0);
lean::inc(x_80);
lean::dec(x_42);
x_83 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_83);
x_85 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_85, 0, x_5);
lean::cnstr_set(x_85, 1, x_83);
lean::cnstr_set(x_85, 2, x_74);
lean::cnstr_set(x_85, 3, x_80);
return x_85;
}
}
default:
{
obj* x_87; 
lean::dec(x_40);
x_87 = lean::box(0);
if (lean::obj_tag(x_42) == 0)
{
obj* x_89; obj* x_90; obj* x_92; 
lean::dec(x_42);
x_89 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
x_90 = lean::box(3);
lean::inc(x_89);
x_92 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_92, 0, x_5);
lean::cnstr_set(x_92, 1, x_89);
lean::cnstr_set(x_92, 2, x_87);
lean::cnstr_set(x_92, 3, x_90);
return x_92;
}
else
{
obj* x_93; obj* x_96; obj* x_98; 
x_93 = lean::cnstr_get(x_42, 0);
lean::inc(x_93);
lean::dec(x_42);
x_96 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
x_98 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_98, 0, x_5);
lean::cnstr_set(x_98, 1, x_96);
lean::cnstr_set(x_98, 2, x_87);
lean::cnstr_set(x_98, 3, x_93);
return x_98;
}
}
}
}
}
else
{
obj* x_99; obj* x_101; obj* x_102; obj* x_105; 
x_99 = lean::cnstr_get(x_26, 0);
lean::inc(x_99);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_101 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_101 = x_26;
}
x_102 = lean::cnstr_get(x_99, 1);
lean::inc(x_102);
lean::dec(x_99);
x_105 = l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__1(x_102);
if (lean::obj_tag(x_17) == 0)
{
obj* x_107; 
lean::dec(x_101);
x_107 = lean::box(0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_109; obj* x_110; 
lean::dec(x_17);
x_109 = lean::box(3);
x_110 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_110, 0, x_5);
lean::cnstr_set(x_110, 1, x_105);
lean::cnstr_set(x_110, 2, x_107);
lean::cnstr_set(x_110, 3, x_109);
return x_110;
}
else
{
obj* x_111; obj* x_114; 
x_111 = lean::cnstr_get(x_17, 0);
lean::inc(x_111);
lean::dec(x_17);
x_114 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_114, 0, x_5);
lean::cnstr_set(x_114, 1, x_105);
lean::cnstr_set(x_114, 2, x_107);
lean::cnstr_set(x_114, 3, x_111);
return x_114;
}
}
else
{
obj* x_115; obj* x_117; 
x_115 = lean::cnstr_get(x_17, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_17, 1);
lean::inc(x_117);
lean::dec(x_17);
switch (lean::obj_tag(x_115)) {
case 0:
{
obj* x_120; obj* x_123; 
x_120 = lean::cnstr_get(x_115, 0);
lean::inc(x_120);
lean::dec(x_115);
if (lean::is_scalar(x_101)) {
 x_123 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_123 = x_101;
}
lean::cnstr_set(x_123, 0, x_120);
if (lean::obj_tag(x_117) == 0)
{
obj* x_125; obj* x_126; 
lean::dec(x_117);
x_125 = lean::box(3);
x_126 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_126, 0, x_5);
lean::cnstr_set(x_126, 1, x_105);
lean::cnstr_set(x_126, 2, x_123);
lean::cnstr_set(x_126, 3, x_125);
return x_126;
}
else
{
obj* x_127; obj* x_130; 
x_127 = lean::cnstr_get(x_117, 0);
lean::inc(x_127);
lean::dec(x_117);
x_130 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_130, 0, x_5);
lean::cnstr_set(x_130, 1, x_105);
lean::cnstr_set(x_130, 2, x_123);
lean::cnstr_set(x_130, 3, x_127);
return x_130;
}
}
case 1:
{
obj* x_133; 
lean::dec(x_101);
lean::dec(x_115);
x_133 = lean::box(0);
if (lean::obj_tag(x_117) == 0)
{
obj* x_135; obj* x_136; 
lean::dec(x_117);
x_135 = lean::box(3);
x_136 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_136, 0, x_5);
lean::cnstr_set(x_136, 1, x_105);
lean::cnstr_set(x_136, 2, x_133);
lean::cnstr_set(x_136, 3, x_135);
return x_136;
}
else
{
obj* x_137; obj* x_140; 
x_137 = lean::cnstr_get(x_117, 0);
lean::inc(x_137);
lean::dec(x_117);
x_140 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_140, 0, x_5);
lean::cnstr_set(x_140, 1, x_105);
lean::cnstr_set(x_140, 2, x_133);
lean::cnstr_set(x_140, 3, x_137);
return x_140;
}
}
case 2:
{
obj* x_143; 
lean::dec(x_101);
lean::dec(x_115);
x_143 = lean::box(0);
if (lean::obj_tag(x_117) == 0)
{
obj* x_145; obj* x_146; 
lean::dec(x_117);
x_145 = lean::box(3);
x_146 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_146, 0, x_5);
lean::cnstr_set(x_146, 1, x_105);
lean::cnstr_set(x_146, 2, x_143);
lean::cnstr_set(x_146, 3, x_145);
return x_146;
}
else
{
obj* x_147; obj* x_150; 
x_147 = lean::cnstr_get(x_117, 0);
lean::inc(x_147);
lean::dec(x_117);
x_150 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_150, 0, x_5);
lean::cnstr_set(x_150, 1, x_105);
lean::cnstr_set(x_150, 2, x_143);
lean::cnstr_set(x_150, 3, x_147);
return x_150;
}
}
default:
{
obj* x_153; 
lean::dec(x_101);
lean::dec(x_115);
x_153 = lean::box(0);
if (lean::obj_tag(x_117) == 0)
{
obj* x_155; obj* x_156; 
lean::dec(x_117);
x_155 = lean::box(3);
x_156 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_156, 0, x_5);
lean::cnstr_set(x_156, 1, x_105);
lean::cnstr_set(x_156, 2, x_153);
lean::cnstr_set(x_156, 3, x_155);
return x_156;
}
else
{
obj* x_157; obj* x_160; 
x_157 = lean::cnstr_get(x_117, 0);
lean::inc(x_157);
lean::dec(x_117);
x_160 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_160, 0, x_5);
lean::cnstr_set(x_160, 1, x_105);
lean::cnstr_set(x_160, 2, x_153);
lean::cnstr_set(x_160, 3, x_157);
return x_160;
}
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_equation_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_1);
x_13 = lean::box(3);
lean::inc(x_13);
x_15 = l_option_get__or__else___main___rarg(x_12, x_13);
x_16 = l_list_map___main___at_lean_parser_command_equation_has__view_x_27___spec__2(x_3);
x_17 = l_lean_parser_no__kind;
lean::inc(x_17);
x_19 = l_lean_parser_syntax_mk__node(x_17, x_16);
lean::inc(x_10);
x_21 = l_option_map___rarg(x_10, x_5);
x_22 = l_option_get__or__else___main___rarg(x_21, x_13);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_7);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_19);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_15);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_lean_parser_command_equation;
lean::inc(x_28);
x_30 = l_lean_parser_syntax_mk__node(x_28, x_27);
return x_30;
}
}
obj* _init_l_lean_parser_command_equation_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_equation_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_equation_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_37; 
x_0 = lean::mk_string("|");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = l_lean_parser_max__prec;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::mk_string(":=");
x_13 = l_string_trim(x_12);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_15, 0, x_13);
lean::inc(x_4);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_17, 0, x_13);
lean::closure_set(x_17, 1, x_4);
lean::closure_set(x_17, 2, x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_18, 0, x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command__parser__m_monad___closed__1;
x_26 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_27 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_28 = l_lean_parser_command__parser__m_alternative___closed__1;
x_29 = l_lean_parser_command_equation;
x_30 = l_lean_parser_command_equation_has__view;
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
x_37 = l_lean_parser_combinators_node_view___rarg(x_25, x_26, x_27, x_28, x_29, x_24, x_30);
return x_37;
}
}
obj* _init_l_lean_parser_command_equation_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::mk_string("|");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_tokens___rarg(x_4);
lean::inc(x_6);
x_8 = l_lean_parser_tokens___rarg(x_6);
x_9 = lean::mk_string(":=");
x_10 = l_lean_parser_symbol_tokens___rarg(x_9, x_1);
x_11 = lean::box(0);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_6, x_11);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_10, x_12);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_8, x_13);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_3, x_14);
x_16 = l_lean_parser_tokens___rarg(x_15);
return x_16;
}
}
obj* l_lean_parser_command_equation_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_equation;
x_5 = l_lean_parser_command_equation_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_equation_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_0 = lean::mk_string("|");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = l_lean_parser_max__prec;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::mk_string(":=");
x_13 = l_string_trim(x_12);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_15, 0, x_13);
lean::inc(x_4);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_17, 0, x_13);
lean::closure_set(x_17, 1, x_4);
lean::closure_set(x_17, 2, x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_18, 0, x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
obj* _init_l_lean_parser_command_simple__decl__val() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("simple_decl_val");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_simple__decl__val_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; 
lean::dec(x_8);
x_13 = l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_13);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_15);
return x_19;
}
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_8, 1);
lean::inc(x_22);
lean::dec(x_8);
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
if (lean::is_scalar(x_7)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_7;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_22);
x_30 = lean::box(3);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_35; 
x_32 = lean::cnstr_get(x_22, 0);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
case 1:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_39; 
lean::dec(x_22);
x_39 = l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_39);
return x_39;
}
else
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_22, 0);
lean::inc(x_41);
lean::dec(x_22);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_41);
return x_45;
}
}
case 2:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_49; 
lean::dec(x_22);
x_49 = l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
else
{
obj* x_51; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_22, 0);
lean::inc(x_51);
lean::dec(x_22);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
return x_55;
}
}
default:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_59; 
lean::dec(x_22);
x_59 = l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_22, 0);
lean::inc(x_61);
lean::dec(x_22);
x_64 = lean::box(0);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
return x_65;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_command_simple__decl__val;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
}
obj* _init_l_lean_parser_command_simple__decl__val_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_simple__decl__val_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_decl__val() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("decl_val");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__val_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__val_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__5;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_86; uint8 x_87; 
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_dec_eq(x_2, x_86);
lean::dec(x_86);
lean::dec(x_2);
if (x_87 == 0)
{
obj* x_90; 
x_90 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_90) == 0)
{
obj* x_92; 
lean::dec(x_90);
x_92 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
return x_92;
}
else
{
obj* x_94; obj* x_97; obj* x_100; obj* x_102; obj* x_103; 
x_94 = lean::cnstr_get(x_90, 0);
lean::inc(x_94);
lean::dec(x_90);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
x_100 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__2;
lean::inc(x_100);
x_102 = l_list_map___main___rarg(x_100, x_97);
x_103 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_104; obj* x_107; obj* x_108; 
x_104 = lean::cnstr_get(x_1, 0);
lean::inc(x_104);
lean::dec(x_1);
x_107 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_107, 0, x_104);
x_108 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
case 1:
{
obj* x_110; 
lean::dec(x_1);
x_110 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
lean::inc(x_110);
return x_110;
}
case 2:
{
obj* x_113; 
lean::dec(x_1);
x_113 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
lean::inc(x_113);
return x_113;
}
default:
{
obj* x_116; 
lean::dec(x_1);
x_116 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
lean::inc(x_116);
return x_116;
}
}
}
}
else
{
obj* x_119; obj* x_120; obj* x_122; obj* x_123; 
lean::dec(x_2);
x_119 = l_lean_parser_command_simple__decl__val_has__view;
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_122 = lean::apply_1(x_120, x_1);
x_123 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_123, 0, x_122);
return x_123;
}
}
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_lean_parser_command_equation_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_equation_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
if (x_9 == 0)
{
obj* x_12; 
x_12 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; 
lean::dec(x_12);
x_14 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__1;
lean::inc(x_14);
return x_14;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__2;
lean::inc(x_22);
x_24 = l_list_map___main___rarg(x_22, x_19);
x_25 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_26; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
case 1:
{
obj* x_32; 
lean::dec(x_0);
x_32 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
lean::inc(x_32);
return x_32;
}
case 2:
{
obj* x_35; 
lean::dec(x_0);
x_35 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
lean::inc(x_35);
return x_35;
}
default:
{
obj* x_38; 
lean::dec(x_0);
x_38 = l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3;
lean::inc(x_38);
return x_38;
}
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_1);
x_41 = l_lean_parser_command_simple__decl__val_has__view;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::apply_1(x_42, x_0);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
}
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("decl_val");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_decl__val_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_simple__decl__val_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_command_decl__val;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
case 1:
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_21);
x_23 = l_option_map___rarg(x_21, x_18);
x_24 = lean::box(3);
x_25 = l_option_get__or__else___main___rarg(x_23, x_24);
lean::inc(x_1);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_28);
x_30 = l_lean_parser_syntax_mk__node(x_28, x_27);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_1);
x_32 = l_lean_parser_command_decl__val;
lean::inc(x_32);
x_34 = l_lean_parser_syntax_mk__node(x_32, x_31);
return x_34;
}
default:
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; 
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
lean::dec(x_0);
x_38 = l_lean_parser_command_decl__val_has__view_x_27___lambda__2___closed__1;
lean::inc(x_38);
x_40 = l_list_map___main___rarg(x_38, x_35);
x_41 = l_lean_parser_no__kind;
lean::inc(x_41);
x_43 = l_lean_parser_syntax_mk__node(x_41, x_40);
lean::inc(x_1);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_1);
x_46 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_syntax_mk__node(x_46, x_45);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_1);
x_50 = l_lean_parser_command_decl__val;
lean::inc(x_50);
x_52 = l_lean_parser_syntax_mk__node(x_50, x_49);
return x_52;
}
}
}
}
obj* _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_equation_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_decl__val_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_decl__val_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_decl__val_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_43; 
x_0 = lean::mk_string(":=");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
lean::inc(x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::box(0);
lean::inc(x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_command_simple__decl__val;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::mk_string(".");
x_18 = l_string_trim(x_17);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_18);
lean::inc(x_4);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_4);
lean::closure_set(x_22, 2, x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_equation_parser), 4, 0);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_24, 0, x_23);
lean::inc(x_10);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_10);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_22);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_16);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_29, 0, x_28);
lean::closure_set(x_29, 1, x_4);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_10);
x_31 = l_lean_parser_command__parser__m_monad___closed__1;
x_32 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_33 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_34 = l_lean_parser_command__parser__m_alternative___closed__1;
x_35 = l_lean_parser_command_decl__val;
x_36 = l_lean_parser_command_decl__val_has__view;
lean::inc(x_36);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
x_43 = l_lean_parser_combinators_node_view___rarg(x_31, x_32, x_33, x_34, x_35, x_30, x_36);
return x_43;
}
}
obj* _init_l_lean_parser_command_decl__val_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_0 = lean::mk_string(":=");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_4);
x_6 = l_lean_parser_tokens___rarg(x_4);
x_7 = lean::box(0);
lean::inc(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_6, x_7);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_3, x_9);
x_11 = l_lean_parser_tokens___rarg(x_10);
x_12 = lean::mk_string(".");
x_13 = l_lean_parser_symbol_tokens___rarg(x_12, x_1);
x_14 = l_lean_parser_command_equation_parser_lean_parser_has__tokens;
lean::inc(x_14);
x_16 = l_lean_parser_tokens___rarg(x_14);
lean::inc(x_7);
x_18 = l_lean_parser_list_cons_tokens___rarg(x_16, x_7);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_13, x_18);
x_20 = l_lean_parser_list_cons_tokens___rarg(x_11, x_19);
x_21 = l_lean_parser_tokens___rarg(x_20);
x_22 = l_lean_parser_list_cons_tokens___rarg(x_21, x_7);
x_23 = l_lean_parser_tokens___rarg(x_22);
return x_23;
}
}
obj* l_lean_parser_command_decl__val_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_decl__val;
x_5 = l_lean_parser_command_decl__val_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_decl__val_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_0 = lean::mk_string(":=");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
lean::inc(x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::box(0);
lean::inc(x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_command_simple__decl__val;
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_13);
x_17 = lean::mk_string(".");
x_18 = l_string_trim(x_17);
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_18);
lean::inc(x_4);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_4);
lean::closure_set(x_22, 2, x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_equation_parser), 4, 0);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_24, 0, x_23);
lean::inc(x_10);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_10);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_22);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_16);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_29, 0, x_28);
lean::closure_set(x_29, 1, x_4);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_10);
return x_30;
}
}
obj* _init_l_lean_parser_command_relaxed__infer__modifier() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("relaxed_infer_modifier");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_relaxed__infer__modifier_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_7 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__2;
lean::inc(x_9);
return x_9;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_4 = x_14;
x_5 = x_17;
goto lbl_6;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_14, 1);
lean::inc(x_20);
lean::dec(x_14);
x_4 = x_20;
x_5 = x_18;
goto lbl_6;
}
}
lbl_3:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
case 1:
{
obj* x_29; obj* x_30; 
lean::dec(x_2);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
case 2:
{
obj* x_32; obj* x_33; 
lean::dec(x_2);
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
default:
{
obj* x_35; obj* x_36; 
lean::dec(x_2);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
lbl_6:
{
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
lean::dec(x_5);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
if (lean::obj_tag(x_4) == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_4);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_4, 0);
lean::inc(x_44);
lean::dec(x_4);
x_1 = x_40;
x_2 = x_44;
goto lbl_3;
}
}
case 1:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_49; 
lean::dec(x_4);
x_49 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
else
{
obj* x_51; obj* x_54; 
x_51 = lean::cnstr_get(x_4, 0);
lean::inc(x_51);
lean::dec(x_4);
x_54 = lean::box(0);
x_1 = x_54;
x_2 = x_51;
goto lbl_3;
}
}
case 2:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_57; 
lean::dec(x_4);
x_57 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
return x_57;
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_4, 0);
lean::inc(x_59);
lean::dec(x_4);
x_62 = lean::box(0);
x_1 = x_62;
x_2 = x_59;
goto lbl_3;
}
}
default:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_65; 
lean::dec(x_4);
x_65 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_65);
return x_65;
}
else
{
obj* x_67; obj* x_70; 
x_67 = lean::cnstr_get(x_4, 0);
lean::inc(x_67);
lean::dec(x_4);
x_70 = lean::box(0);
x_1 = x_70;
x_2 = x_67;
goto lbl_3;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_6 = lean::box(0);
x_7 = lean::box(3);
x_3 = x_6;
x_4 = x_7;
goto lbl_5;
lbl_2:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
case 1:
{
obj* x_14; obj* x_15; 
lean::dec(x_1);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
case 2:
{
obj* x_17; obj* x_18; 
lean::dec(x_1);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
default:
{
obj* x_20; obj* x_21; 
lean::dec(x_1);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
lbl_5:
{
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_4, 0);
lean::inc(x_22);
lean::dec(x_4);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_3);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
x_0 = x_25;
x_1 = x_29;
goto lbl_2;
}
}
case 1:
{
lean::dec(x_4);
if (lean::obj_tag(x_3) == 0)
{
obj* x_34; 
lean::dec(x_3);
x_34 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_34);
return x_34;
}
else
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_3, 0);
lean::inc(x_36);
lean::dec(x_3);
x_39 = lean::box(0);
x_0 = x_39;
x_1 = x_36;
goto lbl_2;
}
}
case 2:
{
lean::dec(x_4);
if (lean::obj_tag(x_3) == 0)
{
obj* x_42; 
lean::dec(x_3);
x_42 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_42);
return x_42;
}
else
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_3, 0);
lean::inc(x_44);
lean::dec(x_3);
x_47 = lean::box(0);
x_0 = x_47;
x_1 = x_44;
goto lbl_2;
}
}
default:
{
lean::dec(x_4);
if (lean::obj_tag(x_3) == 0)
{
obj* x_50; 
lean::dec(x_3);
x_50 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
return x_50;
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_3, 0);
lean::inc(x_52);
lean::dec(x_3);
x_55 = lean::box(0);
x_0 = x_55;
x_1 = x_52;
goto lbl_2;
}
}
}
}
}
}
obj* l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
lean::inc(x_9);
x_11 = l_option_get__or__else___main___rarg(x_8, x_9);
lean::inc(x_6);
x_13 = l_option_map___rarg(x_6, x_3);
x_14 = l_option_get__or__else___main___rarg(x_13, x_9);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_relaxed__infer__modifier;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_relaxed__infer__modifier_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_relaxed__infer__modifier_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_strict__infer__modifier() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("strict_infer_modifier");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_strict__infer__modifier_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; 
x_7 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__2;
lean::inc(x_9);
return x_9;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_4 = x_14;
x_5 = x_17;
goto lbl_6;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_14, 1);
lean::inc(x_20);
lean::dec(x_14);
x_4 = x_20;
x_5 = x_18;
goto lbl_6;
}
}
lbl_3:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
lean::dec(x_2);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
case 1:
{
obj* x_29; obj* x_30; 
lean::dec(x_2);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
case 2:
{
obj* x_32; obj* x_33; 
lean::dec(x_2);
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
default:
{
obj* x_35; obj* x_36; 
lean::dec(x_2);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
lbl_6:
{
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
lean::dec(x_5);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
if (lean::obj_tag(x_4) == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_4);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_4, 0);
lean::inc(x_44);
lean::dec(x_4);
x_1 = x_40;
x_2 = x_44;
goto lbl_3;
}
}
case 1:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_49; 
lean::dec(x_4);
x_49 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
else
{
obj* x_51; obj* x_54; 
x_51 = lean::cnstr_get(x_4, 0);
lean::inc(x_51);
lean::dec(x_4);
x_54 = lean::box(0);
x_1 = x_54;
x_2 = x_51;
goto lbl_3;
}
}
case 2:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_57; 
lean::dec(x_4);
x_57 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
return x_57;
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_4, 0);
lean::inc(x_59);
lean::dec(x_4);
x_62 = lean::box(0);
x_1 = x_62;
x_2 = x_59;
goto lbl_3;
}
}
default:
{
lean::dec(x_5);
if (lean::obj_tag(x_4) == 0)
{
obj* x_65; 
lean::dec(x_4);
x_65 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_65);
return x_65;
}
else
{
obj* x_67; obj* x_70; 
x_67 = lean::cnstr_get(x_4, 0);
lean::inc(x_67);
lean::dec(x_4);
x_70 = lean::box(0);
x_1 = x_70;
x_2 = x_67;
goto lbl_3;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_6 = lean::box(0);
x_7 = lean::box(3);
x_3 = x_6;
x_4 = x_7;
goto lbl_5;
lbl_2:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
case 1:
{
obj* x_14; obj* x_15; 
lean::dec(x_1);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
case 2:
{
obj* x_17; obj* x_18; 
lean::dec(x_1);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
default:
{
obj* x_20; obj* x_21; 
lean::dec(x_1);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
lbl_5:
{
switch (lean::obj_tag(x_4)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_4, 0);
lean::inc(x_22);
lean::dec(x_4);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
if (lean::obj_tag(x_3) == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_3);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_3, 0);
lean::inc(x_29);
lean::dec(x_3);
x_0 = x_25;
x_1 = x_29;
goto lbl_2;
}
}
case 1:
{
lean::dec(x_4);
if (lean::obj_tag(x_3) == 0)
{
obj* x_34; 
lean::dec(x_3);
x_34 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_34);
return x_34;
}
else
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_3, 0);
lean::inc(x_36);
lean::dec(x_3);
x_39 = lean::box(0);
x_0 = x_39;
x_1 = x_36;
goto lbl_2;
}
}
case 2:
{
lean::dec(x_4);
if (lean::obj_tag(x_3) == 0)
{
obj* x_42; 
lean::dec(x_3);
x_42 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_42);
return x_42;
}
else
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_3, 0);
lean::inc(x_44);
lean::dec(x_3);
x_47 = lean::box(0);
x_0 = x_47;
x_1 = x_44;
goto lbl_2;
}
}
default:
{
lean::dec(x_4);
if (lean::obj_tag(x_3) == 0)
{
obj* x_50; 
lean::dec(x_3);
x_50 = l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
return x_50;
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_3, 0);
lean::inc(x_52);
lean::dec(x_3);
x_55 = lean::box(0);
x_0 = x_55;
x_1 = x_52;
goto lbl_2;
}
}
}
}
}
}
obj* l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
lean::inc(x_9);
x_11 = l_option_get__or__else___main___rarg(x_8, x_9);
lean::inc(x_6);
x_13 = l_option_map___rarg(x_6, x_3);
x_14 = l_option_get__or__else___main___rarg(x_13, x_9);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command_strict__infer__modifier;
lean::inc(x_18);
x_20 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_20;
}
}
obj* _init_l_lean_parser_command_strict__infer__modifier_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_strict__infer__modifier_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_infer__modifier() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("infer_modifier");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_infer__modifier_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__2;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
lean::dec(x_2);
if (x_84 == 0)
{
obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_87 = l_lean_parser_command_strict__infer__modifier_has__view;
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::apply_1(x_88, x_1);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
else
{
obj* x_92; obj* x_93; obj* x_95; obj* x_96; 
x_92 = l_lean_parser_command_relaxed__infer__modifier_has__view;
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::apply_1(x_93, x_1);
x_96 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
}
}
}
obj* _init_l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_9 = l_lean_parser_command_strict__infer__modifier_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_0);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_14 = l_lean_parser_command_relaxed__infer__modifier_has__view;
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_0);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
obj* _init_l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("infer_modifier");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_infer__modifier_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_relaxed__infer__modifier_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_command_infer__modifier;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_command_strict__infer__modifier_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_lean_parser_command_infer__modifier;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
}
}
}
obj* _init_l_lean_parser_command_infer__modifier_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_infer__modifier_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_infer__modifier_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_51; 
x_0 = lean::mk_string("{");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("}");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::mk_string("(");
x_19 = l_string_trim(x_18);
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_19);
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_4);
lean::closure_set(x_23, 2, x_21);
x_24 = lean::mk_string(")");
x_25 = l_string_trim(x_24);
lean::inc(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_27, 0, x_25);
lean::inc(x_4);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_29, 0, x_25);
lean::closure_set(x_29, 1, x_4);
lean::closure_set(x_29, 2, x_27);
lean::inc(x_13);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_13);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_23);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__2), 5, 1);
lean::closure_set(x_33, 0, x_32);
lean::inc(x_13);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_13);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_17);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_4);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_13);
x_39 = l_lean_parser_command__parser__m_monad___closed__1;
x_40 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_41 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_42 = l_lean_parser_command__parser__m_alternative___closed__1;
x_43 = l_lean_parser_command_infer__modifier;
x_44 = l_lean_parser_command_infer__modifier_has__view;
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
x_51 = l_lean_parser_combinators_node_view___rarg(x_39, x_40, x_41, x_42, x_43, x_38, x_44);
return x_51;
}
}
obj* l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = l_lean_parser_command_relaxed__infer__modifier;
lean::inc(x_5);
x_7 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_5, x_0, x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
x_13 = l_lean_parser_parsec__t_try__mk__res___rarg(x_8);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
}
obj* l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = l_lean_parser_command_strict__infer__modifier;
lean::inc(x_5);
x_7 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_5, x_0, x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
x_13 = l_lean_parser_parsec__t_try__mk__res___rarg(x_8);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
}
obj* _init_l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_0 = lean::mk_string("{");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::mk_string("}");
lean::inc(x_1);
x_6 = l_lean_parser_symbol_tokens___rarg(x_4, x_1);
x_7 = lean::box(0);
lean::inc(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_6, x_7);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_3, x_9);
x_11 = l_lean_parser_tokens___rarg(x_10);
x_12 = l_lean_parser_tokens___rarg(x_11);
x_13 = lean::mk_string("(");
lean::inc(x_1);
x_15 = l_lean_parser_symbol_tokens___rarg(x_13, x_1);
x_16 = lean::mk_string(")");
x_17 = l_lean_parser_symbol_tokens___rarg(x_16, x_1);
lean::inc(x_7);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_17, x_7);
x_20 = l_lean_parser_list_cons_tokens___rarg(x_15, x_19);
x_21 = l_lean_parser_tokens___rarg(x_20);
x_22 = l_lean_parser_tokens___rarg(x_21);
lean::inc(x_7);
x_24 = l_lean_parser_list_cons_tokens___rarg(x_22, x_7);
x_25 = l_lean_parser_list_cons_tokens___rarg(x_12, x_24);
x_26 = l_lean_parser_tokens___rarg(x_25);
x_27 = l_lean_parser_list_cons_tokens___rarg(x_26, x_7);
x_28 = l_lean_parser_tokens___rarg(x_27);
return x_28;
}
}
obj* l_lean_parser_command_infer__modifier_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_infer__modifier;
x_5 = l_lean_parser_command_infer__modifier_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_infer__modifier_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_0 = lean::mk_string("{");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("}");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::mk_string("(");
x_19 = l_string_trim(x_18);
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_19);
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_23, 0, x_19);
lean::closure_set(x_23, 1, x_4);
lean::closure_set(x_23, 2, x_21);
x_24 = lean::mk_string(")");
x_25 = l_string_trim(x_24);
lean::inc(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_27, 0, x_25);
lean::inc(x_4);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_29, 0, x_25);
lean::closure_set(x_29, 1, x_4);
lean::closure_set(x_29, 2, x_27);
lean::inc(x_13);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_13);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_23);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser_lean_parser_has__view___lambda__2), 5, 1);
lean::closure_set(x_33, 0, x_32);
lean::inc(x_13);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_13);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_17);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_4);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_13);
return x_38;
}
}
obj* _init_l_lean_parser_command_intro__rule() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("intro_rule");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_intro__rule_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_intro__rule_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_intro__rule_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_1;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
lean::dec(x_1);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
switch (lean::obj_tag(x_33)) {
case 0:
{
obj* x_44; 
lean::dec(x_33);
x_44 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_44);
x_41 = x_44;
goto lbl_42;
}
case 1:
{
obj* x_46; 
x_46 = lean::cnstr_get(x_33, 0);
lean::inc(x_46);
lean::dec(x_33);
x_41 = x_46;
goto lbl_42;
}
case 2:
{
obj* x_50; 
lean::dec(x_33);
x_50 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_50);
x_41 = x_50;
goto lbl_42;
}
default:
{
obj* x_53; 
lean::dec(x_33);
x_53 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_53);
x_41 = x_53;
goto lbl_42;
}
}
lbl_42:
{
obj* x_55; obj* x_56; 
if (lean::obj_tag(x_32) == 0)
{
obj* x_58; 
x_58 = lean::box(3);
x_55 = x_32;
x_56 = x_58;
goto lbl_57;
}
else
{
obj* x_59; obj* x_61; 
x_59 = lean::cnstr_get(x_32, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_32, 1);
lean::inc(x_61);
lean::dec(x_32);
x_55 = x_61;
x_56 = x_59;
goto lbl_57;
}
lbl_57:
{
obj* x_64; 
x_64 = l_lean_parser_syntax_as__node___main(x_56);
if (lean::obj_tag(x_64) == 0)
{
lean::dec(x_64);
if (lean::obj_tag(x_55) == 0)
{
obj* x_67; obj* x_68; obj* x_71; 
lean::dec(x_55);
x_67 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
x_68 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_68);
lean::inc(x_67);
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_20);
lean::cnstr_set(x_71, 1, x_41);
lean::cnstr_set(x_71, 2, x_67);
lean::cnstr_set(x_71, 3, x_68);
return x_71;
}
else
{
obj* x_72; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_81; 
x_72 = lean::cnstr_get(x_55, 0);
lean::inc(x_72);
lean::dec(x_55);
x_75 = l_lean_parser_command_opt__decl__sig_has__view;
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::apply_1(x_76, x_72);
x_79 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_79);
x_81 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_81, 0, x_20);
lean::cnstr_set(x_81, 1, x_41);
lean::cnstr_set(x_81, 2, x_79);
lean::cnstr_set(x_81, 3, x_78);
return x_81;
}
}
else
{
obj* x_82; obj* x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_64, 0);
lean::inc(x_82);
if (lean::is_shared(x_64)) {
 lean::dec(x_64);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_64, 0);
 x_84 = x_64;
}
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
if (lean::obj_tag(x_85) == 0)
{
obj* x_90; 
lean::dec(x_84);
lean::dec(x_85);
x_90 = lean::box(0);
if (lean::obj_tag(x_55) == 0)
{
obj* x_92; obj* x_94; 
lean::dec(x_55);
x_92 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_94, 0, x_20);
lean::cnstr_set(x_94, 1, x_41);
lean::cnstr_set(x_94, 2, x_90);
lean::cnstr_set(x_94, 3, x_92);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_99; obj* x_101; obj* x_102; 
x_95 = lean::cnstr_get(x_55, 0);
lean::inc(x_95);
lean::dec(x_55);
x_98 = l_lean_parser_command_opt__decl__sig_has__view;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::apply_1(x_99, x_95);
x_102 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_102, 0, x_20);
lean::cnstr_set(x_102, 1, x_41);
lean::cnstr_set(x_102, 2, x_90);
lean::cnstr_set(x_102, 3, x_101);
return x_102;
}
}
else
{
obj* x_103; obj* x_105; 
x_103 = lean::cnstr_get(x_85, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_85, 1);
lean::inc(x_105);
lean::dec(x_85);
if (lean::obj_tag(x_105) == 0)
{
obj* x_109; obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_105);
x_109 = l_lean_parser_command_infer__modifier_has__view;
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::apply_1(x_110, x_103);
if (lean::is_scalar(x_84)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_84;
}
lean::cnstr_set(x_113, 0, x_112);
if (lean::obj_tag(x_55) == 0)
{
obj* x_115; obj* x_117; 
lean::dec(x_55);
x_115 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_115);
x_117 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_117, 0, x_20);
lean::cnstr_set(x_117, 1, x_41);
lean::cnstr_set(x_117, 2, x_113);
lean::cnstr_set(x_117, 3, x_115);
return x_117;
}
else
{
obj* x_118; obj* x_121; obj* x_122; obj* x_124; obj* x_125; 
x_118 = lean::cnstr_get(x_55, 0);
lean::inc(x_118);
lean::dec(x_55);
x_121 = l_lean_parser_command_opt__decl__sig_has__view;
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::apply_1(x_122, x_118);
x_125 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_125, 0, x_20);
lean::cnstr_set(x_125, 1, x_41);
lean::cnstr_set(x_125, 2, x_113);
lean::cnstr_set(x_125, 3, x_124);
return x_125;
}
}
else
{
lean::dec(x_84);
lean::dec(x_103);
lean::dec(x_105);
if (lean::obj_tag(x_55) == 0)
{
obj* x_130; obj* x_131; obj* x_134; 
lean::dec(x_55);
x_130 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
x_131 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_131);
lean::inc(x_130);
x_134 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_134, 0, x_20);
lean::cnstr_set(x_134, 1, x_41);
lean::cnstr_set(x_134, 2, x_130);
lean::cnstr_set(x_134, 3, x_131);
return x_134;
}
else
{
obj* x_135; obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_144; 
x_135 = lean::cnstr_get(x_55, 0);
lean::inc(x_135);
lean::dec(x_55);
x_138 = l_lean_parser_command_opt__decl__sig_has__view;
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::apply_1(x_139, x_135);
x_142 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_142);
x_144 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_144, 0, x_20);
lean::cnstr_set(x_144, 1, x_41);
lean::cnstr_set(x_144, 2, x_142);
lean::cnstr_set(x_144, 3, x_141);
return x_144;
}
}
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_infer__modifier_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_opt__decl__sig_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = lean::box(3);
x_17 = x_0;
x_18 = x_20;
goto lbl_19;
}
else
{
obj* x_21; obj* x_23; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
x_17 = x_23;
x_18 = x_21;
goto lbl_19;
}
lbl_19:
{
obj* x_26; 
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_29; 
lean::dec(x_18);
x_29 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_29);
x_26 = x_29;
goto lbl_27;
}
case 1:
{
obj* x_31; 
x_31 = lean::cnstr_get(x_18, 0);
lean::inc(x_31);
lean::dec(x_18);
x_26 = x_31;
goto lbl_27;
}
case 2:
{
obj* x_35; 
lean::dec(x_18);
x_35 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_35);
x_26 = x_35;
goto lbl_27;
}
default:
{
obj* x_38; 
lean::dec(x_18);
x_38 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_38);
x_26 = x_38;
goto lbl_27;
}
}
lbl_27:
{
obj* x_40; obj* x_41; 
if (lean::obj_tag(x_17) == 0)
{
obj* x_43; 
x_43 = lean::box(3);
x_40 = x_17;
x_41 = x_43;
goto lbl_42;
}
else
{
obj* x_44; obj* x_46; 
x_44 = lean::cnstr_get(x_17, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_17, 1);
lean::inc(x_46);
lean::dec(x_17);
x_40 = x_46;
x_41 = x_44;
goto lbl_42;
}
lbl_42:
{
obj* x_49; 
x_49 = l_lean_parser_syntax_as__node___main(x_41);
if (lean::obj_tag(x_49) == 0)
{
lean::dec(x_49);
if (lean::obj_tag(x_40) == 0)
{
obj* x_52; obj* x_53; obj* x_56; 
lean::dec(x_40);
x_52 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
x_53 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_53);
lean::inc(x_52);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_5);
lean::cnstr_set(x_56, 1, x_26);
lean::cnstr_set(x_56, 2, x_52);
lean::cnstr_set(x_56, 3, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_66; 
x_57 = lean::cnstr_get(x_40, 0);
lean::inc(x_57);
lean::dec(x_40);
x_60 = l_lean_parser_command_opt__decl__sig_has__view;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::apply_1(x_61, x_57);
x_64 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_66, 0, x_5);
lean::cnstr_set(x_66, 1, x_26);
lean::cnstr_set(x_66, 2, x_64);
lean::cnstr_set(x_66, 3, x_63);
return x_66;
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_49, 0);
lean::inc(x_67);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 x_69 = x_49;
}
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; 
lean::dec(x_69);
lean::dec(x_70);
x_75 = lean::box(0);
if (lean::obj_tag(x_40) == 0)
{
obj* x_77; obj* x_79; 
lean::dec(x_40);
x_77 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_79, 0, x_5);
lean::cnstr_set(x_79, 1, x_26);
lean::cnstr_set(x_79, 2, x_75);
lean::cnstr_set(x_79, 3, x_77);
return x_79;
}
else
{
obj* x_80; obj* x_83; obj* x_84; obj* x_86; obj* x_87; 
x_80 = lean::cnstr_get(x_40, 0);
lean::inc(x_80);
lean::dec(x_40);
x_83 = l_lean_parser_command_opt__decl__sig_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::apply_1(x_84, x_80);
x_87 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_87, 0, x_5);
lean::cnstr_set(x_87, 1, x_26);
lean::cnstr_set(x_87, 2, x_75);
lean::cnstr_set(x_87, 3, x_86);
return x_87;
}
}
else
{
obj* x_88; obj* x_90; 
x_88 = lean::cnstr_get(x_70, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_70, 1);
lean::inc(x_90);
lean::dec(x_70);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_90);
x_94 = l_lean_parser_command_infer__modifier_has__view;
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::apply_1(x_95, x_88);
if (lean::is_scalar(x_69)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_69;
}
lean::cnstr_set(x_98, 0, x_97);
if (lean::obj_tag(x_40) == 0)
{
obj* x_100; obj* x_102; 
lean::dec(x_40);
x_100 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_100);
x_102 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_102, 0, x_5);
lean::cnstr_set(x_102, 1, x_26);
lean::cnstr_set(x_102, 2, x_98);
lean::cnstr_set(x_102, 3, x_100);
return x_102;
}
else
{
obj* x_103; obj* x_106; obj* x_107; obj* x_109; obj* x_110; 
x_103 = lean::cnstr_get(x_40, 0);
lean::inc(x_103);
lean::dec(x_40);
x_106 = l_lean_parser_command_opt__decl__sig_has__view;
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::apply_1(x_107, x_103);
x_110 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_110, 0, x_5);
lean::cnstr_set(x_110, 1, x_26);
lean::cnstr_set(x_110, 2, x_98);
lean::cnstr_set(x_110, 3, x_109);
return x_110;
}
}
else
{
lean::dec(x_69);
lean::dec(x_88);
lean::dec(x_90);
if (lean::obj_tag(x_40) == 0)
{
obj* x_115; obj* x_116; obj* x_119; 
lean::dec(x_40);
x_115 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
x_116 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_116);
lean::inc(x_115);
x_119 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_119, 0, x_5);
lean::cnstr_set(x_119, 1, x_26);
lean::cnstr_set(x_119, 2, x_115);
lean::cnstr_set(x_119, 3, x_116);
return x_119;
}
else
{
obj* x_120; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_129; 
x_120 = lean::cnstr_get(x_40, 0);
lean::inc(x_120);
lean::dec(x_40);
x_123 = l_lean_parser_command_opt__decl__sig_has__view;
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_126 = lean::apply_1(x_124, x_120);
x_127 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_127);
x_129 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_129, 0, x_5);
lean::cnstr_set(x_129, 1, x_26);
lean::cnstr_set(x_129, 2, x_127);
lean::cnstr_set(x_129, 3, x_126);
return x_129;
}
}
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_intro__rule_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_1);
x_13 = lean::box(3);
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_3);
x_16 = l_lean_parser_command_opt__decl__sig_has__view;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_7);
x_20 = lean::box(0);
lean::inc(x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
if (lean::obj_tag(x_5) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_5);
lean::dec(x_20);
x_25 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_22);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_14);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_command_intro__rule;
lean::inc(x_30);
x_32 = l_lean_parser_syntax_mk__node(x_30, x_29);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; 
x_33 = lean::cnstr_get(x_5, 0);
lean::inc(x_33);
lean::dec(x_5);
x_36 = l_lean_parser_command_infer__modifier_has__view;
x_37 = lean::cnstr_get(x_36, 1);
lean::inc(x_37);
x_39 = lean::apply_1(x_37, x_33);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_20);
x_41 = l_lean_parser_no__kind;
lean::inc(x_41);
x_43 = l_lean_parser_syntax_mk__node(x_41, x_40);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_22);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_15);
lean::cnstr_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_14);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_parser_command_intro__rule;
lean::inc(x_47);
x_49 = l_lean_parser_syntax_mk__node(x_47, x_46);
return x_49;
}
}
}
obj* _init_l_lean_parser_command_intro__rule_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_intro__rule_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_5);
x_10 = l_lean_parser_token(x_5, x_2, x_3);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
}
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_27; 
lean::dec(x_16);
lean::dec(x_22);
x_27 = lean::box(0);
x_23 = x_27;
goto lbl_24;
}
case 1:
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_15);
lean::dec(x_5);
lean::dec(x_2);
x_31 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_31);
if (lean::is_scalar(x_22)) {
 x_33 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_33 = x_22;
}
lean::cnstr_set(x_33, 0, x_16);
lean::cnstr_set(x_33, 1, x_18);
lean::cnstr_set(x_33, 2, x_31);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_33);
lean::inc(x_31);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_34);
x_37 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
lean::inc(x_37);
x_39 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_36, x_37);
x_40 = l_lean_parser_parsec__t_try__mk__res___rarg(x_39);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_13);
return x_41;
}
case 2:
{
obj* x_44; 
lean::dec(x_16);
lean::dec(x_22);
x_44 = lean::box(0);
x_23 = x_44;
goto lbl_24;
}
default:
{
obj* x_47; 
lean::dec(x_16);
lean::dec(x_22);
x_47 = lean::box(0);
x_23 = x_47;
goto lbl_24;
}
}
lbl_24:
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_23);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_2);
x_50 = lean::box(0);
x_51 = l_string_join___closed__1;
x_52 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
lean::inc(x_52);
lean::inc(x_51);
x_55 = l_lean_parser_monad__parsec_error___at___private_409789351__finish__comment__block__aux___main___spec__1___rarg(x_51, x_52, x_49, x_50, x_5, x_18, x_13);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_56);
x_62 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_62);
x_64 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_61);
lean::inc(x_52);
x_66 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_64, x_52);
x_67 = l_lean_parser_parsec__t_try__mk__res___rarg(x_66);
if (lean::is_scalar(x_15)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_15;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_58);
return x_68;
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_5);
lean::dec(x_2);
x_71 = lean::cnstr_get(x_11, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_74 = x_11;
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_76);
x_80 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
lean::inc(x_80);
x_82 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_79, x_80);
x_83 = l_lean_parser_parsec__t_try__mk__res___rarg(x_82);
if (lean::is_scalar(x_15)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_15;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_13);
return x_84;
}
}
}
obj* _init_l_lean_parser_command_intro__rule_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_27; 
x_0 = lean::mk_string("|");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_lean_parser_command__parser__m_monad___closed__1;
x_16 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_17 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_18 = l_lean_parser_command__parser__m_alternative___closed__1;
x_19 = l_lean_parser_command_intro__rule;
x_20 = l_lean_parser_command_intro__rule_has__view;
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
x_27 = l_lean_parser_combinators_node_view___rarg(x_15, x_16, x_17, x_18, x_19, x_14, x_20);
return x_27;
}
}
obj* _init_l_lean_parser_command_intro__rule_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::mk_string("|");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens;
lean::inc(x_4);
x_6 = l_lean_parser_tokens___rarg(x_4);
x_7 = l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens;
lean::inc(x_3);
lean::inc(x_7);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_7, x_3);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_6, x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_3, x_11);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_2, x_12);
x_14 = l_lean_parser_tokens___rarg(x_13);
return x_14;
}
}
obj* l_lean_parser_command_intro__rule_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_intro__rule;
x_5 = l_lean_parser_command_intro__rule_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_intro__rule_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::mk_string("|");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* _init_l_lean_parser_command_struct__binder__content() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_binder_content");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_10; obj* x_12; 
lean::dec(x_3);
x_10 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_10);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
case 1:
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
case 2:
{
obj* x_18; obj* x_20; 
lean::dec(x_3);
x_18 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_18);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_8);
return x_20;
}
default:
{
obj* x_22; obj* x_24; 
lean::dec(x_3);
x_22 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_22);
if (lean::is_scalar(x_7)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_7;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_8);
return x_24;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_struct__binder__content_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_22; 
x_22 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; 
lean::dec(x_22);
x_24 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_24);
x_20 = x_24;
goto lbl_21;
}
else
{
obj* x_26; obj* x_29; obj* x_32; 
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__1(x_29);
x_20 = x_32;
goto lbl_21;
}
lbl_21:
{
obj* x_33; obj* x_34; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_36; 
x_36 = lean::box(3);
x_33 = x_1;
x_34 = x_36;
goto lbl_35;
}
else
{
obj* x_37; obj* x_39; 
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 1);
lean::inc(x_39);
lean::dec(x_1);
x_33 = x_39;
x_34 = x_37;
goto lbl_35;
}
lbl_35:
{
obj* x_42; obj* x_44; 
x_44 = l_lean_parser_syntax_as__node___main(x_34);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; 
lean::dec(x_44);
x_46 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_46);
x_42 = x_46;
goto lbl_43;
}
else
{
obj* x_48; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
if (lean::is_shared(x_44)) {
 lean::dec(x_44);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_44, 0);
 x_50 = x_44;
}
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
if (lean::obj_tag(x_51) == 0)
{
obj* x_56; 
lean::dec(x_50);
lean::dec(x_51);
x_56 = lean::box(0);
x_42 = x_56;
goto lbl_43;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_51, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_51, 1);
lean::inc(x_59);
lean::dec(x_51);
if (lean::obj_tag(x_59) == 0)
{
obj* x_63; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_59);
x_63 = l_lean_parser_command_infer__modifier_has__view;
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::apply_1(x_64, x_57);
if (lean::is_scalar(x_50)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_50;
}
lean::cnstr_set(x_67, 0, x_66);
x_42 = x_67;
goto lbl_43;
}
else
{
obj* x_71; 
lean::dec(x_57);
lean::dec(x_59);
lean::dec(x_50);
x_71 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_71);
x_42 = x_71;
goto lbl_43;
}
}
}
lbl_43:
{
obj* x_73; obj* x_74; 
if (lean::obj_tag(x_33) == 0)
{
obj* x_76; 
x_76 = lean::box(3);
x_73 = x_33;
x_74 = x_76;
goto lbl_75;
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_33, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_33, 1);
lean::inc(x_79);
lean::dec(x_33);
x_73 = x_79;
x_74 = x_77;
goto lbl_75;
}
lbl_75:
{
obj* x_82; obj* x_83; obj* x_85; 
x_82 = l_lean_parser_command_opt__decl__sig_has__view;
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::apply_1(x_83, x_74);
if (lean::obj_tag(x_73) == 0)
{
obj* x_87; obj* x_88; 
lean::dec(x_73);
x_87 = lean::box(3);
x_88 = l_lean_parser_syntax_as__node___main(x_87);
if (lean::obj_tag(x_88) == 0)
{
obj* x_90; obj* x_92; 
lean::dec(x_88);
x_90 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_90);
x_92 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_92, 0, x_20);
lean::cnstr_set(x_92, 1, x_42);
lean::cnstr_set(x_92, 2, x_85);
lean::cnstr_set(x_92, 3, x_90);
return x_92;
}
else
{
obj* x_93; obj* x_95; obj* x_96; 
x_93 = lean::cnstr_get(x_88, 0);
lean::inc(x_93);
if (lean::is_shared(x_88)) {
 lean::dec(x_88);
 x_95 = lean::box(0);
} else {
 lean::cnstr_release(x_88, 0);
 x_95 = x_88;
}
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_101; obj* x_102; 
lean::dec(x_95);
lean::dec(x_96);
x_101 = lean::box(0);
x_102 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_102, 0, x_20);
lean::cnstr_set(x_102, 1, x_42);
lean::cnstr_set(x_102, 2, x_85);
lean::cnstr_set(x_102, 3, x_101);
return x_102;
}
else
{
obj* x_103; obj* x_105; 
x_103 = lean::cnstr_get(x_96, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_96, 1);
lean::inc(x_105);
lean::dec(x_96);
if (lean::obj_tag(x_105) == 0)
{
obj* x_109; obj* x_110; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_105);
x_109 = l_lean_parser_term_binder__default_has__view;
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::apply_1(x_110, x_103);
if (lean::is_scalar(x_95)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_95;
}
lean::cnstr_set(x_113, 0, x_112);
x_114 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_114, 0, x_20);
lean::cnstr_set(x_114, 1, x_42);
lean::cnstr_set(x_114, 2, x_85);
lean::cnstr_set(x_114, 3, x_113);
return x_114;
}
else
{
obj* x_118; obj* x_120; 
lean::dec(x_103);
lean::dec(x_105);
lean::dec(x_95);
x_118 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_118);
x_120 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_120, 0, x_20);
lean::cnstr_set(x_120, 1, x_42);
lean::cnstr_set(x_120, 2, x_85);
lean::cnstr_set(x_120, 3, x_118);
return x_120;
}
}
}
}
else
{
obj* x_121; obj* x_124; 
x_121 = lean::cnstr_get(x_73, 0);
lean::inc(x_121);
lean::dec(x_73);
x_124 = l_lean_parser_syntax_as__node___main(x_121);
if (lean::obj_tag(x_124) == 0)
{
obj* x_126; obj* x_128; 
lean::dec(x_124);
x_126 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_126);
x_128 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_128, 0, x_20);
lean::cnstr_set(x_128, 1, x_42);
lean::cnstr_set(x_128, 2, x_85);
lean::cnstr_set(x_128, 3, x_126);
return x_128;
}
else
{
obj* x_129; obj* x_131; obj* x_132; 
x_129 = lean::cnstr_get(x_124, 0);
lean::inc(x_129);
if (lean::is_shared(x_124)) {
 lean::dec(x_124);
 x_131 = lean::box(0);
} else {
 lean::cnstr_release(x_124, 0);
 x_131 = x_124;
}
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
lean::dec(x_129);
if (lean::obj_tag(x_132) == 0)
{
obj* x_137; obj* x_138; 
lean::dec(x_132);
lean::dec(x_131);
x_137 = lean::box(0);
x_138 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_138, 0, x_20);
lean::cnstr_set(x_138, 1, x_42);
lean::cnstr_set(x_138, 2, x_85);
lean::cnstr_set(x_138, 3, x_137);
return x_138;
}
else
{
obj* x_139; obj* x_141; 
x_139 = lean::cnstr_get(x_132, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_132, 1);
lean::inc(x_141);
lean::dec(x_132);
if (lean::obj_tag(x_141) == 0)
{
obj* x_145; obj* x_146; obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_141);
x_145 = l_lean_parser_term_binder__default_has__view;
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
x_148 = lean::apply_1(x_146, x_139);
if (lean::is_scalar(x_131)) {
 x_149 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_149 = x_131;
}
lean::cnstr_set(x_149, 0, x_148);
x_150 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_150, 0, x_20);
lean::cnstr_set(x_150, 1, x_42);
lean::cnstr_set(x_150, 2, x_85);
lean::cnstr_set(x_150, 3, x_149);
return x_150;
}
else
{
obj* x_154; obj* x_156; 
lean::dec(x_139);
lean::dec(x_131);
lean::dec(x_141);
x_154 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_154);
x_156 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_156, 0, x_20);
lean::cnstr_set(x_156, 1, x_42);
lean::cnstr_set(x_156, 2, x_85);
lean::cnstr_set(x_156, 3, x_154);
return x_156;
}
}
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_1);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* _init_l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_7; 
x_7 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_9);
x_5 = x_9;
goto lbl_6;
}
else
{
obj* x_11; obj* x_14; obj* x_17; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__1(x_14);
x_5 = x_17;
goto lbl_6;
}
lbl_6:
{
obj* x_18; obj* x_19; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_21; 
x_21 = lean::box(3);
x_18 = x_0;
x_19 = x_21;
goto lbl_20;
}
else
{
obj* x_22; obj* x_24; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::dec(x_0);
x_18 = x_24;
x_19 = x_22;
goto lbl_20;
}
lbl_20:
{
obj* x_27; obj* x_29; 
x_29 = l_lean_parser_syntax_as__node___main(x_19);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; 
lean::dec(x_29);
x_31 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_31);
x_27 = x_31;
goto lbl_28;
}
else
{
obj* x_33; obj* x_35; obj* x_36; 
x_33 = lean::cnstr_get(x_29, 0);
lean::inc(x_33);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_35 = x_29;
}
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
if (lean::obj_tag(x_36) == 0)
{
obj* x_41; 
lean::dec(x_35);
lean::dec(x_36);
x_41 = lean::box(0);
x_27 = x_41;
goto lbl_28;
}
else
{
obj* x_42; obj* x_44; 
x_42 = lean::cnstr_get(x_36, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_36, 1);
lean::inc(x_44);
lean::dec(x_36);
if (lean::obj_tag(x_44) == 0)
{
obj* x_48; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_44);
x_48 = l_lean_parser_command_infer__modifier_has__view;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::apply_1(x_49, x_42);
if (lean::is_scalar(x_35)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_35;
}
lean::cnstr_set(x_52, 0, x_51);
x_27 = x_52;
goto lbl_28;
}
else
{
obj* x_56; 
lean::dec(x_35);
lean::dec(x_42);
lean::dec(x_44);
x_56 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
x_27 = x_56;
goto lbl_28;
}
}
}
lbl_28:
{
obj* x_58; obj* x_59; 
if (lean::obj_tag(x_18) == 0)
{
obj* x_61; 
x_61 = lean::box(3);
x_58 = x_18;
x_59 = x_61;
goto lbl_60;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_18, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_18, 1);
lean::inc(x_64);
lean::dec(x_18);
x_58 = x_64;
x_59 = x_62;
goto lbl_60;
}
lbl_60:
{
obj* x_67; obj* x_68; obj* x_70; 
x_67 = l_lean_parser_command_opt__decl__sig_has__view;
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::apply_1(x_68, x_59);
if (lean::obj_tag(x_58) == 0)
{
obj* x_72; obj* x_73; 
lean::dec(x_58);
x_72 = lean::box(3);
x_73 = l_lean_parser_syntax_as__node___main(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_75; obj* x_77; 
lean::dec(x_73);
x_75 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_77, 0, x_5);
lean::cnstr_set(x_77, 1, x_27);
lean::cnstr_set(x_77, 2, x_70);
lean::cnstr_set(x_77, 3, x_75);
return x_77;
}
else
{
obj* x_78; obj* x_80; obj* x_81; 
x_78 = lean::cnstr_get(x_73, 0);
lean::inc(x_78);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_80 = x_73;
}
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_81) == 0)
{
obj* x_86; obj* x_87; 
lean::dec(x_81);
lean::dec(x_80);
x_86 = lean::box(0);
x_87 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_87, 0, x_5);
lean::cnstr_set(x_87, 1, x_27);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
return x_87;
}
else
{
obj* x_88; obj* x_90; 
x_88 = lean::cnstr_get(x_81, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_81, 1);
lean::inc(x_90);
lean::dec(x_81);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_90);
x_94 = l_lean_parser_term_binder__default_has__view;
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::apply_1(x_95, x_88);
if (lean::is_scalar(x_80)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_80;
}
lean::cnstr_set(x_98, 0, x_97);
x_99 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_99, 0, x_5);
lean::cnstr_set(x_99, 1, x_27);
lean::cnstr_set(x_99, 2, x_70);
lean::cnstr_set(x_99, 3, x_98);
return x_99;
}
else
{
obj* x_103; obj* x_105; 
lean::dec(x_88);
lean::dec(x_90);
lean::dec(x_80);
x_103 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_103);
x_105 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_105, 0, x_5);
lean::cnstr_set(x_105, 1, x_27);
lean::cnstr_set(x_105, 2, x_70);
lean::cnstr_set(x_105, 3, x_103);
return x_105;
}
}
}
}
else
{
obj* x_106; obj* x_109; 
x_106 = lean::cnstr_get(x_58, 0);
lean::inc(x_106);
lean::dec(x_58);
x_109 = l_lean_parser_syntax_as__node___main(x_106);
if (lean::obj_tag(x_109) == 0)
{
obj* x_111; obj* x_113; 
lean::dec(x_109);
x_111 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_111);
x_113 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_113, 0, x_5);
lean::cnstr_set(x_113, 1, x_27);
lean::cnstr_set(x_113, 2, x_70);
lean::cnstr_set(x_113, 3, x_111);
return x_113;
}
else
{
obj* x_114; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_109, 0);
lean::inc(x_114);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 x_116 = x_109;
}
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
if (lean::obj_tag(x_117) == 0)
{
obj* x_122; obj* x_123; 
lean::dec(x_116);
lean::dec(x_117);
x_122 = lean::box(0);
x_123 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_123, 0, x_5);
lean::cnstr_set(x_123, 1, x_27);
lean::cnstr_set(x_123, 2, x_70);
lean::cnstr_set(x_123, 3, x_122);
return x_123;
}
else
{
obj* x_124; obj* x_126; 
x_124 = lean::cnstr_get(x_117, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_117, 1);
lean::inc(x_126);
lean::dec(x_117);
if (lean::obj_tag(x_126) == 0)
{
obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_126);
x_130 = l_lean_parser_term_binder__default_has__view;
x_131 = lean::cnstr_get(x_130, 0);
lean::inc(x_131);
x_133 = lean::apply_1(x_131, x_124);
if (lean::is_scalar(x_116)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_116;
}
lean::cnstr_set(x_134, 0, x_133);
x_135 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_135, 0, x_5);
lean::cnstr_set(x_135, 1, x_27);
lean::cnstr_set(x_135, 2, x_70);
lean::cnstr_set(x_135, 3, x_134);
return x_135;
}
else
{
obj* x_139; obj* x_141; 
lean::dec(x_116);
lean::dec(x_124);
lean::dec(x_126);
x_139 = l_lean_parser_term_binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_139);
x_141 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_141, 0, x_5);
lean::cnstr_set(x_141, 1, x_27);
lean::cnstr_set(x_141, 2, x_70);
lean::cnstr_set(x_141, 3, x_139);
return x_141;
}
}
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_list_map___main___at_lean_parser_command_struct__binder__content_has__view_x_27___spec__2(x_1);
x_11 = l_lean_parser_no__kind;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = l_lean_parser_command_opt__decl__sig_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_5);
x_18 = lean::box(0);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; 
lean::dec(x_18);
lean::dec(x_7);
x_22 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_17);
lean::cnstr_set(x_24, 1, x_22);
x_25 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_13);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_lean_parser_command_struct__binder__content;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
return x_31;
}
else
{
obj* x_32; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; 
x_32 = lean::cnstr_get(x_7, 0);
lean::inc(x_32);
lean::dec(x_7);
x_35 = l_lean_parser_term_binder__default_has__view;
x_36 = lean::cnstr_get(x_35, 1);
lean::inc(x_36);
x_38 = lean::apply_1(x_36, x_32);
lean::inc(x_18);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_18);
lean::inc(x_11);
x_42 = l_lean_parser_syntax_mk__node(x_11, x_40);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_18);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_17);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_44);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_13);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_lean_parser_command_struct__binder__content;
lean::inc(x_49);
x_51 = l_lean_parser_syntax_mk__node(x_49, x_48);
return x_51;
}
}
else
{
obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_62; 
x_52 = lean::cnstr_get(x_3, 0);
lean::inc(x_52);
lean::dec(x_3);
x_55 = l_lean_parser_command_infer__modifier_has__view;
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::apply_1(x_56, x_52);
lean::inc(x_18);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_18);
lean::inc(x_11);
x_62 = l_lean_parser_syntax_mk__node(x_11, x_60);
if (lean::obj_tag(x_7) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_18);
lean::dec(x_7);
x_65 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_17);
lean::cnstr_set(x_67, 1, x_65);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_62);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_13);
lean::cnstr_set(x_69, 1, x_68);
x_70 = l_lean_parser_command_struct__binder__content;
lean::inc(x_70);
x_72 = l_lean_parser_syntax_mk__node(x_70, x_69);
return x_72;
}
else
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_90; 
x_73 = lean::cnstr_get(x_7, 0);
lean::inc(x_73);
lean::dec(x_7);
x_76 = l_lean_parser_term_binder__default_has__view;
x_77 = lean::cnstr_get(x_76, 1);
lean::inc(x_77);
x_79 = lean::apply_1(x_77, x_73);
lean::inc(x_18);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_18);
lean::inc(x_11);
x_83 = l_lean_parser_syntax_mk__node(x_11, x_81);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_18);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_17);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_62);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_13);
lean::cnstr_set(x_87, 1, x_86);
x_88 = l_lean_parser_command_struct__binder__content;
lean::inc(x_88);
x_90 = l_lean_parser_syntax_mk__node(x_88, x_87);
return x_90;
}
}
}
}
obj* _init_l_lean_parser_command_struct__binder__content_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_struct__binder__content_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_struct__binder__content_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_25; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_binder__default_parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_lean_parser_command__parser__m_monad___closed__1;
x_14 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_15 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_16 = l_lean_parser_command__parser__m_alternative___closed__1;
x_17 = l_lean_parser_command_struct__binder__content;
x_18 = l_lean_parser_command_struct__binder__content_has__view;
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
x_25 = l_lean_parser_combinators_node_view___rarg(x_13, x_14, x_15, x_16, x_17, x_12, x_18);
return x_25;
}
}
obj* _init_l_lean_parser_command_struct__binder__content_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_lean_parser_term_binder__default_parser_lean_parser_has__tokens;
lean::inc(x_6);
x_8 = l_lean_parser_tokens___rarg(x_6);
x_9 = l_lean_parser_tokens___rarg(x_8);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_9, x_0);
x_11 = l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens;
lean::inc(x_11);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_11, x_10);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_5, x_13);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_2, x_14);
x_16 = l_lean_parser_tokens___rarg(x_15);
return x_16;
}
}
obj* l_lean_parser_command_struct__binder__content_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_struct__binder__content;
x_5 = l_lean_parser_command_struct__binder__content_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_struct__binder__content_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_binder__default_parser), 5, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder__content() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_explicit_binder_content");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder__content_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__2;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
lean::dec(x_2);
if (x_84 == 0)
{
obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_87 = l_lean_parser_command_struct__binder__content_has__view;
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::apply_1(x_88, x_1);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
else
{
obj* x_92; obj* x_93; obj* x_95; obj* x_96; 
x_92 = l_lean_parser_command_notation__like_has__view;
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::apply_1(x_93, x_1);
x_96 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
}
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_9 = l_lean_parser_command_struct__binder__content_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_0);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_14 = l_lean_parser_command_notation__like_has__view;
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_0);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_explicit_binder_content");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_notation__like_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_command_struct__explicit__binder__content;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_command_struct__binder__content_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_lean_parser_command_struct__explicit__binder__content;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
}
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder__content_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_struct__explicit__binder__content_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_explicit_binder");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__2;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_5 = x_15;
x_6 = x_18;
goto lbl_7;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_5 = x_21;
x_6 = x_19;
goto lbl_7;
}
}
lbl_4:
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l_lean_parser_command_struct__explicit__binder__content_has__view;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_3);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
lean::dec(x_3);
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_34; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_27);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
case 1:
{
obj* x_40; obj* x_41; 
lean::dec(x_31);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_27);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
case 2:
{
obj* x_43; obj* x_44; 
lean::dec(x_31);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_27);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
default:
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_27);
lean::cnstr_set(x_47, 2, x_46);
return x_47;
}
}
}
}
lbl_7:
{
obj* x_48; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_53;
goto lbl_49;
}
else
{
obj* x_54; obj* x_56; 
x_54 = lean::cnstr_get(x_5, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_5, 1);
lean::inc(x_56);
lean::dec(x_5);
x_1 = x_53;
x_2 = x_54;
x_3 = x_56;
goto lbl_4;
}
}
case 1:
{
obj* x_60; 
lean::dec(x_6);
x_60 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_60;
goto lbl_49;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_5, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_5, 1);
lean::inc(x_63);
lean::dec(x_5);
x_1 = x_60;
x_2 = x_61;
x_3 = x_63;
goto lbl_4;
}
}
case 2:
{
obj* x_67; 
lean::dec(x_6);
x_67 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_67;
goto lbl_49;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_5, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_5, 1);
lean::inc(x_70);
lean::dec(x_5);
x_1 = x_67;
x_2 = x_68;
x_3 = x_70;
goto lbl_4;
}
}
default:
{
obj* x_74; 
lean::dec(x_6);
x_74 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_74;
goto lbl_49;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_5, 1);
lean::inc(x_77);
lean::dec(x_5);
x_1 = x_74;
x_2 = x_75;
x_3 = x_77;
goto lbl_4;
}
}
}
lbl_49:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_5);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_48);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
else
{
obj* x_85; 
x_85 = lean::cnstr_get(x_5, 0);
lean::inc(x_85);
lean::dec(x_5);
switch (lean::obj_tag(x_85)) {
case 0:
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; 
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
x_92 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_48);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
case 1:
{
obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_85);
x_96 = lean::box(0);
x_97 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_48);
lean::cnstr_set(x_99, 1, x_97);
lean::cnstr_set(x_99, 2, x_96);
return x_99;
}
case 2:
{
obj* x_101; obj* x_102; obj* x_104; 
lean::dec(x_85);
x_101 = lean::box(0);
x_102 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
x_104 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_104, 0, x_48);
lean::cnstr_set(x_104, 1, x_102);
lean::cnstr_set(x_104, 2, x_101);
return x_104;
}
default:
{
obj* x_106; obj* x_107; obj* x_109; 
lean::dec(x_85);
x_106 = lean::box(0);
x_107 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_109, 0, x_48);
lean::cnstr_set(x_109, 1, x_107);
lean::cnstr_set(x_109, 2, x_106);
return x_109;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_struct__explicit__binder__content_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::box(3);
x_4 = x_7;
x_5 = x_8;
goto lbl_6;
lbl_3:
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = l_lean_parser_command_struct__explicit__binder__content_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_12);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
case 1:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_0);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
case 2:
{
obj* x_28; obj* x_29; 
lean::dec(x_16);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_12);
lean::cnstr_set(x_29, 2, x_28);
return x_29;
}
default:
{
obj* x_31; obj* x_32; 
lean::dec(x_16);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_0);
lean::cnstr_set(x_32, 1, x_12);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
}
}
}
lbl_6:
{
obj* x_33; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_5, 0);
lean::inc(x_35);
lean::dec(x_5);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_35);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_38;
goto lbl_34;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_4, 1);
lean::inc(x_41);
lean::dec(x_4);
x_0 = x_38;
x_1 = x_39;
x_2 = x_41;
goto lbl_3;
}
}
case 1:
{
obj* x_45; 
lean::dec(x_5);
x_45 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_45;
goto lbl_34;
}
else
{
obj* x_46; obj* x_48; 
x_46 = lean::cnstr_get(x_4, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_4, 1);
lean::inc(x_48);
lean::dec(x_4);
x_0 = x_45;
x_1 = x_46;
x_2 = x_48;
goto lbl_3;
}
}
case 2:
{
obj* x_52; 
lean::dec(x_5);
x_52 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_52;
goto lbl_34;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_4, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_4, 1);
lean::inc(x_55);
lean::dec(x_4);
x_0 = x_52;
x_1 = x_53;
x_2 = x_55;
goto lbl_3;
}
}
default:
{
obj* x_59; 
lean::dec(x_5);
x_59 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_59;
goto lbl_34;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_4, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_4, 1);
lean::inc(x_62);
lean::dec(x_4);
x_0 = x_59;
x_1 = x_60;
x_2 = x_62;
goto lbl_3;
}
}
}
lbl_34:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_66; obj* x_67; obj* x_69; 
lean::dec(x_4);
x_66 = lean::box(0);
x_67 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_69, 0, x_33);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set(x_69, 2, x_66);
return x_69;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_4, 0);
lean::inc(x_70);
lean::dec(x_4);
switch (lean::obj_tag(x_70)) {
case 0:
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
lean::dec(x_70);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_73);
x_77 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_33);
lean::cnstr_set(x_79, 1, x_77);
lean::cnstr_set(x_79, 2, x_76);
return x_79;
}
case 1:
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_70);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_33);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
case 2:
{
obj* x_86; obj* x_87; obj* x_89; 
lean::dec(x_70);
x_86 = lean::box(0);
x_87 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_87);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_33);
lean::cnstr_set(x_89, 1, x_87);
lean::cnstr_set(x_89, 2, x_86);
return x_89;
}
default:
{
obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_70);
x_91 = lean::box(0);
x_92 = l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_33);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
}
}
}
}
}
}
obj* l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_lean_parser_command_struct__explicit__binder__content_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_3);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_struct__explicit__binder;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_struct__explicit__binder_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_struct__explicit__binder_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_struct__implicit__binder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("struct_implicit_binder");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_struct__implicit__binder_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__2;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_5 = x_15;
x_6 = x_18;
goto lbl_7;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_5 = x_21;
x_6 = x_19;
goto lbl_7;
}
}
lbl_4:
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l_lean_parser_command_struct__binder__content_has__view;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_3);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
lean::dec(x_3);
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_34; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_27);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
case 1:
{
obj* x_40; obj* x_41; 
lean::dec(x_31);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_27);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
case 2:
{
obj* x_43; obj* x_44; 
lean::dec(x_31);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_27);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
default:
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_27);
lean::cnstr_set(x_47, 2, x_46);
return x_47;
}
}
}
}
lbl_7:
{
obj* x_48; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_53;
goto lbl_49;
}
else
{
obj* x_54; obj* x_56; 
x_54 = lean::cnstr_get(x_5, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_5, 1);
lean::inc(x_56);
lean::dec(x_5);
x_1 = x_53;
x_2 = x_54;
x_3 = x_56;
goto lbl_4;
}
}
case 1:
{
obj* x_60; 
lean::dec(x_6);
x_60 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_60;
goto lbl_49;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_5, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_5, 1);
lean::inc(x_63);
lean::dec(x_5);
x_1 = x_60;
x_2 = x_61;
x_3 = x_63;
goto lbl_4;
}
}
case 2:
{
obj* x_67; 
lean::dec(x_6);
x_67 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_67;
goto lbl_49;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_5, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_5, 1);
lean::inc(x_70);
lean::dec(x_5);
x_1 = x_67;
x_2 = x_68;
x_3 = x_70;
goto lbl_4;
}
}
default:
{
obj* x_74; 
lean::dec(x_6);
x_74 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_74;
goto lbl_49;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_5, 1);
lean::inc(x_77);
lean::dec(x_5);
x_1 = x_74;
x_2 = x_75;
x_3 = x_77;
goto lbl_4;
}
}
}
lbl_49:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_5);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_48);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
else
{
obj* x_85; 
x_85 = lean::cnstr_get(x_5, 0);
lean::inc(x_85);
lean::dec(x_5);
switch (lean::obj_tag(x_85)) {
case 0:
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; 
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
x_92 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_48);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
case 1:
{
obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_85);
x_96 = lean::box(0);
x_97 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_48);
lean::cnstr_set(x_99, 1, x_97);
lean::cnstr_set(x_99, 2, x_96);
return x_99;
}
case 2:
{
obj* x_101; obj* x_102; obj* x_104; 
lean::dec(x_85);
x_101 = lean::box(0);
x_102 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
x_104 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_104, 0, x_48);
lean::cnstr_set(x_104, 1, x_102);
lean::cnstr_set(x_104, 2, x_101);
return x_104;
}
default:
{
obj* x_106; obj* x_107; obj* x_109; 
lean::dec(x_85);
x_106 = lean::box(0);
x_107 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_109, 0, x_48);
lean::cnstr_set(x_109, 1, x_107);
lean::cnstr_set(x_109, 2, x_106);
return x_109;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_struct__binder__content_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::box(3);
x_4 = x_7;
x_5 = x_8;
goto lbl_6;
lbl_3:
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = l_lean_parser_command_struct__binder__content_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_12);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
case 1:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_0);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
case 2:
{
obj* x_28; obj* x_29; 
lean::dec(x_16);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_12);
lean::cnstr_set(x_29, 2, x_28);
return x_29;
}
default:
{
obj* x_31; obj* x_32; 
lean::dec(x_16);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_0);
lean::cnstr_set(x_32, 1, x_12);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
}
}
}
lbl_6:
{
obj* x_33; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_5, 0);
lean::inc(x_35);
lean::dec(x_5);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_35);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_38;
goto lbl_34;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_4, 1);
lean::inc(x_41);
lean::dec(x_4);
x_0 = x_38;
x_1 = x_39;
x_2 = x_41;
goto lbl_3;
}
}
case 1:
{
obj* x_45; 
lean::dec(x_5);
x_45 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_45;
goto lbl_34;
}
else
{
obj* x_46; obj* x_48; 
x_46 = lean::cnstr_get(x_4, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_4, 1);
lean::inc(x_48);
lean::dec(x_4);
x_0 = x_45;
x_1 = x_46;
x_2 = x_48;
goto lbl_3;
}
}
case 2:
{
obj* x_52; 
lean::dec(x_5);
x_52 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_52;
goto lbl_34;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_4, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_4, 1);
lean::inc(x_55);
lean::dec(x_4);
x_0 = x_52;
x_1 = x_53;
x_2 = x_55;
goto lbl_3;
}
}
default:
{
obj* x_59; 
lean::dec(x_5);
x_59 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_59;
goto lbl_34;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_4, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_4, 1);
lean::inc(x_62);
lean::dec(x_4);
x_0 = x_59;
x_1 = x_60;
x_2 = x_62;
goto lbl_3;
}
}
}
lbl_34:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_66; obj* x_67; obj* x_69; 
lean::dec(x_4);
x_66 = lean::box(0);
x_67 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_69, 0, x_33);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set(x_69, 2, x_66);
return x_69;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_4, 0);
lean::inc(x_70);
lean::dec(x_4);
switch (lean::obj_tag(x_70)) {
case 0:
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
lean::dec(x_70);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_73);
x_77 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_33);
lean::cnstr_set(x_79, 1, x_77);
lean::cnstr_set(x_79, 2, x_76);
return x_79;
}
case 1:
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_70);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_33);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
case 2:
{
obj* x_86; obj* x_87; obj* x_89; 
lean::dec(x_70);
x_86 = lean::box(0);
x_87 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_87);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_33);
lean::cnstr_set(x_89, 1, x_87);
lean::cnstr_set(x_89, 2, x_86);
return x_89;
}
default:
{
obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_70);
x_91 = lean::box(0);
x_92 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_33);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
}
}
}
}
}
}
obj* l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_lean_parser_command_struct__binder__content_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_3);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_struct__implicit__binder;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_struct__implicit__binder_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_struct__implicit__binder_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_strict__implicit__binder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("strict_implicit_binder");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_strict__implicit__binder_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_5 = x_15;
x_6 = x_18;
goto lbl_7;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_5 = x_21;
x_6 = x_19;
goto lbl_7;
}
}
lbl_4:
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l_lean_parser_command_struct__binder__content_has__view;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_3);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
lean::dec(x_3);
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_34; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_27);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
case 1:
{
obj* x_40; obj* x_41; 
lean::dec(x_31);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_27);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
case 2:
{
obj* x_43; obj* x_44; 
lean::dec(x_31);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_27);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
default:
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_27);
lean::cnstr_set(x_47, 2, x_46);
return x_47;
}
}
}
}
lbl_7:
{
obj* x_48; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_53;
goto lbl_49;
}
else
{
obj* x_54; obj* x_56; 
x_54 = lean::cnstr_get(x_5, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_5, 1);
lean::inc(x_56);
lean::dec(x_5);
x_1 = x_53;
x_2 = x_54;
x_3 = x_56;
goto lbl_4;
}
}
case 1:
{
obj* x_60; 
lean::dec(x_6);
x_60 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_60;
goto lbl_49;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_5, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_5, 1);
lean::inc(x_63);
lean::dec(x_5);
x_1 = x_60;
x_2 = x_61;
x_3 = x_63;
goto lbl_4;
}
}
case 2:
{
obj* x_67; 
lean::dec(x_6);
x_67 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_67;
goto lbl_49;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_5, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_5, 1);
lean::inc(x_70);
lean::dec(x_5);
x_1 = x_67;
x_2 = x_68;
x_3 = x_70;
goto lbl_4;
}
}
default:
{
obj* x_74; 
lean::dec(x_6);
x_74 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_74;
goto lbl_49;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_5, 1);
lean::inc(x_77);
lean::dec(x_5);
x_1 = x_74;
x_2 = x_75;
x_3 = x_77;
goto lbl_4;
}
}
}
lbl_49:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_5);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_48);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
else
{
obj* x_85; 
x_85 = lean::cnstr_get(x_5, 0);
lean::inc(x_85);
lean::dec(x_5);
switch (lean::obj_tag(x_85)) {
case 0:
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; 
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
x_92 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_48);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
case 1:
{
obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_85);
x_96 = lean::box(0);
x_97 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_48);
lean::cnstr_set(x_99, 1, x_97);
lean::cnstr_set(x_99, 2, x_96);
return x_99;
}
case 2:
{
obj* x_101; obj* x_102; obj* x_104; 
lean::dec(x_85);
x_101 = lean::box(0);
x_102 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
x_104 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_104, 0, x_48);
lean::cnstr_set(x_104, 1, x_102);
lean::cnstr_set(x_104, 2, x_101);
return x_104;
}
default:
{
obj* x_106; obj* x_107; obj* x_109; 
lean::dec(x_85);
x_106 = lean::box(0);
x_107 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_109, 0, x_48);
lean::cnstr_set(x_109, 1, x_107);
lean::cnstr_set(x_109, 2, x_106);
return x_109;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::box(3);
x_4 = x_7;
x_5 = x_8;
goto lbl_6;
lbl_3:
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = l_lean_parser_command_struct__binder__content_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_12);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
case 1:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_0);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
case 2:
{
obj* x_28; obj* x_29; 
lean::dec(x_16);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_12);
lean::cnstr_set(x_29, 2, x_28);
return x_29;
}
default:
{
obj* x_31; obj* x_32; 
lean::dec(x_16);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_0);
lean::cnstr_set(x_32, 1, x_12);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
}
}
}
lbl_6:
{
obj* x_33; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_5, 0);
lean::inc(x_35);
lean::dec(x_5);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_35);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_38;
goto lbl_34;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_4, 1);
lean::inc(x_41);
lean::dec(x_4);
x_0 = x_38;
x_1 = x_39;
x_2 = x_41;
goto lbl_3;
}
}
case 1:
{
obj* x_45; 
lean::dec(x_5);
x_45 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_45;
goto lbl_34;
}
else
{
obj* x_46; obj* x_48; 
x_46 = lean::cnstr_get(x_4, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_4, 1);
lean::inc(x_48);
lean::dec(x_4);
x_0 = x_45;
x_1 = x_46;
x_2 = x_48;
goto lbl_3;
}
}
case 2:
{
obj* x_52; 
lean::dec(x_5);
x_52 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_52;
goto lbl_34;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_4, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_4, 1);
lean::inc(x_55);
lean::dec(x_4);
x_0 = x_52;
x_1 = x_53;
x_2 = x_55;
goto lbl_3;
}
}
default:
{
obj* x_59; 
lean::dec(x_5);
x_59 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_59;
goto lbl_34;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_4, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_4, 1);
lean::inc(x_62);
lean::dec(x_4);
x_0 = x_59;
x_1 = x_60;
x_2 = x_62;
goto lbl_3;
}
}
}
lbl_34:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_66; obj* x_67; obj* x_69; 
lean::dec(x_4);
x_66 = lean::box(0);
x_67 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_69, 0, x_33);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set(x_69, 2, x_66);
return x_69;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_4, 0);
lean::inc(x_70);
lean::dec(x_4);
switch (lean::obj_tag(x_70)) {
case 0:
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
lean::dec(x_70);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_73);
x_77 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_33);
lean::cnstr_set(x_79, 1, x_77);
lean::cnstr_set(x_79, 2, x_76);
return x_79;
}
case 1:
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_70);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_33);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
case 2:
{
obj* x_86; obj* x_87; obj* x_89; 
lean::dec(x_70);
x_86 = lean::box(0);
x_87 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_87);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_33);
lean::cnstr_set(x_89, 1, x_87);
lean::cnstr_set(x_89, 2, x_86);
return x_89;
}
default:
{
obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_70);
x_91 = lean::box(0);
x_92 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_33);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
}
}
}
}
}
}
obj* l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_lean_parser_command_struct__binder__content_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_3);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_strict__implicit__binder;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_strict__implicit__binder_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_strict__implicit__binder_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_inst__implicit__binder() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inst_implicit_binder");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_inst__implicit__binder_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_5 = x_15;
x_6 = x_18;
goto lbl_7;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_5 = x_21;
x_6 = x_19;
goto lbl_7;
}
}
lbl_4:
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l_lean_parser_command_struct__binder__content_has__view;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_3);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_27);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
lean::dec(x_3);
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_34; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_27);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
case 1:
{
obj* x_40; obj* x_41; 
lean::dec(x_31);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_27);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
case 2:
{
obj* x_43; obj* x_44; 
lean::dec(x_31);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_27);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
default:
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_27);
lean::cnstr_set(x_47, 2, x_46);
return x_47;
}
}
}
}
lbl_7:
{
obj* x_48; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_50);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_53;
goto lbl_49;
}
else
{
obj* x_54; obj* x_56; 
x_54 = lean::cnstr_get(x_5, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_5, 1);
lean::inc(x_56);
lean::dec(x_5);
x_1 = x_53;
x_2 = x_54;
x_3 = x_56;
goto lbl_4;
}
}
case 1:
{
obj* x_60; 
lean::dec(x_6);
x_60 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_60;
goto lbl_49;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_5, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_5, 1);
lean::inc(x_63);
lean::dec(x_5);
x_1 = x_60;
x_2 = x_61;
x_3 = x_63;
goto lbl_4;
}
}
case 2:
{
obj* x_67; 
lean::dec(x_6);
x_67 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_67;
goto lbl_49;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_5, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_5, 1);
lean::inc(x_70);
lean::dec(x_5);
x_1 = x_67;
x_2 = x_68;
x_3 = x_70;
goto lbl_4;
}
}
default:
{
obj* x_74; 
lean::dec(x_6);
x_74 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_48 = x_74;
goto lbl_49;
}
else
{
obj* x_75; obj* x_77; 
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_5, 1);
lean::inc(x_77);
lean::dec(x_5);
x_1 = x_74;
x_2 = x_75;
x_3 = x_77;
goto lbl_4;
}
}
}
lbl_49:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_5);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_48);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
else
{
obj* x_85; 
x_85 = lean::cnstr_get(x_5, 0);
lean::inc(x_85);
lean::dec(x_5);
switch (lean::obj_tag(x_85)) {
case 0:
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; 
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
x_92 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_48);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
case 1:
{
obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_85);
x_96 = lean::box(0);
x_97 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_48);
lean::cnstr_set(x_99, 1, x_97);
lean::cnstr_set(x_99, 2, x_96);
return x_99;
}
case 2:
{
obj* x_101; obj* x_102; obj* x_104; 
lean::dec(x_85);
x_101 = lean::box(0);
x_102 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
x_104 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_104, 0, x_48);
lean::cnstr_set(x_104, 1, x_102);
lean::cnstr_set(x_104, 2, x_101);
return x_104;
}
default:
{
obj* x_106; obj* x_107; obj* x_109; 
lean::dec(x_85);
x_106 = lean::box(0);
x_107 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_109, 0, x_48);
lean::cnstr_set(x_109, 1, x_107);
lean::cnstr_set(x_109, 2, x_106);
return x_109;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::box(3);
x_4 = x_7;
x_5 = x_8;
goto lbl_6;
lbl_3:
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = l_lean_parser_command_struct__binder__content_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_19; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_12);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
case 1:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_0);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
case 2:
{
obj* x_28; obj* x_29; 
lean::dec(x_16);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_12);
lean::cnstr_set(x_29, 2, x_28);
return x_29;
}
default:
{
obj* x_31; obj* x_32; 
lean::dec(x_16);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_0);
lean::cnstr_set(x_32, 1, x_12);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
}
}
}
lbl_6:
{
obj* x_33; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_5, 0);
lean::inc(x_35);
lean::dec(x_5);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_35);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_38;
goto lbl_34;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_4, 1);
lean::inc(x_41);
lean::dec(x_4);
x_0 = x_38;
x_1 = x_39;
x_2 = x_41;
goto lbl_3;
}
}
case 1:
{
obj* x_45; 
lean::dec(x_5);
x_45 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_45;
goto lbl_34;
}
else
{
obj* x_46; obj* x_48; 
x_46 = lean::cnstr_get(x_4, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_4, 1);
lean::inc(x_48);
lean::dec(x_4);
x_0 = x_45;
x_1 = x_46;
x_2 = x_48;
goto lbl_3;
}
}
case 2:
{
obj* x_52; 
lean::dec(x_5);
x_52 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_52;
goto lbl_34;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_4, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_4, 1);
lean::inc(x_55);
lean::dec(x_4);
x_0 = x_52;
x_1 = x_53;
x_2 = x_55;
goto lbl_3;
}
}
default:
{
obj* x_59; 
lean::dec(x_5);
x_59 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_33 = x_59;
goto lbl_34;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_4, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_4, 1);
lean::inc(x_62);
lean::dec(x_4);
x_0 = x_59;
x_1 = x_60;
x_2 = x_62;
goto lbl_3;
}
}
}
lbl_34:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_66; obj* x_67; obj* x_69; 
lean::dec(x_4);
x_66 = lean::box(0);
x_67 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_69, 0, x_33);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set(x_69, 2, x_66);
return x_69;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_4, 0);
lean::inc(x_70);
lean::dec(x_4);
switch (lean::obj_tag(x_70)) {
case 0:
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
x_73 = lean::cnstr_get(x_70, 0);
lean::inc(x_73);
lean::dec(x_70);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_73);
x_77 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_33);
lean::cnstr_set(x_79, 1, x_77);
lean::cnstr_set(x_79, 2, x_76);
return x_79;
}
case 1:
{
obj* x_81; obj* x_82; obj* x_84; 
lean::dec(x_70);
x_81 = lean::box(0);
x_82 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_33);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set(x_84, 2, x_81);
return x_84;
}
case 2:
{
obj* x_86; obj* x_87; obj* x_89; 
lean::dec(x_70);
x_86 = lean::box(0);
x_87 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_87);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_33);
lean::cnstr_set(x_89, 1, x_87);
lean::cnstr_set(x_89, 2, x_86);
return x_89;
}
default:
{
obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_70);
x_91 = lean::box(0);
x_92 = l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_94, 0, x_33);
lean::cnstr_set(x_94, 1, x_92);
lean::cnstr_set(x_94, 2, x_91);
return x_94;
}
}
}
}
}
}
}
obj* l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_lean_parser_command_struct__binder__content_has__view;
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
x_17 = lean::apply_1(x_15, x_3);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_inst__implicit__binder;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_inst__implicit__binder_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_inst__implicit__binder_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_structure__field__block() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure_field_block");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_structure__field__block_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__field__block_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__2;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_86; uint8 x_87; 
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_dec_eq(x_2, x_86);
lean::dec(x_86);
if (x_87 == 0)
{
obj* x_89; uint8 x_90; 
x_89 = lean::mk_nat_obj(2u);
x_90 = lean::nat_dec_eq(x_2, x_89);
lean::dec(x_89);
lean::dec(x_2);
if (x_90 == 0)
{
obj* x_93; obj* x_94; obj* x_96; obj* x_97; 
x_93 = l_lean_parser_command_inst__implicit__binder_has__view;
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::apply_1(x_94, x_1);
x_97 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
else
{
obj* x_98; obj* x_99; obj* x_101; obj* x_102; 
x_98 = l_lean_parser_command_strict__implicit__binder_has__view;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::apply_1(x_99, x_1);
x_102 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
else
{
obj* x_104; obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_2);
x_104 = l_lean_parser_command_struct__implicit__binder_has__view;
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_107 = lean::apply_1(x_105, x_1);
x_108 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
}
else
{
obj* x_110; obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_2);
x_110 = l_lean_parser_command_struct__explicit__binder_has__view;
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::apply_1(x_111, x_1);
x_114 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_114, 0, x_113);
return x_114;
}
}
}
}
obj* _init_l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(2u);
x_12 = lean::nat_dec_eq(x_1, x_11);
lean::dec(x_11);
lean::dec(x_1);
if (x_12 == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_15 = l_lean_parser_command_inst__implicit__binder_has__view;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::apply_1(x_16, x_0);
x_19 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
x_20 = l_lean_parser_command_strict__implicit__binder_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_0);
x_24 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
else
{
obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_1);
x_26 = l_lean_parser_command_struct__implicit__binder_has__view;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_0);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
else
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_32 = l_lean_parser_command_struct__explicit__binder_has__view;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::apply_1(x_33, x_0);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
}
}
}
obj* _init_l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure_field_block");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_structure__field__block_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_struct__explicit__binder_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_command_structure__field__block;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
case 1:
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_command_struct__implicit__binder_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_lean_parser_command_structure__field__block;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
}
case 2:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_49; 
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = l_lean_parser_command_strict__implicit__binder_has__view;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
x_40 = lean::apply_1(x_38, x_34);
lean::inc(x_1);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_1);
x_43 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_43);
x_45 = l_lean_parser_syntax_mk__node(x_43, x_42);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_1);
x_47 = l_lean_parser_command_structure__field__block;
lean::inc(x_47);
x_49 = l_lean_parser_syntax_mk__node(x_47, x_46);
return x_49;
}
default:
{
obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
lean::dec(x_0);
x_53 = l_lean_parser_command_inst__implicit__binder_has__view;
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
x_56 = lean::apply_1(x_54, x_50);
lean::inc(x_1);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_1);
x_59 = l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
lean::inc(x_59);
x_61 = l_lean_parser_syntax_mk__node(x_59, x_58);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_1);
x_63 = l_lean_parser_command_structure__field__block;
lean::inc(x_63);
x_65 = l_lean_parser_syntax_mk__node(x_63, x_62);
return x_65;
}
}
}
}
obj* _init_l_lean_parser_command_structure__field__block_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_structure__field__block_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_structure__field__block_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_113; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_notation__like_parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__binder__content_parser), 4, 0);
lean::inc(x_9);
lean::inc(x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_9);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_13);
lean::inc(x_4);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_4);
lean::inc(x_9);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_9);
x_19 = l_lean_parser_command_struct__explicit__binder__content;
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_18);
x_22 = lean::mk_string(")");
x_23 = l_string_trim(x_22);
lean::inc(x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_25, 0, x_23);
lean::inc(x_4);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_27, 0, x_23);
lean::closure_set(x_27, 1, x_4);
lean::closure_set(x_27, 2, x_25);
lean::inc(x_9);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_9);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_21);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_6);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_lean_parser_command_struct__explicit__binder;
lean::inc(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_31);
x_35 = lean::mk_string("{");
x_36 = l_string_trim(x_35);
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_38, 0, x_36);
lean::inc(x_4);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_4);
lean::closure_set(x_40, 2, x_38);
x_41 = lean::mk_string("}");
x_42 = l_string_trim(x_41);
lean::inc(x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_44, 0, x_42);
lean::inc(x_4);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_46, 0, x_42);
lean::closure_set(x_46, 1, x_4);
lean::closure_set(x_46, 2, x_44);
lean::inc(x_9);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_9);
lean::inc(x_10);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_10);
lean::cnstr_set(x_50, 1, x_48);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_40);
lean::cnstr_set(x_51, 1, x_50);
x_52 = l_lean_parser_command_struct__implicit__binder;
lean::inc(x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_54, 0, x_52);
lean::closure_set(x_54, 1, x_51);
x_55 = lean::mk_string("\xe2\xa6\x83");
x_56 = l_string_trim(x_55);
lean::inc(x_56);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_58, 0, x_56);
lean::inc(x_4);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_60, 0, x_56);
lean::closure_set(x_60, 1, x_4);
lean::closure_set(x_60, 2, x_58);
x_61 = lean::mk_string("\xe2\xa6\x84");
x_62 = l_string_trim(x_61);
lean::inc(x_62);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_64, 0, x_62);
lean::inc(x_4);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_66, 0, x_62);
lean::closure_set(x_66, 1, x_4);
lean::closure_set(x_66, 2, x_64);
lean::inc(x_9);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_9);
lean::inc(x_10);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_10);
lean::cnstr_set(x_70, 1, x_68);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_60);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l_lean_parser_command_strict__implicit__binder;
lean::inc(x_72);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_74, 0, x_72);
lean::closure_set(x_74, 1, x_71);
x_75 = lean::mk_string("[");
x_76 = l_string_trim(x_75);
lean::inc(x_76);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_78, 0, x_76);
lean::inc(x_4);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_80, 0, x_76);
lean::closure_set(x_80, 1, x_4);
lean::closure_set(x_80, 2, x_78);
x_81 = lean::mk_string("]");
x_82 = l_string_trim(x_81);
lean::inc(x_82);
x_84 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_84, 0, x_82);
lean::inc(x_4);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_86, 0, x_82);
lean::closure_set(x_86, 1, x_4);
lean::closure_set(x_86, 2, x_84);
lean::inc(x_9);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_9);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_10);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_80);
lean::cnstr_set(x_90, 1, x_89);
x_91 = l_lean_parser_command_inst__implicit__binder;
lean::inc(x_91);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_93, 0, x_91);
lean::closure_set(x_93, 1, x_90);
lean::inc(x_9);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_9);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_74);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_54);
lean::cnstr_set(x_97, 1, x_96);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_34);
lean::cnstr_set(x_98, 1, x_97);
x_99 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_99, 0, x_98);
lean::closure_set(x_99, 1, x_4);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_9);
x_101 = l_lean_parser_command__parser__m_monad___closed__1;
x_102 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_103 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_104 = l_lean_parser_command__parser__m_alternative___closed__1;
x_105 = l_lean_parser_command_structure__field__block;
x_106 = l_lean_parser_command_structure__field__block_has__view;
lean::inc(x_106);
lean::inc(x_105);
lean::inc(x_104);
lean::inc(x_103);
lean::inc(x_102);
lean::inc(x_101);
x_113 = l_lean_parser_combinators_node_view___rarg(x_101, x_102, x_103, x_104, x_105, x_100, x_106);
return x_113;
}
}
obj* _init_l_lean_parser_command_structure__field__block_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_0 = lean::mk_string("(");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = l_lean_parser_command_notation__like_parser_lean_parser_has__tokens;
lean::inc(x_4);
x_6 = l_lean_parser_tokens___rarg(x_4);
x_7 = lean::box(0);
x_8 = l_lean_parser_command_struct__binder__content_parser_lean_parser_has__tokens;
lean::inc(x_7);
lean::inc(x_8);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_8, x_7);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_6, x_11);
x_13 = l_lean_parser_tokens___rarg(x_12);
lean::inc(x_7);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_13, x_7);
x_16 = l_lean_parser_tokens___rarg(x_15);
x_17 = lean::mk_string(")");
lean::inc(x_1);
x_19 = l_lean_parser_symbol_tokens___rarg(x_17, x_1);
lean::inc(x_7);
x_21 = l_lean_parser_list_cons_tokens___rarg(x_19, x_7);
x_22 = l_lean_parser_list_cons_tokens___rarg(x_16, x_21);
x_23 = l_lean_parser_list_cons_tokens___rarg(x_3, x_22);
x_24 = l_lean_parser_tokens___rarg(x_23);
x_25 = lean::mk_string("{");
lean::inc(x_1);
x_27 = l_lean_parser_symbol_tokens___rarg(x_25, x_1);
x_28 = lean::mk_string("}");
lean::inc(x_1);
x_30 = l_lean_parser_symbol_tokens___rarg(x_28, x_1);
lean::inc(x_7);
x_32 = l_lean_parser_list_cons_tokens___rarg(x_30, x_7);
lean::inc(x_8);
x_34 = l_lean_parser_list_cons_tokens___rarg(x_8, x_32);
x_35 = l_lean_parser_list_cons_tokens___rarg(x_27, x_34);
x_36 = l_lean_parser_tokens___rarg(x_35);
x_37 = lean::mk_string("\xe2\xa6\x83");
lean::inc(x_1);
x_39 = l_lean_parser_symbol_tokens___rarg(x_37, x_1);
x_40 = lean::mk_string("\xe2\xa6\x84");
lean::inc(x_1);
x_42 = l_lean_parser_symbol_tokens___rarg(x_40, x_1);
lean::inc(x_7);
x_44 = l_lean_parser_list_cons_tokens___rarg(x_42, x_7);
lean::inc(x_8);
x_46 = l_lean_parser_list_cons_tokens___rarg(x_8, x_44);
x_47 = l_lean_parser_list_cons_tokens___rarg(x_39, x_46);
x_48 = l_lean_parser_tokens___rarg(x_47);
x_49 = lean::mk_string("[");
lean::inc(x_1);
x_51 = l_lean_parser_symbol_tokens___rarg(x_49, x_1);
x_52 = lean::mk_string("]");
x_53 = l_lean_parser_symbol_tokens___rarg(x_52, x_1);
lean::inc(x_7);
x_55 = l_lean_parser_list_cons_tokens___rarg(x_53, x_7);
lean::inc(x_8);
x_57 = l_lean_parser_list_cons_tokens___rarg(x_8, x_55);
x_58 = l_lean_parser_list_cons_tokens___rarg(x_51, x_57);
x_59 = l_lean_parser_tokens___rarg(x_58);
lean::inc(x_7);
x_61 = l_lean_parser_list_cons_tokens___rarg(x_59, x_7);
x_62 = l_lean_parser_list_cons_tokens___rarg(x_48, x_61);
x_63 = l_lean_parser_list_cons_tokens___rarg(x_36, x_62);
x_64 = l_lean_parser_list_cons_tokens___rarg(x_24, x_63);
x_65 = l_lean_parser_tokens___rarg(x_64);
x_66 = l_lean_parser_list_cons_tokens___rarg(x_65, x_7);
x_67 = l_lean_parser_tokens___rarg(x_66);
return x_67;
}
}
obj* l_lean_parser_command_structure__field__block_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_structure__field__block;
x_5 = l_lean_parser_command_structure__field__block_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_structure__field__block_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_notation__like_parser), 5, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_struct__binder__content_parser), 4, 0);
lean::inc(x_9);
lean::inc(x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_9);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_13);
lean::inc(x_4);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_4);
lean::inc(x_9);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_9);
x_19 = l_lean_parser_command_struct__explicit__binder__content;
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_18);
x_22 = lean::mk_string(")");
x_23 = l_string_trim(x_22);
lean::inc(x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_25, 0, x_23);
lean::inc(x_4);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_27, 0, x_23);
lean::closure_set(x_27, 1, x_4);
lean::closure_set(x_27, 2, x_25);
lean::inc(x_9);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_9);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_21);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_6);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_lean_parser_command_struct__explicit__binder;
lean::inc(x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_31);
x_35 = lean::mk_string("{");
x_36 = l_string_trim(x_35);
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_38, 0, x_36);
lean::inc(x_4);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_4);
lean::closure_set(x_40, 2, x_38);
x_41 = lean::mk_string("}");
x_42 = l_string_trim(x_41);
lean::inc(x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_44, 0, x_42);
lean::inc(x_4);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_46, 0, x_42);
lean::closure_set(x_46, 1, x_4);
lean::closure_set(x_46, 2, x_44);
lean::inc(x_9);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_9);
lean::inc(x_10);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_10);
lean::cnstr_set(x_50, 1, x_48);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_40);
lean::cnstr_set(x_51, 1, x_50);
x_52 = l_lean_parser_command_struct__implicit__binder;
lean::inc(x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_54, 0, x_52);
lean::closure_set(x_54, 1, x_51);
x_55 = lean::mk_string("\xe2\xa6\x83");
x_56 = l_string_trim(x_55);
lean::inc(x_56);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_58, 0, x_56);
lean::inc(x_4);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_60, 0, x_56);
lean::closure_set(x_60, 1, x_4);
lean::closure_set(x_60, 2, x_58);
x_61 = lean::mk_string("\xe2\xa6\x84");
x_62 = l_string_trim(x_61);
lean::inc(x_62);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_64, 0, x_62);
lean::inc(x_4);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_66, 0, x_62);
lean::closure_set(x_66, 1, x_4);
lean::closure_set(x_66, 2, x_64);
lean::inc(x_9);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_9);
lean::inc(x_10);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_10);
lean::cnstr_set(x_70, 1, x_68);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_60);
lean::cnstr_set(x_71, 1, x_70);
x_72 = l_lean_parser_command_strict__implicit__binder;
lean::inc(x_72);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_74, 0, x_72);
lean::closure_set(x_74, 1, x_71);
x_75 = lean::mk_string("[");
x_76 = l_string_trim(x_75);
lean::inc(x_76);
x_78 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_78, 0, x_76);
lean::inc(x_4);
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_80, 0, x_76);
lean::closure_set(x_80, 1, x_4);
lean::closure_set(x_80, 2, x_78);
x_81 = lean::mk_string("]");
x_82 = l_string_trim(x_81);
lean::inc(x_82);
x_84 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_84, 0, x_82);
lean::inc(x_4);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_86, 0, x_82);
lean::closure_set(x_86, 1, x_4);
lean::closure_set(x_86, 2, x_84);
lean::inc(x_9);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_9);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_10);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_80);
lean::cnstr_set(x_90, 1, x_89);
x_91 = l_lean_parser_command_inst__implicit__binder;
lean::inc(x_91);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_93, 0, x_91);
lean::closure_set(x_93, 1, x_90);
lean::inc(x_9);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_9);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_74);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_54);
lean::cnstr_set(x_97, 1, x_96);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_34);
lean::cnstr_set(x_98, 1, x_97);
x_99 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_99, 0, x_98);
lean::closure_set(x_99, 1, x_4);
x_100 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_9);
return x_100;
}
}
obj* _init_l_lean_parser_command_old__univ__params() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("old_univ_params");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_10; obj* x_12; 
lean::dec(x_3);
x_10 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_10);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
case 1:
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
case 2:
{
obj* x_18; obj* x_20; 
lean::dec(x_3);
x_18 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_18);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_8);
return x_20;
}
default:
{
obj* x_22; obj* x_24; 
lean::dec(x_3);
x_22 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_22);
if (lean::is_scalar(x_7)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_7;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_8);
return x_24;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_old__univ__params_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_old__univ__params_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_1;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
lean::dec(x_1);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_33);
if (lean::obj_tag(x_41) == 0)
{
lean::dec(x_41);
if (lean::obj_tag(x_32) == 0)
{
obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_32);
x_44 = lean::box(0);
x_45 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 2, x_44);
return x_47;
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_32, 0);
lean::inc(x_48);
lean::dec(x_32);
switch (lean::obj_tag(x_48)) {
case 0:
{
obj* x_51; obj* x_54; obj* x_55; obj* x_57; 
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
lean::dec(x_48);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_51);
x_55 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_20);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
case 1:
{
obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_48);
x_59 = lean::box(0);
x_60 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_20);
lean::cnstr_set(x_62, 1, x_60);
lean::cnstr_set(x_62, 2, x_59);
return x_62;
}
case 2:
{
obj* x_64; obj* x_65; obj* x_67; 
lean::dec(x_48);
x_64 = lean::box(0);
x_65 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_67, 0, x_20);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set(x_67, 2, x_64);
return x_67;
}
default:
{
obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_48);
x_69 = lean::box(0);
x_70 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_20);
lean::cnstr_set(x_72, 1, x_70);
lean::cnstr_set(x_72, 2, x_69);
return x_72;
}
}
}
}
else
{
obj* x_73; obj* x_75; obj* x_76; obj* x_79; 
x_73 = lean::cnstr_get(x_41, 0);
lean::inc(x_73);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_75 = x_41;
}
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__1(x_76);
if (lean::obj_tag(x_32) == 0)
{
obj* x_82; obj* x_83; 
lean::dec(x_75);
lean::dec(x_32);
x_82 = lean::box(0);
x_83 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_83, 0, x_20);
lean::cnstr_set(x_83, 1, x_79);
lean::cnstr_set(x_83, 2, x_82);
return x_83;
}
else
{
obj* x_84; 
x_84 = lean::cnstr_get(x_32, 0);
lean::inc(x_84);
lean::dec(x_32);
switch (lean::obj_tag(x_84)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
lean::dec(x_84);
if (lean::is_scalar(x_75)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_75;
}
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_20);
lean::cnstr_set(x_91, 1, x_79);
lean::cnstr_set(x_91, 2, x_90);
return x_91;
}
case 1:
{
obj* x_94; obj* x_95; 
lean::dec(x_84);
lean::dec(x_75);
x_94 = lean::box(0);
x_95 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_95, 0, x_20);
lean::cnstr_set(x_95, 1, x_79);
lean::cnstr_set(x_95, 2, x_94);
return x_95;
}
case 2:
{
obj* x_98; obj* x_99; 
lean::dec(x_84);
lean::dec(x_75);
x_98 = lean::box(0);
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_20);
lean::cnstr_set(x_99, 1, x_79);
lean::cnstr_set(x_99, 2, x_98);
return x_99;
}
default:
{
obj* x_102; obj* x_103; 
lean::dec(x_84);
lean::dec(x_75);
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_20);
lean::cnstr_set(x_103, 1, x_79);
lean::cnstr_set(x_103, 2, x_102);
return x_103;
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = lean::box(3);
x_17 = x_0;
x_18 = x_20;
goto lbl_19;
}
else
{
obj* x_21; obj* x_23; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
x_17 = x_23;
x_18 = x_21;
goto lbl_19;
}
lbl_19:
{
obj* x_26; 
x_26 = l_lean_parser_syntax_as__node___main(x_18);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_26);
if (lean::obj_tag(x_17) == 0)
{
obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_17);
x_29 = lean::box(0);
x_30 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_29);
return x_32;
}
else
{
obj* x_33; 
x_33 = lean::cnstr_get(x_17, 0);
lean::inc(x_33);
lean::dec(x_17);
switch (lean::obj_tag(x_33)) {
case 0:
{
obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
lean::dec(x_33);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_36);
x_40 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 2, x_39);
return x_42;
}
case 1:
{
obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_33);
x_44 = lean::box(0);
x_45 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_5);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 2, x_44);
return x_47;
}
case 2:
{
obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_33);
x_49 = lean::box(0);
x_50 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_5);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set(x_52, 2, x_49);
return x_52;
}
default:
{
obj* x_54; obj* x_55; obj* x_57; 
lean::dec(x_33);
x_54 = lean::box(0);
x_55 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
}
}
}
else
{
obj* x_58; obj* x_60; obj* x_61; obj* x_64; 
x_58 = lean::cnstr_get(x_26, 0);
lean::inc(x_58);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_60 = x_26;
}
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__1(x_61);
if (lean::obj_tag(x_17) == 0)
{
obj* x_67; obj* x_68; 
lean::dec(x_17);
lean::dec(x_60);
x_67 = lean::box(0);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_5);
lean::cnstr_set(x_68, 1, x_64);
lean::cnstr_set(x_68, 2, x_67);
return x_68;
}
else
{
obj* x_69; 
x_69 = lean::cnstr_get(x_17, 0);
lean::inc(x_69);
lean::dec(x_17);
switch (lean::obj_tag(x_69)) {
case 0:
{
obj* x_72; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
lean::dec(x_69);
if (lean::is_scalar(x_60)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_60;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_5);
lean::cnstr_set(x_76, 1, x_64);
lean::cnstr_set(x_76, 2, x_75);
return x_76;
}
case 1:
{
obj* x_79; obj* x_80; 
lean::dec(x_69);
lean::dec(x_60);
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_5);
lean::cnstr_set(x_80, 1, x_64);
lean::cnstr_set(x_80, 2, x_79);
return x_80;
}
case 2:
{
obj* x_83; obj* x_84; 
lean::dec(x_69);
lean::dec(x_60);
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_5);
lean::cnstr_set(x_84, 1, x_64);
lean::cnstr_set(x_84, 2, x_83);
return x_84;
}
default:
{
obj* x_87; obj* x_88; 
lean::dec(x_69);
lean::dec(x_60);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_5);
lean::cnstr_set(x_88, 1, x_64);
lean::cnstr_set(x_88, 2, x_87);
return x_88;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_old__univ__params_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_list_map___main___at_lean_parser_command_old__univ__params_has__view_x_27___spec__2(x_3);
x_15 = l_lean_parser_no__kind;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_old__univ__params;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_old__univ__params_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_old__univ__params_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_old__univ__params_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_30; 
x_0 = lean::mk_string("{");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("}");
x_10 = l_string_trim(x_9);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_12, 0, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_command__parser__m_monad___closed__1;
x_19 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_20 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_21 = l_lean_parser_command__parser__m_alternative___closed__1;
x_22 = l_lean_parser_command_old__univ__params;
x_23 = l_lean_parser_command_old__univ__params_has__view;
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
x_30 = l_lean_parser_combinators_node_view___rarg(x_18, x_19, x_20, x_21, x_22, x_17, x_23);
return x_30;
}
}
obj* _init_l_lean_parser_command_old__univ__params_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::mk_string("{");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::box(0);
lean::inc(x_4);
x_6 = l_lean_parser_tokens___rarg(x_4);
x_7 = lean::mk_string("}");
x_8 = l_lean_parser_symbol_tokens___rarg(x_7, x_1);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_8, x_4);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_6, x_9);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_3, x_10);
x_12 = l_lean_parser_tokens___rarg(x_11);
return x_12;
}
}
obj* l_lean_parser_command_old__univ__params_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_old__univ__params;
x_5 = l_lean_parser_command_old__univ__params_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_old__univ__params_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::mk_string("{");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string("}");
x_10 = l_string_trim(x_9);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_12, 0, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* _init_l_lean_parser_command_univ__params() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("univ_params");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_10; obj* x_12; 
lean::dec(x_3);
x_10 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_10);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
case 1:
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
case 2:
{
obj* x_18; obj* x_20; 
lean::dec(x_3);
x_18 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_18);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_8);
return x_20;
}
default:
{
obj* x_22; obj* x_24; 
lean::dec(x_3);
x_22 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_22);
if (lean::is_scalar(x_7)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_7;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_8);
return x_24;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_lean_parser_command_univ__params_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_univ__params_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_univ__params_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_univ__params_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_35; 
x_35 = lean::box(3);
x_32 = x_1;
x_33 = x_35;
goto lbl_34;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
lean::dec(x_1);
x_32 = x_38;
x_33 = x_36;
goto lbl_34;
}
lbl_34:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_33);
if (lean::obj_tag(x_41) == 0)
{
lean::dec(x_41);
if (lean::obj_tag(x_32) == 0)
{
obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_32);
x_44 = lean::box(0);
x_45 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_20);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 2, x_44);
return x_47;
}
else
{
obj* x_48; 
x_48 = lean::cnstr_get(x_32, 0);
lean::inc(x_48);
lean::dec(x_32);
switch (lean::obj_tag(x_48)) {
case 0:
{
obj* x_51; obj* x_54; obj* x_55; obj* x_57; 
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
lean::dec(x_48);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_51);
x_55 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_20);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
case 1:
{
obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_48);
x_59 = lean::box(0);
x_60 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_20);
lean::cnstr_set(x_62, 1, x_60);
lean::cnstr_set(x_62, 2, x_59);
return x_62;
}
case 2:
{
obj* x_64; obj* x_65; obj* x_67; 
lean::dec(x_48);
x_64 = lean::box(0);
x_65 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_67, 0, x_20);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set(x_67, 2, x_64);
return x_67;
}
default:
{
obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_48);
x_69 = lean::box(0);
x_70 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_20);
lean::cnstr_set(x_72, 1, x_70);
lean::cnstr_set(x_72, 2, x_69);
return x_72;
}
}
}
}
else
{
obj* x_73; obj* x_75; obj* x_76; obj* x_79; 
x_73 = lean::cnstr_get(x_41, 0);
lean::inc(x_73);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_75 = x_41;
}
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__1(x_76);
if (lean::obj_tag(x_32) == 0)
{
obj* x_82; obj* x_83; 
lean::dec(x_75);
lean::dec(x_32);
x_82 = lean::box(0);
x_83 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_83, 0, x_20);
lean::cnstr_set(x_83, 1, x_79);
lean::cnstr_set(x_83, 2, x_82);
return x_83;
}
else
{
obj* x_84; 
x_84 = lean::cnstr_get(x_32, 0);
lean::inc(x_84);
lean::dec(x_32);
switch (lean::obj_tag(x_84)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
lean::dec(x_84);
if (lean::is_scalar(x_75)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_75;
}
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_91, 0, x_20);
lean::cnstr_set(x_91, 1, x_79);
lean::cnstr_set(x_91, 2, x_90);
return x_91;
}
case 1:
{
obj* x_94; obj* x_95; 
lean::dec(x_84);
lean::dec(x_75);
x_94 = lean::box(0);
x_95 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_95, 0, x_20);
lean::cnstr_set(x_95, 1, x_79);
lean::cnstr_set(x_95, 2, x_94);
return x_95;
}
case 2:
{
obj* x_98; obj* x_99; 
lean::dec(x_84);
lean::dec(x_75);
x_98 = lean::box(0);
x_99 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_99, 0, x_20);
lean::cnstr_set(x_99, 1, x_79);
lean::cnstr_set(x_99, 2, x_98);
return x_99;
}
default:
{
obj* x_102; obj* x_103; 
lean::dec(x_84);
lean::dec(x_75);
x_102 = lean::box(0);
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_20);
lean::cnstr_set(x_103, 1, x_79);
lean::cnstr_set(x_103, 2, x_102);
return x_103;
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_univ__params_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = lean::box(3);
x_17 = x_0;
x_18 = x_20;
goto lbl_19;
}
else
{
obj* x_21; obj* x_23; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
x_17 = x_23;
x_18 = x_21;
goto lbl_19;
}
lbl_19:
{
obj* x_26; 
x_26 = l_lean_parser_syntax_as__node___main(x_18);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_26);
if (lean::obj_tag(x_17) == 0)
{
obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_17);
x_29 = lean::box(0);
x_30 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_29);
return x_32;
}
else
{
obj* x_33; 
x_33 = lean::cnstr_get(x_17, 0);
lean::inc(x_33);
lean::dec(x_17);
switch (lean::obj_tag(x_33)) {
case 0:
{
obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
lean::dec(x_33);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_36);
x_40 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 2, x_39);
return x_42;
}
case 1:
{
obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_33);
x_44 = lean::box(0);
x_45 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_5);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set(x_47, 2, x_44);
return x_47;
}
case 2:
{
obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_33);
x_49 = lean::box(0);
x_50 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_5);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set(x_52, 2, x_49);
return x_52;
}
default:
{
obj* x_54; obj* x_55; obj* x_57; 
lean::dec(x_33);
x_54 = lean::box(0);
x_55 = l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
}
}
}
else
{
obj* x_58; obj* x_60; obj* x_61; obj* x_64; 
x_58 = lean::cnstr_get(x_26, 0);
lean::inc(x_58);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_60 = x_26;
}
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__1(x_61);
if (lean::obj_tag(x_17) == 0)
{
obj* x_67; obj* x_68; 
lean::dec(x_17);
lean::dec(x_60);
x_67 = lean::box(0);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_5);
lean::cnstr_set(x_68, 1, x_64);
lean::cnstr_set(x_68, 2, x_67);
return x_68;
}
else
{
obj* x_69; 
x_69 = lean::cnstr_get(x_17, 0);
lean::inc(x_69);
lean::dec(x_17);
switch (lean::obj_tag(x_69)) {
case 0:
{
obj* x_72; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_69, 0);
lean::inc(x_72);
lean::dec(x_69);
if (lean::is_scalar(x_60)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_60;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_5);
lean::cnstr_set(x_76, 1, x_64);
lean::cnstr_set(x_76, 2, x_75);
return x_76;
}
case 1:
{
obj* x_79; obj* x_80; 
lean::dec(x_69);
lean::dec(x_60);
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_5);
lean::cnstr_set(x_80, 1, x_64);
lean::cnstr_set(x_80, 2, x_79);
return x_80;
}
case 2:
{
obj* x_83; obj* x_84; 
lean::dec(x_69);
lean::dec(x_60);
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_5);
lean::cnstr_set(x_84, 1, x_64);
lean::cnstr_set(x_84, 2, x_83);
return x_84;
}
default:
{
obj* x_87; obj* x_88; 
lean::dec(x_69);
lean::dec(x_60);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_5);
lean::cnstr_set(x_88, 1, x_64);
lean::cnstr_set(x_88, 2, x_87);
return x_88;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_univ__params_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
x_14 = l_list_map___main___at_lean_parser_command_univ__params_has__view_x_27___spec__2(x_3);
x_15 = l_lean_parser_no__kind;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_univ__params;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_univ__params_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_univ__params_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_ident__univ__params() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("ident_univ_params");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__5;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_23; 
lean::dec(x_2);
x_23 = lean::box(0);
x_20 = x_23;
goto lbl_21;
}
case 1:
{
obj* x_24; 
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_1);
x_28 = lean::box(3);
x_29 = l_lean_parser_syntax_as__node___main(x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_33; 
lean::dec(x_29);
x_31 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_29, 0);
lean::inc(x_34);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_36 = x_29;
}
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_36);
lean::dec(x_37);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_24);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
else
{
obj* x_44; obj* x_46; 
x_44 = lean::cnstr_get(x_37, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_37, 1);
lean::inc(x_46);
lean::dec(x_37);
if (lean::obj_tag(x_46) == 0)
{
obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_46);
x_50 = l_lean_parser_command_univ__params_has__view;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::apply_1(x_51, x_44);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_24);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
else
{
obj* x_59; obj* x_61; 
lean::dec(x_36);
lean::dec(x_44);
lean::dec(x_46);
x_59 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_24);
lean::cnstr_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
obj* x_62; obj* x_65; 
x_62 = lean::cnstr_get(x_1, 0);
lean::inc(x_62);
lean::dec(x_1);
x_65 = l_lean_parser_syntax_as__node___main(x_62);
if (lean::obj_tag(x_65) == 0)
{
obj* x_67; obj* x_69; 
lean::dec(x_65);
x_67 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_24);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
else
{
obj* x_70; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_65, 0);
lean::inc(x_70);
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 x_72 = x_65;
}
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_79; 
lean::dec(x_73);
lean::dec(x_72);
x_78 = lean::box(0);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_24);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
else
{
obj* x_80; obj* x_82; 
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_73, 1);
lean::inc(x_82);
lean::dec(x_73);
if (lean::obj_tag(x_82) == 0)
{
obj* x_86; obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_82);
x_86 = l_lean_parser_command_univ__params_has__view;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::apply_1(x_87, x_80);
if (lean::is_scalar(x_72)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_72;
}
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_24);
lean::cnstr_set(x_91, 1, x_90);
return x_91;
}
else
{
obj* x_95; obj* x_97; 
lean::dec(x_80);
lean::dec(x_72);
lean::dec(x_82);
x_95 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_95);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_24);
lean::cnstr_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
case 2:
{
obj* x_99; 
lean::dec(x_2);
x_99 = lean::box(0);
x_20 = x_99;
goto lbl_21;
}
default:
{
obj* x_101; 
lean::dec(x_2);
x_101 = lean::box(0);
x_20 = x_101;
goto lbl_21;
}
}
lbl_21:
{
lean::dec(x_20);
if (lean::obj_tag(x_1) == 0)
{
obj* x_104; 
lean::dec(x_1);
x_104 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__3;
lean::inc(x_104);
return x_104;
}
else
{
obj* x_106; obj* x_109; 
x_106 = lean::cnstr_get(x_1, 0);
lean::inc(x_106);
lean::dec(x_1);
x_109 = l_lean_parser_syntax_as__node___main(x_106);
if (lean::obj_tag(x_109) == 0)
{
obj* x_111; 
lean::dec(x_109);
x_111 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_111);
return x_111;
}
else
{
obj* x_113; obj* x_115; obj* x_116; 
x_113 = lean::cnstr_get(x_109, 0);
lean::inc(x_113);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 x_115 = x_109;
}
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
if (lean::obj_tag(x_116) == 0)
{
obj* x_121; 
lean::dec(x_115);
lean::dec(x_116);
x_121 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2;
lean::inc(x_121);
return x_121;
}
else
{
obj* x_123; obj* x_125; 
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_116, 1);
lean::inc(x_125);
lean::dec(x_116);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_136; 
lean::dec(x_125);
x_129 = l_lean_parser_command_univ__params_has__view;
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_132 = lean::apply_1(x_130, x_123);
if (lean::is_scalar(x_115)) {
 x_133 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_133 = x_115;
}
lean::cnstr_set(x_133, 0, x_132);
x_134 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_134);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_134);
lean::cnstr_set(x_136, 1, x_133);
return x_136;
}
else
{
obj* x_140; 
lean::dec(x_123);
lean::dec(x_125);
lean::dec(x_115);
x_140 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_140);
return x_140;
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
lean::inc(x_0);
x_5 = lean::name_mk_string(x_0, x_1);
lean::inc(x_0);
lean::inc(x_0);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_0);
lean::cnstr_set(x_8, 4, x_0);
x_9 = l_lean_parser_command_univ__params_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::box(3);
x_13 = lean::apply_1(x_10, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
lean::inc(x_0);
x_5 = lean::name_mk_string(x_0, x_1);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set(x_9, 2, x_5);
lean::cnstr_set(x_9, 3, x_0);
lean::cnstr_set(x_9, 4, x_0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_0);
return x_10;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; 
lean::dec(x_7);
lean::dec(x_8);
x_13 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2;
lean::inc(x_13);
return x_13;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_17);
x_21 = l_lean_parser_command_univ__params_has__view;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_15);
if (lean::is_scalar(x_7)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_7;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
else
{
obj* x_32; 
lean::dec(x_7);
lean::dec(x_15);
lean::dec(x_17);
x_32 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_32);
return x_32;
}
}
}
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_univ__params_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::box(0);
x_5 = x_8;
goto lbl_6;
}
case 1:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_0);
x_13 = lean::box(3);
x_14 = l_lean_parser_syntax_as__node___main(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_18; 
lean::dec(x_14);
x_16 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_21 = x_14;
}
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_21);
lean::dec(x_22);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_9);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_31; 
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
lean::dec(x_22);
if (lean::obj_tag(x_31) == 0)
{
obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_31);
x_35 = l_lean_parser_command_univ__params_has__view;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::apply_1(x_36, x_29);
if (lean::is_scalar(x_21)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_21;
}
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_9);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
obj* x_44; obj* x_46; 
lean::dec(x_21);
lean::dec(x_29);
lean::dec(x_31);
x_44 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_9);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
}
}
}
else
{
obj* x_47; obj* x_50; 
x_47 = lean::cnstr_get(x_0, 0);
lean::inc(x_47);
lean::dec(x_0);
x_50 = l_lean_parser_syntax_as__node___main(x_47);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_54; 
lean::dec(x_50);
x_52 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_9);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_58; 
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
if (lean::is_shared(x_50)) {
 lean::dec(x_50);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_50, 0);
 x_57 = x_50;
}
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::obj_tag(x_58) == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_57);
lean::dec(x_58);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_9);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_67; 
x_65 = lean::cnstr_get(x_58, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_58, 1);
lean::inc(x_67);
lean::dec(x_58);
if (lean::obj_tag(x_67) == 0)
{
obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_67);
x_71 = l_lean_parser_command_univ__params_has__view;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::apply_1(x_72, x_65);
if (lean::is_scalar(x_57)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_57;
}
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_9);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
else
{
obj* x_80; obj* x_82; 
lean::dec(x_57);
lean::dec(x_65);
lean::dec(x_67);
x_80 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4;
lean::inc(x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_9);
lean::cnstr_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
case 2:
{
obj* x_84; 
lean::dec(x_1);
x_84 = lean::box(0);
x_5 = x_84;
goto lbl_6;
}
default:
{
obj* x_86; 
lean::dec(x_1);
x_86 = lean::box(0);
x_5 = x_86;
goto lbl_6;
}
}
lbl_6:
{
lean::dec(x_5);
if (lean::obj_tag(x_0) == 0)
{
obj* x_89; 
lean::dec(x_0);
x_89 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__3;
lean::inc(x_89);
return x_89;
}
else
{
obj* x_91; obj* x_94; 
x_91 = lean::cnstr_get(x_0, 0);
lean::inc(x_91);
lean::dec(x_0);
x_94 = l_lean_parser_syntax_as__node___main(x_91);
if (lean::obj_tag(x_94) == 0)
{
obj* x_96; 
lean::dec(x_94);
x_96 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
return x_96;
}
else
{
obj* x_98; obj* x_100; obj* x_101; 
x_98 = lean::cnstr_get(x_94, 0);
lean::inc(x_98);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_100 = x_94;
}
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
if (lean::obj_tag(x_101) == 0)
{
obj* x_106; 
lean::dec(x_100);
lean::dec(x_101);
x_106 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2;
lean::inc(x_106);
return x_106;
}
else
{
obj* x_108; obj* x_110; 
x_108 = lean::cnstr_get(x_101, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_101, 1);
lean::inc(x_110);
lean::dec(x_101);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_121; 
lean::dec(x_110);
x_114 = l_lean_parser_command_univ__params_has__view;
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::apply_1(x_115, x_108);
if (lean::is_scalar(x_100)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_100;
}
lean::cnstr_set(x_118, 0, x_117);
x_119 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_119);
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_118);
return x_121;
}
else
{
obj* x_125; 
lean::dec(x_100);
lean::dec(x_108);
lean::dec(x_110);
x_125 = l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1;
lean::inc(x_125);
return x_125;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; 
lean::dec(x_3);
x_8 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_lean_parser_command_ident__univ__params;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; 
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
lean::dec(x_3);
x_17 = lean::box(0);
x_18 = l_lean_parser_command_univ__params_has__view;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
x_21 = lean::apply_1(x_19, x_14);
lean::inc(x_17);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_17);
x_24 = l_lean_parser_no__kind;
lean::inc(x_24);
x_26 = l_lean_parser_syntax_mk__node(x_24, x_23);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_17);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_6);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_lean_parser_command_ident__univ__params;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
return x_31;
}
}
}
obj* _init_l_lean_parser_command_ident__univ__params_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_ident__univ__params_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_38; 
x_0 = lean::mk_string(".{");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::mk_string("}");
x_11 = l_string_trim(x_10);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_4);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
lean::inc(x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_6);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_lean_parser_command_univ__params;
lean::inc(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_19);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_lean_parser_command__parser__m_monad___closed__1;
x_27 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_28 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_29 = l_lean_parser_command__parser__m_alternative___closed__1;
x_30 = l_lean_parser_command_ident__univ__params;
x_31 = l_lean_parser_command_ident__univ__params_has__view;
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
x_38 = l_lean_parser_combinators_node_view___rarg(x_26, x_27, x_28, x_29, x_30, x_25, x_31);
return x_38;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::box(0);
x_1 = lean::mk_string(".{");
x_2 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_4 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
lean::inc(x_0);
x_6 = l_lean_parser_tokens___rarg(x_0);
x_7 = lean::mk_string("}");
x_8 = l_lean_parser_symbol_tokens___rarg(x_7, x_2);
lean::inc(x_0);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_8, x_0);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_6, x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_4, x_11);
x_13 = l_lean_parser_tokens___rarg(x_12);
x_14 = l_lean_parser_tokens___rarg(x_13);
lean::inc(x_0);
x_16 = l_lean_parser_list_cons_tokens___rarg(x_14, x_0);
x_17 = l_lean_parser_list_cons_tokens___rarg(x_0, x_16);
x_18 = l_lean_parser_tokens___rarg(x_17);
return x_18;
}
}
obj* l_lean_parser_command_ident__univ__params_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_ident__univ__params;
x_5 = l_lean_parser_command_ident__univ__params_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_ident__univ__params_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::mk_string(".{");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__3), 5, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::mk_string("}");
x_11 = l_string_trim(x_10);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_4);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
lean::inc(x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_9);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_6);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_lean_parser_command_univ__params;
lean::inc(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_19);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* _init_l_lean_parser_command_structure__kw() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure_kw");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_structure__kw_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__kw_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__kw_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__4;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
lean::dec(x_2);
if (x_84 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
lean::dec(x_1);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
case 1:
{
obj* x_93; 
lean::dec(x_1);
x_93 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
lean::inc(x_93);
return x_93;
}
case 2:
{
obj* x_96; 
lean::dec(x_1);
x_96 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
return x_96;
}
default:
{
obj* x_99; 
lean::dec(x_1);
x_99 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
return x_99;
}
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_101; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_1, 0);
lean::inc(x_101);
lean::dec(x_1);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_101);
x_105 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
case 1:
{
obj* x_107; 
lean::dec(x_1);
x_107 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
lean::inc(x_107);
return x_107;
}
case 2:
{
obj* x_110; 
lean::dec(x_1);
x_110 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
lean::inc(x_110);
return x_110;
}
default:
{
obj* x_113; 
lean::dec(x_1);
x_113 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
lean::inc(x_113);
return x_113;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_9; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
case 1:
{
obj* x_15; 
lean::dec(x_0);
x_15 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
lean::inc(x_15);
return x_15;
}
case 2:
{
obj* x_18; 
lean::dec(x_0);
x_18 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
return x_18;
}
default:
{
obj* x_21; 
lean::dec(x_0);
x_21 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
case 1:
{
obj* x_29; 
lean::dec(x_0);
x_29 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
lean::inc(x_29);
return x_29;
}
case 2:
{
obj* x_32; 
lean::dec(x_0);
x_32 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
lean::inc(x_32);
return x_32;
}
default:
{
obj* x_35; 
lean::dec(x_0);
x_35 = l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2;
lean::inc(x_35);
return x_35;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure_kw");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_structure__kw_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_5);
x_7 = l_option_map___rarg(x_5, x_2);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_1);
x_12 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = l_lean_parser_command_structure__kw;
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mk__node(x_16, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_22);
x_24 = l_option_map___rarg(x_22, x_19);
x_25 = lean::box(3);
x_26 = l_option_get__or__else___main___rarg(x_24, x_25);
lean::inc(x_1);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_command_structure__kw;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
}
}
obj* _init_l_lean_parser_command_structure__kw_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_structure__kw_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_extends() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("extends");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_5);
x_9 = lean::box(0);
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_9);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_18; 
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::dec(x_5);
x_18 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(x_15);
switch (lean::obj_tag(x_13)) {
case 0:
{
obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_3);
lean::cnstr_set(x_24, 1, x_23);
if (lean::is_scalar(x_7)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_7;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
case 1:
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_13);
x_27 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_3);
lean::cnstr_set(x_29, 1, x_27);
if (lean::is_scalar(x_7)) {
 x_30 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_30 = x_7;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_18);
return x_30;
}
case 2:
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_13);
x_32 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_3);
lean::cnstr_set(x_34, 1, x_32);
if (lean::is_scalar(x_7)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_7;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_18);
return x_35;
}
default:
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_13);
x_37 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_3);
lean::cnstr_set(x_39, 1, x_37);
if (lean::is_scalar(x_7)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_7;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_18);
return x_40;
}
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_command_extends_has__view_x_27___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_list_map___main___at_lean_parser_command_extends_has__view_x_27___spec__2(x_5);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_10);
x_15 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
lean::dec(x_10);
x_21 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_21);
x_23 = l_option_map___rarg(x_21, x_18);
x_24 = lean::box(3);
x_25 = l_option_get__or__else___main___rarg(x_23, x_24);
x_26 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_27 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_27 = x_7;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_8);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_13);
return x_29;
}
}
}
}
obj* _init_l_lean_parser_command_extends_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_extends_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_extends_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_extends_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_22; obj* x_23; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
x_20 = x_28;
goto lbl_21;
}
else
{
obj* x_30; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_22 = x_28;
x_23 = x_30;
goto lbl_24;
}
}
case 1:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_35; 
lean::dec(x_1);
x_35 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
return x_35;
}
else
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
lean::dec(x_1);
x_40 = lean::box(0);
x_22 = x_40;
x_23 = x_37;
goto lbl_24;
}
}
case 2:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_43; 
lean::dec(x_1);
x_43 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
return x_43;
}
else
{
obj* x_45; obj* x_48; 
x_45 = lean::cnstr_get(x_1, 0);
lean::inc(x_45);
lean::dec(x_1);
x_48 = lean::box(0);
x_22 = x_48;
x_23 = x_45;
goto lbl_24;
}
}
default:
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_51; 
lean::dec(x_1);
x_51 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
lean::inc(x_51);
return x_51;
}
else
{
obj* x_53; obj* x_56; 
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
x_56 = lean::box(0);
x_22 = x_56;
x_23 = x_53;
goto lbl_24;
}
}
}
lbl_21:
{
obj* x_57; obj* x_58; 
x_57 = lean::box(3);
x_58 = l_lean_parser_syntax_as__node___main(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_62; 
lean::dec(x_58);
x_60 = l_lean_parser_term_tuple_has__view_x_27___lambda__1___closed__1;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_20);
lean::cnstr_set(x_62, 1, x_60);
return x_62;
}
else
{
obj* x_63; obj* x_66; obj* x_69; obj* x_70; 
x_63 = lean::cnstr_get(x_58, 0);
lean::inc(x_63);
lean::dec(x_58);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
x_69 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(x_66);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_20);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
}
lbl_24:
{
obj* x_71; 
x_71 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; 
lean::dec(x_71);
x_73 = l_lean_parser_term_tuple_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_22);
lean::cnstr_set(x_75, 1, x_73);
return x_75;
}
else
{
obj* x_76; obj* x_79; obj* x_82; obj* x_83; 
x_76 = lean::cnstr_get(x_71, 0);
lean::inc(x_76);
lean::dec(x_71);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(x_79);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_22);
lean::cnstr_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
obj* _init_l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_2 = lean::box(0);
x_0 = x_2;
goto lbl_1;
lbl_1:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_4);
x_6 = l_lean_parser_term_tuple_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* _init_l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_7; obj* x_8; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_0);
x_5 = x_13;
goto lbl_6;
}
else
{
obj* x_15; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_7 = x_13;
x_8 = x_15;
goto lbl_9;
}
}
case 1:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
lean::dec(x_0);
x_20 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_0, 0);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::box(0);
x_7 = x_25;
x_8 = x_22;
goto lbl_9;
}
}
case 2:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_28; 
lean::dec(x_0);
x_28 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
lean::inc(x_28);
return x_28;
}
else
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::box(0);
x_7 = x_33;
x_8 = x_30;
goto lbl_9;
}
}
default:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_36; 
lean::dec(x_0);
x_36 = l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1;
lean::inc(x_36);
return x_36;
}
else
{
obj* x_38; obj* x_41; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = lean::box(0);
x_7 = x_41;
x_8 = x_38;
goto lbl_9;
}
}
}
lbl_6:
{
obj* x_42; obj* x_43; 
x_42 = lean::box(3);
x_43 = l_lean_parser_syntax_as__node___main(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_45; obj* x_47; 
lean::dec(x_43);
x_45 = l_lean_parser_term_tuple_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_5);
lean::cnstr_set(x_47, 1, x_45);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_54; obj* x_55; 
x_48 = lean::cnstr_get(x_43, 0);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(x_51);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_5);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
lbl_9:
{
obj* x_56; 
x_56 = l_lean_parser_syntax_as__node___main(x_8);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_60; 
lean::dec(x_56);
x_58 = l_lean_parser_term_tuple_has__view_x_27___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_7);
lean::cnstr_set(x_60, 1, x_58);
return x_60;
}
else
{
obj* x_61; obj* x_64; obj* x_67; obj* x_68; 
x_61 = lean::cnstr_get(x_56, 0);
lean::inc(x_61);
lean::dec(x_56);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l___private_3265500769__sep__by_view__aux___main___at_lean_parser_command_extends_has__view_x_27___spec__1(x_64);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_7);
lean::cnstr_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
obj* l_lean_parser_command_extends_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_list_map___main___at_lean_parser_command_extends_has__view_x_27___spec__2(x_3);
x_12 = l_list_join___main___rarg(x_11);
x_13 = l_lean_parser_no__kind;
lean::inc(x_13);
x_15 = l_lean_parser_syntax_mk__node(x_13, x_12);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_lean_parser_command_extends;
lean::inc(x_19);
x_21 = l_lean_parser_syntax_mk__node(x_19, x_18);
return x_21;
}
}
obj* _init_l_lean_parser_command_extends_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_extends_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_structure__ctor() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure_ctor");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_structure__ctor_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__ctor_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_23; 
lean::dec(x_2);
x_23 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_23);
x_20 = x_23;
goto lbl_21;
}
case 1:
{
obj* x_25; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_20 = x_25;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_29);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_32; 
lean::dec(x_2);
x_32 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_32);
x_20 = x_32;
goto lbl_21;
}
}
lbl_21:
{
obj* x_34; obj* x_35; obj* x_37; obj* x_38; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_40; 
x_40 = lean::box(3);
x_37 = x_1;
x_38 = x_40;
goto lbl_39;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
lean::dec(x_1);
x_37 = x_43;
x_38 = x_41;
goto lbl_39;
}
lbl_36:
{
switch (lean::obj_tag(x_35)) {
case 0:
{
obj* x_46; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_35, 0);
lean::inc(x_46);
lean::dec(x_35);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_46);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_20);
lean::cnstr_set(x_50, 1, x_34);
lean::cnstr_set(x_50, 2, x_49);
return x_50;
}
case 1:
{
obj* x_52; obj* x_53; 
lean::dec(x_35);
x_52 = lean::box(0);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_20);
lean::cnstr_set(x_53, 1, x_34);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
case 2:
{
obj* x_55; obj* x_56; 
lean::dec(x_35);
x_55 = lean::box(0);
x_56 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_56, 0, x_20);
lean::cnstr_set(x_56, 1, x_34);
lean::cnstr_set(x_56, 2, x_55);
return x_56;
}
default:
{
obj* x_58; obj* x_59; 
lean::dec(x_35);
x_58 = lean::box(0);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_20);
lean::cnstr_set(x_59, 1, x_34);
lean::cnstr_set(x_59, 2, x_58);
return x_59;
}
}
}
lbl_39:
{
obj* x_60; 
x_60 = l_lean_parser_syntax_as__node___main(x_38);
if (lean::obj_tag(x_60) == 0)
{
lean::dec(x_60);
if (lean::obj_tag(x_37) == 0)
{
obj* x_63; obj* x_64; obj* x_66; 
lean::dec(x_37);
x_63 = lean::box(0);
x_64 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_20);
lean::cnstr_set(x_66, 1, x_64);
lean::cnstr_set(x_66, 2, x_63);
return x_66;
}
else
{
obj* x_67; obj* x_70; 
x_67 = lean::cnstr_get(x_37, 0);
lean::inc(x_67);
lean::dec(x_37);
x_70 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_70);
x_34 = x_70;
x_35 = x_67;
goto lbl_36;
}
}
else
{
obj* x_72; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_60, 0);
lean::inc(x_72);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_74 = x_60;
}
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; 
lean::dec(x_75);
lean::dec(x_74);
x_80 = lean::box(0);
if (lean::obj_tag(x_37) == 0)
{
obj* x_83; 
lean::dec(x_37);
lean::inc(x_80);
x_83 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_83, 0, x_20);
lean::cnstr_set(x_83, 1, x_80);
lean::cnstr_set(x_83, 2, x_80);
return x_83;
}
else
{
obj* x_84; 
x_84 = lean::cnstr_get(x_37, 0);
lean::inc(x_84);
lean::dec(x_37);
x_34 = x_80;
x_35 = x_84;
goto lbl_36;
}
}
else
{
obj* x_87; obj* x_89; 
x_87 = lean::cnstr_get(x_75, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_75, 1);
lean::inc(x_89);
lean::dec(x_75);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; obj* x_94; obj* x_96; obj* x_97; 
lean::dec(x_89);
x_93 = l_lean_parser_command_infer__modifier_has__view;
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::apply_1(x_94, x_87);
if (lean::is_scalar(x_74)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_74;
}
lean::cnstr_set(x_97, 0, x_96);
if (lean::obj_tag(x_37) == 0)
{
obj* x_99; obj* x_100; 
lean::dec(x_37);
x_99 = lean::box(0);
x_100 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_100, 0, x_20);
lean::cnstr_set(x_100, 1, x_97);
lean::cnstr_set(x_100, 2, x_99);
return x_100;
}
else
{
obj* x_101; 
x_101 = lean::cnstr_get(x_37, 0);
lean::inc(x_101);
lean::dec(x_37);
x_34 = x_97;
x_35 = x_101;
goto lbl_36;
}
}
else
{
lean::dec(x_87);
lean::dec(x_74);
lean::dec(x_89);
if (lean::obj_tag(x_37) == 0)
{
obj* x_108; obj* x_109; obj* x_111; 
lean::dec(x_37);
x_108 = lean::box(0);
x_109 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_109);
x_111 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_111, 0, x_20);
lean::cnstr_set(x_111, 1, x_109);
lean::cnstr_set(x_111, 2, x_108);
return x_111;
}
else
{
obj* x_112; obj* x_115; 
x_112 = lean::cnstr_get(x_37, 0);
lean::inc(x_112);
lean::dec(x_37);
x_115 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_115);
x_34 = x_115;
x_35 = x_112;
goto lbl_36;
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; 
lean::dec(x_1);
x_8 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_8);
x_5 = x_8;
goto lbl_6;
}
case 1:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_5 = x_10;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_14);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_17; 
lean::dec(x_1);
x_17 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_17);
x_5 = x_17;
goto lbl_6;
}
}
lbl_6:
{
obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_25; 
x_25 = lean::box(3);
x_22 = x_0;
x_23 = x_25;
goto lbl_24;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
lean::dec(x_0);
x_22 = x_28;
x_23 = x_26;
goto lbl_24;
}
lbl_21:
{
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_31; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_20, 0);
lean::inc(x_31);
lean::dec(x_20);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_5);
lean::cnstr_set(x_35, 1, x_19);
lean::cnstr_set(x_35, 2, x_34);
return x_35;
}
case 1:
{
obj* x_37; obj* x_38; 
lean::dec(x_20);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_5);
lean::cnstr_set(x_38, 1, x_19);
lean::cnstr_set(x_38, 2, x_37);
return x_38;
}
case 2:
{
obj* x_40; obj* x_41; 
lean::dec(x_20);
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_5);
lean::cnstr_set(x_41, 1, x_19);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
default:
{
obj* x_43; obj* x_44; 
lean::dec(x_20);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_5);
lean::cnstr_set(x_44, 1, x_19);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
}
}
lbl_24:
{
obj* x_45; 
x_45 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_45) == 0)
{
lean::dec(x_45);
if (lean::obj_tag(x_22) == 0)
{
obj* x_48; obj* x_49; obj* x_51; 
lean::dec(x_22);
x_48 = lean::box(0);
x_49 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_5);
lean::cnstr_set(x_51, 1, x_49);
lean::cnstr_set(x_51, 2, x_48);
return x_51;
}
else
{
obj* x_52; obj* x_55; 
x_52 = lean::cnstr_get(x_22, 0);
lean::inc(x_52);
lean::dec(x_22);
x_55 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_55);
x_19 = x_55;
x_20 = x_52;
goto lbl_21;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_45, 0);
lean::inc(x_57);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 x_59 = x_45;
}
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_65; 
lean::dec(x_59);
lean::dec(x_60);
x_65 = lean::box(0);
if (lean::obj_tag(x_22) == 0)
{
obj* x_68; 
lean::dec(x_22);
lean::inc(x_65);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_5);
lean::cnstr_set(x_68, 1, x_65);
lean::cnstr_set(x_68, 2, x_65);
return x_68;
}
else
{
obj* x_69; 
x_69 = lean::cnstr_get(x_22, 0);
lean::inc(x_69);
lean::dec(x_22);
x_19 = x_65;
x_20 = x_69;
goto lbl_21;
}
}
else
{
obj* x_72; obj* x_74; 
x_72 = lean::cnstr_get(x_60, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_60, 1);
lean::inc(x_74);
lean::dec(x_60);
if (lean::obj_tag(x_74) == 0)
{
obj* x_78; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_74);
x_78 = l_lean_parser_command_infer__modifier_has__view;
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::apply_1(x_79, x_72);
if (lean::is_scalar(x_59)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_59;
}
lean::cnstr_set(x_82, 0, x_81);
if (lean::obj_tag(x_22) == 0)
{
obj* x_84; obj* x_85; 
lean::dec(x_22);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_85, 0, x_5);
lean::cnstr_set(x_85, 1, x_82);
lean::cnstr_set(x_85, 2, x_84);
return x_85;
}
else
{
obj* x_86; 
x_86 = lean::cnstr_get(x_22, 0);
lean::inc(x_86);
lean::dec(x_22);
x_19 = x_82;
x_20 = x_86;
goto lbl_21;
}
}
else
{
lean::dec(x_59);
lean::dec(x_72);
lean::dec(x_74);
if (lean::obj_tag(x_22) == 0)
{
obj* x_93; obj* x_94; obj* x_96; 
lean::dec(x_22);
x_93 = lean::box(0);
x_94 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_94);
x_96 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_96, 0, x_5);
lean::cnstr_set(x_96, 1, x_94);
lean::cnstr_set(x_96, 2, x_93);
return x_96;
}
else
{
obj* x_97; obj* x_100; 
x_97 = lean::cnstr_get(x_22, 0);
lean::inc(x_97);
lean::dec(x_22);
x_100 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1;
lean::inc(x_100);
x_19 = x_100;
x_20 = x_97;
goto lbl_21;
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_structure__ctor_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_1);
x_9 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_9);
x_11 = l_option_map___rarg(x_9, x_5);
x_12 = lean::box(3);
x_13 = l_option_get__or__else___main___rarg(x_11, x_12);
x_14 = lean::box(0);
lean::inc(x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
if (lean::obj_tag(x_3) == 0)
{
obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; 
lean::dec(x_14);
lean::dec(x_3);
x_19 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_16);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_lean_parser_command_structure__ctor;
lean::inc(x_23);
x_25 = l_lean_parser_syntax_mk__node(x_23, x_22);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
x_26 = lean::cnstr_get(x_3, 0);
lean::inc(x_26);
lean::dec(x_3);
x_29 = l_lean_parser_command_infer__modifier_has__view;
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_26);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_14);
x_34 = l_lean_parser_no__kind;
lean::inc(x_34);
x_36 = l_lean_parser_syntax_mk__node(x_34, x_33);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_16);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_structure__ctor;
lean::inc(x_39);
x_41 = l_lean_parser_syntax_mk__node(x_39, x_38);
return x_41;
}
}
}
obj* _init_l_lean_parser_command_structure__ctor_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_structure__ctor_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_structure() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("structure");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_structure_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__6;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_20 = l_lean_parser_command_structure__kw_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_27; 
x_27 = lean::box(3);
x_24 = x_1;
x_25 = x_27;
goto lbl_26;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_1, 1);
lean::inc(x_30);
lean::dec(x_1);
x_24 = x_30;
x_25 = x_28;
goto lbl_26;
}
lbl_26:
{
obj* x_33; obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; 
lean::dec(x_35);
x_37 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_37);
x_33 = x_37;
goto lbl_34;
}
else
{
obj* x_39; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_35, 0);
lean::inc(x_39);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_41 = x_35;
}
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; 
lean::dec(x_42);
lean::dec(x_41);
x_47 = lean::box(0);
x_33 = x_47;
goto lbl_34;
}
else
{
obj* x_48; obj* x_50; 
x_48 = lean::cnstr_get(x_42, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_42, 1);
lean::inc(x_50);
lean::dec(x_42);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_50);
x_54 = l_lean_parser_command_old__univ__params_has__view;
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::apply_1(x_55, x_48);
if (lean::is_scalar(x_41)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_41;
}
lean::cnstr_set(x_58, 0, x_57);
x_33 = x_58;
goto lbl_34;
}
else
{
obj* x_62; 
lean::dec(x_50);
lean::dec(x_48);
lean::dec(x_41);
x_62 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_62);
x_33 = x_62;
goto lbl_34;
}
}
}
lbl_34:
{
obj* x_64; obj* x_65; 
if (lean::obj_tag(x_24) == 0)
{
obj* x_67; 
x_67 = lean::box(3);
x_64 = x_24;
x_65 = x_67;
goto lbl_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_24, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_24, 1);
lean::inc(x_70);
lean::dec(x_24);
x_64 = x_70;
x_65 = x_68;
goto lbl_66;
}
lbl_66:
{
obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
x_73 = l_lean_parser_command_ident__univ__params_has__view;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::apply_1(x_74, x_65);
if (lean::obj_tag(x_64) == 0)
{
obj* x_80; 
x_80 = lean::box(3);
x_77 = x_64;
x_78 = x_80;
goto lbl_79;
}
else
{
obj* x_81; obj* x_83; 
x_81 = lean::cnstr_get(x_64, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_64, 1);
lean::inc(x_83);
lean::dec(x_64);
x_77 = x_83;
x_78 = x_81;
goto lbl_79;
}
lbl_79:
{
obj* x_86; obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
x_86 = l_lean_parser_command_opt__decl__sig_has__view;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::apply_1(x_87, x_78);
if (lean::obj_tag(x_77) == 0)
{
obj* x_93; 
x_93 = lean::box(3);
x_90 = x_77;
x_91 = x_93;
goto lbl_92;
}
else
{
obj* x_94; obj* x_96; 
x_94 = lean::cnstr_get(x_77, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_77, 1);
lean::inc(x_96);
lean::dec(x_77);
x_90 = x_96;
x_91 = x_94;
goto lbl_92;
}
lbl_92:
{
obj* x_99; obj* x_101; 
x_101 = l_lean_parser_syntax_as__node___main(x_91);
if (lean::obj_tag(x_101) == 0)
{
obj* x_103; 
lean::dec(x_101);
x_103 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4;
lean::inc(x_103);
x_99 = x_103;
goto lbl_100;
}
else
{
obj* x_105; obj* x_107; obj* x_108; 
x_105 = lean::cnstr_get(x_101, 0);
lean::inc(x_105);
if (lean::is_shared(x_101)) {
 lean::dec(x_101);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_101, 0);
 x_107 = x_101;
}
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
if (lean::obj_tag(x_108) == 0)
{
obj* x_113; 
lean::dec(x_108);
lean::dec(x_107);
x_113 = lean::box(0);
x_99 = x_113;
goto lbl_100;
}
else
{
obj* x_114; obj* x_116; 
x_114 = lean::cnstr_get(x_108, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_108, 1);
lean::inc(x_116);
lean::dec(x_108);
if (lean::obj_tag(x_116) == 0)
{
obj* x_120; obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_116);
x_120 = l_lean_parser_command_extends_has__view;
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::apply_1(x_121, x_114);
if (lean::is_scalar(x_107)) {
 x_124 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_124 = x_107;
}
lean::cnstr_set(x_124, 0, x_123);
x_99 = x_124;
goto lbl_100;
}
else
{
obj* x_128; 
lean::dec(x_107);
lean::dec(x_114);
lean::dec(x_116);
x_128 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4;
lean::inc(x_128);
x_99 = x_128;
goto lbl_100;
}
}
}
lbl_100:
{
obj* x_130; obj* x_131; 
if (lean::obj_tag(x_90) == 0)
{
obj* x_133; 
x_133 = lean::box(3);
x_130 = x_90;
x_131 = x_133;
goto lbl_132;
}
else
{
obj* x_134; obj* x_136; 
x_134 = lean::cnstr_get(x_90, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_90, 1);
lean::inc(x_136);
lean::dec(x_90);
x_130 = x_136;
x_131 = x_134;
goto lbl_132;
}
lbl_132:
{
obj* x_139; 
switch (lean::obj_tag(x_131)) {
case 0:
{
obj* x_141; obj* x_144; 
x_141 = lean::cnstr_get(x_131, 0);
lean::inc(x_141);
lean::dec(x_131);
x_144 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_144, 0, x_141);
x_139 = x_144;
goto lbl_140;
}
case 1:
{
obj* x_146; 
lean::dec(x_131);
x_146 = lean::box(0);
x_139 = x_146;
goto lbl_140;
}
case 2:
{
obj* x_148; 
lean::dec(x_131);
x_148 = lean::box(0);
x_139 = x_148;
goto lbl_140;
}
default:
{
obj* x_150; 
lean::dec(x_131);
x_150 = lean::box(0);
x_139 = x_150;
goto lbl_140;
}
}
lbl_140:
{
obj* x_151; obj* x_153; obj* x_154; obj* x_156; obj* x_157; 
if (lean::obj_tag(x_130) == 0)
{
obj* x_159; 
x_159 = lean::box(3);
x_156 = x_130;
x_157 = x_159;
goto lbl_158;
}
else
{
obj* x_160; obj* x_162; 
x_160 = lean::cnstr_get(x_130, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_130, 1);
lean::inc(x_162);
lean::dec(x_130);
x_156 = x_162;
x_157 = x_160;
goto lbl_158;
}
lbl_152:
{
obj* x_165; obj* x_166; 
x_165 = lean::box(3);
x_166 = l_lean_parser_syntax_as__node___main(x_165);
if (lean::obj_tag(x_166) == 0)
{
obj* x_168; obj* x_170; 
lean::dec(x_166);
x_168 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1;
lean::inc(x_168);
x_170 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_170, 0, x_23);
lean::cnstr_set(x_170, 1, x_33);
lean::cnstr_set(x_170, 2, x_76);
lean::cnstr_set(x_170, 3, x_89);
lean::cnstr_set(x_170, 4, x_99);
lean::cnstr_set(x_170, 5, x_139);
lean::cnstr_set(x_170, 6, x_151);
lean::cnstr_set(x_170, 7, x_168);
return x_170;
}
else
{
obj* x_171; obj* x_174; obj* x_177; obj* x_179; obj* x_180; 
x_171 = lean::cnstr_get(x_166, 0);
lean::inc(x_171);
lean::dec(x_166);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
lean::dec(x_171);
x_177 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2;
lean::inc(x_177);
x_179 = l_list_map___main___rarg(x_177, x_174);
x_180 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_180, 0, x_23);
lean::cnstr_set(x_180, 1, x_33);
lean::cnstr_set(x_180, 2, x_76);
lean::cnstr_set(x_180, 3, x_89);
lean::cnstr_set(x_180, 4, x_99);
lean::cnstr_set(x_180, 5, x_139);
lean::cnstr_set(x_180, 6, x_151);
lean::cnstr_set(x_180, 7, x_179);
return x_180;
}
}
lbl_155:
{
obj* x_181; 
x_181 = l_lean_parser_syntax_as__node___main(x_154);
if (lean::obj_tag(x_181) == 0)
{
obj* x_183; obj* x_185; 
lean::dec(x_181);
x_183 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1;
lean::inc(x_183);
x_185 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_185, 0, x_23);
lean::cnstr_set(x_185, 1, x_33);
lean::cnstr_set(x_185, 2, x_76);
lean::cnstr_set(x_185, 3, x_89);
lean::cnstr_set(x_185, 4, x_99);
lean::cnstr_set(x_185, 5, x_139);
lean::cnstr_set(x_185, 6, x_153);
lean::cnstr_set(x_185, 7, x_183);
return x_185;
}
else
{
obj* x_186; obj* x_189; obj* x_192; obj* x_194; obj* x_195; 
x_186 = lean::cnstr_get(x_181, 0);
lean::inc(x_186);
lean::dec(x_181);
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
lean::dec(x_186);
x_192 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2;
lean::inc(x_192);
x_194 = l_list_map___main___rarg(x_192, x_189);
x_195 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_195, 0, x_23);
lean::cnstr_set(x_195, 1, x_33);
lean::cnstr_set(x_195, 2, x_76);
lean::cnstr_set(x_195, 3, x_89);
lean::cnstr_set(x_195, 4, x_99);
lean::cnstr_set(x_195, 5, x_139);
lean::cnstr_set(x_195, 6, x_153);
lean::cnstr_set(x_195, 7, x_194);
return x_195;
}
}
lbl_158:
{
obj* x_196; 
x_196 = l_lean_parser_syntax_as__node___main(x_157);
if (lean::obj_tag(x_196) == 0)
{
lean::dec(x_196);
if (lean::obj_tag(x_156) == 0)
{
obj* x_199; 
lean::dec(x_156);
x_199 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_199);
x_151 = x_199;
goto lbl_152;
}
else
{
obj* x_201; obj* x_204; 
x_201 = lean::cnstr_get(x_156, 0);
lean::inc(x_201);
lean::dec(x_156);
x_204 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_204);
x_153 = x_204;
x_154 = x_201;
goto lbl_155;
}
}
else
{
obj* x_206; obj* x_208; obj* x_209; 
x_206 = lean::cnstr_get(x_196, 0);
lean::inc(x_206);
if (lean::is_shared(x_196)) {
 lean::dec(x_196);
 x_208 = lean::box(0);
} else {
 lean::cnstr_release(x_196, 0);
 x_208 = x_196;
}
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
lean::dec(x_206);
if (lean::obj_tag(x_209) == 0)
{
obj* x_214; 
lean::dec(x_209);
lean::dec(x_208);
x_214 = lean::box(0);
if (lean::obj_tag(x_156) == 0)
{
lean::dec(x_156);
x_151 = x_214;
goto lbl_152;
}
else
{
obj* x_216; 
x_216 = lean::cnstr_get(x_156, 0);
lean::inc(x_216);
lean::dec(x_156);
x_153 = x_214;
x_154 = x_216;
goto lbl_155;
}
}
else
{
obj* x_219; obj* x_221; 
x_219 = lean::cnstr_get(x_209, 0);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_209, 1);
lean::inc(x_221);
lean::dec(x_209);
if (lean::obj_tag(x_221) == 0)
{
obj* x_225; obj* x_226; obj* x_228; obj* x_229; 
lean::dec(x_221);
x_225 = l_lean_parser_command_structure__ctor_has__view;
x_226 = lean::cnstr_get(x_225, 0);
lean::inc(x_226);
x_228 = lean::apply_1(x_226, x_219);
if (lean::is_scalar(x_208)) {
 x_229 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_229 = x_208;
}
lean::cnstr_set(x_229, 0, x_228);
if (lean::obj_tag(x_156) == 0)
{
lean::dec(x_156);
x_151 = x_229;
goto lbl_152;
}
else
{
obj* x_231; 
x_231 = lean::cnstr_get(x_156, 0);
lean::inc(x_231);
lean::dec(x_156);
x_153 = x_229;
x_154 = x_231;
goto lbl_155;
}
}
else
{
lean::dec(x_221);
lean::dec(x_219);
lean::dec(x_208);
if (lean::obj_tag(x_156) == 0)
{
obj* x_238; 
lean::dec(x_156);
x_238 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_238);
x_151 = x_238;
goto lbl_152;
}
else
{
obj* x_240; obj* x_243; 
x_240 = lean::cnstr_get(x_156, 0);
lean::inc(x_240);
lean::dec(x_156);
x_243 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_243);
x_153 = x_243;
x_154 = x_240;
goto lbl_155;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_command_structure__field__block_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_structure__field__block_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_structure__ctor_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_extends_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_old__univ__params_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = l_lean_parser_command_structure__kw_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_12; 
x_12 = lean::box(3);
x_9 = x_0;
x_10 = x_12;
goto lbl_11;
}
else
{
obj* x_13; obj* x_15; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::dec(x_0);
x_9 = x_15;
x_10 = x_13;
goto lbl_11;
}
lbl_11:
{
obj* x_18; obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_10);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; 
lean::dec(x_20);
x_22 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_22);
x_18 = x_22;
goto lbl_19;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_26 = x_20;
}
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; 
lean::dec(x_26);
lean::dec(x_27);
x_32 = lean::box(0);
x_18 = x_32;
goto lbl_19;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_27, 1);
lean::inc(x_35);
lean::dec(x_27);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_35);
x_39 = l_lean_parser_command_old__univ__params_has__view;
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::apply_1(x_40, x_33);
if (lean::is_scalar(x_26)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_26;
}
lean::cnstr_set(x_43, 0, x_42);
x_18 = x_43;
goto lbl_19;
}
else
{
obj* x_47; 
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_26);
x_47 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_47);
x_18 = x_47;
goto lbl_19;
}
}
}
lbl_19:
{
obj* x_49; obj* x_50; 
if (lean::obj_tag(x_9) == 0)
{
obj* x_52; 
x_52 = lean::box(3);
x_49 = x_9;
x_50 = x_52;
goto lbl_51;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_9, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_9, 1);
lean::inc(x_55);
lean::dec(x_9);
x_49 = x_55;
x_50 = x_53;
goto lbl_51;
}
lbl_51:
{
obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
x_58 = l_lean_parser_command_ident__univ__params_has__view;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::apply_1(x_59, x_50);
if (lean::obj_tag(x_49) == 0)
{
obj* x_65; 
x_65 = lean::box(3);
x_62 = x_49;
x_63 = x_65;
goto lbl_64;
}
else
{
obj* x_66; obj* x_68; 
x_66 = lean::cnstr_get(x_49, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_49, 1);
lean::inc(x_68);
lean::dec(x_49);
x_62 = x_68;
x_63 = x_66;
goto lbl_64;
}
lbl_64:
{
obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
x_71 = l_lean_parser_command_opt__decl__sig_has__view;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::apply_1(x_72, x_63);
if (lean::obj_tag(x_62) == 0)
{
obj* x_78; 
x_78 = lean::box(3);
x_75 = x_62;
x_76 = x_78;
goto lbl_77;
}
else
{
obj* x_79; obj* x_81; 
x_79 = lean::cnstr_get(x_62, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_62, 1);
lean::inc(x_81);
lean::dec(x_62);
x_75 = x_81;
x_76 = x_79;
goto lbl_77;
}
lbl_77:
{
obj* x_84; obj* x_86; 
x_86 = l_lean_parser_syntax_as__node___main(x_76);
if (lean::obj_tag(x_86) == 0)
{
obj* x_88; 
lean::dec(x_86);
x_88 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4;
lean::inc(x_88);
x_84 = x_88;
goto lbl_85;
}
else
{
obj* x_90; obj* x_92; obj* x_93; 
x_90 = lean::cnstr_get(x_86, 0);
lean::inc(x_90);
if (lean::is_shared(x_86)) {
 lean::dec(x_86);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_86, 0);
 x_92 = x_86;
}
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
if (lean::obj_tag(x_93) == 0)
{
obj* x_98; 
lean::dec(x_92);
lean::dec(x_93);
x_98 = lean::box(0);
x_84 = x_98;
goto lbl_85;
}
else
{
obj* x_99; obj* x_101; 
x_99 = lean::cnstr_get(x_93, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_93, 1);
lean::inc(x_101);
lean::dec(x_93);
if (lean::obj_tag(x_101) == 0)
{
obj* x_105; obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_101);
x_105 = l_lean_parser_command_extends_has__view;
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::apply_1(x_106, x_99);
if (lean::is_scalar(x_92)) {
 x_109 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_109 = x_92;
}
lean::cnstr_set(x_109, 0, x_108);
x_84 = x_109;
goto lbl_85;
}
else
{
obj* x_113; 
lean::dec(x_92);
lean::dec(x_99);
lean::dec(x_101);
x_113 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4;
lean::inc(x_113);
x_84 = x_113;
goto lbl_85;
}
}
}
lbl_85:
{
obj* x_115; obj* x_116; 
if (lean::obj_tag(x_75) == 0)
{
obj* x_118; 
x_118 = lean::box(3);
x_115 = x_75;
x_116 = x_118;
goto lbl_117;
}
else
{
obj* x_119; obj* x_121; 
x_119 = lean::cnstr_get(x_75, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_75, 1);
lean::inc(x_121);
lean::dec(x_75);
x_115 = x_121;
x_116 = x_119;
goto lbl_117;
}
lbl_117:
{
obj* x_124; 
switch (lean::obj_tag(x_116)) {
case 0:
{
obj* x_126; obj* x_129; 
x_126 = lean::cnstr_get(x_116, 0);
lean::inc(x_126);
lean::dec(x_116);
x_129 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_129, 0, x_126);
x_124 = x_129;
goto lbl_125;
}
case 1:
{
obj* x_131; 
lean::dec(x_116);
x_131 = lean::box(0);
x_124 = x_131;
goto lbl_125;
}
case 2:
{
obj* x_133; 
lean::dec(x_116);
x_133 = lean::box(0);
x_124 = x_133;
goto lbl_125;
}
default:
{
obj* x_135; 
lean::dec(x_116);
x_135 = lean::box(0);
x_124 = x_135;
goto lbl_125;
}
}
lbl_125:
{
obj* x_136; obj* x_138; obj* x_139; obj* x_141; obj* x_142; 
if (lean::obj_tag(x_115) == 0)
{
obj* x_144; 
x_144 = lean::box(3);
x_141 = x_115;
x_142 = x_144;
goto lbl_143;
}
else
{
obj* x_145; obj* x_147; 
x_145 = lean::cnstr_get(x_115, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_115, 1);
lean::inc(x_147);
lean::dec(x_115);
x_141 = x_147;
x_142 = x_145;
goto lbl_143;
}
lbl_137:
{
obj* x_150; obj* x_151; 
x_150 = lean::box(3);
x_151 = l_lean_parser_syntax_as__node___main(x_150);
if (lean::obj_tag(x_151) == 0)
{
obj* x_153; obj* x_155; 
lean::dec(x_151);
x_153 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1;
lean::inc(x_153);
x_155 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_155, 0, x_8);
lean::cnstr_set(x_155, 1, x_18);
lean::cnstr_set(x_155, 2, x_61);
lean::cnstr_set(x_155, 3, x_74);
lean::cnstr_set(x_155, 4, x_84);
lean::cnstr_set(x_155, 5, x_124);
lean::cnstr_set(x_155, 6, x_136);
lean::cnstr_set(x_155, 7, x_153);
return x_155;
}
else
{
obj* x_156; obj* x_159; obj* x_162; obj* x_164; obj* x_165; 
x_156 = lean::cnstr_get(x_151, 0);
lean::inc(x_156);
lean::dec(x_151);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
x_162 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2;
lean::inc(x_162);
x_164 = l_list_map___main___rarg(x_162, x_159);
x_165 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_165, 0, x_8);
lean::cnstr_set(x_165, 1, x_18);
lean::cnstr_set(x_165, 2, x_61);
lean::cnstr_set(x_165, 3, x_74);
lean::cnstr_set(x_165, 4, x_84);
lean::cnstr_set(x_165, 5, x_124);
lean::cnstr_set(x_165, 6, x_136);
lean::cnstr_set(x_165, 7, x_164);
return x_165;
}
}
lbl_140:
{
obj* x_166; 
x_166 = l_lean_parser_syntax_as__node___main(x_139);
if (lean::obj_tag(x_166) == 0)
{
obj* x_168; obj* x_170; 
lean::dec(x_166);
x_168 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1;
lean::inc(x_168);
x_170 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_170, 0, x_8);
lean::cnstr_set(x_170, 1, x_18);
lean::cnstr_set(x_170, 2, x_61);
lean::cnstr_set(x_170, 3, x_74);
lean::cnstr_set(x_170, 4, x_84);
lean::cnstr_set(x_170, 5, x_124);
lean::cnstr_set(x_170, 6, x_138);
lean::cnstr_set(x_170, 7, x_168);
return x_170;
}
else
{
obj* x_171; obj* x_174; obj* x_177; obj* x_179; obj* x_180; 
x_171 = lean::cnstr_get(x_166, 0);
lean::inc(x_171);
lean::dec(x_166);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
lean::dec(x_171);
x_177 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2;
lean::inc(x_177);
x_179 = l_list_map___main___rarg(x_177, x_174);
x_180 = lean::alloc_cnstr(0, 8, 0);
lean::cnstr_set(x_180, 0, x_8);
lean::cnstr_set(x_180, 1, x_18);
lean::cnstr_set(x_180, 2, x_61);
lean::cnstr_set(x_180, 3, x_74);
lean::cnstr_set(x_180, 4, x_84);
lean::cnstr_set(x_180, 5, x_124);
lean::cnstr_set(x_180, 6, x_138);
lean::cnstr_set(x_180, 7, x_179);
return x_180;
}
}
lbl_143:
{
obj* x_181; 
x_181 = l_lean_parser_syntax_as__node___main(x_142);
if (lean::obj_tag(x_181) == 0)
{
lean::dec(x_181);
if (lean::obj_tag(x_141) == 0)
{
obj* x_184; 
lean::dec(x_141);
x_184 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_184);
x_136 = x_184;
goto lbl_137;
}
else
{
obj* x_186; obj* x_189; 
x_186 = lean::cnstr_get(x_141, 0);
lean::inc(x_186);
lean::dec(x_141);
x_189 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_189);
x_138 = x_189;
x_139 = x_186;
goto lbl_140;
}
}
else
{
obj* x_191; obj* x_193; obj* x_194; 
x_191 = lean::cnstr_get(x_181, 0);
lean::inc(x_191);
if (lean::is_shared(x_181)) {
 lean::dec(x_181);
 x_193 = lean::box(0);
} else {
 lean::cnstr_release(x_181, 0);
 x_193 = x_181;
}
x_194 = lean::cnstr_get(x_191, 1);
lean::inc(x_194);
lean::dec(x_191);
if (lean::obj_tag(x_194) == 0)
{
obj* x_199; 
lean::dec(x_194);
lean::dec(x_193);
x_199 = lean::box(0);
if (lean::obj_tag(x_141) == 0)
{
lean::dec(x_141);
x_136 = x_199;
goto lbl_137;
}
else
{
obj* x_201; 
x_201 = lean::cnstr_get(x_141, 0);
lean::inc(x_201);
lean::dec(x_141);
x_138 = x_199;
x_139 = x_201;
goto lbl_140;
}
}
else
{
obj* x_204; obj* x_206; 
x_204 = lean::cnstr_get(x_194, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_194, 1);
lean::inc(x_206);
lean::dec(x_194);
if (lean::obj_tag(x_206) == 0)
{
obj* x_210; obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_206);
x_210 = l_lean_parser_command_structure__ctor_has__view;
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
x_213 = lean::apply_1(x_211, x_204);
if (lean::is_scalar(x_193)) {
 x_214 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_214 = x_193;
}
lean::cnstr_set(x_214, 0, x_213);
if (lean::obj_tag(x_141) == 0)
{
lean::dec(x_141);
x_136 = x_214;
goto lbl_137;
}
else
{
obj* x_216; 
x_216 = lean::cnstr_get(x_141, 0);
lean::inc(x_216);
lean::dec(x_141);
x_138 = x_214;
x_139 = x_216;
goto lbl_140;
}
}
else
{
lean::dec(x_206);
lean::dec(x_204);
lean::dec(x_193);
if (lean::obj_tag(x_141) == 0)
{
obj* x_223; 
lean::dec(x_141);
x_223 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_223);
x_136 = x_223;
goto lbl_137;
}
else
{
obj* x_225; obj* x_228; 
x_225 = lean::cnstr_get(x_141, 0);
lean::inc(x_225);
lean::dec(x_141);
x_228 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3;
lean::inc(x_228);
x_138 = x_228;
x_139 = x_225;
goto lbl_140;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_structure_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 7);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_lean_parser_command_structure__kw_has__view;
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
x_21 = lean::apply_1(x_19, x_1);
x_22 = l_lean_parser_command_ident__univ__params_has__view;
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = lean::apply_1(x_23, x_5);
x_26 = l_lean_parser_command_opt__decl__sig_has__view;
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_7);
x_30 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_30);
x_32 = l_option_map___rarg(x_30, x_11);
x_33 = lean::box(3);
x_34 = l_option_get__or__else___main___rarg(x_32, x_33);
x_35 = l_lean_parser_command_structure_has__view_x_27___lambda__2___closed__1;
lean::inc(x_35);
x_37 = l_list_map___main___rarg(x_35, x_15);
x_38 = l_lean_parser_no__kind;
lean::inc(x_38);
x_40 = l_lean_parser_syntax_mk__node(x_38, x_37);
x_41 = lean::box(0);
lean::inc(x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
if (lean::obj_tag(x_9) == 0)
{
obj* x_51; 
lean::dec(x_9);
x_51 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_51);
x_44 = x_51;
goto lbl_45;
}
else
{
obj* x_53; obj* x_56; 
x_53 = lean::cnstr_get(x_9, 0);
lean::inc(x_53);
lean::dec(x_9);
x_56 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_56);
x_46 = x_56;
x_47 = x_53;
goto lbl_48;
}
}
else
{
obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; 
x_58 = lean::cnstr_get(x_3, 0);
lean::inc(x_58);
lean::dec(x_3);
x_61 = l_lean_parser_command_old__univ__params_has__view;
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_64 = lean::apply_1(x_62, x_58);
lean::inc(x_41);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_41);
lean::inc(x_38);
x_68 = l_lean_parser_syntax_mk__node(x_38, x_66);
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_9);
x_44 = x_68;
goto lbl_45;
}
else
{
obj* x_70; 
x_70 = lean::cnstr_get(x_9, 0);
lean::inc(x_70);
lean::dec(x_9);
x_46 = x_68;
x_47 = x_70;
goto lbl_48;
}
}
lbl_45:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_87; 
lean::dec(x_13);
lean::dec(x_41);
x_75 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_43);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_34);
lean::cnstr_set(x_78, 1, x_77);
lean::inc(x_75);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_75);
lean::cnstr_set(x_80, 1, x_78);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_29);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_25);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_44);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_21);
lean::cnstr_set(x_84, 1, x_83);
x_85 = l_lean_parser_command_structure;
lean::inc(x_85);
x_87 = l_lean_parser_syntax_mk__node(x_85, x_84);
return x_87;
}
else
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_109; 
x_88 = lean::cnstr_get(x_13, 0);
lean::inc(x_88);
lean::dec(x_13);
x_91 = l_lean_parser_command_structure__ctor_has__view;
x_92 = lean::cnstr_get(x_91, 1);
lean::inc(x_92);
x_94 = lean::apply_1(x_92, x_88);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_41);
lean::inc(x_38);
x_97 = l_lean_parser_syntax_mk__node(x_38, x_95);
x_98 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_43);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_34);
lean::cnstr_set(x_99, 1, x_98);
x_100 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_100);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_99);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_29);
lean::cnstr_set(x_103, 1, x_102);
x_104 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_104, 0, x_25);
lean::cnstr_set(x_104, 1, x_103);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_44);
lean::cnstr_set(x_105, 1, x_104);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_21);
lean::cnstr_set(x_106, 1, x_105);
x_107 = l_lean_parser_command_structure;
lean::inc(x_107);
x_109 = l_lean_parser_syntax_mk__node(x_107, x_106);
return x_109;
}
}
lbl_48:
{
obj* x_110; obj* x_111; obj* x_113; obj* x_115; obj* x_117; 
x_110 = l_lean_parser_command_extends_has__view;
x_111 = lean::cnstr_get(x_110, 1);
lean::inc(x_111);
x_113 = lean::apply_1(x_111, x_47);
lean::inc(x_41);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_41);
lean::inc(x_38);
x_117 = l_lean_parser_syntax_mk__node(x_38, x_115);
if (lean::obj_tag(x_13) == 0)
{
obj* x_120; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_131; 
lean::dec(x_13);
lean::dec(x_41);
x_120 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_120);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_43);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_34);
lean::cnstr_set(x_123, 1, x_122);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_117);
lean::cnstr_set(x_124, 1, x_123);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_29);
lean::cnstr_set(x_125, 1, x_124);
x_126 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_126, 0, x_25);
lean::cnstr_set(x_126, 1, x_125);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_46);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_21);
lean::cnstr_set(x_128, 1, x_127);
x_129 = l_lean_parser_command_structure;
lean::inc(x_129);
x_131 = l_lean_parser_syntax_mk__node(x_129, x_128);
return x_131;
}
else
{
obj* x_132; obj* x_135; obj* x_136; obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_151; 
x_132 = lean::cnstr_get(x_13, 0);
lean::inc(x_132);
lean::dec(x_13);
x_135 = l_lean_parser_command_structure__ctor_has__view;
x_136 = lean::cnstr_get(x_135, 1);
lean::inc(x_136);
x_138 = lean::apply_1(x_136, x_132);
x_139 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_41);
lean::inc(x_38);
x_141 = l_lean_parser_syntax_mk__node(x_38, x_139);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_43);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_34);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_117);
lean::cnstr_set(x_144, 1, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_29);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_146, 0, x_25);
lean::cnstr_set(x_146, 1, x_145);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_46);
lean::cnstr_set(x_147, 1, x_146);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_21);
lean::cnstr_set(x_148, 1, x_147);
x_149 = l_lean_parser_command_structure;
lean::inc(x_149);
x_151 = l_lean_parser_syntax_mk__node(x_149, x_148);
return x_151;
}
}
}
}
obj* _init_l_lean_parser_command_structure_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_structure__field__block_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_structure_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_structure_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_structure_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_97; 
x_0 = lean::mk_string("structure");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("class");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_15);
lean::inc(x_4);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_18, 0, x_16);
lean::closure_set(x_18, 1, x_4);
lean::inc(x_13);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_13);
x_21 = l_lean_parser_command_structure__kw;
lean::inc(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_old__univ__params_parser), 4, 0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_25, 0, x_24);
x_26 = lean::mk_string("extends");
x_27 = l_string_trim(x_26);
lean::inc(x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_29, 0, x_27);
lean::inc(x_4);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_4);
lean::closure_set(x_31, 2, x_29);
lean::inc(x_4);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_33, 0, x_4);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_34, 0, x_33);
x_35 = lean::mk_string(",");
x_36 = l_string_trim(x_35);
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_38, 0, x_36);
lean::inc(x_4);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_4);
lean::closure_set(x_40, 2, x_38);
x_41 = 1;
x_42 = lean::box(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1___boxed), 7, 3);
lean::closure_set(x_43, 0, x_34);
lean::closure_set(x_43, 1, x_40);
lean::closure_set(x_43, 2, x_42);
lean::inc(x_13);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_13);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_31);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_parser_command_extends;
lean::inc(x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_49, 0, x_47);
lean::closure_set(x_49, 1, x_46);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_50, 0, x_49);
x_51 = lean::mk_string(":=");
x_52 = l_string_trim(x_51);
lean::inc(x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_54, 0, x_52);
lean::inc(x_4);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_56, 0, x_52);
lean::closure_set(x_56, 1, x_4);
lean::closure_set(x_56, 2, x_54);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser), 4, 0);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_58, 0, x_57);
x_59 = lean::mk_string("::");
x_60 = l_string_trim(x_59);
lean::inc(x_60);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_62, 0, x_60);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_63, 0, x_60);
lean::closure_set(x_63, 1, x_4);
lean::closure_set(x_63, 2, x_62);
lean::inc(x_13);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_13);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_58);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
x_69 = l_lean_parser_command_structure__ctor;
lean::inc(x_69);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_71, 0, x_69);
lean::closure_set(x_71, 1, x_68);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_72, 0, x_71);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__field__block_parser), 4, 0);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2), 5, 1);
lean::closure_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_13);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_72);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_56);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_50);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_ident__univ__params_parser), 4, 0);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_25);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_23);
lean::cnstr_set(x_84, 1, x_83);
x_85 = l_lean_parser_command__parser__m_monad___closed__1;
x_86 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_87 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_88 = l_lean_parser_command__parser__m_alternative___closed__1;
x_89 = l_lean_parser_command_structure;
x_90 = l_lean_parser_command_structure_has__view;
lean::inc(x_90);
lean::inc(x_89);
lean::inc(x_88);
lean::inc(x_87);
lean::inc(x_86);
lean::inc(x_85);
x_97 = l_lean_parser_combinators_node_view___rarg(x_85, x_86, x_87, x_88, x_89, x_84, x_90);
return x_97;
}
}
obj* _init_l_lean_parser_command_structure_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_0 = lean::mk_string("structure");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::mk_string("class");
lean::inc(x_1);
x_6 = l_lean_parser_symbol_tokens___rarg(x_4, x_1);
x_7 = lean::box(0);
lean::inc(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_6, x_7);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_3, x_9);
x_11 = l_lean_parser_tokens___rarg(x_10);
lean::inc(x_7);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_11, x_7);
x_14 = l_lean_parser_tokens___rarg(x_13);
x_15 = l_lean_parser_command_old__univ__params_parser_lean_parser_has__tokens;
lean::inc(x_15);
x_17 = l_lean_parser_tokens___rarg(x_15);
x_18 = lean::mk_string("extends");
lean::inc(x_1);
x_20 = l_lean_parser_symbol_tokens___rarg(x_18, x_1);
x_21 = l_lean_parser_term_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_21);
x_23 = l_lean_parser_tokens___rarg(x_21);
x_24 = lean::mk_string(",");
lean::inc(x_1);
x_26 = l_lean_parser_symbol_tokens___rarg(x_24, x_1);
x_27 = l_lean_parser_combinators_sep__by1_tokens___rarg(x_23, x_26);
lean::inc(x_7);
x_29 = l_lean_parser_list_cons_tokens___rarg(x_27, x_7);
x_30 = l_lean_parser_list_cons_tokens___rarg(x_20, x_29);
x_31 = l_lean_parser_tokens___rarg(x_30);
x_32 = l_lean_parser_tokens___rarg(x_31);
x_33 = lean::mk_string(":=");
lean::inc(x_1);
x_35 = l_lean_parser_symbol_tokens___rarg(x_33, x_1);
x_36 = l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens;
lean::inc(x_36);
x_38 = l_lean_parser_tokens___rarg(x_36);
x_39 = lean::mk_string("::");
x_40 = l_lean_parser_symbol_tokens___rarg(x_39, x_1);
lean::inc(x_7);
x_42 = l_lean_parser_list_cons_tokens___rarg(x_40, x_7);
x_43 = l_lean_parser_list_cons_tokens___rarg(x_38, x_42);
lean::inc(x_7);
x_45 = l_lean_parser_list_cons_tokens___rarg(x_7, x_43);
x_46 = l_lean_parser_tokens___rarg(x_45);
x_47 = l_lean_parser_tokens___rarg(x_46);
x_48 = l_lean_parser_command_structure__field__block_parser_lean_parser_has__tokens;
lean::inc(x_48);
x_50 = l_lean_parser_tokens___rarg(x_48);
x_51 = l_lean_parser_list_cons_tokens___rarg(x_50, x_7);
x_52 = l_lean_parser_list_cons_tokens___rarg(x_47, x_51);
x_53 = l_lean_parser_list_cons_tokens___rarg(x_35, x_52);
x_54 = l_lean_parser_list_cons_tokens___rarg(x_32, x_53);
x_55 = l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens;
lean::inc(x_55);
x_57 = l_lean_parser_list_cons_tokens___rarg(x_55, x_54);
x_58 = l_lean_parser_command_ident__univ__params_parser_lean_parser_has__tokens;
lean::inc(x_58);
x_60 = l_lean_parser_list_cons_tokens___rarg(x_58, x_57);
x_61 = l_lean_parser_list_cons_tokens___rarg(x_17, x_60);
x_62 = l_lean_parser_list_cons_tokens___rarg(x_14, x_61);
x_63 = l_lean_parser_tokens___rarg(x_62);
return x_63;
}
}
obj* l_lean_parser_command_structure_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_structure;
x_5 = l_lean_parser_command_structure_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_structure_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_0 = lean::mk_string("structure");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("class");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_15);
lean::inc(x_4);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_18, 0, x_16);
lean::closure_set(x_18, 1, x_4);
lean::inc(x_13);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_13);
x_21 = l_lean_parser_command_structure__kw;
lean::inc(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_old__univ__params_parser), 4, 0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_25, 0, x_24);
x_26 = lean::mk_string("extends");
x_27 = l_string_trim(x_26);
lean::inc(x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_29, 0, x_27);
lean::inc(x_4);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_31, 0, x_27);
lean::closure_set(x_31, 1, x_4);
lean::closure_set(x_31, 2, x_29);
lean::inc(x_4);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term_parser), 6, 1);
lean::closure_set(x_33, 0, x_4);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_34, 0, x_33);
x_35 = lean::mk_string(",");
x_36 = l_string_trim(x_35);
lean::inc(x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_38, 0, x_36);
lean::inc(x_4);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_40, 0, x_36);
lean::closure_set(x_40, 1, x_4);
lean::closure_set(x_40, 2, x_38);
x_41 = 1;
x_42 = lean::box(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_sep__by1___at_lean_parser_command_decl__attributes_parser_lean_parser_has__view___spec__1___boxed), 7, 3);
lean::closure_set(x_43, 0, x_34);
lean::closure_set(x_43, 1, x_40);
lean::closure_set(x_43, 2, x_42);
lean::inc(x_13);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_13);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_31);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_parser_command_extends;
lean::inc(x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_49, 0, x_47);
lean::closure_set(x_49, 1, x_46);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_50, 0, x_49);
x_51 = lean::mk_string(":=");
x_52 = l_string_trim(x_51);
lean::inc(x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_54, 0, x_52);
lean::inc(x_4);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_56, 0, x_52);
lean::closure_set(x_56, 1, x_4);
lean::closure_set(x_56, 2, x_54);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_infer__modifier_parser), 4, 0);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_58, 0, x_57);
x_59 = lean::mk_string("::");
x_60 = l_string_trim(x_59);
lean::inc(x_60);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_62, 0, x_60);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_63, 0, x_60);
lean::closure_set(x_63, 1, x_4);
lean::closure_set(x_63, 2, x_62);
lean::inc(x_13);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_13);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_58);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_command_intro__rule_parser_lean_parser_has__view___spec__1), 4, 0);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
x_69 = l_lean_parser_command_structure__ctor;
lean::inc(x_69);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_71, 0, x_69);
lean::closure_set(x_71, 1, x_68);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_72, 0, x_71);
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure__field__block_parser), 4, 0);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2), 5, 1);
lean::closure_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_13);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_72);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_56);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_50);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_ident__univ__params_parser), 4, 0);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_25);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_23);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
obj* _init_l_lean_parser_command_def__like_kind() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("def_like");
x_8 = lean::name_mk_string(x_6, x_7);
x_9 = lean::mk_string("kind");
x_10 = lean::name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_def__like_kind_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__5;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_86; uint8 x_87; 
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_dec_eq(x_2, x_86);
lean::dec(x_86);
lean::dec(x_2);
if (x_87 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_90; obj* x_93; obj* x_94; 
x_90 = lean::cnstr_get(x_1, 0);
lean::inc(x_90);
lean::dec(x_1);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_90);
x_94 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
return x_94;
}
case 1:
{
obj* x_96; 
lean::dec(x_1);
x_96 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
return x_96;
}
case 2:
{
obj* x_99; 
lean::dec(x_1);
x_99 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
return x_99;
}
default:
{
obj* x_102; 
lean::dec(x_1);
x_102 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
return x_102;
}
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_104; obj* x_107; obj* x_108; 
x_104 = lean::cnstr_get(x_1, 0);
lean::inc(x_104);
lean::dec(x_1);
x_107 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_107, 0, x_104);
x_108 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
case 1:
{
obj* x_110; 
lean::dec(x_1);
x_110 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
lean::inc(x_110);
return x_110;
}
case 2:
{
obj* x_113; 
lean::dec(x_1);
x_113 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
lean::inc(x_113);
return x_113;
}
default:
{
obj* x_116; 
lean::dec(x_1);
x_116 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
lean::inc(x_116);
return x_116;
}
}
}
}
else
{
lean::dec(x_2);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_119; obj* x_122; obj* x_123; 
x_119 = lean::cnstr_get(x_1, 0);
lean::inc(x_119);
lean::dec(x_1);
x_122 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_122, 0, x_119);
x_123 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_123, 0, x_122);
return x_123;
}
case 1:
{
obj* x_125; 
lean::dec(x_1);
x_125 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
lean::inc(x_125);
return x_125;
}
case 2:
{
obj* x_128; 
lean::dec(x_1);
x_128 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
lean::inc(x_128);
return x_128;
}
default:
{
obj* x_131; 
lean::dec(x_1);
x_131 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
lean::inc(x_131);
return x_131;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
if (x_9 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_12; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
x_16 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
case 1:
{
obj* x_18; 
lean::dec(x_0);
x_18 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
return x_18;
}
case 2:
{
obj* x_21; 
lean::dec(x_0);
x_21 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
default:
{
obj* x_24; 
lean::dec(x_0);
x_24 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1;
lean::inc(x_24);
return x_24;
}
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_26; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
case 1:
{
obj* x_32; 
lean::dec(x_0);
x_32 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
lean::inc(x_32);
return x_32;
}
case 2:
{
obj* x_35; 
lean::dec(x_0);
x_35 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
lean::inc(x_35);
return x_35;
}
default:
{
obj* x_38; 
lean::dec(x_0);
x_38 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2;
lean::inc(x_38);
return x_38;
}
}
}
}
else
{
lean::dec(x_1);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_0, 0);
lean::inc(x_41);
lean::dec(x_0);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_41);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
case 1:
{
obj* x_47; 
lean::dec(x_0);
x_47 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
lean::inc(x_47);
return x_47;
}
case 2:
{
obj* x_50; 
lean::dec(x_0);
x_50 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
lean::inc(x_50);
return x_50;
}
default:
{
obj* x_53; 
lean::dec(x_0);
x_53 = l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3;
lean::inc(x_53);
return x_53;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("def_like");
x_8 = lean::name_mk_string(x_6, x_7);
x_9 = lean::mk_string("kind");
x_10 = lean::name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_lean_parser_command_def__like_kind_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_5);
x_7 = l_option_map___rarg(x_5, x_2);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_1);
x_12 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = l_lean_parser_command_def__like_kind;
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mk__node(x_16, x_15);
return x_18;
}
case 1:
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_22);
x_24 = l_option_map___rarg(x_22, x_19);
x_25 = lean::box(3);
x_26 = l_option_get__or__else___main___rarg(x_24, x_25);
lean::inc(x_1);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_command_def__like_kind;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; 
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_39);
x_41 = l_option_map___rarg(x_39, x_36);
x_42 = lean::box(3);
x_43 = l_option_get__or__else___main___rarg(x_41, x_42);
lean::inc(x_1);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_1);
x_46 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_syntax_mk__node(x_46, x_45);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_1);
x_50 = l_lean_parser_command_def__like_kind;
lean::inc(x_50);
x_52 = l_lean_parser_syntax_mk__node(x_50, x_49);
return x_52;
}
}
}
}
obj* _init_l_lean_parser_command_def__like_kind_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_def__like_kind_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_def__like() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("def_like");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_def__like_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_def__like_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_def__like_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_def__like_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_20 = l_lean_parser_command_def__like_kind_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_27; 
x_27 = lean::box(3);
x_24 = x_1;
x_25 = x_27;
goto lbl_26;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_1, 1);
lean::inc(x_30);
lean::dec(x_1);
x_24 = x_30;
x_25 = x_28;
goto lbl_26;
}
lbl_26:
{
obj* x_33; obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; 
lean::dec(x_35);
x_37 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_37);
x_33 = x_37;
goto lbl_34;
}
else
{
obj* x_39; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_35, 0);
lean::inc(x_39);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_41 = x_35;
}
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; 
lean::dec(x_42);
lean::dec(x_41);
x_47 = lean::box(0);
x_33 = x_47;
goto lbl_34;
}
else
{
obj* x_48; obj* x_50; 
x_48 = lean::cnstr_get(x_42, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_42, 1);
lean::inc(x_50);
lean::dec(x_42);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_50);
x_54 = l_lean_parser_command_old__univ__params_has__view;
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::apply_1(x_55, x_48);
if (lean::is_scalar(x_41)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_41;
}
lean::cnstr_set(x_58, 0, x_57);
x_33 = x_58;
goto lbl_34;
}
else
{
obj* x_62; 
lean::dec(x_50);
lean::dec(x_48);
lean::dec(x_41);
x_62 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_62);
x_33 = x_62;
goto lbl_34;
}
}
}
lbl_34:
{
obj* x_64; obj* x_65; 
if (lean::obj_tag(x_24) == 0)
{
obj* x_67; 
x_67 = lean::box(3);
x_64 = x_24;
x_65 = x_67;
goto lbl_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_24, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_24, 1);
lean::inc(x_70);
lean::dec(x_24);
x_64 = x_70;
x_65 = x_68;
goto lbl_66;
}
lbl_66:
{
obj* x_73; obj* x_74; obj* x_76; 
x_73 = l_lean_parser_command_ident__univ__params_has__view;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::apply_1(x_74, x_65);
if (lean::obj_tag(x_64) == 0)
{
if (lean::obj_tag(x_64) == 0)
{
obj* x_78; obj* x_79; obj* x_82; 
lean::dec(x_64);
x_78 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
x_79 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_79);
lean::inc(x_78);
x_82 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_82, 0, x_23);
lean::cnstr_set(x_82, 1, x_33);
lean::cnstr_set(x_82, 2, x_76);
lean::cnstr_set(x_82, 3, x_78);
lean::cnstr_set(x_82, 4, x_79);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_87; obj* x_89; obj* x_90; obj* x_92; 
x_83 = lean::cnstr_get(x_64, 0);
lean::inc(x_83);
lean::dec(x_64);
x_86 = l_lean_parser_command_decl__val_has__view;
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::apply_1(x_87, x_83);
x_90 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_90);
x_92 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_92, 0, x_23);
lean::cnstr_set(x_92, 1, x_33);
lean::cnstr_set(x_92, 2, x_76);
lean::cnstr_set(x_92, 3, x_90);
lean::cnstr_set(x_92, 4, x_89);
return x_92;
}
}
else
{
obj* x_93; obj* x_95; obj* x_98; obj* x_99; obj* x_101; 
x_93 = lean::cnstr_get(x_64, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_64, 1);
lean::inc(x_95);
lean::dec(x_64);
x_98 = l_lean_parser_command_opt__decl__sig_has__view;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::apply_1(x_99, x_93);
if (lean::obj_tag(x_95) == 0)
{
obj* x_103; obj* x_105; 
lean::dec(x_95);
x_103 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_103);
x_105 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_105, 0, x_23);
lean::cnstr_set(x_105, 1, x_33);
lean::cnstr_set(x_105, 2, x_76);
lean::cnstr_set(x_105, 3, x_101);
lean::cnstr_set(x_105, 4, x_103);
return x_105;
}
else
{
obj* x_106; obj* x_109; obj* x_110; obj* x_112; obj* x_113; 
x_106 = lean::cnstr_get(x_95, 0);
lean::inc(x_106);
lean::dec(x_95);
x_109 = l_lean_parser_command_decl__val_has__view;
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::apply_1(x_110, x_106);
x_113 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_113, 0, x_23);
lean::cnstr_set(x_113, 1, x_33);
lean::cnstr_set(x_113, 2, x_76);
lean::cnstr_set(x_113, 3, x_101);
lean::cnstr_set(x_113, 4, x_112);
return x_113;
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_decl__val_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = l_lean_parser_command_def__like_kind_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_12; 
x_12 = lean::box(3);
x_9 = x_0;
x_10 = x_12;
goto lbl_11;
}
else
{
obj* x_13; obj* x_15; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::dec(x_0);
x_9 = x_15;
x_10 = x_13;
goto lbl_11;
}
lbl_11:
{
obj* x_18; obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_10);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; 
lean::dec(x_20);
x_22 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_22);
x_18 = x_22;
goto lbl_19;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_26 = x_20;
}
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; 
lean::dec(x_26);
lean::dec(x_27);
x_32 = lean::box(0);
x_18 = x_32;
goto lbl_19;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_27, 1);
lean::inc(x_35);
lean::dec(x_27);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_35);
x_39 = l_lean_parser_command_old__univ__params_has__view;
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::apply_1(x_40, x_33);
if (lean::is_scalar(x_26)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_26;
}
lean::cnstr_set(x_43, 0, x_42);
x_18 = x_43;
goto lbl_19;
}
else
{
obj* x_47; 
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_26);
x_47 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_47);
x_18 = x_47;
goto lbl_19;
}
}
}
lbl_19:
{
obj* x_49; obj* x_50; 
if (lean::obj_tag(x_9) == 0)
{
obj* x_52; 
x_52 = lean::box(3);
x_49 = x_9;
x_50 = x_52;
goto lbl_51;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_9, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_9, 1);
lean::inc(x_55);
lean::dec(x_9);
x_49 = x_55;
x_50 = x_53;
goto lbl_51;
}
lbl_51:
{
obj* x_58; obj* x_59; obj* x_61; 
x_58 = l_lean_parser_command_ident__univ__params_has__view;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::apply_1(x_59, x_50);
if (lean::obj_tag(x_49) == 0)
{
if (lean::obj_tag(x_49) == 0)
{
obj* x_63; obj* x_64; obj* x_67; 
lean::dec(x_49);
x_63 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
x_64 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
lean::inc(x_63);
x_67 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_67, 0, x_8);
lean::cnstr_set(x_67, 1, x_18);
lean::cnstr_set(x_67, 2, x_61);
lean::cnstr_set(x_67, 3, x_63);
lean::cnstr_set(x_67, 4, x_64);
return x_67;
}
else
{
obj* x_68; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_68 = lean::cnstr_get(x_49, 0);
lean::inc(x_68);
lean::dec(x_49);
x_71 = l_lean_parser_command_decl__val_has__view;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::apply_1(x_72, x_68);
x_75 = l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_77, 0, x_8);
lean::cnstr_set(x_77, 1, x_18);
lean::cnstr_set(x_77, 2, x_61);
lean::cnstr_set(x_77, 3, x_75);
lean::cnstr_set(x_77, 4, x_74);
return x_77;
}
}
else
{
obj* x_78; obj* x_80; obj* x_83; obj* x_84; obj* x_86; 
x_78 = lean::cnstr_get(x_49, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_49, 1);
lean::inc(x_80);
lean::dec(x_49);
x_83 = l_lean_parser_command_opt__decl__sig_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::apply_1(x_84, x_78);
if (lean::obj_tag(x_80) == 0)
{
obj* x_88; obj* x_90; 
lean::dec(x_80);
x_88 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_88);
x_90 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_90, 0, x_8);
lean::cnstr_set(x_90, 1, x_18);
lean::cnstr_set(x_90, 2, x_61);
lean::cnstr_set(x_90, 3, x_86);
lean::cnstr_set(x_90, 4, x_88);
return x_90;
}
else
{
obj* x_91; obj* x_94; obj* x_95; obj* x_97; obj* x_98; 
x_91 = lean::cnstr_get(x_80, 0);
lean::inc(x_91);
lean::dec(x_80);
x_94 = l_lean_parser_command_decl__val_has__view;
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::apply_1(x_95, x_91);
x_98 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_98, 0, x_8);
lean::cnstr_set(x_98, 1, x_18);
lean::cnstr_set(x_98, 2, x_61);
lean::cnstr_set(x_98, 3, x_86);
lean::cnstr_set(x_98, 4, x_97);
return x_98;
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_def__like_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_parser_command_def__like_kind_has__view;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::apply_1(x_13, x_1);
x_16 = l_lean_parser_command_ident__univ__params_has__view;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_5);
x_20 = l_lean_parser_command_opt__decl__sig_has__view;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_7);
x_24 = l_lean_parser_command_decl__val_has__view;
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_9);
x_28 = lean::box(0);
lean::inc(x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_23);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_19);
lean::cnstr_set(x_32, 1, x_31);
if (lean::obj_tag(x_3) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_3);
lean::dec(x_28);
x_35 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_32);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_15);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_lean_parser_command_def__like;
lean::inc(x_39);
x_41 = l_lean_parser_syntax_mk__node(x_39, x_38);
return x_41;
}
else
{
obj* x_42; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_57; 
x_42 = lean::cnstr_get(x_3, 0);
lean::inc(x_42);
lean::dec(x_3);
x_45 = l_lean_parser_command_old__univ__params_has__view;
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
x_48 = lean::apply_1(x_46, x_42);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_28);
x_50 = l_lean_parser_no__kind;
lean::inc(x_50);
x_52 = l_lean_parser_syntax_mk__node(x_50, x_49);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_32);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_15);
lean::cnstr_set(x_54, 1, x_53);
x_55 = l_lean_parser_command_def__like;
lean::inc(x_55);
x_57 = l_lean_parser_syntax_mk__node(x_55, x_54);
return x_57;
}
}
}
obj* _init_l_lean_parser_command_def__like_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_def__like_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_instance() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("instance");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_instance_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_instance_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_instance_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_instance_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_39; 
x_39 = lean::box(3);
x_36 = x_1;
x_37 = x_39;
goto lbl_38;
}
else
{
obj* x_40; obj* x_42; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
lean::dec(x_1);
x_36 = x_42;
x_37 = x_40;
goto lbl_38;
}
lbl_35:
{
obj* x_45; obj* x_46; obj* x_48; 
x_45 = l_lean_parser_command_decl__sig_has__view;
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::apply_1(x_46, x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_50; obj* x_52; 
lean::dec(x_34);
x_50 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_52, 0, x_20);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_48);
lean::cnstr_set(x_52, 3, x_50);
return x_52;
}
else
{
obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_60; 
x_53 = lean::cnstr_get(x_34, 0);
lean::inc(x_53);
lean::dec(x_34);
x_56 = l_lean_parser_command_decl__val_has__view;
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::apply_1(x_57, x_53);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_20);
lean::cnstr_set(x_60, 1, x_32);
lean::cnstr_set(x_60, 2, x_48);
lean::cnstr_set(x_60, 3, x_59);
return x_60;
}
}
lbl_38:
{
obj* x_61; obj* x_63; 
x_63 = l_lean_parser_syntax_as__node___main(x_37);
if (lean::obj_tag(x_63) == 0)
{
lean::dec(x_63);
if (lean::obj_tag(x_36) == 0)
{
obj* x_65; 
x_65 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_65);
x_61 = x_65;
goto lbl_62;
}
else
{
obj* x_67; obj* x_69; obj* x_72; 
x_67 = lean::cnstr_get(x_36, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_36, 1);
lean::inc(x_69);
lean::dec(x_36);
x_72 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_72);
x_32 = x_72;
x_33 = x_67;
x_34 = x_69;
goto lbl_35;
}
}
else
{
obj* x_74; obj* x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_63, 0);
lean::inc(x_74);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_76 = x_63;
}
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_77) == 0)
{
obj* x_82; 
lean::dec(x_76);
lean::dec(x_77);
x_82 = lean::box(0);
if (lean::obj_tag(x_36) == 0)
{
x_61 = x_82;
goto lbl_62;
}
else
{
obj* x_83; obj* x_85; 
x_83 = lean::cnstr_get(x_36, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_36, 1);
lean::inc(x_85);
lean::dec(x_36);
x_32 = x_82;
x_33 = x_83;
x_34 = x_85;
goto lbl_35;
}
}
else
{
obj* x_88; obj* x_90; 
x_88 = lean::cnstr_get(x_77, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_77, 1);
lean::inc(x_90);
lean::dec(x_77);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_90);
x_94 = l_lean_parser_command_ident__univ__params_has__view;
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::apply_1(x_95, x_88);
if (lean::is_scalar(x_76)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_76;
}
lean::cnstr_set(x_98, 0, x_97);
if (lean::obj_tag(x_36) == 0)
{
x_61 = x_98;
goto lbl_62;
}
else
{
obj* x_99; obj* x_101; 
x_99 = lean::cnstr_get(x_36, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_36, 1);
lean::inc(x_101);
lean::dec(x_36);
x_32 = x_98;
x_33 = x_99;
x_34 = x_101;
goto lbl_35;
}
}
else
{
lean::dec(x_88);
lean::dec(x_90);
lean::dec(x_76);
if (lean::obj_tag(x_36) == 0)
{
obj* x_107; 
x_107 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_107);
x_61 = x_107;
goto lbl_62;
}
else
{
obj* x_109; obj* x_111; obj* x_114; 
x_109 = lean::cnstr_get(x_36, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_36, 1);
lean::inc(x_111);
lean::dec(x_36);
x_114 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_114);
x_32 = x_114;
x_33 = x_109;
x_34 = x_111;
goto lbl_35;
}
}
}
}
lbl_62:
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_117; obj* x_118; obj* x_121; 
lean::dec(x_36);
x_117 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
x_118 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_118);
lean::inc(x_117);
x_121 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_121, 0, x_20);
lean::cnstr_set(x_121, 1, x_61);
lean::cnstr_set(x_121, 2, x_117);
lean::cnstr_set(x_121, 3, x_118);
return x_121;
}
else
{
obj* x_122; obj* x_125; obj* x_126; obj* x_128; obj* x_129; obj* x_131; 
x_122 = lean::cnstr_get(x_36, 0);
lean::inc(x_122);
lean::dec(x_36);
x_125 = l_lean_parser_command_decl__val_has__view;
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::apply_1(x_126, x_122);
x_129 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_129);
x_131 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_131, 0, x_20);
lean::cnstr_set(x_131, 1, x_61);
lean::cnstr_set(x_131, 2, x_129);
lean::cnstr_set(x_131, 3, x_128);
return x_131;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_decl__sig_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_ident__univ__params_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_21 = x_0;
x_22 = x_24;
goto lbl_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
lean::dec(x_0);
x_21 = x_27;
x_22 = x_25;
goto lbl_23;
}
lbl_20:
{
obj* x_30; obj* x_31; obj* x_33; 
x_30 = l_lean_parser_command_decl__sig_has__view;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::apply_1(x_31, x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_35; obj* x_37; 
lean::dec(x_19);
x_35 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_37, 0, x_5);
lean::cnstr_set(x_37, 1, x_17);
lean::cnstr_set(x_37, 2, x_33);
lean::cnstr_set(x_37, 3, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
lean::dec(x_19);
x_41 = l_lean_parser_command_decl__val_has__view;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::apply_1(x_42, x_38);
x_45 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_45, 0, x_5);
lean::cnstr_set(x_45, 1, x_17);
lean::cnstr_set(x_45, 2, x_33);
lean::cnstr_set(x_45, 3, x_44);
return x_45;
}
}
lbl_23:
{
obj* x_46; obj* x_48; 
x_48 = l_lean_parser_syntax_as__node___main(x_22);
if (lean::obj_tag(x_48) == 0)
{
lean::dec(x_48);
if (lean::obj_tag(x_21) == 0)
{
obj* x_50; 
x_50 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_50);
x_46 = x_50;
goto lbl_47;
}
else
{
obj* x_52; obj* x_54; obj* x_57; 
x_52 = lean::cnstr_get(x_21, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_21, 1);
lean::inc(x_54);
lean::dec(x_21);
x_57 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_57);
x_17 = x_57;
x_18 = x_52;
x_19 = x_54;
goto lbl_20;
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_48, 0);
lean::inc(x_59);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_61 = x_48;
}
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_67; 
lean::dec(x_62);
lean::dec(x_61);
x_67 = lean::box(0);
if (lean::obj_tag(x_21) == 0)
{
x_46 = x_67;
goto lbl_47;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_21, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_21, 1);
lean::inc(x_70);
lean::dec(x_21);
x_17 = x_67;
x_18 = x_68;
x_19 = x_70;
goto lbl_20;
}
}
else
{
obj* x_73; obj* x_75; 
x_73 = lean::cnstr_get(x_62, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_62, 1);
lean::inc(x_75);
lean::dec(x_62);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_75);
x_79 = l_lean_parser_command_ident__univ__params_has__view;
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::apply_1(x_80, x_73);
if (lean::is_scalar(x_61)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_61;
}
lean::cnstr_set(x_83, 0, x_82);
if (lean::obj_tag(x_21) == 0)
{
x_46 = x_83;
goto lbl_47;
}
else
{
obj* x_84; obj* x_86; 
x_84 = lean::cnstr_get(x_21, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_21, 1);
lean::inc(x_86);
lean::dec(x_21);
x_17 = x_83;
x_18 = x_84;
x_19 = x_86;
goto lbl_20;
}
}
else
{
lean::dec(x_61);
lean::dec(x_73);
lean::dec(x_75);
if (lean::obj_tag(x_21) == 0)
{
obj* x_92; 
x_92 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_92);
x_46 = x_92;
goto lbl_47;
}
else
{
obj* x_94; obj* x_96; obj* x_99; 
x_94 = lean::cnstr_get(x_21, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_21, 1);
lean::inc(x_96);
lean::dec(x_21);
x_99 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2;
lean::inc(x_99);
x_17 = x_99;
x_18 = x_94;
x_19 = x_96;
goto lbl_20;
}
}
}
}
lbl_47:
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_102; obj* x_103; obj* x_106; 
lean::dec(x_21);
x_102 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
x_103 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_103);
lean::inc(x_102);
x_106 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_106, 0, x_5);
lean::cnstr_set(x_106, 1, x_46);
lean::cnstr_set(x_106, 2, x_102);
lean::cnstr_set(x_106, 3, x_103);
return x_106;
}
else
{
obj* x_107; obj* x_110; obj* x_111; obj* x_113; obj* x_114; obj* x_116; 
x_107 = lean::cnstr_get(x_21, 0);
lean::inc(x_107);
lean::dec(x_21);
x_110 = l_lean_parser_command_decl__val_has__view;
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::apply_1(x_111, x_107);
x_114 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_114);
x_116 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_116, 0, x_5);
lean::cnstr_set(x_116, 1, x_46);
lean::cnstr_set(x_116, 2, x_114);
lean::cnstr_set(x_116, 3, x_113);
return x_116;
}
}
}
}
}
}
}
obj* l_lean_parser_command_instance_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_10);
x_12 = l_option_map___rarg(x_10, x_1);
x_13 = lean::box(3);
x_14 = l_option_get__or__else___main___rarg(x_12, x_13);
x_15 = l_lean_parser_command_decl__sig_has__view;
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
x_18 = lean::apply_1(x_16, x_5);
x_19 = l_lean_parser_command_decl__val_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::apply_1(x_20, x_7);
x_23 = lean::box(0);
lean::inc(x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_25);
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
lean::dec(x_23);
lean::dec(x_3);
x_29 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_26);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_14);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l_lean_parser_command_instance;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
else
{
obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; 
x_36 = lean::cnstr_get(x_3, 0);
lean::inc(x_36);
lean::dec(x_3);
x_39 = l_lean_parser_command_ident__univ__params_has__view;
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
x_42 = lean::apply_1(x_40, x_36);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_23);
x_44 = l_lean_parser_no__kind;
lean::inc(x_44);
x_46 = l_lean_parser_syntax_mk__node(x_44, x_43);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_26);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_14);
lean::cnstr_set(x_48, 1, x_47);
x_49 = l_lean_parser_command_instance;
lean::inc(x_49);
x_51 = l_lean_parser_syntax_mk__node(x_49, x_48);
return x_51;
}
}
}
obj* _init_l_lean_parser_command_instance_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_instance_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_example() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("example");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_example_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_example_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_example_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_example_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l_lean_parser_command_example_has__view_x_27___lambda__1___closed__1;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_5 = x_15;
x_6 = x_18;
goto lbl_7;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_5 = x_21;
x_6 = x_19;
goto lbl_7;
}
}
lbl_4:
{
obj* x_24; obj* x_25; obj* x_27; 
x_24 = l_lean_parser_command_decl__sig_has__view;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_29; obj* x_31; 
lean::dec(x_3);
x_29 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_27);
lean::cnstr_set(x_31, 2, x_29);
return x_31;
}
else
{
obj* x_32; obj* x_35; obj* x_36; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_3, 0);
lean::inc(x_32);
lean::dec(x_3);
x_35 = l_lean_parser_command_decl__val_has__view;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::apply_1(x_36, x_32);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_1);
lean::cnstr_set(x_39, 1, x_27);
lean::cnstr_set(x_39, 2, x_38);
return x_39;
}
}
lbl_7:
{
obj* x_40; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_6, 0);
lean::inc(x_42);
lean::dec(x_6);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::obj_tag(x_5) == 0)
{
x_40 = x_45;
goto lbl_41;
}
else
{
obj* x_46; obj* x_48; 
x_46 = lean::cnstr_get(x_5, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_5, 1);
lean::inc(x_48);
lean::dec(x_5);
x_1 = x_45;
x_2 = x_46;
x_3 = x_48;
goto lbl_4;
}
}
case 1:
{
obj* x_52; 
lean::dec(x_6);
x_52 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_40 = x_52;
goto lbl_41;
}
else
{
obj* x_53; obj* x_55; 
x_53 = lean::cnstr_get(x_5, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_5, 1);
lean::inc(x_55);
lean::dec(x_5);
x_1 = x_52;
x_2 = x_53;
x_3 = x_55;
goto lbl_4;
}
}
case 2:
{
obj* x_59; 
lean::dec(x_6);
x_59 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_40 = x_59;
goto lbl_41;
}
else
{
obj* x_60; obj* x_62; 
x_60 = lean::cnstr_get(x_5, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_5, 1);
lean::inc(x_62);
lean::dec(x_5);
x_1 = x_59;
x_2 = x_60;
x_3 = x_62;
goto lbl_4;
}
}
default:
{
obj* x_66; 
lean::dec(x_6);
x_66 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_40 = x_66;
goto lbl_41;
}
else
{
obj* x_67; obj* x_69; 
x_67 = lean::cnstr_get(x_5, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_5, 1);
lean::inc(x_69);
lean::dec(x_5);
x_1 = x_66;
x_2 = x_67;
x_3 = x_69;
goto lbl_4;
}
}
}
lbl_41:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_73; obj* x_74; obj* x_77; 
lean::dec(x_5);
x_73 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
x_74 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_74);
lean::inc(x_73);
x_77 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_77, 0, x_40);
lean::cnstr_set(x_77, 1, x_73);
lean::cnstr_set(x_77, 2, x_74);
return x_77;
}
else
{
obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_87; 
x_78 = lean::cnstr_get(x_5, 0);
lean::inc(x_78);
lean::dec(x_5);
x_81 = l_lean_parser_command_decl__val_has__view;
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::apply_1(x_82, x_78);
x_85 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_85);
x_87 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_87, 0, x_40);
lean::cnstr_set(x_87, 1, x_85);
lean::cnstr_set(x_87, 2, x_84);
return x_87;
}
}
}
}
}
obj* _init_l_lean_parser_command_example_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::box(3);
x_4 = x_7;
x_5 = x_8;
goto lbl_6;
lbl_3:
{
obj* x_9; obj* x_10; obj* x_12; 
x_9 = l_lean_parser_command_decl__sig_has__view;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::apply_1(x_10, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_14; obj* x_16; 
lean::dec(x_2);
x_14 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_14);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
lean::dec(x_2);
x_20 = l_lean_parser_command_decl__val_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_17);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_12);
lean::cnstr_set(x_24, 2, x_23);
return x_24;
}
}
lbl_6:
{
obj* x_25; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_5, 0);
lean::inc(x_27);
lean::dec(x_5);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
if (lean::obj_tag(x_4) == 0)
{
x_25 = x_30;
goto lbl_26;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_4, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_4, 1);
lean::inc(x_33);
lean::dec(x_4);
x_0 = x_30;
x_1 = x_31;
x_2 = x_33;
goto lbl_3;
}
}
case 1:
{
obj* x_37; 
lean::dec(x_5);
x_37 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_25 = x_37;
goto lbl_26;
}
else
{
obj* x_38; obj* x_40; 
x_38 = lean::cnstr_get(x_4, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_4, 1);
lean::inc(x_40);
lean::dec(x_4);
x_0 = x_37;
x_1 = x_38;
x_2 = x_40;
goto lbl_3;
}
}
case 2:
{
obj* x_44; 
lean::dec(x_5);
x_44 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_25 = x_44;
goto lbl_26;
}
else
{
obj* x_45; obj* x_47; 
x_45 = lean::cnstr_get(x_4, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_4, 1);
lean::inc(x_47);
lean::dec(x_4);
x_0 = x_44;
x_1 = x_45;
x_2 = x_47;
goto lbl_3;
}
}
default:
{
obj* x_51; 
lean::dec(x_5);
x_51 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_25 = x_51;
goto lbl_26;
}
else
{
obj* x_52; obj* x_54; 
x_52 = lean::cnstr_get(x_4, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_4, 1);
lean::inc(x_54);
lean::dec(x_4);
x_0 = x_51;
x_1 = x_52;
x_2 = x_54;
goto lbl_3;
}
}
}
lbl_26:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_58; obj* x_59; obj* x_62; 
lean::dec(x_4);
x_58 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
x_59 = l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
lean::inc(x_58);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_25);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set(x_62, 2, x_59);
return x_62;
}
else
{
obj* x_63; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
x_63 = lean::cnstr_get(x_4, 0);
lean::inc(x_63);
lean::dec(x_4);
x_66 = l_lean_parser_command_decl__val_has__view;
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::apply_1(x_67, x_63);
x_70 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_25);
lean::cnstr_set(x_72, 1, x_70);
lean::cnstr_set(x_72, 2, x_69);
return x_72;
}
}
}
}
}
obj* l_lean_parser_command_example_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
x_13 = l_lean_parser_command_decl__sig_has__view;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_16 = lean::apply_1(x_14, x_3);
x_17 = l_lean_parser_command_decl__val_has__view;
x_18 = lean::cnstr_get(x_17, 1);
lean::inc(x_18);
x_20 = lean::apply_1(x_18, x_5);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_12);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_command_example;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_command_example_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_example_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_constant__keyword() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("constant_keyword");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_constant__keyword_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_constant__keyword_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__4;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
lean::dec(x_2);
if (x_84 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
lean::dec(x_1);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
case 1:
{
obj* x_93; 
lean::dec(x_1);
x_93 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
lean::inc(x_93);
return x_93;
}
case 2:
{
obj* x_96; 
lean::dec(x_1);
x_96 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
return x_96;
}
default:
{
obj* x_99; 
lean::dec(x_1);
x_99 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
return x_99;
}
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_101; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_1, 0);
lean::inc(x_101);
lean::dec(x_1);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_101);
x_105 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
case 1:
{
obj* x_107; 
lean::dec(x_1);
x_107 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
lean::inc(x_107);
return x_107;
}
case 2:
{
obj* x_110; 
lean::dec(x_1);
x_110 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
lean::inc(x_110);
return x_110;
}
default:
{
obj* x_113; 
lean::dec(x_1);
x_113 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
lean::inc(x_113);
return x_113;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_9; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
case 1:
{
obj* x_15; 
lean::dec(x_0);
x_15 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
lean::inc(x_15);
return x_15;
}
case 2:
{
obj* x_18; 
lean::dec(x_0);
x_18 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
return x_18;
}
default:
{
obj* x_21; 
lean::dec(x_0);
x_21 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
case 1:
{
obj* x_29; 
lean::dec(x_0);
x_29 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
lean::inc(x_29);
return x_29;
}
case 2:
{
obj* x_32; 
lean::dec(x_0);
x_32 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
lean::inc(x_32);
return x_32;
}
default:
{
obj* x_35; 
lean::dec(x_0);
x_35 = l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2;
lean::inc(x_35);
return x_35;
}
}
}
}
}
}
obj* _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("constant_keyword");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_command_constant__keyword_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_5);
x_7 = l_option_map___rarg(x_5, x_2);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_1);
x_12 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = l_lean_parser_command_constant__keyword;
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mk__node(x_16, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_22);
x_24 = l_option_map___rarg(x_22, x_19);
x_25 = lean::box(3);
x_26 = l_option_get__or__else___main___rarg(x_24, x_25);
lean::inc(x_1);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_command_constant__keyword;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
}
}
obj* _init_l_lean_parser_command_constant__keyword_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_constant__keyword_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_constant() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("constant");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_constant_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_constant_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_constant_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_constant_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_21; obj* x_23; 
x_20 = l_lean_parser_command_constant__keyword_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_2);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_1);
x_25 = l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1;
x_26 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_26);
lean::inc(x_25);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_23);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set(x_29, 2, x_26);
return x_29;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_39; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_33 = l_lean_parser_command_decl__sig_has__view;
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::apply_1(x_34, x_30);
x_37 = l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_23);
lean::cnstr_set(x_39, 1, x_37);
lean::cnstr_set(x_39, 2, x_36);
return x_39;
}
}
else
{
obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_48; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
lean::dec(x_1);
x_45 = l_lean_parser_command_ident__univ__params_has__view;
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::apply_1(x_46, x_40);
if (lean::obj_tag(x_42) == 0)
{
obj* x_50; obj* x_52; 
lean::dec(x_42);
x_50 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_23);
lean::cnstr_set(x_52, 1, x_48);
lean::cnstr_set(x_52, 2, x_50);
return x_52;
}
else
{
obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_60; 
x_53 = lean::cnstr_get(x_42, 0);
lean::inc(x_53);
lean::dec(x_42);
x_56 = l_lean_parser_command_decl__sig_has__view;
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::apply_1(x_57, x_53);
x_60 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_60, 0, x_23);
lean::cnstr_set(x_60, 1, x_48);
lean::cnstr_set(x_60, 2, x_59);
return x_60;
}
}
}
}
}
obj* _init_l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_ident__univ__params_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_6; obj* x_8; 
x_5 = l_lean_parser_command_constant__keyword_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_1);
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_11; obj* x_14; 
lean::dec(x_0);
x_10 = l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1;
x_11 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_11);
lean::inc(x_10);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_lean_parser_command_decl__sig_has__view;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::apply_1(x_19, x_15);
x_22 = l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_22);
lean::cnstr_set(x_24, 2, x_21);
return x_24;
}
}
else
{
obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_33; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
lean::dec(x_0);
x_30 = l_lean_parser_command_ident__univ__params_has__view;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::apply_1(x_31, x_25);
if (lean::obj_tag(x_27) == 0)
{
obj* x_35; obj* x_37; 
lean::dec(x_27);
x_35 = l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_8);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_27, 0);
lean::inc(x_38);
lean::dec(x_27);
x_41 = l_lean_parser_command_decl__sig_has__view;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::apply_1(x_42, x_38);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_8);
lean::cnstr_set(x_45, 1, x_33);
lean::cnstr_set(x_45, 2, x_44);
return x_45;
}
}
}
}
}
obj* l_lean_parser_command_constant_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_command_constant__keyword_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_11 = lean::apply_1(x_9, x_1);
x_12 = l_lean_parser_command_ident__univ__params_has__view;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::apply_1(x_13, x_3);
x_16 = l_lean_parser_command_decl__sig_has__view;
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_5);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_15);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_lean_parser_command_constant;
lean::inc(x_24);
x_26 = l_lean_parser_syntax_mk__node(x_24, x_23);
return x_26;
}
}
obj* _init_l_lean_parser_command_constant_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_constant_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_inductive() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("inductive");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_inductive_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_inductive_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_inductive_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__4;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
else
{
obj* x_20; obj* x_22; obj* x_25; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_parser_syntax_as__node___main(x_20);
if (lean::obj_tag(x_25) == 0)
{
lean::dec(x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; 
x_27 = lean::box(3);
x_1 = x_22;
x_2 = x_27;
goto lbl_3;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_22, 1);
lean::inc(x_30);
lean::dec(x_22);
x_1 = x_30;
x_2 = x_28;
goto lbl_3;
}
}
else
{
obj* x_33; obj* x_36; obj* x_39; 
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_list_append___rarg(x_36, x_22);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; 
x_40 = lean::box(3);
x_1 = x_39;
x_2 = x_40;
goto lbl_3;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
lean::dec(x_39);
x_1 = x_43;
x_2 = x_41;
goto lbl_3;
}
}
}
}
lbl_3:
{
obj* x_46; obj* x_48; 
x_48 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; 
lean::dec(x_48);
x_50 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_50);
x_46 = x_50;
goto lbl_47;
}
else
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_48, 0);
lean::inc(x_52);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_54 = x_48;
}
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; 
lean::dec(x_54);
lean::dec(x_55);
x_60 = lean::box(0);
x_46 = x_60;
goto lbl_47;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_55, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_55, 1);
lean::inc(x_63);
lean::dec(x_55);
if (lean::obj_tag(x_63) == 0)
{
lean::dec(x_63);
switch (lean::obj_tag(x_61)) {
case 0:
{
obj* x_67; obj* x_70; obj* x_71; 
x_67 = lean::cnstr_get(x_61, 0);
lean::inc(x_67);
lean::dec(x_61);
if (lean::is_scalar(x_54)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_54;
}
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_46 = x_71;
goto lbl_47;
}
case 1:
{
obj* x_74; 
lean::dec(x_61);
lean::dec(x_54);
x_74 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_74);
x_46 = x_74;
goto lbl_47;
}
case 2:
{
obj* x_78; 
lean::dec(x_61);
lean::dec(x_54);
x_78 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_78);
x_46 = x_78;
goto lbl_47;
}
default:
{
obj* x_82; 
lean::dec(x_61);
lean::dec(x_54);
x_82 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_46 = x_82;
goto lbl_47;
}
}
}
else
{
obj* x_87; 
lean::dec(x_61);
lean::dec(x_54);
lean::dec(x_63);
x_87 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_87);
x_46 = x_87;
goto lbl_47;
}
}
}
lbl_47:
{
obj* x_89; obj* x_90; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_92; 
x_92 = lean::box(3);
x_89 = x_1;
x_90 = x_92;
goto lbl_91;
}
else
{
obj* x_93; obj* x_95; 
x_93 = lean::cnstr_get(x_1, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_1, 1);
lean::inc(x_95);
lean::dec(x_1);
x_89 = x_95;
x_90 = x_93;
goto lbl_91;
}
lbl_91:
{
obj* x_98; 
switch (lean::obj_tag(x_90)) {
case 0:
{
obj* x_100; obj* x_103; 
x_100 = lean::cnstr_get(x_90, 0);
lean::inc(x_100);
lean::dec(x_90);
x_103 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_103, 0, x_100);
x_98 = x_103;
goto lbl_99;
}
case 1:
{
obj* x_105; 
lean::dec(x_90);
x_105 = lean::box(0);
x_98 = x_105;
goto lbl_99;
}
case 2:
{
obj* x_107; 
lean::dec(x_90);
x_107 = lean::box(0);
x_98 = x_107;
goto lbl_99;
}
default:
{
obj* x_109; 
lean::dec(x_90);
x_109 = lean::box(0);
x_98 = x_109;
goto lbl_99;
}
}
lbl_99:
{
obj* x_110; obj* x_111; 
if (lean::obj_tag(x_89) == 0)
{
obj* x_113; 
x_113 = lean::box(3);
x_110 = x_89;
x_111 = x_113;
goto lbl_112;
}
else
{
obj* x_114; obj* x_116; 
x_114 = lean::cnstr_get(x_89, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_89, 1);
lean::inc(x_116);
lean::dec(x_89);
x_110 = x_116;
x_111 = x_114;
goto lbl_112;
}
lbl_112:
{
obj* x_119; obj* x_121; 
x_121 = l_lean_parser_syntax_as__node___main(x_111);
if (lean::obj_tag(x_121) == 0)
{
obj* x_123; 
lean::dec(x_121);
x_123 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_123);
x_119 = x_123;
goto lbl_120;
}
else
{
obj* x_125; obj* x_127; obj* x_128; 
x_125 = lean::cnstr_get(x_121, 0);
lean::inc(x_125);
if (lean::is_shared(x_121)) {
 lean::dec(x_121);
 x_127 = lean::box(0);
} else {
 lean::cnstr_release(x_121, 0);
 x_127 = x_121;
}
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
if (lean::obj_tag(x_128) == 0)
{
obj* x_133; 
lean::dec(x_127);
lean::dec(x_128);
x_133 = lean::box(0);
x_119 = x_133;
goto lbl_120;
}
else
{
obj* x_134; obj* x_136; 
x_134 = lean::cnstr_get(x_128, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_128, 1);
lean::inc(x_136);
lean::dec(x_128);
if (lean::obj_tag(x_136) == 0)
{
obj* x_140; obj* x_141; obj* x_143; obj* x_144; 
lean::dec(x_136);
x_140 = l_lean_parser_command_old__univ__params_has__view;
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_143 = lean::apply_1(x_141, x_134);
if (lean::is_scalar(x_127)) {
 x_144 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_144 = x_127;
}
lean::cnstr_set(x_144, 0, x_143);
x_119 = x_144;
goto lbl_120;
}
else
{
obj* x_148; 
lean::dec(x_136);
lean::dec(x_134);
lean::dec(x_127);
x_148 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_148);
x_119 = x_148;
goto lbl_120;
}
}
}
lbl_120:
{
obj* x_150; obj* x_151; 
if (lean::obj_tag(x_110) == 0)
{
obj* x_153; 
x_153 = lean::box(3);
x_150 = x_110;
x_151 = x_153;
goto lbl_152;
}
else
{
obj* x_154; obj* x_156; 
x_154 = lean::cnstr_get(x_110, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_110, 1);
lean::inc(x_156);
lean::dec(x_110);
x_150 = x_156;
x_151 = x_154;
goto lbl_152;
}
lbl_152:
{
obj* x_159; obj* x_160; obj* x_162; obj* x_163; obj* x_164; 
x_159 = l_lean_parser_command_ident__univ__params_has__view;
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::apply_1(x_160, x_151);
if (lean::obj_tag(x_150) == 0)
{
obj* x_166; 
x_166 = lean::box(3);
x_163 = x_150;
x_164 = x_166;
goto lbl_165;
}
else
{
obj* x_167; obj* x_169; 
x_167 = lean::cnstr_get(x_150, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_150, 1);
lean::inc(x_169);
lean::dec(x_150);
x_163 = x_169;
x_164 = x_167;
goto lbl_165;
}
lbl_165:
{
obj* x_172; obj* x_173; obj* x_175; obj* x_176; obj* x_178; obj* x_179; obj* x_181; obj* x_182; 
x_172 = l_lean_parser_command_opt__decl__sig_has__view;
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_175 = lean::apply_1(x_173, x_164);
if (lean::obj_tag(x_163) == 0)
{
obj* x_184; 
x_184 = lean::box(3);
x_181 = x_163;
x_182 = x_184;
goto lbl_183;
}
else
{
obj* x_185; obj* x_187; 
x_185 = lean::cnstr_get(x_163, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_163, 1);
lean::inc(x_187);
lean::dec(x_163);
x_181 = x_187;
x_182 = x_185;
goto lbl_183;
}
lbl_177:
{
obj* x_190; obj* x_191; 
x_190 = lean::box(3);
x_191 = l_lean_parser_syntax_as__node___main(x_190);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; 
lean::dec(x_191);
x_193 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1;
lean::inc(x_193);
x_195 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_195, 0, x_46);
lean::cnstr_set(x_195, 1, x_98);
lean::cnstr_set(x_195, 2, x_119);
lean::cnstr_set(x_195, 3, x_162);
lean::cnstr_set(x_195, 4, x_175);
lean::cnstr_set(x_195, 5, x_176);
lean::cnstr_set(x_195, 6, x_193);
return x_195;
}
else
{
obj* x_196; obj* x_199; obj* x_202; obj* x_204; obj* x_205; 
x_196 = lean::cnstr_get(x_191, 0);
lean::inc(x_196);
lean::dec(x_191);
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
x_202 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2;
lean::inc(x_202);
x_204 = l_list_map___main___rarg(x_202, x_199);
x_205 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_205, 0, x_46);
lean::cnstr_set(x_205, 1, x_98);
lean::cnstr_set(x_205, 2, x_119);
lean::cnstr_set(x_205, 3, x_162);
lean::cnstr_set(x_205, 4, x_175);
lean::cnstr_set(x_205, 5, x_176);
lean::cnstr_set(x_205, 6, x_204);
return x_205;
}
}
lbl_180:
{
obj* x_206; 
x_206 = l_lean_parser_syntax_as__node___main(x_179);
if (lean::obj_tag(x_206) == 0)
{
obj* x_208; obj* x_210; 
lean::dec(x_206);
x_208 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1;
lean::inc(x_208);
x_210 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_210, 0, x_46);
lean::cnstr_set(x_210, 1, x_98);
lean::cnstr_set(x_210, 2, x_119);
lean::cnstr_set(x_210, 3, x_162);
lean::cnstr_set(x_210, 4, x_175);
lean::cnstr_set(x_210, 5, x_178);
lean::cnstr_set(x_210, 6, x_208);
return x_210;
}
else
{
obj* x_211; obj* x_214; obj* x_217; obj* x_219; obj* x_220; 
x_211 = lean::cnstr_get(x_206, 0);
lean::inc(x_211);
lean::dec(x_206);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
lean::dec(x_211);
x_217 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2;
lean::inc(x_217);
x_219 = l_list_map___main___rarg(x_217, x_214);
x_220 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_220, 0, x_46);
lean::cnstr_set(x_220, 1, x_98);
lean::cnstr_set(x_220, 2, x_119);
lean::cnstr_set(x_220, 3, x_162);
lean::cnstr_set(x_220, 4, x_175);
lean::cnstr_set(x_220, 5, x_178);
lean::cnstr_set(x_220, 6, x_219);
return x_220;
}
}
lbl_183:
{
obj* x_221; 
x_221 = l_lean_parser_syntax_as__node___main(x_182);
if (lean::obj_tag(x_221) == 0)
{
lean::dec(x_221);
if (lean::obj_tag(x_181) == 0)
{
obj* x_224; 
lean::dec(x_181);
x_224 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_224);
x_176 = x_224;
goto lbl_177;
}
else
{
obj* x_226; obj* x_229; 
x_226 = lean::cnstr_get(x_181, 0);
lean::inc(x_226);
lean::dec(x_181);
x_229 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_229);
x_178 = x_229;
x_179 = x_226;
goto lbl_180;
}
}
else
{
obj* x_231; obj* x_233; obj* x_234; 
x_231 = lean::cnstr_get(x_221, 0);
lean::inc(x_231);
if (lean::is_shared(x_221)) {
 lean::dec(x_221);
 x_233 = lean::box(0);
} else {
 lean::cnstr_release(x_221, 0);
 x_233 = x_221;
}
x_234 = lean::cnstr_get(x_231, 1);
lean::inc(x_234);
lean::dec(x_231);
if (lean::obj_tag(x_234) == 0)
{
obj* x_239; 
lean::dec(x_233);
lean::dec(x_234);
x_239 = lean::box(0);
if (lean::obj_tag(x_181) == 0)
{
lean::dec(x_181);
x_176 = x_239;
goto lbl_177;
}
else
{
obj* x_241; 
x_241 = lean::cnstr_get(x_181, 0);
lean::inc(x_241);
lean::dec(x_181);
x_178 = x_239;
x_179 = x_241;
goto lbl_180;
}
}
else
{
obj* x_244; obj* x_246; 
x_244 = lean::cnstr_get(x_234, 0);
lean::inc(x_244);
x_246 = lean::cnstr_get(x_234, 1);
lean::inc(x_246);
lean::dec(x_234);
if (lean::obj_tag(x_246) == 0)
{
obj* x_250; obj* x_251; obj* x_253; obj* x_254; 
lean::dec(x_246);
x_250 = l_lean_parser_command_notation__like_has__view;
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::apply_1(x_251, x_244);
if (lean::is_scalar(x_233)) {
 x_254 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_254 = x_233;
}
lean::cnstr_set(x_254, 0, x_253);
if (lean::obj_tag(x_181) == 0)
{
lean::dec(x_181);
x_176 = x_254;
goto lbl_177;
}
else
{
obj* x_256; 
x_256 = lean::cnstr_get(x_181, 0);
lean::inc(x_256);
lean::dec(x_181);
x_178 = x_254;
x_179 = x_256;
goto lbl_180;
}
}
else
{
lean::dec(x_246);
lean::dec(x_233);
lean::dec(x_244);
if (lean::obj_tag(x_181) == 0)
{
obj* x_263; 
lean::dec(x_181);
x_263 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_263);
x_176 = x_263;
goto lbl_177;
}
else
{
obj* x_265; obj* x_268; 
x_265 = lean::cnstr_get(x_181, 0);
lean::inc(x_265);
lean::dec(x_181);
x_268 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_268);
x_178 = x_268;
x_179 = x_265;
goto lbl_180;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_command_intro__rule_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_intro__rule_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_command_notation__like_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; obj* x_7; 
x_7 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_9);
x_5 = x_9;
goto lbl_6;
}
else
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_13 = x_7;
}
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; 
lean::dec(x_14);
lean::dec(x_13);
x_19 = lean::box(0);
x_5 = x_19;
goto lbl_6;
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_14, 1);
lean::inc(x_22);
lean::dec(x_14);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_22);
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_26; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_20, 0);
lean::inc(x_26);
lean::dec(x_20);
if (lean::is_scalar(x_13)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_13;
}
lean::cnstr_set(x_29, 0, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_5 = x_30;
goto lbl_6;
}
case 1:
{
obj* x_33; 
lean::dec(x_13);
lean::dec(x_20);
x_33 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
x_5 = x_33;
goto lbl_6;
}
case 2:
{
obj* x_37; 
lean::dec(x_13);
lean::dec(x_20);
x_37 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_37);
x_5 = x_37;
goto lbl_6;
}
default:
{
obj* x_41; 
lean::dec(x_13);
lean::dec(x_20);
x_41 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_41);
x_5 = x_41;
goto lbl_6;
}
}
}
else
{
obj* x_46; 
lean::dec(x_22);
lean::dec(x_13);
lean::dec(x_20);
x_46 = l_lean_parser_command_notation_has__view_x_27___lambda__1___closed__1;
lean::inc(x_46);
x_5 = x_46;
goto lbl_6;
}
}
}
lbl_6:
{
obj* x_48; obj* x_49; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_51; 
x_51 = lean::box(3);
x_48 = x_0;
x_49 = x_51;
goto lbl_50;
}
else
{
obj* x_52; obj* x_54; 
x_52 = lean::cnstr_get(x_0, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_0, 1);
lean::inc(x_54);
lean::dec(x_0);
x_48 = x_54;
x_49 = x_52;
goto lbl_50;
}
lbl_50:
{
obj* x_57; 
switch (lean::obj_tag(x_49)) {
case 0:
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_49, 0);
lean::inc(x_59);
lean::dec(x_49);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_59);
x_57 = x_62;
goto lbl_58;
}
case 1:
{
obj* x_64; 
lean::dec(x_49);
x_64 = lean::box(0);
x_57 = x_64;
goto lbl_58;
}
case 2:
{
obj* x_66; 
lean::dec(x_49);
x_66 = lean::box(0);
x_57 = x_66;
goto lbl_58;
}
default:
{
obj* x_68; 
lean::dec(x_49);
x_68 = lean::box(0);
x_57 = x_68;
goto lbl_58;
}
}
lbl_58:
{
obj* x_69; obj* x_70; 
if (lean::obj_tag(x_48) == 0)
{
obj* x_72; 
x_72 = lean::box(3);
x_69 = x_48;
x_70 = x_72;
goto lbl_71;
}
else
{
obj* x_73; obj* x_75; 
x_73 = lean::cnstr_get(x_48, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_48, 1);
lean::inc(x_75);
lean::dec(x_48);
x_69 = x_75;
x_70 = x_73;
goto lbl_71;
}
lbl_71:
{
obj* x_78; obj* x_80; 
x_80 = l_lean_parser_syntax_as__node___main(x_70);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; 
lean::dec(x_80);
x_82 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_82);
x_78 = x_82;
goto lbl_79;
}
else
{
obj* x_84; obj* x_86; obj* x_87; 
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_86 = x_80;
}
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
lean::dec(x_84);
if (lean::obj_tag(x_87) == 0)
{
obj* x_92; 
lean::dec(x_86);
lean::dec(x_87);
x_92 = lean::box(0);
x_78 = x_92;
goto lbl_79;
}
else
{
obj* x_93; obj* x_95; 
x_93 = lean::cnstr_get(x_87, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_87, 1);
lean::inc(x_95);
lean::dec(x_87);
if (lean::obj_tag(x_95) == 0)
{
obj* x_99; obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_95);
x_99 = l_lean_parser_command_old__univ__params_has__view;
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
x_102 = lean::apply_1(x_100, x_93);
if (lean::is_scalar(x_86)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_86;
}
lean::cnstr_set(x_103, 0, x_102);
x_78 = x_103;
goto lbl_79;
}
else
{
obj* x_107; 
lean::dec(x_93);
lean::dec(x_95);
lean::dec(x_86);
x_107 = l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5;
lean::inc(x_107);
x_78 = x_107;
goto lbl_79;
}
}
}
lbl_79:
{
obj* x_109; obj* x_110; 
if (lean::obj_tag(x_69) == 0)
{
obj* x_112; 
x_112 = lean::box(3);
x_109 = x_69;
x_110 = x_112;
goto lbl_111;
}
else
{
obj* x_113; obj* x_115; 
x_113 = lean::cnstr_get(x_69, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_69, 1);
lean::inc(x_115);
lean::dec(x_69);
x_109 = x_115;
x_110 = x_113;
goto lbl_111;
}
lbl_111:
{
obj* x_118; obj* x_119; obj* x_121; obj* x_122; obj* x_123; 
x_118 = l_lean_parser_command_ident__univ__params_has__view;
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::apply_1(x_119, x_110);
if (lean::obj_tag(x_109) == 0)
{
obj* x_125; 
x_125 = lean::box(3);
x_122 = x_109;
x_123 = x_125;
goto lbl_124;
}
else
{
obj* x_126; obj* x_128; 
x_126 = lean::cnstr_get(x_109, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_109, 1);
lean::inc(x_128);
lean::dec(x_109);
x_122 = x_128;
x_123 = x_126;
goto lbl_124;
}
lbl_124:
{
obj* x_131; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_141; 
x_131 = l_lean_parser_command_opt__decl__sig_has__view;
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::apply_1(x_132, x_123);
if (lean::obj_tag(x_122) == 0)
{
obj* x_143; 
x_143 = lean::box(3);
x_140 = x_122;
x_141 = x_143;
goto lbl_142;
}
else
{
obj* x_144; obj* x_146; 
x_144 = lean::cnstr_get(x_122, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_122, 1);
lean::inc(x_146);
lean::dec(x_122);
x_140 = x_146;
x_141 = x_144;
goto lbl_142;
}
lbl_136:
{
obj* x_149; obj* x_150; 
x_149 = lean::box(3);
x_150 = l_lean_parser_syntax_as__node___main(x_149);
if (lean::obj_tag(x_150) == 0)
{
obj* x_152; obj* x_154; 
lean::dec(x_150);
x_152 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1;
lean::inc(x_152);
x_154 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_154, 0, x_5);
lean::cnstr_set(x_154, 1, x_57);
lean::cnstr_set(x_154, 2, x_78);
lean::cnstr_set(x_154, 3, x_121);
lean::cnstr_set(x_154, 4, x_134);
lean::cnstr_set(x_154, 5, x_135);
lean::cnstr_set(x_154, 6, x_152);
return x_154;
}
else
{
obj* x_155; obj* x_158; obj* x_161; obj* x_163; obj* x_164; 
x_155 = lean::cnstr_get(x_150, 0);
lean::inc(x_155);
lean::dec(x_150);
x_158 = lean::cnstr_get(x_155, 1);
lean::inc(x_158);
lean::dec(x_155);
x_161 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2;
lean::inc(x_161);
x_163 = l_list_map___main___rarg(x_161, x_158);
x_164 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_164, 0, x_5);
lean::cnstr_set(x_164, 1, x_57);
lean::cnstr_set(x_164, 2, x_78);
lean::cnstr_set(x_164, 3, x_121);
lean::cnstr_set(x_164, 4, x_134);
lean::cnstr_set(x_164, 5, x_135);
lean::cnstr_set(x_164, 6, x_163);
return x_164;
}
}
lbl_139:
{
obj* x_165; 
x_165 = l_lean_parser_syntax_as__node___main(x_138);
if (lean::obj_tag(x_165) == 0)
{
obj* x_167; obj* x_169; 
lean::dec(x_165);
x_167 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1;
lean::inc(x_167);
x_169 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_169, 0, x_5);
lean::cnstr_set(x_169, 1, x_57);
lean::cnstr_set(x_169, 2, x_78);
lean::cnstr_set(x_169, 3, x_121);
lean::cnstr_set(x_169, 4, x_134);
lean::cnstr_set(x_169, 5, x_137);
lean::cnstr_set(x_169, 6, x_167);
return x_169;
}
else
{
obj* x_170; obj* x_173; obj* x_176; obj* x_178; obj* x_179; 
x_170 = lean::cnstr_get(x_165, 0);
lean::inc(x_170);
lean::dec(x_165);
x_173 = lean::cnstr_get(x_170, 1);
lean::inc(x_173);
lean::dec(x_170);
x_176 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2;
lean::inc(x_176);
x_178 = l_list_map___main___rarg(x_176, x_173);
x_179 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_179, 0, x_5);
lean::cnstr_set(x_179, 1, x_57);
lean::cnstr_set(x_179, 2, x_78);
lean::cnstr_set(x_179, 3, x_121);
lean::cnstr_set(x_179, 4, x_134);
lean::cnstr_set(x_179, 5, x_137);
lean::cnstr_set(x_179, 6, x_178);
return x_179;
}
}
lbl_142:
{
obj* x_180; 
x_180 = l_lean_parser_syntax_as__node___main(x_141);
if (lean::obj_tag(x_180) == 0)
{
lean::dec(x_180);
if (lean::obj_tag(x_140) == 0)
{
obj* x_183; 
lean::dec(x_140);
x_183 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_183);
x_135 = x_183;
goto lbl_136;
}
else
{
obj* x_185; obj* x_188; 
x_185 = lean::cnstr_get(x_140, 0);
lean::inc(x_185);
lean::dec(x_140);
x_188 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_188);
x_137 = x_188;
x_138 = x_185;
goto lbl_139;
}
}
else
{
obj* x_190; obj* x_192; obj* x_193; 
x_190 = lean::cnstr_get(x_180, 0);
lean::inc(x_190);
if (lean::is_shared(x_180)) {
 lean::dec(x_180);
 x_192 = lean::box(0);
} else {
 lean::cnstr_release(x_180, 0);
 x_192 = x_180;
}
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
lean::dec(x_190);
if (lean::obj_tag(x_193) == 0)
{
obj* x_198; 
lean::dec(x_192);
lean::dec(x_193);
x_198 = lean::box(0);
if (lean::obj_tag(x_140) == 0)
{
lean::dec(x_140);
x_135 = x_198;
goto lbl_136;
}
else
{
obj* x_200; 
x_200 = lean::cnstr_get(x_140, 0);
lean::inc(x_200);
lean::dec(x_140);
x_137 = x_198;
x_138 = x_200;
goto lbl_139;
}
}
else
{
obj* x_203; obj* x_205; 
x_203 = lean::cnstr_get(x_193, 0);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_193, 1);
lean::inc(x_205);
lean::dec(x_193);
if (lean::obj_tag(x_205) == 0)
{
obj* x_209; obj* x_210; obj* x_212; obj* x_213; 
lean::dec(x_205);
x_209 = l_lean_parser_command_notation__like_has__view;
x_210 = lean::cnstr_get(x_209, 0);
lean::inc(x_210);
x_212 = lean::apply_1(x_210, x_203);
if (lean::is_scalar(x_192)) {
 x_213 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_213 = x_192;
}
lean::cnstr_set(x_213, 0, x_212);
if (lean::obj_tag(x_140) == 0)
{
lean::dec(x_140);
x_135 = x_213;
goto lbl_136;
}
else
{
obj* x_215; 
x_215 = lean::cnstr_get(x_140, 0);
lean::inc(x_215);
lean::dec(x_140);
x_137 = x_213;
x_138 = x_215;
goto lbl_139;
}
}
else
{
lean::dec(x_192);
lean::dec(x_205);
lean::dec(x_203);
if (lean::obj_tag(x_140) == 0)
{
obj* x_222; 
lean::dec(x_140);
x_222 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_222);
x_135 = x_222;
goto lbl_136;
}
else
{
obj* x_224; obj* x_227; 
x_224 = lean::cnstr_get(x_140, 0);
lean::inc(x_224);
lean::dec(x_140);
x_227 = l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3;
lean::inc(x_227);
x_137 = x_227;
x_138 = x_224;
goto lbl_139;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_lean_parser_command_inductive_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_41; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 5);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 6);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_16);
x_18 = l_option_map___rarg(x_16, x_3);
x_19 = lean::box(3);
lean::inc(x_19);
x_21 = l_option_get__or__else___main___rarg(x_18, x_19);
x_22 = lean::box(0);
lean::inc(x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_22);
x_25 = l_lean_parser_command_ident__univ__params_has__view;
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
x_28 = lean::apply_1(x_26, x_7);
x_29 = l_lean_parser_command_opt__decl__sig_has__view;
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_9);
x_33 = l_lean_parser_command_inductive_has__view_x_27___lambda__2___closed__1;
lean::inc(x_33);
x_35 = l_list_map___main___rarg(x_33, x_13);
x_36 = l_lean_parser_no__kind;
lean::inc(x_36);
x_38 = l_lean_parser_syntax_mk__node(x_36, x_35);
lean::inc(x_22);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_22);
if (lean::obj_tag(x_1) == 0)
{
obj* x_45; 
lean::dec(x_19);
lean::dec(x_1);
x_45 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_45);
x_41 = x_45;
goto lbl_42;
}
else
{
obj* x_47; obj* x_51; obj* x_52; obj* x_54; obj* x_56; 
x_47 = lean::cnstr_get(x_1, 0);
lean::inc(x_47);
lean::dec(x_1);
lean::inc(x_16);
x_51 = l_option_map___rarg(x_16, x_47);
x_52 = l_option_get__or__else___main___rarg(x_51, x_19);
lean::inc(x_22);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_22);
lean::inc(x_36);
x_56 = l_lean_parser_syntax_mk__node(x_36, x_54);
x_41 = x_56;
goto lbl_42;
}
lbl_42:
{
obj* x_57; obj* x_59; 
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_41);
lean::cnstr_set(x_57, 1, x_24);
lean::inc(x_36);
x_59 = l_lean_parser_syntax_mk__node(x_36, x_57);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_73; 
lean::dec(x_11);
lean::dec(x_22);
x_63 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_40);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_32);
lean::cnstr_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_28);
lean::cnstr_set(x_67, 1, x_66);
lean::inc(x_63);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_63);
lean::cnstr_set(x_69, 1, x_67);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_59);
lean::cnstr_set(x_70, 1, x_69);
x_71 = l_lean_parser_command_inductive;
lean::inc(x_71);
x_73 = l_lean_parser_syntax_mk__node(x_71, x_70);
return x_73;
}
else
{
obj* x_74; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_93; 
x_74 = lean::cnstr_get(x_11, 0);
lean::inc(x_74);
lean::dec(x_11);
x_77 = l_lean_parser_command_notation__like_has__view;
x_78 = lean::cnstr_get(x_77, 1);
lean::inc(x_78);
x_80 = lean::apply_1(x_78, x_74);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_22);
lean::inc(x_36);
x_83 = l_lean_parser_syntax_mk__node(x_36, x_81);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_40);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_32);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_28);
lean::cnstr_set(x_86, 1, x_85);
x_87 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_86);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_59);
lean::cnstr_set(x_90, 1, x_89);
x_91 = l_lean_parser_command_inductive;
lean::inc(x_91);
x_93 = l_lean_parser_syntax_mk__node(x_91, x_90);
return x_93;
}
}
else
{
obj* x_94; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; 
x_94 = lean::cnstr_get(x_5, 0);
lean::inc(x_94);
lean::dec(x_5);
x_97 = l_lean_parser_command_old__univ__params_has__view;
x_98 = lean::cnstr_get(x_97, 1);
lean::inc(x_98);
x_100 = lean::apply_1(x_98, x_94);
lean::inc(x_22);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_22);
lean::inc(x_36);
x_104 = l_lean_parser_syntax_mk__node(x_36, x_102);
if (lean::obj_tag(x_11) == 0)
{
obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_116; 
lean::dec(x_11);
lean::dec(x_22);
x_107 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_40);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_32);
lean::cnstr_set(x_110, 1, x_109);
x_111 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_111, 0, x_28);
lean::cnstr_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_112, 0, x_104);
lean::cnstr_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_113, 0, x_59);
lean::cnstr_set(x_113, 1, x_112);
x_114 = l_lean_parser_command_inductive;
lean::inc(x_114);
x_116 = l_lean_parser_syntax_mk__node(x_114, x_113);
return x_116;
}
else
{
obj* x_117; obj* x_120; obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_134; 
x_117 = lean::cnstr_get(x_11, 0);
lean::inc(x_117);
lean::dec(x_11);
x_120 = l_lean_parser_command_notation__like_has__view;
x_121 = lean::cnstr_get(x_120, 1);
lean::inc(x_121);
x_123 = lean::apply_1(x_121, x_117);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_22);
lean::inc(x_36);
x_126 = l_lean_parser_syntax_mk__node(x_36, x_124);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_40);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_32);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_28);
lean::cnstr_set(x_129, 1, x_128);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_104);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_59);
lean::cnstr_set(x_131, 1, x_130);
x_132 = l_lean_parser_command_inductive;
lean::inc(x_132);
x_134 = l_lean_parser_syntax_mk__node(x_132, x_131);
return x_134;
}
}
}
}
}
obj* _init_l_lean_parser_command_inductive_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_intro__rule_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_command_inductive_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_inductive_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_declaration_inner() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declaration");
x_8 = lean::name_mk_string(x_6, x_7);
x_9 = lean::mk_string("inner");
x_10 = lean::name_mk_string(x_8, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_command_declaration_inner_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_inner_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__2;
x_17 = lean::name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_86; uint8 x_87; 
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_dec_eq(x_2, x_86);
lean::dec(x_86);
if (x_87 == 0)
{
obj* x_89; uint8 x_90; 
x_89 = lean::mk_nat_obj(2u);
x_90 = lean::nat_dec_eq(x_2, x_89);
lean::dec(x_89);
if (x_90 == 0)
{
obj* x_92; uint8 x_93; 
x_92 = lean::mk_nat_obj(3u);
x_93 = lean::nat_dec_eq(x_2, x_92);
lean::dec(x_92);
if (x_93 == 0)
{
obj* x_95; uint8 x_96; 
x_95 = lean::mk_nat_obj(4u);
x_96 = lean::nat_dec_eq(x_2, x_95);
lean::dec(x_95);
lean::dec(x_2);
if (x_96 == 0)
{
obj* x_99; obj* x_100; obj* x_102; obj* x_103; 
x_99 = l_lean_parser_command_structure_has__view;
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
x_102 = lean::apply_1(x_100, x_1);
x_103 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
return x_103;
}
else
{
obj* x_104; obj* x_105; obj* x_107; obj* x_108; 
x_104 = l_lean_parser_command_inductive_has__view;
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_107 = lean::apply_1(x_105, x_1);
x_108 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
}
else
{
obj* x_110; obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_2);
x_110 = l_lean_parser_command_constant_has__view;
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::apply_1(x_111, x_1);
x_114 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_114, 0, x_113);
return x_114;
}
}
else
{
obj* x_116; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_2);
x_116 = l_lean_parser_command_example_has__view;
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
x_119 = lean::apply_1(x_117, x_1);
x_120 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_120, 0, x_119);
return x_120;
}
}
else
{
obj* x_122; obj* x_123; obj* x_125; obj* x_126; 
lean::dec(x_2);
x_122 = l_lean_parser_command_instance_has__view;
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::apply_1(x_123, x_1);
x_126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_126, 0, x_125);
return x_126;
}
}
else
{
obj* x_128; obj* x_129; obj* x_131; obj* x_132; 
lean::dec(x_2);
x_128 = l_lean_parser_command_def__like_has__view;
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::apply_1(x_129, x_1);
x_132 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
return x_132;
}
}
}
}
obj* _init_l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(2u);
x_12 = lean::nat_dec_eq(x_1, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_14; uint8 x_15; 
x_14 = lean::mk_nat_obj(3u);
x_15 = lean::nat_dec_eq(x_1, x_14);
lean::dec(x_14);
if (x_15 == 0)
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(4u);
x_18 = lean::nat_dec_eq(x_1, x_17);
lean::dec(x_17);
lean::dec(x_1);
if (x_18 == 0)
{
obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
x_21 = l_lean_parser_command_structure_has__view;
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_0);
x_25 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
x_26 = l_lean_parser_command_inductive_has__view;
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_0);
x_30 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
else
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_32 = l_lean_parser_command_constant_has__view;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::apply_1(x_33, x_0);
x_36 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
}
else
{
obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_1);
x_38 = l_lean_parser_command_example_has__view;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::apply_1(x_39, x_0);
x_42 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
else
{
obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_1);
x_44 = l_lean_parser_command_instance_has__view;
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::apply_1(x_45, x_0);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
}
else
{
obj* x_50; obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_1);
x_50 = l_lean_parser_command_def__like_has__view;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::apply_1(x_51, x_0);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
return x_54;
}
}
}
}
obj* _init_l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declaration");
x_8 = lean::name_mk_string(x_6, x_7);
x_9 = lean::mk_string("inner");
x_10 = lean::name_mk_string(x_8, x_9);
return x_10;
}
}
obj* l_lean_parser_command_declaration_inner_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_command_def__like_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_command_declaration_inner;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
case 1:
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_command_instance_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_lean_parser_command_declaration_inner;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
}
case 2:
{
obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_49; 
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = l_lean_parser_command_example_has__view;
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
x_40 = lean::apply_1(x_38, x_34);
lean::inc(x_1);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_1);
x_43 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_43);
x_45 = l_lean_parser_syntax_mk__node(x_43, x_42);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_1);
x_47 = l_lean_parser_command_declaration_inner;
lean::inc(x_47);
x_49 = l_lean_parser_syntax_mk__node(x_47, x_46);
return x_49;
}
case 3:
{
obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
lean::dec(x_0);
x_53 = l_lean_parser_command_constant_has__view;
x_54 = lean::cnstr_get(x_53, 1);
lean::inc(x_54);
x_56 = lean::apply_1(x_54, x_50);
lean::inc(x_1);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_1);
x_59 = l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
lean::inc(x_59);
x_61 = l_lean_parser_syntax_mk__node(x_59, x_58);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_1);
x_63 = l_lean_parser_command_declaration_inner;
lean::inc(x_63);
x_65 = l_lean_parser_syntax_mk__node(x_63, x_62);
return x_65;
}
case 4:
{
obj* x_66; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_81; 
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
lean::dec(x_0);
x_69 = l_lean_parser_command_inductive_has__view;
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
x_72 = lean::apply_1(x_70, x_66);
lean::inc(x_1);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_1);
x_75 = l_lean_parser_command_mixfix_kind_has__view_x_27___lambda__2___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_syntax_mk__node(x_75, x_74);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_1);
x_79 = l_lean_parser_command_declaration_inner;
lean::inc(x_79);
x_81 = l_lean_parser_syntax_mk__node(x_79, x_78);
return x_81;
}
default:
{
obj* x_82; obj* x_85; obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_93; obj* x_94; obj* x_95; obj* x_97; 
x_82 = lean::cnstr_get(x_0, 0);
lean::inc(x_82);
lean::dec(x_0);
x_85 = l_lean_parser_command_structure_has__view;
x_86 = lean::cnstr_get(x_85, 1);
lean::inc(x_86);
x_88 = lean::apply_1(x_86, x_82);
lean::inc(x_1);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_1);
x_91 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
lean::inc(x_91);
x_93 = l_lean_parser_syntax_mk__node(x_91, x_90);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_1);
x_95 = l_lean_parser_command_declaration_inner;
lean::inc(x_95);
x_97 = l_lean_parser_syntax_mk__node(x_95, x_94);
return x_97;
}
}
}
}
obj* _init_l_lean_parser_command_declaration_inner_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_declaration_inner_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_declaration() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("command");
x_6 = lean::name_mk_string(x_4, x_5);
x_7 = lean::mk_string("declaration");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_command_declaration_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_8);
x_12 = l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__1;
lean::inc(x_12);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_17 = l_lean_parser_command_declaration_inner_has__view;
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::apply_1(x_18, x_14);
x_21 = l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__2;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_20);
return x_23;
}
}
else
{
obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_32; 
x_24 = lean::cnstr_get(x_8, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_8, 1);
lean::inc(x_26);
lean::dec(x_8);
x_29 = l_lean_parser_command_decl__modifiers_has__view;
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_24);
if (lean::obj_tag(x_26) == 0)
{
obj* x_34; obj* x_36; 
lean::dec(x_26);
x_34 = l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__3;
lean::inc(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_26, 0);
lean::inc(x_37);
lean::dec(x_26);
x_40 = l_lean_parser_command_declaration_inner_has__view;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_37);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_32);
lean::cnstr_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
obj* _init_l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_0 = l_lean_parser_command_decl__modifiers_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
lean::inc(x_3);
x_5 = lean::apply_1(x_1, x_3);
x_6 = l_lean_parser_command_declaration_inner_has__view;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::apply_1(x_7, x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_decl__modifiers_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command_declaration_inner_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_command_declaration_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_command_decl__modifiers_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_7, x_1);
x_10 = l_lean_parser_command_declaration_inner_has__view;
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_13 = lean::apply_1(x_11, x_3);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_lean_parser_command_declaration;
lean::inc(x_17);
x_19 = l_lean_parser_syntax_mk__node(x_17, x_16);
return x_19;
}
}
obj* _init_l_lean_parser_command_declaration_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_command_declaration_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_command_declaration_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_148; obj* x_149; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_167; 
x_0 = lean::mk_string("def");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("abbreviation");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::mk_string("theorem");
x_14 = l_string_trim(x_13);
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_16, 0, x_14);
lean::inc(x_4);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_4);
lean::closure_set(x_18, 2, x_16);
x_19 = lean::box(0);
lean::inc(x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_22);
lean::inc(x_4);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_4);
lean::inc(x_19);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_19);
x_28 = l_lean_parser_command_def__like_kind;
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_27);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_old__univ__params_parser), 4, 0);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_32, 0, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__val_parser), 4, 0);
lean::inc(x_19);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_19);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
lean::inc(x_35);
lean::inc(x_36);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_35);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_ident__univ__params_parser), 4, 0);
lean::inc(x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_39);
lean::inc(x_32);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_32);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_lean_parser_command_def__like;
lean::inc(x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_48, 0, x_46);
lean::closure_set(x_48, 1, x_45);
x_49 = lean::mk_string("instance");
x_50 = l_string_trim(x_49);
lean::inc(x_50);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_52, 0, x_50);
lean::inc(x_4);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_54, 0, x_50);
lean::closure_set(x_54, 1, x_4);
lean::closure_set(x_54, 2, x_52);
lean::inc(x_40);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_56, 0, x_40);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__sig_parser), 4, 0);
lean::inc(x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_35);
lean::inc(x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_61);
x_63 = l_lean_parser_command_instance;
lean::inc(x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_65, 0, x_63);
lean::closure_set(x_65, 1, x_62);
x_66 = lean::mk_string("example");
x_67 = l_string_trim(x_66);
lean::inc(x_67);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_69, 0, x_67);
lean::inc(x_4);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_71, 0, x_67);
lean::closure_set(x_71, 1, x_4);
lean::closure_set(x_71, 2, x_69);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_59);
x_73 = l_lean_parser_command_example;
lean::inc(x_73);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_75, 0, x_73);
lean::closure_set(x_75, 1, x_72);
x_76 = lean::mk_string("constant");
x_77 = l_string_trim(x_76);
lean::inc(x_77);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_79, 0, x_77);
lean::inc(x_4);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_81, 0, x_77);
lean::closure_set(x_81, 1, x_4);
lean::closure_set(x_81, 2, x_79);
x_82 = lean::mk_string("axiom");
x_83 = l_string_trim(x_82);
lean::inc(x_83);
x_85 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_85, 0, x_83);
lean::inc(x_4);
x_87 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_87, 0, x_83);
lean::closure_set(x_87, 1, x_4);
lean::closure_set(x_87, 2, x_85);
lean::inc(x_19);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_19);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_81);
lean::cnstr_set(x_90, 1, x_89);
lean::inc(x_4);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_92, 0, x_90);
lean::closure_set(x_92, 1, x_4);
lean::inc(x_19);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_19);
x_95 = l_lean_parser_command_constant__keyword;
lean::inc(x_95);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_97, 0, x_95);
lean::closure_set(x_97, 1, x_94);
lean::inc(x_19);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_57);
lean::cnstr_set(x_99, 1, x_19);
lean::inc(x_40);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_40);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_97);
lean::cnstr_set(x_102, 1, x_101);
x_103 = l_lean_parser_command_constant;
lean::inc(x_103);
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_105, 0, x_103);
lean::closure_set(x_105, 1, x_102);
x_106 = lean::mk_string("class");
x_107 = l_string_trim(x_106);
lean::inc(x_107);
x_109 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_109, 0, x_107);
lean::inc(x_4);
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_111, 0, x_107);
lean::closure_set(x_111, 1, x_4);
lean::closure_set(x_111, 2, x_109);
x_112 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_112, 0, x_111);
x_113 = lean::mk_string("inductive");
x_114 = l_string_trim(x_113);
lean::inc(x_114);
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_116, 0, x_114);
lean::inc(x_4);
x_118 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_118, 0, x_114);
lean::closure_set(x_118, 1, x_4);
lean::closure_set(x_118, 2, x_116);
lean::inc(x_19);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_19);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_112);
lean::cnstr_set(x_121, 1, x_120);
x_122 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_122, 0, x_121);
x_123 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_notation__like_parser), 5, 0);
x_124 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_124, 0, x_123);
x_125 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_125, 0, x_124);
x_126 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_intro__rule_parser), 4, 0);
x_127 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2), 5, 1);
lean::closure_set(x_127, 0, x_126);
lean::inc(x_19);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_19);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_125);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_36);
lean::cnstr_set(x_131, 1, x_130);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_40);
lean::cnstr_set(x_132, 1, x_131);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_32);
lean::cnstr_set(x_133, 1, x_132);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_122);
lean::cnstr_set(x_134, 1, x_133);
x_135 = l_lean_parser_command_inductive;
lean::inc(x_135);
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_137, 0, x_135);
lean::closure_set(x_137, 1, x_134);
x_138 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure_parser), 4, 0);
lean::inc(x_19);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_19);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_105);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_75);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_65);
lean::cnstr_set(x_144, 1, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_48);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_146, 0, x_145);
lean::closure_set(x_146, 1, x_4);
lean::inc(x_19);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_146);
lean::cnstr_set(x_148, 1, x_19);
x_149 = l_lean_parser_command_declaration_inner;
lean::inc(x_149);
x_151 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_151, 0, x_149);
lean::closure_set(x_151, 1, x_148);
x_152 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_19);
x_153 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__modifiers_parser), 4, 0);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_152);
x_155 = l_lean_parser_command__parser__m_monad___closed__1;
x_156 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_157 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_158 = l_lean_parser_command__parser__m_alternative___closed__1;
x_159 = l_lean_parser_command_declaration;
x_160 = l_lean_parser_command_declaration_has__view;
lean::inc(x_160);
lean::inc(x_159);
lean::inc(x_158);
lean::inc(x_157);
lean::inc(x_156);
lean::inc(x_155);
x_167 = l_lean_parser_combinators_node_view___rarg(x_155, x_156, x_157, x_158, x_159, x_154, x_160);
return x_167;
}
}
obj* l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_5 = l_lean_parser_no__kind;
lean::inc(x_5);
x_7 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_5, x_0, x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
x_13 = l_lean_parser_parsec__t_try__mk__res___rarg(x_8);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
}
obj* _init_l_lean_parser_command_declaration_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_118; obj* x_119; 
x_0 = lean::mk_string("def");
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::mk_string("abbreviation");
lean::inc(x_1);
x_6 = l_lean_parser_symbol_tokens___rarg(x_4, x_1);
x_7 = lean::mk_string("theorem");
lean::inc(x_1);
x_9 = l_lean_parser_symbol_tokens___rarg(x_7, x_1);
x_10 = lean::box(0);
lean::inc(x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_9, x_10);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_6, x_12);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_3, x_13);
x_15 = l_lean_parser_tokens___rarg(x_14);
lean::inc(x_10);
x_17 = l_lean_parser_list_cons_tokens___rarg(x_15, x_10);
x_18 = l_lean_parser_tokens___rarg(x_17);
x_19 = l_lean_parser_command_old__univ__params_parser_lean_parser_has__tokens;
lean::inc(x_19);
x_21 = l_lean_parser_tokens___rarg(x_19);
x_22 = l_lean_parser_command_decl__val_parser_lean_parser_has__tokens;
lean::inc(x_10);
lean::inc(x_22);
x_25 = l_lean_parser_list_cons_tokens___rarg(x_22, x_10);
x_26 = l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens;
lean::inc(x_25);
lean::inc(x_26);
x_29 = l_lean_parser_list_cons_tokens___rarg(x_26, x_25);
x_30 = l_lean_parser_command_ident__univ__params_parser_lean_parser_has__tokens;
lean::inc(x_30);
x_32 = l_lean_parser_list_cons_tokens___rarg(x_30, x_29);
lean::inc(x_21);
x_34 = l_lean_parser_list_cons_tokens___rarg(x_21, x_32);
x_35 = l_lean_parser_list_cons_tokens___rarg(x_18, x_34);
x_36 = l_lean_parser_tokens___rarg(x_35);
x_37 = lean::mk_string("instance");
lean::inc(x_1);
x_39 = l_lean_parser_symbol_tokens___rarg(x_37, x_1);
lean::inc(x_30);
x_41 = l_lean_parser_tokens___rarg(x_30);
x_42 = l_lean_parser_command_decl__sig_parser_lean_parser_has__tokens;
lean::inc(x_42);
x_44 = l_lean_parser_list_cons_tokens___rarg(x_42, x_25);
lean::inc(x_44);
x_46 = l_lean_parser_list_cons_tokens___rarg(x_41, x_44);
x_47 = l_lean_parser_list_cons_tokens___rarg(x_39, x_46);
x_48 = l_lean_parser_tokens___rarg(x_47);
x_49 = lean::mk_string("example");
lean::inc(x_1);
x_51 = l_lean_parser_symbol_tokens___rarg(x_49, x_1);
x_52 = l_lean_parser_list_cons_tokens___rarg(x_51, x_44);
x_53 = l_lean_parser_tokens___rarg(x_52);
x_54 = lean::mk_string("constant");
lean::inc(x_1);
x_56 = l_lean_parser_symbol_tokens___rarg(x_54, x_1);
x_57 = lean::mk_string("axiom");
lean::inc(x_1);
x_59 = l_lean_parser_symbol_tokens___rarg(x_57, x_1);
lean::inc(x_10);
x_61 = l_lean_parser_list_cons_tokens___rarg(x_59, x_10);
x_62 = l_lean_parser_list_cons_tokens___rarg(x_56, x_61);
x_63 = l_lean_parser_tokens___rarg(x_62);
lean::inc(x_10);
x_65 = l_lean_parser_list_cons_tokens___rarg(x_63, x_10);
x_66 = l_lean_parser_tokens___rarg(x_65);
lean::inc(x_10);
lean::inc(x_42);
x_69 = l_lean_parser_list_cons_tokens___rarg(x_42, x_10);
lean::inc(x_30);
x_71 = l_lean_parser_list_cons_tokens___rarg(x_30, x_69);
x_72 = l_lean_parser_list_cons_tokens___rarg(x_66, x_71);
x_73 = l_lean_parser_tokens___rarg(x_72);
x_74 = lean::mk_string("class");
lean::inc(x_1);
x_76 = l_lean_parser_symbol_tokens___rarg(x_74, x_1);
x_77 = l_lean_parser_tokens___rarg(x_76);
x_78 = lean::mk_string("inductive");
x_79 = l_lean_parser_symbol_tokens___rarg(x_78, x_1);
lean::inc(x_10);
x_81 = l_lean_parser_list_cons_tokens___rarg(x_79, x_10);
x_82 = l_lean_parser_list_cons_tokens___rarg(x_77, x_81);
x_83 = l_lean_parser_tokens___rarg(x_82);
x_84 = l_lean_parser_tokens___rarg(x_83);
x_85 = l_lean_parser_command_notation__like_parser_lean_parser_has__tokens;
lean::inc(x_85);
x_87 = l_lean_parser_tokens___rarg(x_85);
x_88 = l_lean_parser_tokens___rarg(x_87);
x_89 = l_lean_parser_command_intro__rule_parser_lean_parser_has__tokens;
lean::inc(x_89);
x_91 = l_lean_parser_tokens___rarg(x_89);
lean::inc(x_10);
x_93 = l_lean_parser_list_cons_tokens___rarg(x_91, x_10);
x_94 = l_lean_parser_list_cons_tokens___rarg(x_88, x_93);
lean::inc(x_26);
x_96 = l_lean_parser_list_cons_tokens___rarg(x_26, x_94);
lean::inc(x_30);
x_98 = l_lean_parser_list_cons_tokens___rarg(x_30, x_96);
x_99 = l_lean_parser_list_cons_tokens___rarg(x_21, x_98);
x_100 = l_lean_parser_list_cons_tokens___rarg(x_84, x_99);
x_101 = l_lean_parser_tokens___rarg(x_100);
x_102 = l_lean_parser_command_structure_parser_lean_parser_has__tokens;
lean::inc(x_10);
lean::inc(x_102);
x_105 = l_lean_parser_list_cons_tokens___rarg(x_102, x_10);
x_106 = l_lean_parser_list_cons_tokens___rarg(x_101, x_105);
x_107 = l_lean_parser_list_cons_tokens___rarg(x_73, x_106);
x_108 = l_lean_parser_list_cons_tokens___rarg(x_53, x_107);
x_109 = l_lean_parser_list_cons_tokens___rarg(x_48, x_108);
x_110 = l_lean_parser_list_cons_tokens___rarg(x_36, x_109);
x_111 = l_lean_parser_tokens___rarg(x_110);
lean::inc(x_10);
x_113 = l_lean_parser_list_cons_tokens___rarg(x_111, x_10);
x_114 = l_lean_parser_tokens___rarg(x_113);
x_115 = l_lean_parser_list_cons_tokens___rarg(x_114, x_10);
x_116 = l_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens;
lean::inc(x_116);
x_118 = l_lean_parser_list_cons_tokens___rarg(x_116, x_115);
x_119 = l_lean_parser_tokens___rarg(x_118);
return x_119;
}
}
obj* l_lean_parser_command_declaration_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_command_declaration;
x_5 = l_lean_parser_command_declaration_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_command_declaration_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_116; obj* x_118; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_148; obj* x_149; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_0 = lean::mk_string("def");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_string("abbreviation");
x_8 = l_string_trim(x_7);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_8);
lean::inc(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_12, 0, x_8);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_10);
x_13 = lean::mk_string("theorem");
x_14 = l_string_trim(x_13);
lean::inc(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_16, 0, x_14);
lean::inc(x_4);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_18, 0, x_14);
lean::closure_set(x_18, 1, x_4);
lean::closure_set(x_18, 2, x_16);
x_19 = lean::box(0);
lean::inc(x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_12);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_22);
lean::inc(x_4);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_4);
lean::inc(x_19);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_19);
x_28 = l_lean_parser_command_def__like_kind;
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_27);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_old__univ__params_parser), 4, 0);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_32, 0, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__val_parser), 4, 0);
lean::inc(x_19);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_19);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_opt__decl__sig_parser), 4, 0);
lean::inc(x_35);
lean::inc(x_36);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_35);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_ident__univ__params_parser), 4, 0);
lean::inc(x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_39);
lean::inc(x_32);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_32);
lean::cnstr_set(x_44, 1, x_42);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_44);
x_46 = l_lean_parser_command_def__like;
lean::inc(x_46);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_48, 0, x_46);
lean::closure_set(x_48, 1, x_45);
x_49 = lean::mk_string("instance");
x_50 = l_string_trim(x_49);
lean::inc(x_50);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_52, 0, x_50);
lean::inc(x_4);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_54, 0, x_50);
lean::closure_set(x_54, 1, x_4);
lean::closure_set(x_54, 2, x_52);
lean::inc(x_40);
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_56, 0, x_40);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__sig_parser), 4, 0);
lean::inc(x_57);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_35);
lean::inc(x_59);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_59);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_61);
x_63 = l_lean_parser_command_instance;
lean::inc(x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_65, 0, x_63);
lean::closure_set(x_65, 1, x_62);
x_66 = lean::mk_string("example");
x_67 = l_string_trim(x_66);
lean::inc(x_67);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_69, 0, x_67);
lean::inc(x_4);
x_71 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_71, 0, x_67);
lean::closure_set(x_71, 1, x_4);
lean::closure_set(x_71, 2, x_69);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_59);
x_73 = l_lean_parser_command_example;
lean::inc(x_73);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_75, 0, x_73);
lean::closure_set(x_75, 1, x_72);
x_76 = lean::mk_string("constant");
x_77 = l_string_trim(x_76);
lean::inc(x_77);
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_79, 0, x_77);
lean::inc(x_4);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_81, 0, x_77);
lean::closure_set(x_81, 1, x_4);
lean::closure_set(x_81, 2, x_79);
x_82 = lean::mk_string("axiom");
x_83 = l_string_trim(x_82);
lean::inc(x_83);
x_85 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_85, 0, x_83);
lean::inc(x_4);
x_87 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_87, 0, x_83);
lean::closure_set(x_87, 1, x_4);
lean::closure_set(x_87, 2, x_85);
lean::inc(x_19);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_19);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_81);
lean::cnstr_set(x_90, 1, x_89);
lean::inc(x_4);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_92, 0, x_90);
lean::closure_set(x_92, 1, x_4);
lean::inc(x_19);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_19);
x_95 = l_lean_parser_command_constant__keyword;
lean::inc(x_95);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_97, 0, x_95);
lean::closure_set(x_97, 1, x_94);
lean::inc(x_19);
x_99 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_99, 0, x_57);
lean::cnstr_set(x_99, 1, x_19);
lean::inc(x_40);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_40);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_97);
lean::cnstr_set(x_102, 1, x_101);
x_103 = l_lean_parser_command_constant;
lean::inc(x_103);
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_105, 0, x_103);
lean::closure_set(x_105, 1, x_102);
x_106 = lean::mk_string("class");
x_107 = l_string_trim(x_106);
lean::inc(x_107);
x_109 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_109, 0, x_107);
lean::inc(x_4);
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_111, 0, x_107);
lean::closure_set(x_111, 1, x_4);
lean::closure_set(x_111, 2, x_109);
x_112 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_112, 0, x_111);
x_113 = lean::mk_string("inductive");
x_114 = l_string_trim(x_113);
lean::inc(x_114);
x_116 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_116, 0, x_114);
lean::inc(x_4);
x_118 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_doc__comment_parser_lean_parser_has__view___spec__1), 7, 3);
lean::closure_set(x_118, 0, x_114);
lean::closure_set(x_118, 1, x_4);
lean::closure_set(x_118, 2, x_116);
lean::inc(x_19);
x_120 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set(x_120, 1, x_19);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_112);
lean::cnstr_set(x_121, 1, x_120);
x_122 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_declaration_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_122, 0, x_121);
x_123 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_notation__like_parser), 5, 0);
x_124 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_term__parser_run), 5, 1);
lean::closure_set(x_124, 0, x_123);
x_125 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__1), 5, 1);
lean::closure_set(x_125, 0, x_124);
x_126 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_intro__rule_parser), 4, 0);
x_127 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_command_attr__instance_parser_lean_parser_has__view___spec__2), 5, 1);
lean::closure_set(x_127, 0, x_126);
lean::inc(x_19);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_19);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_125);
lean::cnstr_set(x_130, 1, x_129);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_36);
lean::cnstr_set(x_131, 1, x_130);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_40);
lean::cnstr_set(x_132, 1, x_131);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_32);
lean::cnstr_set(x_133, 1, x_132);
x_134 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_134, 0, x_122);
lean::cnstr_set(x_134, 1, x_133);
x_135 = l_lean_parser_command_inductive;
lean::inc(x_135);
x_137 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_137, 0, x_135);
lean::closure_set(x_137, 1, x_134);
x_138 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_structure_parser), 4, 0);
lean::inc(x_19);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_19);
x_141 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set(x_141, 1, x_140);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_105);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_143, 0, x_75);
lean::cnstr_set(x_143, 1, x_142);
x_144 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_144, 0, x_65);
lean::cnstr_set(x_144, 1, x_143);
x_145 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_145, 0, x_48);
lean::cnstr_set(x_145, 1, x_144);
x_146 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_command_decl__modifiers_parser_lean_parser_has__view___spec__2), 6, 2);
lean::closure_set(x_146, 0, x_145);
lean::closure_set(x_146, 1, x_4);
lean::inc(x_19);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_146);
lean::cnstr_set(x_148, 1, x_19);
x_149 = l_lean_parser_command_declaration_inner;
lean::inc(x_149);
x_151 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_command_doc__comment_parser___spec__4), 6, 2);
lean::closure_set(x_151, 0, x_149);
lean::closure_set(x_151, 1, x_148);
x_152 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_19);
x_153 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_decl__modifiers_parser), 4, 0);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_152);
return x_154;
}
}
void initialize_init_lean_parser_term();
static bool _G_initialized = false;
void initialize_init_lean_parser_declaration() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_term();
 l_lean_parser_command_doc__comment = _init_l_lean_parser_command_doc__comment();
 l_lean_parser_command_doc__comment_has__view_x_27 = _init_l_lean_parser_command_doc__comment_has__view_x_27();
 l_lean_parser_command_doc__comment_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_doc__comment_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_doc__comment_has__view = _init_l_lean_parser_command_doc__comment_has__view();
 l_lean_parser_command_doc__comment_parser_lean_parser_has__view = _init_l_lean_parser_command_doc__comment_parser_lean_parser_has__view();
 l_lean_parser_command_doc__comment_parser_lean_parser_has__tokens = _init_l_lean_parser_command_doc__comment_parser_lean_parser_has__tokens();
 l_lean_parser_command_doc__comment_parser___closed__1 = _init_l_lean_parser_command_doc__comment_parser___closed__1();
 l_lean_parser_command_attr__instance = _init_l_lean_parser_command_attr__instance();
 l_lean_parser_command_attr__instance_has__view_x_27 = _init_l_lean_parser_command_attr__instance_has__view_x_27();
 l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_attr__instance_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_attr__instance_has__view = _init_l_lean_parser_command_attr__instance_has__view();
 l_lean_parser_command_attr__instance_parser_lean_parser_has__view = _init_l_lean_parser_command_attr__instance_parser_lean_parser_has__view();
 l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens = _init_l_lean_parser_command_attr__instance_parser_lean_parser_has__tokens();
 l_lean_parser_command_attr__instance_parser___closed__1 = _init_l_lean_parser_command_attr__instance_parser___closed__1();
 l_lean_parser_command_decl__attributes = _init_l_lean_parser_command_decl__attributes();
 l_lean_parser_command_decl__attributes_has__view_x_27 = _init_l_lean_parser_command_decl__attributes_has__view_x_27();
 l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_decl__attributes_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_decl__attributes_has__view = _init_l_lean_parser_command_decl__attributes_has__view();
 l_lean_parser_command_decl__attributes_parser_lean_parser_has__view = _init_l_lean_parser_command_decl__attributes_parser_lean_parser_has__view();
 l_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens = _init_l_lean_parser_command_decl__attributes_parser_lean_parser_has__tokens();
 l_lean_parser_command_decl__attributes_parser___closed__1 = _init_l_lean_parser_command_decl__attributes_parser___closed__1();
 l_lean_parser_command_visibility = _init_l_lean_parser_command_visibility();
 l_lean_parser_command_visibility_has__view_x_27 = _init_l_lean_parser_command_visibility_has__view_x_27();
 l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_visibility_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_visibility_has__view = _init_l_lean_parser_command_visibility_has__view();
 l_lean_parser_command_decl__modifiers = _init_l_lean_parser_command_decl__modifiers();
 l_lean_parser_command_decl__modifiers_has__view_x_27 = _init_l_lean_parser_command_decl__modifiers_has__view_x_27();
 l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_decl__modifiers_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_decl__modifiers_has__view = _init_l_lean_parser_command_decl__modifiers_has__view();
 l_lean_parser_command_decl__modifiers_parser_lean_parser_has__view = _init_l_lean_parser_command_decl__modifiers_parser_lean_parser_has__view();
 l_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens = _init_l_lean_parser_command_decl__modifiers_parser_lean_parser_has__tokens();
 l_lean_parser_command_decl__modifiers_parser___closed__1 = _init_l_lean_parser_command_decl__modifiers_parser___closed__1();
 l_lean_parser_command_decl__sig = _init_l_lean_parser_command_decl__sig();
 l_lean_parser_command_decl__sig_has__view_x_27 = _init_l_lean_parser_command_decl__sig_has__view_x_27();
 l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_decl__sig_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_decl__sig_has__view = _init_l_lean_parser_command_decl__sig_has__view();
 l_lean_parser_command_decl__sig_parser_lean_parser_has__view = _init_l_lean_parser_command_decl__sig_parser_lean_parser_has__view();
 l_lean_parser_command_decl__sig_parser_lean_parser_has__tokens = _init_l_lean_parser_command_decl__sig_parser_lean_parser_has__tokens();
 l_lean_parser_command_decl__sig_parser___closed__1 = _init_l_lean_parser_command_decl__sig_parser___closed__1();
 l_lean_parser_command_opt__decl__sig = _init_l_lean_parser_command_opt__decl__sig();
 l_lean_parser_command_opt__decl__sig_has__view_x_27 = _init_l_lean_parser_command_opt__decl__sig_has__view_x_27();
 l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_opt__decl__sig_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_opt__decl__sig_has__view = _init_l_lean_parser_command_opt__decl__sig_has__view();
 l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__view = _init_l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__view();
 l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens = _init_l_lean_parser_command_opt__decl__sig_parser_lean_parser_has__tokens();
 l_lean_parser_command_opt__decl__sig_parser___closed__1 = _init_l_lean_parser_command_opt__decl__sig_parser___closed__1();
 l_lean_parser_command_equation = _init_l_lean_parser_command_equation();
 l_lean_parser_command_equation_has__view_x_27 = _init_l_lean_parser_command_equation_has__view_x_27();
 l_lean_parser_command_equation_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_equation_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_equation_has__view = _init_l_lean_parser_command_equation_has__view();
 l_lean_parser_command_equation_parser_lean_parser_has__view = _init_l_lean_parser_command_equation_parser_lean_parser_has__view();
 l_lean_parser_command_equation_parser_lean_parser_has__tokens = _init_l_lean_parser_command_equation_parser_lean_parser_has__tokens();
 l_lean_parser_command_equation_parser___closed__1 = _init_l_lean_parser_command_equation_parser___closed__1();
 l_lean_parser_command_simple__decl__val = _init_l_lean_parser_command_simple__decl__val();
 l_lean_parser_command_simple__decl__val_has__view_x_27 = _init_l_lean_parser_command_simple__decl__val_has__view_x_27();
 l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_simple__decl__val_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_simple__decl__val_has__view = _init_l_lean_parser_command_simple__decl__val_has__view();
 l_lean_parser_command_decl__val = _init_l_lean_parser_command_decl__val();
 l_lean_parser_command_decl__val_has__view_x_27 = _init_l_lean_parser_command_decl__val_has__view_x_27();
 l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_command_decl__val_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_command_decl__val_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_command_decl__val_has__view = _init_l_lean_parser_command_decl__val_has__view();
 l_lean_parser_command_decl__val_parser_lean_parser_has__view = _init_l_lean_parser_command_decl__val_parser_lean_parser_has__view();
 l_lean_parser_command_decl__val_parser_lean_parser_has__tokens = _init_l_lean_parser_command_decl__val_parser_lean_parser_has__tokens();
 l_lean_parser_command_decl__val_parser___closed__1 = _init_l_lean_parser_command_decl__val_parser___closed__1();
 l_lean_parser_command_relaxed__infer__modifier = _init_l_lean_parser_command_relaxed__infer__modifier();
 l_lean_parser_command_relaxed__infer__modifier_has__view_x_27 = _init_l_lean_parser_command_relaxed__infer__modifier_has__view_x_27();
 l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_relaxed__infer__modifier_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_relaxed__infer__modifier_has__view = _init_l_lean_parser_command_relaxed__infer__modifier_has__view();
 l_lean_parser_command_strict__infer__modifier = _init_l_lean_parser_command_strict__infer__modifier();
 l_lean_parser_command_strict__infer__modifier_has__view_x_27 = _init_l_lean_parser_command_strict__infer__modifier_has__view_x_27();
 l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_strict__infer__modifier_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_strict__infer__modifier_has__view = _init_l_lean_parser_command_strict__infer__modifier_has__view();
 l_lean_parser_command_infer__modifier = _init_l_lean_parser_command_infer__modifier();
 l_lean_parser_command_infer__modifier_has__view_x_27 = _init_l_lean_parser_command_infer__modifier_has__view_x_27();
 l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_infer__modifier_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_infer__modifier_has__view = _init_l_lean_parser_command_infer__modifier_has__view();
 l_lean_parser_command_infer__modifier_parser_lean_parser_has__view = _init_l_lean_parser_command_infer__modifier_parser_lean_parser_has__view();
 l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens = _init_l_lean_parser_command_infer__modifier_parser_lean_parser_has__tokens();
 l_lean_parser_command_infer__modifier_parser___closed__1 = _init_l_lean_parser_command_infer__modifier_parser___closed__1();
 l_lean_parser_command_intro__rule = _init_l_lean_parser_command_intro__rule();
 l_lean_parser_command_intro__rule_has__view_x_27 = _init_l_lean_parser_command_intro__rule_has__view_x_27();
 l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_intro__rule_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_intro__rule_has__view = _init_l_lean_parser_command_intro__rule_has__view();
 l_lean_parser_command_intro__rule_parser_lean_parser_has__view = _init_l_lean_parser_command_intro__rule_parser_lean_parser_has__view();
 l_lean_parser_command_intro__rule_parser_lean_parser_has__tokens = _init_l_lean_parser_command_intro__rule_parser_lean_parser_has__tokens();
 l_lean_parser_command_intro__rule_parser___closed__1 = _init_l_lean_parser_command_intro__rule_parser___closed__1();
 l_lean_parser_command_struct__binder__content = _init_l_lean_parser_command_struct__binder__content();
 l_lean_parser_command_struct__binder__content_has__view_x_27 = _init_l_lean_parser_command_struct__binder__content_has__view_x_27();
 l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_struct__binder__content_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_struct__binder__content_has__view = _init_l_lean_parser_command_struct__binder__content_has__view();
 l_lean_parser_command_struct__binder__content_parser_lean_parser_has__view = _init_l_lean_parser_command_struct__binder__content_parser_lean_parser_has__view();
 l_lean_parser_command_struct__binder__content_parser_lean_parser_has__tokens = _init_l_lean_parser_command_struct__binder__content_parser_lean_parser_has__tokens();
 l_lean_parser_command_struct__binder__content_parser___closed__1 = _init_l_lean_parser_command_struct__binder__content_parser___closed__1();
 l_lean_parser_command_struct__explicit__binder__content = _init_l_lean_parser_command_struct__explicit__binder__content();
 l_lean_parser_command_struct__explicit__binder__content_has__view_x_27 = _init_l_lean_parser_command_struct__explicit__binder__content_has__view_x_27();
 l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_struct__explicit__binder__content_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_struct__explicit__binder__content_has__view = _init_l_lean_parser_command_struct__explicit__binder__content_has__view();
 l_lean_parser_command_struct__explicit__binder = _init_l_lean_parser_command_struct__explicit__binder();
 l_lean_parser_command_struct__explicit__binder_has__view_x_27 = _init_l_lean_parser_command_struct__explicit__binder_has__view_x_27();
 l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_struct__explicit__binder_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_struct__explicit__binder_has__view = _init_l_lean_parser_command_struct__explicit__binder_has__view();
 l_lean_parser_command_struct__implicit__binder = _init_l_lean_parser_command_struct__implicit__binder();
 l_lean_parser_command_struct__implicit__binder_has__view_x_27 = _init_l_lean_parser_command_struct__implicit__binder_has__view_x_27();
 l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_struct__implicit__binder_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_struct__implicit__binder_has__view = _init_l_lean_parser_command_struct__implicit__binder_has__view();
 l_lean_parser_command_strict__implicit__binder = _init_l_lean_parser_command_strict__implicit__binder();
 l_lean_parser_command_strict__implicit__binder_has__view_x_27 = _init_l_lean_parser_command_strict__implicit__binder_has__view_x_27();
 l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_strict__implicit__binder_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_strict__implicit__binder_has__view = _init_l_lean_parser_command_strict__implicit__binder_has__view();
 l_lean_parser_command_inst__implicit__binder = _init_l_lean_parser_command_inst__implicit__binder();
 l_lean_parser_command_inst__implicit__binder_has__view_x_27 = _init_l_lean_parser_command_inst__implicit__binder_has__view_x_27();
 l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_inst__implicit__binder_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_inst__implicit__binder_has__view = _init_l_lean_parser_command_inst__implicit__binder_has__view();
 l_lean_parser_command_structure__field__block = _init_l_lean_parser_command_structure__field__block();
 l_lean_parser_command_structure__field__block_has__view_x_27 = _init_l_lean_parser_command_structure__field__block_has__view_x_27();
 l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_structure__field__block_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_structure__field__block_has__view = _init_l_lean_parser_command_structure__field__block_has__view();
 l_lean_parser_command_structure__field__block_parser_lean_parser_has__view = _init_l_lean_parser_command_structure__field__block_parser_lean_parser_has__view();
 l_lean_parser_command_structure__field__block_parser_lean_parser_has__tokens = _init_l_lean_parser_command_structure__field__block_parser_lean_parser_has__tokens();
 l_lean_parser_command_structure__field__block_parser___closed__1 = _init_l_lean_parser_command_structure__field__block_parser___closed__1();
 l_lean_parser_command_old__univ__params = _init_l_lean_parser_command_old__univ__params();
 l_lean_parser_command_old__univ__params_has__view_x_27 = _init_l_lean_parser_command_old__univ__params_has__view_x_27();
 l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_old__univ__params_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_old__univ__params_has__view = _init_l_lean_parser_command_old__univ__params_has__view();
 l_lean_parser_command_old__univ__params_parser_lean_parser_has__view = _init_l_lean_parser_command_old__univ__params_parser_lean_parser_has__view();
 l_lean_parser_command_old__univ__params_parser_lean_parser_has__tokens = _init_l_lean_parser_command_old__univ__params_parser_lean_parser_has__tokens();
 l_lean_parser_command_old__univ__params_parser___closed__1 = _init_l_lean_parser_command_old__univ__params_parser___closed__1();
 l_lean_parser_command_univ__params = _init_l_lean_parser_command_univ__params();
 l_lean_parser_command_univ__params_has__view_x_27 = _init_l_lean_parser_command_univ__params_has__view_x_27();
 l_lean_parser_command_univ__params_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_univ__params_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_univ__params_has__view = _init_l_lean_parser_command_univ__params_has__view();
 l_lean_parser_command_ident__univ__params = _init_l_lean_parser_command_ident__univ__params();
 l_lean_parser_command_ident__univ__params_has__view_x_27 = _init_l_lean_parser_command_ident__univ__params_has__view_x_27();
 l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_command_ident__univ__params_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_command_ident__univ__params_has__view = _init_l_lean_parser_command_ident__univ__params_has__view();
 l_lean_parser_command_ident__univ__params_parser_lean_parser_has__view = _init_l_lean_parser_command_ident__univ__params_parser_lean_parser_has__view();
 l_lean_parser_command_ident__univ__params_parser_lean_parser_has__tokens = _init_l_lean_parser_command_ident__univ__params_parser_lean_parser_has__tokens();
 l_lean_parser_command_ident__univ__params_parser___closed__1 = _init_l_lean_parser_command_ident__univ__params_parser___closed__1();
 l_lean_parser_command_structure__kw = _init_l_lean_parser_command_structure__kw();
 l_lean_parser_command_structure__kw_has__view_x_27 = _init_l_lean_parser_command_structure__kw_has__view_x_27();
 l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_structure__kw_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_structure__kw_has__view = _init_l_lean_parser_command_structure__kw_has__view();
 l_lean_parser_command_extends = _init_l_lean_parser_command_extends();
 l_lean_parser_command_extends_has__view_x_27 = _init_l_lean_parser_command_extends_has__view_x_27();
 l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_extends_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_extends_has__view = _init_l_lean_parser_command_extends_has__view();
 l_lean_parser_command_structure__ctor = _init_l_lean_parser_command_structure__ctor();
 l_lean_parser_command_structure__ctor_has__view_x_27 = _init_l_lean_parser_command_structure__ctor_has__view_x_27();
 l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_structure__ctor_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_structure__ctor_has__view = _init_l_lean_parser_command_structure__ctor_has__view();
 l_lean_parser_command_structure = _init_l_lean_parser_command_structure();
 l_lean_parser_command_structure_has__view_x_27 = _init_l_lean_parser_command_structure_has__view_x_27();
 l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__6 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__1___closed__6();
 l_lean_parser_command_structure_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_command_structure_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_command_structure_has__view = _init_l_lean_parser_command_structure_has__view();
 l_lean_parser_command_structure_parser_lean_parser_has__view = _init_l_lean_parser_command_structure_parser_lean_parser_has__view();
 l_lean_parser_command_structure_parser_lean_parser_has__tokens = _init_l_lean_parser_command_structure_parser_lean_parser_has__tokens();
 l_lean_parser_command_structure_parser___closed__1 = _init_l_lean_parser_command_structure_parser___closed__1();
 l_lean_parser_command_def__like_kind = _init_l_lean_parser_command_def__like_kind();
 l_lean_parser_command_def__like_kind_has__view_x_27 = _init_l_lean_parser_command_def__like_kind_has__view_x_27();
 l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_command_def__like_kind_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_command_def__like_kind_has__view = _init_l_lean_parser_command_def__like_kind_has__view();
 l_lean_parser_command_def__like = _init_l_lean_parser_command_def__like();
 l_lean_parser_command_def__like_has__view_x_27 = _init_l_lean_parser_command_def__like_has__view_x_27();
 l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_def__like_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_def__like_has__view = _init_l_lean_parser_command_def__like_has__view();
 l_lean_parser_command_instance = _init_l_lean_parser_command_instance();
 l_lean_parser_command_instance_has__view_x_27 = _init_l_lean_parser_command_instance_has__view_x_27();
 l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_instance_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_instance_has__view = _init_l_lean_parser_command_instance_has__view();
 l_lean_parser_command_example = _init_l_lean_parser_command_example();
 l_lean_parser_command_example_has__view_x_27 = _init_l_lean_parser_command_example_has__view_x_27();
 l_lean_parser_command_example_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_example_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_example_has__view = _init_l_lean_parser_command_example_has__view();
 l_lean_parser_command_constant__keyword = _init_l_lean_parser_command_constant__keyword();
 l_lean_parser_command_constant__keyword_has__view_x_27 = _init_l_lean_parser_command_constant__keyword_has__view_x_27();
 l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_constant__keyword_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_constant__keyword_has__view = _init_l_lean_parser_command_constant__keyword_has__view();
 l_lean_parser_command_constant = _init_l_lean_parser_command_constant();
 l_lean_parser_command_constant_has__view_x_27 = _init_l_lean_parser_command_constant_has__view_x_27();
 l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_constant_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_constant_has__view = _init_l_lean_parser_command_constant_has__view();
 l_lean_parser_command_inductive = _init_l_lean_parser_command_inductive();
 l_lean_parser_command_inductive_has__view_x_27 = _init_l_lean_parser_command_inductive_has__view_x_27();
 l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_command_inductive_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_command_inductive_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_command_inductive_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_command_inductive_has__view = _init_l_lean_parser_command_inductive_has__view();
 l_lean_parser_command_declaration_inner = _init_l_lean_parser_command_declaration_inner();
 l_lean_parser_command_declaration_inner_has__view_x_27 = _init_l_lean_parser_command_declaration_inner_has__view_x_27();
 l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_declaration_inner_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_declaration_inner_has__view = _init_l_lean_parser_command_declaration_inner_has__view();
 l_lean_parser_command_declaration = _init_l_lean_parser_command_declaration();
 l_lean_parser_command_declaration_has__view_x_27 = _init_l_lean_parser_command_declaration_has__view_x_27();
 l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_command_declaration_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_command_declaration_has__view = _init_l_lean_parser_command_declaration_has__view();
 l_lean_parser_command_declaration_parser_lean_parser_has__view = _init_l_lean_parser_command_declaration_parser_lean_parser_has__view();
 l_lean_parser_command_declaration_parser_lean_parser_has__tokens = _init_l_lean_parser_command_declaration_parser_lean_parser_has__tokens();
 l_lean_parser_command_declaration_parser___closed__1 = _init_l_lean_parser_command_declaration_parser___closed__1();
}
