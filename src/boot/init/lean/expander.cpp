// Lean compiler output
// Module: init.lean.expander
// Imports: init.lean.parser.module init.lean.expr
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
extern obj* l_lean_parser_command_reserve__mixfix;
obj* l___private_1776961947__expand__core(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
extern obj* l_lean_parser_term_subtype;
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj*, obj*, obj*);
obj* l_lean_expander_mk__simple__binder___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_command_variables;
extern obj* l_lean_parser_term_arrow_has__view;
obj* l_lean_expander_let_transform___closed__1;
obj* l_lean_expander_binding__annotation__update_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__name__ident(obj*);
obj* l_lean_expander_expand__bracketed__binder(obj*, obj*);
obj* l_lean_expander_sorry_transform___closed__1;
obj* l_lean_expander_pi_transform___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_parser_term_binder__ident_has__view;
obj* l_lean_expander_if_transform___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(uint8, obj*, obj*);
extern obj* l_lean_parser_command_constant_has__view;
obj* l_lean_expander_coe__simple__binder__binders(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_level_leading_has__view;
extern obj* l_lean_parser_command_universes;
obj* l_lean_expander_expand(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__2;
extern obj* l_lean_parser_command_reserve__notation_has__view;
obj* l_lean_expander_if_transform(obj*, obj*);
extern obj* l_lean_parser_command_declaration;
obj* l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(obj*);
obj* l_lean_expander_universes_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20___boxed(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(uint8, obj*, obj*);
obj* l_lean_expander_variables_transform(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
obj* l_lean_expander_mixfix_transform___closed__2;
extern obj* l_lean_parser_command_variable;
extern obj* l_lean_parser_term_match_has__view;
obj* l_lean_expander_mixfix_transform___closed__1;
obj* l_lean_expander_coe__binders__ext___rarg(obj*, obj*);
obj* l_id_monad___lambda__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_if_has__view;
extern obj* l_lean_parser_term_bracketed__binders;
obj* l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_expander_if_transform___closed__2;
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(obj*, obj*);
obj* l_lean_expander_coe__binders__ext(obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(obj*, obj*);
obj* l_lean_parser_syntax_flip__scopes___main(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(obj*, obj*, obj*);
obj* l_lean_expander_error___at___private_1776961947__expand__core___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_assume_transform___closed__1;
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view;
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1(obj*);
obj* l___private_4083062675__pop__stx__arg___closed__1;
extern obj* l_lean_parser_command_mixfix_has__view;
obj* l_lean_expander_intro__rule_transform(obj*, obj*);
extern obj* l_lean_parser_command_universes_has__view;
obj* l_lean_expander_expand__bracketed__binder___main___closed__6;
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(uint8, obj*, obj*, obj*);
obj* l_lean_expander_subtype_transform___closed__1;
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_expander_transform__m_monad;
obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
extern obj* l_lean_parser_command_variable_has__view;
obj* l_lean_expander_arrow_transform___closed__1;
obj* l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(obj*);
extern obj* l_lean_parser_level_leading;
obj* l_lean_expander_mk__notation__transformer___lambda__1(obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__3;
obj* l_lean_expander_builtin__transformers;
obj* l_lean_expander_mk__simple__binder___closed__4;
obj* l_lean_expander_if_transform___closed__3;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
extern obj* l_lean_parser_term_pi_has__view;
extern obj* l_lean_parser_command_universe_has__view;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj*);
extern obj* l_lean_parser_ident__univs;
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_let_transform___spec__1(obj*);
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2(obj*);
extern obj* l_lean_parser_term_sorry;
obj* l_lean_expander_reserve__mixfix_transform___closed__1;
extern obj* l_lean_parser_command_intro__rule_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj*, obj*);
obj* l_lean_expander_bracketed__binders_transform(obj*, obj*);
obj* l_except__t_monad__except___rarg(obj*);
extern obj* l_lean_parser_command_variables_has__view;
obj* l_lean_expander_mk__simple__binder___closed__7;
obj* l_lean_expander_binding__annotation__update_parser___closed__1;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(obj*, obj*);
extern obj* l_lean_parser_term_binders_has__view;
obj* l___private_1776961947__expand__core___main(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_reserve__mixfix_has__view;
obj* l_lean_expander_mixfix__to__notation__spec___closed__2;
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_id_bind(obj*, obj*);
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2(obj*);
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
obj* l_lean_parser_syntax_get__pos(obj*);
obj* l_lean_expander_sorry_transform(obj*, obj*);
obj* l_lean_expander_arrow_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj*, obj*);
obj* l___private_1776961947__expand__core___main___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__3;
obj* l_list_map___main___at_lean_expander_paren_transform___spec__1(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__ident__binder__id(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view_x_27;
obj* l_lean_expander_coe__binder__bracketed__binder___closed__2;
obj* l_lean_expander_glob__id(obj*);
obj* l_lean_expander_mk__simple__binder(obj*, uint8, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_expander_error___at___private_1776961947__expand__core___main___spec__1(obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__5;
obj* l_lean_expander_mk__scope(obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__6;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(uint8, obj*, obj*);
extern obj* l_lean_parser_term_bracketed__binders_has__view;
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2(obj*, obj*, obj*);
obj* l_lean_expander_lambda_transform___closed__1;
extern obj* l_lean_parser_term_pi;
extern obj* l_lean_parser_term_paren_has__view;
extern obj* l_lean_parser_term__parser__m_lean_parser_monad__parsec;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
obj* l_id(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(uint8, obj*, obj*);
obj* l_lean_expander_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_binding__annotation__update;
extern obj* l_lean_parser_term__parser__m_monad;
extern obj* l_lean_parser_term_let_has__view;
obj* l_lean_expander_transform__m_monad__reader;
obj* l_lean_expander_mk__simple__binder___closed__2;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_pi_transform(obj*, obj*);
obj* l_lean_expander_transformer;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___main___at___private_1776961947__expand__core___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__1;
obj* l_lean_expander_subtype_transform(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2(obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mixfix_transform___closed__4;
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1;
obj* l_lean_expander_lambda_transform(obj*, obj*);
obj* l_lean_expander_declaration_transform(obj*, obj*);
obj* l_lean_expander_arrow_transform___closed__2;
obj* l_lean_expander_no__expansion(obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__2;
obj* l_lean_expander_get__opt__type___main(obj*);
obj* l_lean_expander_binder__ident__to__ident(obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_expander_binder__ident__to__ident___main(obj*);
extern obj* l_lean_parser_term_lambda_has__view;
obj* l_lean_expander_declaration_transform___closed__3;
obj* l_except__t_monad___rarg(obj*);
extern obj* l_lean_parser_term_app_has__view;
obj* l_lean_expander_expander__config_has__lift(obj*);
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj*, obj*);
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(obj*, obj*);
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(obj*);
obj* l_id_monad___lambda__3(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univs_has__view;
obj* l_lean_expander_lambda_transform___lambda__1(obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_expander_mk__simple__binder___closed__6;
obj* l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(obj*);
extern obj* l_lean_parser_term_assume_has__view;
obj* l_list_mmap___main___at___private_1776961947__expand__core___main___spec__5(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_intro__rule;
obj* l___private_4083062675__pop__stx__arg(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(obj*);
obj* l_lean_expander_binder__ident__to__ident___main___closed__1;
obj* l_lean_expander_transform__m_monad__except;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(uint8, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__3;
extern obj* l_lean_parser_term_paren;
extern obj* l_lean_parser_term_hole_has__view;
obj* l_lean_expander_error(obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
obj* l_lean_expander_coe__binder__bracketed__binder___closed__1;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(obj*, obj*);
obj* l_lean_expander_declaration_transform___closed__1;
obj* l_rbmap_find___main___at___private_1776961947__expand__core___main___spec__2(obj*, obj*);
obj* l_lean_expander_coe__binders__ext__binders(obj*);
obj* l_lean_expander_mixfix_transform(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__7;
obj* l_lean_expander_paren_transform___closed__1;
obj* l_lean_expander_coe__ident__ident__univs(obj*);
obj* l_lean_expander_paren_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_expander_transformer__config__coe__frontend__config(obj*);
obj* l_lean_expander_expand__bracketed__binder___main(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1(obj*);
obj* l_string_trim(obj*);
obj* l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_expander_variable_transform___closed__1;
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(obj*, obj*);
obj* l_lean_expander_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_transform__m;
extern obj* l_lean_parser_command_constant;
obj* l_lean_expander_paren_transform___closed__2;
extern obj* l_lean_parser_term_if;
extern obj* l_lean_parser_term_assume;
obj* l_lean_expander_mk__notation__transformer(obj*, obj*, obj*);
obj* l_lean_expander_mixfix__to__notation__spec___closed__6;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(uint8, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
obj* l_lean_expander_mixfix_transform___closed__5;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22___boxed(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
extern obj* l_lean_parser_command_declaration_has__view;
obj* l_lean_expander_assume_transform(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(obj*, obj*);
obj* l_list_map___main___at_lean_expander_constant_transform___spec__1(obj*);
obj* l_lean_expander_mk__simple__binder___closed__1;
extern obj* l_lean_parser_command_notation__spec_precedence_has__view;
obj* l_lean_expander_variable_transform(obj*, obj*);
obj* l_lean_expander_expand__bracketed__binder___main___closed__5;
obj* l_lean_expander_expand__binders(obj*, obj*, obj*, obj*);
obj* l_lean_expander_mk__simple__binder___closed__5;
obj* l_lean_expander_expander__state_new;
extern obj* l_lean_parser_term_anonymous__constructor_has__view;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_term_subtype_has__view;
extern obj* l_lean_parser_term_binder__default_has__view;
extern obj* l_lean_parser_command_mixfix;
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_lambda;
extern obj* l_lean_parser_term_arrow;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_expander_get__opt__type(obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_id_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_expander_reserve__mixfix_transform(obj*, obj*);
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
obj* l_lean_expander_level_leading_transform(obj*, obj*);
obj* l_lean_expander_binding__annotation__update_parser_lean_parser_has__view;
obj* l_list_map___main___at___private_1776961947__expand__core___main___spec__4(obj*, obj*);
obj* l_lean_expander_expander__m;
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_expander_get__opt__type___main___closed__1;
obj* l_lean_expander_constant_transform___closed__1;
obj* l_lean_expander_mixfix__to__notation__spec___closed__4;
obj* l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_coe__binder__bracketed__binder(obj*);
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_expander_no__expansion___closed__1;
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8, obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
extern obj* l_lean_parser_term__parser__m_monad__except;
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1(obj*);
obj* l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_expander_mk__simple__binder___closed__3;
obj* l_lean_expander_let_transform(obj*, obj*);
extern obj* l_lean_parser_term_let;
obj* l_lean_expander_expand__bracketed__binder___main___closed__7;
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(obj*, obj*);
obj* l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1(obj*);
extern obj* l_lean_parser_command_notation_has__view;
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_expander_constant_transform(obj*, obj*);
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj*, obj*, obj*);
extern obj* l_lean_parser_term__parser__m_alternative;
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_expander_transformer__config__coe__frontend__config(obj* x_0) {
_start:
{
return x_0;
}
}
obj* _init_l_lean_expander_transform__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad__except___rarg(x_9);
x_11 = l_reader__t_monad__except___rarg(x_10);
return x_11;
}
}
obj* _init_l_lean_expander_transform__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad___rarg(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
}
obj* _init_l_lean_expander_transform__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_except__t_monad___rarg(x_9);
x_11 = l_reader__t_monad___rarg(x_10);
return x_11;
}
}
obj* _init_l_lean_expander_transform__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_transformer() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_no__expansion___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_expander_no__expansion(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* l_lean_expander_error___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_11, 0, x_3);
lean::closure_set(x_11, 1, x_2);
lean::closure_set(x_11, 2, x_5);
lean::closure_set(x_11, 3, x_6);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_1, x_11);
return x_12;
}
}
obj* l_lean_expander_error___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_1(x_1, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l_lean_parser_syntax_get__pos(x_2);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_option_get__or__else___main___rarg(x_14, x_15);
x_17 = l_lean_file__map_to__position(x_11, x_16);
x_18 = lean::box(0);
x_19 = 2;
x_20 = l_string_join___closed__1;
lean::inc(x_20);
x_22 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_22, 2, x_18);
lean::cnstr_set(x_22, 3, x_20);
lean::cnstr_set(x_22, 4, x_3);
lean::cnstr_set_scalar(x_22, sizeof(void*)*5, x_19);
x_23 = x_22;
x_24 = lean::apply_2(x_5, lean::box(0), x_23);
return x_24;
}
}
obj* l_lean_expander_error(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___rarg), 7, 0);
return x_4;
}
}
obj* l_lean_expander_coe__name__ident(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_9; 
x_1 = lean::box(0);
x_2 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
lean::inc(x_2);
x_5 = l_lean_name_to__string__with__sep___main(x_2, x_0);
x_6 = l_lean_parser_substring_of__string(x_5);
lean::inc(x_1);
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_0);
lean::cnstr_set(x_9, 3, x_1);
lean::cnstr_set(x_9, 4, x_1);
return x_9;
}
}
obj* l_lean_expander_glob__id(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::box(0);
x_5 = l_lean_name_to__string___closed__1;
lean::inc(x_0);
lean::inc(x_5);
x_8 = l_lean_name_to__string__with__sep___main(x_5, x_0);
x_9 = l_lean_parser_substring_of__string(x_8);
lean::inc(x_4);
lean::inc(x_0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_4);
lean::inc(x_4);
lean::inc(x_4);
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_9);
lean::cnstr_set(x_15, 2, x_0);
lean::cnstr_set(x_15, 3, x_12);
lean::cnstr_set(x_15, 4, x_4);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_4);
x_17 = lean::apply_1(x_2, x_16);
return x_17;
}
}
obj* l_lean_expander_coe__ident__ident__univs(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_expander_coe__ident__binder__id(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_coe___at_lean_expander_coe__binders__ext___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___at_lean_expander_coe__binders__ext___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_list_map___main___at_lean_expander_coe__binders__ext___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_expander_coe__binders__ext___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_list_map___main___at_lean_expander_coe__binders__ext___spec__2___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_lean_expander_coe__binders__ext(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_coe__binders__ext___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_expander_coe__binders__ext__binders(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_expander_coe__simple__binder__binders(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_expander_coe__binder__bracketed__binder___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("(");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_coe__binder__bracketed__binder___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(")");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_coe__binder__bracketed__binder(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_9 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_9);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_7);
lean::cnstr_set(x_12, 2, x_9);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_3, 2);
lean::inc(x_7);
lean::dec(x_3);
x_10 = l_lean_parser_syntax_get__pos(x_0);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
x_13 = l_lean_file__map_to__position(x_7, x_12);
x_14 = lean::box(0);
x_15 = 2;
x_16 = l_string_join___closed__1;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_13);
lean::cnstr_set(x_18, 2, x_14);
lean::cnstr_set(x_18, 3, x_16);
lean::cnstr_set(x_18, 4, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*5, x_15);
x_19 = x_18;
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
obj* l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* _init_l___private_4083062675__pop__stx__arg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("mk_notation_transformer: unreachable");
return x_0;
}
}
obj* l___private_4083062675__pop__stx__arg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_7; obj* x_9; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = l___private_4083062675__pop__stx__arg___closed__1;
lean::inc(x_7);
x_9 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_5, x_7, x_0, x_1);
return x_9;
}
else
{
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 2);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 3);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_18);
lean::cnstr_set(x_23, 3, x_20);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_parser_syntax_get__pos(x_0);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_file__map_to__position(x_5, x_10);
x_12 = lean::box(0);
x_13 = 2;
x_14 = l_string_join___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_11);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set(x_16, 3, x_14);
lean::cnstr_set(x_16, 4, x_1);
lean::cnstr_set_scalar(x_16, sizeof(void*)*5, x_13);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
obj* l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_coe___at_lean_expander_mk__notation__transformer___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(obj* x_0) {
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
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_5);
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
obj* _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("mk_notation_transformer: unimplemented");
return x_0;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xce\xbb");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(",");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_19, 1);
lean::inc(x_21);
lean::dec(x_19);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_29; 
lean::dec(x_21);
x_25 = l___private_4083062675__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_25);
lean::inc(x_0);
x_29 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_25, x_2, x_3);
if (lean::obj_tag(x_29) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_29, 0);
lean::inc(x_35);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_37 = x_29;
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
return x_38;
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_15 = x_39;
goto lbl_16;
}
}
else
{
obj* x_45; 
lean::dec(x_14);
lean::dec(x_21);
lean::inc(x_3);
x_45 = l___private_4083062675__pop__stx__arg(x_2, x_3);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_3);
lean::dec(x_0);
x_50 = lean::cnstr_get(x_45, 0);
lean::inc(x_50);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 x_52 = x_45;
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_45, 0);
lean::inc(x_54);
lean::dec(x_45);
x_17 = x_54;
goto lbl_18;
}
}
lbl_16:
{
obj* x_57; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_15, 1);
lean::inc(x_57);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_59 = x_15;
}
x_60 = lean::cnstr_get(x_10, 1);
lean::inc(x_60);
lean::dec(x_10);
if (lean::obj_tag(x_60) == 0)
{
lean::dec(x_14);
lean::dec(x_60);
lean::dec(x_59);
x_1 = x_12;
x_2 = x_57;
goto _start;
}
else
{
obj* x_67; obj* x_69; 
x_67 = lean::cnstr_get(x_60, 0);
lean::inc(x_67);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_69 = x_60;
}
switch (lean::obj_tag(x_67)) {
case 0:
{
obj* x_73; 
lean::dec(x_59);
lean::dec(x_67);
lean::inc(x_3);
x_73 = l___private_4083062675__pop__stx__arg(x_57, x_3);
if (lean::obj_tag(x_73) == 0)
{
obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_69);
x_79 = lean::cnstr_get(x_73, 0);
lean::inc(x_79);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_81 = x_73;
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_88; obj* x_91; obj* x_93; obj* x_95; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_83 = lean::cnstr_get(x_73, 0);
lean::inc(x_83);
lean::dec(x_73);
x_86 = lean::cnstr_get(x_83, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 1);
lean::inc(x_88);
lean::dec(x_83);
x_91 = lean::cnstr_get(x_88, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_88, 2);
lean::inc(x_95);
lean::dec(x_88);
x_98 = l_lean_parser_term_binder__ident_has__view;
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::apply_1(x_99, x_86);
x_102 = lean::box(0);
lean::inc(x_102);
if (lean::is_scalar(x_14)) {
 x_104 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_104 = x_14;
}
lean::cnstr_set(x_104, 0, x_101);
lean::cnstr_set(x_104, 1, x_102);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_102);
x_106 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_106, 0, x_105);
if (lean::is_scalar(x_69)) {
 x_107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_107 = x_69;
}
lean::cnstr_set(x_107, 0, x_106);
x_108 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_108, 0, x_91);
lean::cnstr_set(x_108, 1, x_93);
lean::cnstr_set(x_108, 2, x_95);
lean::cnstr_set(x_108, 3, x_107);
x_1 = x_12;
x_2 = x_108;
goto _start;
}
}
case 1:
{
obj* x_114; 
lean::dec(x_14);
lean::dec(x_59);
lean::dec(x_67);
lean::inc(x_3);
x_114 = l___private_4083062675__pop__stx__arg(x_57, x_3);
if (lean::obj_tag(x_114) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_69);
x_119 = lean::cnstr_get(x_114, 0);
lean::inc(x_119);
if (lean::is_shared(x_114)) {
 lean::dec(x_114);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_114, 0);
 x_121 = x_114;
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
return x_122;
}
else
{
obj* x_123; obj* x_126; obj* x_128; obj* x_131; obj* x_133; obj* x_135; obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_143; 
x_123 = lean::cnstr_get(x_114, 0);
lean::inc(x_123);
lean::dec(x_114);
x_126 = lean::cnstr_get(x_123, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_123, 1);
lean::inc(x_128);
lean::dec(x_123);
x_131 = lean::cnstr_get(x_128, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_128, 2);
lean::inc(x_135);
lean::dec(x_128);
x_138 = l_lean_parser_term_binders_has__view;
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::apply_1(x_139, x_126);
if (lean::is_scalar(x_69)) {
 x_142 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_142 = x_69;
}
lean::cnstr_set(x_142, 0, x_141);
x_143 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_143, 0, x_131);
lean::cnstr_set(x_143, 1, x_133);
lean::cnstr_set(x_143, 2, x_135);
lean::cnstr_set(x_143, 3, x_142);
x_1 = x_12;
x_2 = x_143;
goto _start;
}
}
default:
{
obj* x_146; obj* x_149; obj* x_151; 
lean::dec(x_69);
x_146 = lean::cnstr_get(x_67, 0);
lean::inc(x_146);
lean::dec(x_67);
x_149 = lean::cnstr_get(x_146, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_146, 1);
lean::inc(x_151);
lean::dec(x_146);
if (lean::obj_tag(x_151) == 0)
{
obj* x_156; 
lean::dec(x_151);
lean::inc(x_3);
x_156 = l___private_4083062675__pop__stx__arg(x_57, x_3);
if (lean::obj_tag(x_156) == 0)
{
obj* x_163; obj* x_165; obj* x_166; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_59);
lean::dec(x_149);
x_163 = lean::cnstr_get(x_156, 0);
lean::inc(x_163);
if (lean::is_shared(x_156)) {
 lean::dec(x_156);
 x_165 = lean::box(0);
} else {
 lean::cnstr_release(x_156, 0);
 x_165 = x_156;
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
return x_166;
}
else
{
obj* x_167; obj* x_170; obj* x_172; obj* x_175; obj* x_177; obj* x_179; obj* x_180; obj* x_182; obj* x_183; obj* x_186; 
x_167 = lean::cnstr_get(x_156, 0);
lean::inc(x_167);
lean::dec(x_156);
x_170 = lean::cnstr_get(x_167, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_167, 1);
lean::inc(x_172);
lean::dec(x_167);
x_175 = lean::cnstr_get(x_172, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_172, 1);
lean::inc(x_177);
if (lean::is_scalar(x_59)) {
 x_179 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_179 = x_59;
}
lean::cnstr_set(x_179, 0, x_149);
lean::cnstr_set(x_179, 1, x_170);
x_180 = lean::cnstr_get(x_172, 2);
lean::inc(x_180);
if (lean::is_scalar(x_14)) {
 x_182 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_182 = x_14;
}
lean::cnstr_set(x_182, 0, x_179);
lean::cnstr_set(x_182, 1, x_180);
x_183 = lean::cnstr_get(x_172, 3);
lean::inc(x_183);
lean::dec(x_172);
x_186 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_186, 0, x_175);
lean::cnstr_set(x_186, 1, x_177);
lean::cnstr_set(x_186, 2, x_182);
lean::cnstr_set(x_186, 3, x_183);
x_1 = x_12;
x_2 = x_186;
goto _start;
}
}
else
{
obj* x_188; obj* x_191; 
x_188 = lean::cnstr_get(x_151, 0);
lean::inc(x_188);
lean::dec(x_151);
x_191 = lean::cnstr_get(x_188, 1);
lean::inc(x_191);
lean::dec(x_188);
switch (lean::obj_tag(x_191)) {
case 0:
{
obj* x_196; 
lean::dec(x_191);
lean::inc(x_3);
x_196 = l___private_4083062675__pop__stx__arg(x_57, x_3);
if (lean::obj_tag(x_196) == 0)
{
obj* x_203; obj* x_205; obj* x_206; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_59);
lean::dec(x_149);
x_203 = lean::cnstr_get(x_196, 0);
lean::inc(x_203);
if (lean::is_shared(x_196)) {
 lean::dec(x_196);
 x_205 = lean::box(0);
} else {
 lean::cnstr_release(x_196, 0);
 x_205 = x_196;
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_203);
return x_206;
}
else
{
obj* x_207; obj* x_210; obj* x_212; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_223; obj* x_226; 
x_207 = lean::cnstr_get(x_196, 0);
lean::inc(x_207);
lean::dec(x_196);
x_210 = lean::cnstr_get(x_207, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_207, 1);
lean::inc(x_212);
lean::dec(x_207);
x_215 = lean::cnstr_get(x_212, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 1);
lean::inc(x_217);
if (lean::is_scalar(x_59)) {
 x_219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_219 = x_59;
}
lean::cnstr_set(x_219, 0, x_149);
lean::cnstr_set(x_219, 1, x_210);
x_220 = lean::cnstr_get(x_212, 2);
lean::inc(x_220);
if (lean::is_scalar(x_14)) {
 x_222 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_222 = x_14;
}
lean::cnstr_set(x_222, 0, x_219);
lean::cnstr_set(x_222, 1, x_220);
x_223 = lean::cnstr_get(x_212, 3);
lean::inc(x_223);
lean::dec(x_212);
x_226 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_226, 0, x_215);
lean::cnstr_set(x_226, 1, x_217);
lean::cnstr_set(x_226, 2, x_222);
lean::cnstr_set(x_226, 3, x_223);
x_1 = x_12;
x_2 = x_226;
goto _start;
}
}
case 1:
{
obj* x_232; obj* x_236; 
lean::dec(x_191);
lean::dec(x_14);
lean::dec(x_59);
lean::dec(x_149);
x_232 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_232);
lean::inc(x_0);
x_236 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_232, x_57, x_3);
if (lean::obj_tag(x_236) == 0)
{
obj* x_240; obj* x_242; obj* x_243; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_240 = lean::cnstr_get(x_236, 0);
lean::inc(x_240);
if (lean::is_shared(x_236)) {
 lean::dec(x_236);
 x_242 = lean::box(0);
} else {
 lean::cnstr_release(x_236, 0);
 x_242 = x_236;
}
if (lean::is_scalar(x_242)) {
 x_243 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_243 = x_242;
}
lean::cnstr_set(x_243, 0, x_240);
return x_243;
}
else
{
obj* x_244; obj* x_247; 
x_244 = lean::cnstr_get(x_236, 0);
lean::inc(x_244);
lean::dec(x_236);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
lean::dec(x_244);
x_1 = x_12;
x_2 = x_247;
goto _start;
}
}
case 2:
{
obj* x_251; obj* x_255; 
x_251 = lean::cnstr_get(x_191, 0);
lean::inc(x_251);
lean::dec(x_191);
lean::inc(x_3);
x_255 = l___private_4083062675__pop__stx__arg(x_57, x_3);
if (lean::obj_tag(x_255) == 0)
{
obj* x_263; obj* x_265; obj* x_266; 
lean::dec(x_251);
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_59);
lean::dec(x_149);
x_263 = lean::cnstr_get(x_255, 0);
lean::inc(x_263);
if (lean::is_shared(x_255)) {
 lean::dec(x_255);
 x_265 = lean::box(0);
} else {
 lean::cnstr_release(x_255, 0);
 x_265 = x_255;
}
if (lean::is_scalar(x_265)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_265;
}
lean::cnstr_set(x_266, 0, x_263);
return x_266;
}
else
{
obj* x_267; obj* x_269; obj* x_270; obj* x_272; obj* x_275; obj* x_277; obj* x_279; obj* x_281; 
x_267 = lean::cnstr_get(x_255, 0);
lean::inc(x_267);
if (lean::is_shared(x_255)) {
 lean::dec(x_255);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_255, 0);
 x_269 = x_255;
}
x_270 = lean::cnstr_get(x_267, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_267, 1);
lean::inc(x_272);
lean::dec(x_267);
x_275 = lean::cnstr_get(x_272, 0);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_272, 1);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_272, 2);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_272, 3);
lean::inc(x_281);
if (lean::obj_tag(x_281) == 0)
{
obj* x_292; obj* x_296; 
lean::dec(x_275);
lean::dec(x_277);
lean::dec(x_279);
lean::dec(x_281);
lean::dec(x_270);
lean::dec(x_251);
lean::dec(x_14);
lean::dec(x_59);
lean::dec(x_149);
x_292 = l___private_4083062675__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_292);
lean::inc(x_0);
x_296 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_292, x_272, x_3);
if (lean::obj_tag(x_296) == 0)
{
obj* x_300; obj* x_303; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_300 = lean::cnstr_get(x_296, 0);
lean::inc(x_300);
lean::dec(x_296);
if (lean::is_scalar(x_269)) {
 x_303 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_303 = x_269;
 lean::cnstr_set_tag(x_269, 0);
}
lean::cnstr_set(x_303, 0, x_300);
return x_303;
}
else
{
obj* x_305; obj* x_308; 
lean::dec(x_269);
x_305 = lean::cnstr_get(x_296, 0);
lean::inc(x_305);
lean::dec(x_296);
x_308 = lean::cnstr_get(x_305, 1);
lean::inc(x_308);
lean::dec(x_305);
x_1 = x_12;
x_2 = x_308;
goto _start;
}
}
else
{
obj* x_314; obj* x_316; obj* x_317; obj* x_319; obj* x_320; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_330; obj* x_331; obj* x_334; obj* x_336; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_344; obj* x_345; obj* x_346; obj* x_347; obj* x_348; 
lean::dec(x_269);
lean::dec(x_272);
x_314 = lean::cnstr_get(x_281, 0);
lean::inc(x_314);
x_316 = l_lean_parser_term_lambda_has__view;
x_317 = lean::cnstr_get(x_316, 1);
lean::inc(x_317);
x_319 = lean::box(0);
x_320 = lean::cnstr_get(x_251, 3);
lean::inc(x_320);
lean::inc(x_319);
if (lean::is_scalar(x_14)) {
 x_323 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_323 = x_14;
}
lean::cnstr_set(x_323, 0, x_320);
lean::cnstr_set(x_323, 1, x_319);
x_324 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_323);
x_325 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_325, 0, x_324);
lean::cnstr_set(x_325, 1, x_319);
x_326 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_326, 0, x_325);
x_327 = lean::cnstr_get(x_251, 5);
lean::inc(x_327);
lean::dec(x_251);
x_330 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_331 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_331);
lean::inc(x_330);
x_334 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_334, 0, x_330);
lean::cnstr_set(x_334, 1, x_326);
lean::cnstr_set(x_334, 2, x_331);
lean::cnstr_set(x_334, 3, x_327);
lean::inc(x_317);
x_336 = lean::apply_1(x_317, x_334);
lean::inc(x_331);
lean::inc(x_330);
x_339 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_339, 0, x_330);
lean::cnstr_set(x_339, 1, x_314);
lean::cnstr_set(x_339, 2, x_331);
lean::cnstr_set(x_339, 3, x_270);
x_340 = lean::apply_1(x_317, x_339);
x_341 = l_lean_parser_term_app_has__view;
x_342 = lean::cnstr_get(x_341, 1);
lean::inc(x_342);
x_344 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_344, 0, x_336);
lean::cnstr_set(x_344, 1, x_340);
x_345 = lean::apply_1(x_342, x_344);
if (lean::is_scalar(x_59)) {
 x_346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_346 = x_59;
}
lean::cnstr_set(x_346, 0, x_149);
lean::cnstr_set(x_346, 1, x_345);
x_347 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_347, 0, x_346);
lean::cnstr_set(x_347, 1, x_279);
x_348 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_348, 0, x_275);
lean::cnstr_set(x_348, 1, x_277);
lean::cnstr_set(x_348, 2, x_347);
lean::cnstr_set(x_348, 3, x_281);
x_1 = x_12;
x_2 = x_348;
goto _start;
}
}
}
default:
{
obj* x_354; obj* x_358; 
lean::dec(x_191);
lean::dec(x_14);
lean::dec(x_59);
lean::dec(x_149);
x_354 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_354);
lean::inc(x_0);
x_358 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_354, x_57, x_3);
if (lean::obj_tag(x_358) == 0)
{
obj* x_362; obj* x_364; obj* x_365; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_362 = lean::cnstr_get(x_358, 0);
lean::inc(x_362);
if (lean::is_shared(x_358)) {
 lean::dec(x_358);
 x_364 = lean::box(0);
} else {
 lean::cnstr_release(x_358, 0);
 x_364 = x_358;
}
if (lean::is_scalar(x_364)) {
 x_365 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_365 = x_364;
}
lean::cnstr_set(x_365, 0, x_362);
return x_365;
}
else
{
obj* x_366; obj* x_369; 
x_366 = lean::cnstr_get(x_358, 0);
lean::inc(x_366);
lean::dec(x_358);
x_369 = lean::cnstr_get(x_366, 1);
lean::inc(x_369);
lean::dec(x_366);
x_1 = x_12;
x_2 = x_369;
goto _start;
}
}
}
}
}
}
}
}
lbl_18:
{
obj* x_373; obj* x_375; obj* x_376; 
x_373 = lean::cnstr_get(x_17, 1);
lean::inc(x_373);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_375 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 x_375 = x_17;
}
x_376 = lean::cnstr_get(x_10, 1);
lean::inc(x_376);
lean::dec(x_10);
if (lean::obj_tag(x_376) == 0)
{
lean::dec(x_375);
lean::dec(x_376);
x_1 = x_12;
x_2 = x_373;
goto _start;
}
else
{
obj* x_382; obj* x_384; 
x_382 = lean::cnstr_get(x_376, 0);
lean::inc(x_382);
if (lean::is_shared(x_376)) {
 lean::dec(x_376);
 x_384 = lean::box(0);
} else {
 lean::cnstr_release(x_376, 0);
 x_384 = x_376;
}
switch (lean::obj_tag(x_382)) {
case 0:
{
obj* x_388; 
lean::dec(x_375);
lean::dec(x_382);
lean::inc(x_3);
x_388 = l___private_4083062675__pop__stx__arg(x_373, x_3);
if (lean::obj_tag(x_388) == 0)
{
obj* x_393; obj* x_395; obj* x_396; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_384);
x_393 = lean::cnstr_get(x_388, 0);
lean::inc(x_393);
if (lean::is_shared(x_388)) {
 lean::dec(x_388);
 x_395 = lean::box(0);
} else {
 lean::cnstr_release(x_388, 0);
 x_395 = x_388;
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_393);
return x_396;
}
else
{
obj* x_397; obj* x_400; obj* x_402; obj* x_405; obj* x_407; obj* x_409; obj* x_412; obj* x_413; obj* x_415; obj* x_416; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
x_397 = lean::cnstr_get(x_388, 0);
lean::inc(x_397);
lean::dec(x_388);
x_400 = lean::cnstr_get(x_397, 0);
lean::inc(x_400);
x_402 = lean::cnstr_get(x_397, 1);
lean::inc(x_402);
lean::dec(x_397);
x_405 = lean::cnstr_get(x_402, 0);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_402, 1);
lean::inc(x_407);
x_409 = lean::cnstr_get(x_402, 2);
lean::inc(x_409);
lean::dec(x_402);
x_412 = l_lean_parser_term_binder__ident_has__view;
x_413 = lean::cnstr_get(x_412, 0);
lean::inc(x_413);
x_415 = lean::apply_1(x_413, x_400);
x_416 = lean::box(0);
lean::inc(x_416);
x_418 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_418, 0, x_415);
lean::cnstr_set(x_418, 1, x_416);
x_419 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_419, 0, x_418);
lean::cnstr_set(x_419, 1, x_416);
x_420 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_420, 0, x_419);
if (lean::is_scalar(x_384)) {
 x_421 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_421 = x_384;
}
lean::cnstr_set(x_421, 0, x_420);
x_422 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_422, 0, x_405);
lean::cnstr_set(x_422, 1, x_407);
lean::cnstr_set(x_422, 2, x_409);
lean::cnstr_set(x_422, 3, x_421);
x_1 = x_12;
x_2 = x_422;
goto _start;
}
}
case 1:
{
obj* x_427; 
lean::dec(x_375);
lean::dec(x_382);
lean::inc(x_3);
x_427 = l___private_4083062675__pop__stx__arg(x_373, x_3);
if (lean::obj_tag(x_427) == 0)
{
obj* x_432; obj* x_434; obj* x_435; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_384);
x_432 = lean::cnstr_get(x_427, 0);
lean::inc(x_432);
if (lean::is_shared(x_427)) {
 lean::dec(x_427);
 x_434 = lean::box(0);
} else {
 lean::cnstr_release(x_427, 0);
 x_434 = x_427;
}
if (lean::is_scalar(x_434)) {
 x_435 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_435 = x_434;
}
lean::cnstr_set(x_435, 0, x_432);
return x_435;
}
else
{
obj* x_436; obj* x_439; obj* x_441; obj* x_444; obj* x_446; obj* x_448; obj* x_451; obj* x_452; obj* x_454; obj* x_455; obj* x_456; 
x_436 = lean::cnstr_get(x_427, 0);
lean::inc(x_436);
lean::dec(x_427);
x_439 = lean::cnstr_get(x_436, 0);
lean::inc(x_439);
x_441 = lean::cnstr_get(x_436, 1);
lean::inc(x_441);
lean::dec(x_436);
x_444 = lean::cnstr_get(x_441, 0);
lean::inc(x_444);
x_446 = lean::cnstr_get(x_441, 1);
lean::inc(x_446);
x_448 = lean::cnstr_get(x_441, 2);
lean::inc(x_448);
lean::dec(x_441);
x_451 = l_lean_parser_term_binders_has__view;
x_452 = lean::cnstr_get(x_451, 0);
lean::inc(x_452);
x_454 = lean::apply_1(x_452, x_439);
if (lean::is_scalar(x_384)) {
 x_455 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_455 = x_384;
}
lean::cnstr_set(x_455, 0, x_454);
x_456 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_456, 0, x_444);
lean::cnstr_set(x_456, 1, x_446);
lean::cnstr_set(x_456, 2, x_448);
lean::cnstr_set(x_456, 3, x_455);
x_1 = x_12;
x_2 = x_456;
goto _start;
}
}
default:
{
obj* x_459; obj* x_462; obj* x_464; 
lean::dec(x_384);
x_459 = lean::cnstr_get(x_382, 0);
lean::inc(x_459);
lean::dec(x_382);
x_462 = lean::cnstr_get(x_459, 0);
lean::inc(x_462);
x_464 = lean::cnstr_get(x_459, 1);
lean::inc(x_464);
lean::dec(x_459);
if (lean::obj_tag(x_464) == 0)
{
obj* x_469; 
lean::dec(x_464);
lean::inc(x_3);
x_469 = l___private_4083062675__pop__stx__arg(x_373, x_3);
if (lean::obj_tag(x_469) == 0)
{
obj* x_475; obj* x_477; obj* x_478; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_375);
lean::dec(x_462);
x_475 = lean::cnstr_get(x_469, 0);
lean::inc(x_475);
if (lean::is_shared(x_469)) {
 lean::dec(x_469);
 x_477 = lean::box(0);
} else {
 lean::cnstr_release(x_469, 0);
 x_477 = x_469;
}
if (lean::is_scalar(x_477)) {
 x_478 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_478 = x_477;
}
lean::cnstr_set(x_478, 0, x_475);
return x_478;
}
else
{
obj* x_479; obj* x_482; obj* x_484; obj* x_487; obj* x_489; obj* x_491; obj* x_492; obj* x_494; obj* x_495; obj* x_498; 
x_479 = lean::cnstr_get(x_469, 0);
lean::inc(x_479);
lean::dec(x_469);
x_482 = lean::cnstr_get(x_479, 0);
lean::inc(x_482);
x_484 = lean::cnstr_get(x_479, 1);
lean::inc(x_484);
lean::dec(x_479);
x_487 = lean::cnstr_get(x_484, 0);
lean::inc(x_487);
x_489 = lean::cnstr_get(x_484, 1);
lean::inc(x_489);
if (lean::is_scalar(x_375)) {
 x_491 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_491 = x_375;
}
lean::cnstr_set(x_491, 0, x_462);
lean::cnstr_set(x_491, 1, x_482);
x_492 = lean::cnstr_get(x_484, 2);
lean::inc(x_492);
x_494 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_494, 0, x_491);
lean::cnstr_set(x_494, 1, x_492);
x_495 = lean::cnstr_get(x_484, 3);
lean::inc(x_495);
lean::dec(x_484);
x_498 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_498, 0, x_487);
lean::cnstr_set(x_498, 1, x_489);
lean::cnstr_set(x_498, 2, x_494);
lean::cnstr_set(x_498, 3, x_495);
x_1 = x_12;
x_2 = x_498;
goto _start;
}
}
else
{
obj* x_500; obj* x_503; 
x_500 = lean::cnstr_get(x_464, 0);
lean::inc(x_500);
lean::dec(x_464);
x_503 = lean::cnstr_get(x_500, 1);
lean::inc(x_503);
lean::dec(x_500);
switch (lean::obj_tag(x_503)) {
case 0:
{
obj* x_508; 
lean::dec(x_503);
lean::inc(x_3);
x_508 = l___private_4083062675__pop__stx__arg(x_373, x_3);
if (lean::obj_tag(x_508) == 0)
{
obj* x_514; obj* x_516; obj* x_517; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_375);
lean::dec(x_462);
x_514 = lean::cnstr_get(x_508, 0);
lean::inc(x_514);
if (lean::is_shared(x_508)) {
 lean::dec(x_508);
 x_516 = lean::box(0);
} else {
 lean::cnstr_release(x_508, 0);
 x_516 = x_508;
}
if (lean::is_scalar(x_516)) {
 x_517 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_517 = x_516;
}
lean::cnstr_set(x_517, 0, x_514);
return x_517;
}
else
{
obj* x_518; obj* x_521; obj* x_523; obj* x_526; obj* x_528; obj* x_530; obj* x_531; obj* x_533; obj* x_534; obj* x_537; 
x_518 = lean::cnstr_get(x_508, 0);
lean::inc(x_518);
lean::dec(x_508);
x_521 = lean::cnstr_get(x_518, 0);
lean::inc(x_521);
x_523 = lean::cnstr_get(x_518, 1);
lean::inc(x_523);
lean::dec(x_518);
x_526 = lean::cnstr_get(x_523, 0);
lean::inc(x_526);
x_528 = lean::cnstr_get(x_523, 1);
lean::inc(x_528);
if (lean::is_scalar(x_375)) {
 x_530 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_530 = x_375;
}
lean::cnstr_set(x_530, 0, x_462);
lean::cnstr_set(x_530, 1, x_521);
x_531 = lean::cnstr_get(x_523, 2);
lean::inc(x_531);
x_533 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_533, 0, x_530);
lean::cnstr_set(x_533, 1, x_531);
x_534 = lean::cnstr_get(x_523, 3);
lean::inc(x_534);
lean::dec(x_523);
x_537 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_537, 0, x_526);
lean::cnstr_set(x_537, 1, x_528);
lean::cnstr_set(x_537, 2, x_533);
lean::cnstr_set(x_537, 3, x_534);
x_1 = x_12;
x_2 = x_537;
goto _start;
}
}
case 1:
{
obj* x_542; obj* x_546; 
lean::dec(x_375);
lean::dec(x_503);
lean::dec(x_462);
x_542 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_542);
lean::inc(x_0);
x_546 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_542, x_373, x_3);
if (lean::obj_tag(x_546) == 0)
{
obj* x_550; obj* x_552; obj* x_553; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_550 = lean::cnstr_get(x_546, 0);
lean::inc(x_550);
if (lean::is_shared(x_546)) {
 lean::dec(x_546);
 x_552 = lean::box(0);
} else {
 lean::cnstr_release(x_546, 0);
 x_552 = x_546;
}
if (lean::is_scalar(x_552)) {
 x_553 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_553 = x_552;
}
lean::cnstr_set(x_553, 0, x_550);
return x_553;
}
else
{
obj* x_554; obj* x_557; 
x_554 = lean::cnstr_get(x_546, 0);
lean::inc(x_554);
lean::dec(x_546);
x_557 = lean::cnstr_get(x_554, 1);
lean::inc(x_557);
lean::dec(x_554);
x_1 = x_12;
x_2 = x_557;
goto _start;
}
}
case 2:
{
obj* x_561; obj* x_565; 
x_561 = lean::cnstr_get(x_503, 0);
lean::inc(x_561);
lean::dec(x_503);
lean::inc(x_3);
x_565 = l___private_4083062675__pop__stx__arg(x_373, x_3);
if (lean::obj_tag(x_565) == 0)
{
obj* x_572; obj* x_574; obj* x_575; 
lean::dec(x_561);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_375);
lean::dec(x_462);
x_572 = lean::cnstr_get(x_565, 0);
lean::inc(x_572);
if (lean::is_shared(x_565)) {
 lean::dec(x_565);
 x_574 = lean::box(0);
} else {
 lean::cnstr_release(x_565, 0);
 x_574 = x_565;
}
if (lean::is_scalar(x_574)) {
 x_575 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_575 = x_574;
}
lean::cnstr_set(x_575, 0, x_572);
return x_575;
}
else
{
obj* x_576; obj* x_578; obj* x_579; obj* x_581; obj* x_584; obj* x_586; obj* x_588; obj* x_590; 
x_576 = lean::cnstr_get(x_565, 0);
lean::inc(x_576);
if (lean::is_shared(x_565)) {
 lean::dec(x_565);
 x_578 = lean::box(0);
} else {
 lean::cnstr_release(x_565, 0);
 x_578 = x_565;
}
x_579 = lean::cnstr_get(x_576, 0);
lean::inc(x_579);
x_581 = lean::cnstr_get(x_576, 1);
lean::inc(x_581);
lean::dec(x_576);
x_584 = lean::cnstr_get(x_581, 0);
lean::inc(x_584);
x_586 = lean::cnstr_get(x_581, 1);
lean::inc(x_586);
x_588 = lean::cnstr_get(x_581, 2);
lean::inc(x_588);
x_590 = lean::cnstr_get(x_581, 3);
lean::inc(x_590);
if (lean::obj_tag(x_590) == 0)
{
obj* x_600; obj* x_604; 
lean::dec(x_579);
lean::dec(x_584);
lean::dec(x_588);
lean::dec(x_590);
lean::dec(x_561);
lean::dec(x_586);
lean::dec(x_375);
lean::dec(x_462);
x_600 = l___private_4083062675__pop__stx__arg___closed__1;
lean::inc(x_3);
lean::inc(x_600);
lean::inc(x_0);
x_604 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_600, x_581, x_3);
if (lean::obj_tag(x_604) == 0)
{
obj* x_608; obj* x_611; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_608 = lean::cnstr_get(x_604, 0);
lean::inc(x_608);
lean::dec(x_604);
if (lean::is_scalar(x_578)) {
 x_611 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_611 = x_578;
 lean::cnstr_set_tag(x_578, 0);
}
lean::cnstr_set(x_611, 0, x_608);
return x_611;
}
else
{
obj* x_613; obj* x_616; 
lean::dec(x_578);
x_613 = lean::cnstr_get(x_604, 0);
lean::inc(x_613);
lean::dec(x_604);
x_616 = lean::cnstr_get(x_613, 1);
lean::inc(x_616);
lean::dec(x_613);
x_1 = x_12;
x_2 = x_616;
goto _start;
}
}
else
{
obj* x_622; obj* x_624; obj* x_625; obj* x_627; obj* x_628; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_638; obj* x_639; obj* x_642; obj* x_644; obj* x_647; obj* x_648; obj* x_649; obj* x_650; obj* x_652; obj* x_653; obj* x_654; obj* x_655; obj* x_656; 
lean::dec(x_581);
lean::dec(x_578);
x_622 = lean::cnstr_get(x_590, 0);
lean::inc(x_622);
x_624 = l_lean_parser_term_lambda_has__view;
x_625 = lean::cnstr_get(x_624, 1);
lean::inc(x_625);
x_627 = lean::box(0);
x_628 = lean::cnstr_get(x_561, 3);
lean::inc(x_628);
lean::inc(x_627);
x_631 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_631, 0, x_628);
lean::cnstr_set(x_631, 1, x_627);
x_632 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__3(x_631);
x_633 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_633, 0, x_632);
lean::cnstr_set(x_633, 1, x_627);
x_634 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_634, 0, x_633);
x_635 = lean::cnstr_get(x_561, 5);
lean::inc(x_635);
lean::dec(x_561);
x_638 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_639 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_639);
lean::inc(x_638);
x_642 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_642, 0, x_638);
lean::cnstr_set(x_642, 1, x_634);
lean::cnstr_set(x_642, 2, x_639);
lean::cnstr_set(x_642, 3, x_635);
lean::inc(x_625);
x_644 = lean::apply_1(x_625, x_642);
lean::inc(x_639);
lean::inc(x_638);
x_647 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_647, 0, x_638);
lean::cnstr_set(x_647, 1, x_622);
lean::cnstr_set(x_647, 2, x_639);
lean::cnstr_set(x_647, 3, x_579);
x_648 = lean::apply_1(x_625, x_647);
x_649 = l_lean_parser_term_app_has__view;
x_650 = lean::cnstr_get(x_649, 1);
lean::inc(x_650);
x_652 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_652, 0, x_644);
lean::cnstr_set(x_652, 1, x_648);
x_653 = lean::apply_1(x_650, x_652);
if (lean::is_scalar(x_375)) {
 x_654 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_654 = x_375;
}
lean::cnstr_set(x_654, 0, x_462);
lean::cnstr_set(x_654, 1, x_653);
x_655 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_655, 0, x_654);
lean::cnstr_set(x_655, 1, x_588);
x_656 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_656, 0, x_584);
lean::cnstr_set(x_656, 1, x_586);
lean::cnstr_set(x_656, 2, x_655);
lean::cnstr_set(x_656, 3, x_590);
x_1 = x_12;
x_2 = x_656;
goto _start;
}
}
}
default:
{
obj* x_661; obj* x_665; 
lean::dec(x_375);
lean::dec(x_503);
lean::dec(x_462);
x_661 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1;
lean::inc(x_3);
lean::inc(x_661);
lean::inc(x_0);
x_665 = l_lean_expander_error___at___private_4083062675__pop__stx__arg___spec__1___rarg(x_0, x_661, x_373, x_3);
if (lean::obj_tag(x_665) == 0)
{
obj* x_669; obj* x_671; obj* x_672; 
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_669 = lean::cnstr_get(x_665, 0);
lean::inc(x_669);
if (lean::is_shared(x_665)) {
 lean::dec(x_665);
 x_671 = lean::box(0);
} else {
 lean::cnstr_release(x_665, 0);
 x_671 = x_665;
}
if (lean::is_scalar(x_671)) {
 x_672 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_672 = x_671;
}
lean::cnstr_set(x_672, 0, x_669);
return x_672;
}
else
{
obj* x_673; obj* x_676; 
x_673 = lean::cnstr_get(x_665, 0);
lean::inc(x_673);
lean::dec(x_665);
x_676 = lean::cnstr_get(x_673, 1);
lean::inc(x_676);
lean::dec(x_673);
x_1 = x_12;
x_2 = x_676;
goto _start;
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
obj* l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
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
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_12 = x_3;
}
x_13 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_5);
x_14 = lean::cnstr_get(x_8, 2);
lean::inc(x_14);
lean::dec(x_8);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_10);
if (lean::is_scalar(x_7)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_7;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
}
}
obj* l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(obj* x_0) {
_start:
{
obj* x_1; uint8 x_4; 
x_1 = l_lean_parser_ident__univs;
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_4 == 0)
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = l_lean_parser_ident__univs_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::apply_1(x_8, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; uint8 x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::name_dec_eq(x_10, x_1);
lean::dec(x_10);
if (x_15 == 0)
{
lean::dec(x_12);
x_0 = x_7;
goto _start;
}
else
{
obj* x_21; 
lean::dec(x_7);
lean::dec(x_1);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_12);
return x_21;
}
}
}
}
obj* l_lean_expander_mk__notation__transformer(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_4);
lean::dec(x_0);
x_7 = l___private_4083062675__pop__stx__arg___closed__1;
lean::inc(x_7);
x_9 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_1, x_7, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_20; obj* x_21; obj* x_24; obj* x_26; obj* x_28; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::box(0);
lean::inc(x_16);
lean::inc(x_16);
lean::inc(x_1);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_16);
lean::cnstr_set(x_20, 3, x_16);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::dec(x_0);
x_24 = lean::cnstr_get(x_21, 2);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; 
lean::dec(x_26);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_16);
lean::cnstr_set(x_31, 1, x_20);
x_28 = x_31;
goto lbl_29;
}
else
{
obj* x_32; obj* x_36; 
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
lean::inc(x_2);
x_36 = l___private_4083062675__pop__stx__arg(x_20, x_2);
if (lean::obj_tag(x_36) == 0)
{
obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_2);
lean::dec(x_32);
x_44 = lean::cnstr_get(x_36, 0);
lean::inc(x_44);
if (lean::is_shared(x_36)) {
 lean::dec(x_36);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_36, 0);
 x_46 = x_36;
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_67; obj* x_68; 
x_48 = lean::cnstr_get(x_36, 0);
lean::inc(x_48);
lean::dec(x_36);
x_51 = lean::cnstr_get(x_48, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_55 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_55 = x_48;
}
x_56 = lean::cnstr_get(x_53, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_53, 1);
lean::inc(x_58);
if (lean::is_scalar(x_55)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_55;
}
lean::cnstr_set(x_60, 0, x_32);
lean::cnstr_set(x_60, 1, x_51);
x_61 = lean::cnstr_get(x_53, 2);
lean::inc(x_61);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
x_64 = lean::cnstr_get(x_53, 3);
lean::inc(x_64);
lean::dec(x_53);
x_67 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_67, 0, x_56);
lean::cnstr_set(x_67, 1, x_58);
lean::cnstr_set(x_67, 2, x_63);
lean::cnstr_set(x_67, 3, x_64);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_16);
lean::cnstr_set(x_68, 1, x_67);
x_28 = x_68;
goto lbl_29;
}
}
lbl_29:
{
obj* x_69; obj* x_72; obj* x_75; 
x_69 = lean::cnstr_get(x_28, 1);
lean::inc(x_69);
lean::dec(x_28);
x_72 = lean::cnstr_get(x_24, 1);
lean::inc(x_72);
lean::dec(x_24);
x_75 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4(x_1, x_72, x_69, x_2);
if (lean::obj_tag(x_75) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_12);
lean::dec(x_21);
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_80 = x_75;
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; obj* x_88; obj* x_91; obj* x_92; obj* x_93; obj* x_96; obj* x_97; obj* x_98; 
x_82 = lean::cnstr_get(x_75, 0);
lean::inc(x_82);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_84 = x_75;
}
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_88 = lean::cnstr_get(x_85, 2);
lean::inc(x_88);
lean::dec(x_85);
x_91 = l_list_map___main___at_lean_expander_mk__notation__transformer___spec__5(x_88);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mk__notation__transformer___lambda__1), 2, 1);
lean::closure_set(x_92, 0, x_91);
x_93 = lean::cnstr_get(x_21, 4);
lean::inc(x_93);
lean::dec(x_21);
x_96 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_92, x_93);
if (lean::is_scalar(x_12)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_12;
}
lean::cnstr_set(x_97, 0, x_96);
if (lean::is_scalar(x_84)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_84;
}
lean::cnstr_set(x_98, 0, x_97);
return x_98;
}
}
}
}
}
obj* l_lean_expander_mk__notation__transformer___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_try__view___at_lean_expander_mk__notation__transformer___spec__6(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_11; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_18; 
lean::dec(x_11);
x_15 = lean::cnstr_get(x_9, 2);
lean::inc(x_15);
lean::dec(x_9);
x_18 = l_list_assoc___main___at_lean_expander_mk__notation__transformer___spec__7(x_0, x_15);
return x_18;
}
else
{
obj* x_22; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_0);
x_22 = lean::box(0);
return x_22;
}
}
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("b");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix__to__notation__spec___lambda__2), 1, 0);
return x_0;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix__to__notation__spec___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("b");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mixfix__to__notation__spec___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid `infixr` declaration, given precedence must greater than zero");
return x_0;
}
}
obj* l_lean_expander_mixfix__to__notation__spec(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_5);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::box(0);
x_12 = l_lean_expander_mixfix__to__notation__spec___closed__3;
lean::inc(x_12);
x_14 = l_option_map___rarg(x_12, x_5);
x_15 = l_lean_expander_mixfix__to__notation__spec___closed__4;
lean::inc(x_15);
x_17 = l_option_map___rarg(x_15, x_14);
x_18 = l_lean_expander_mixfix__to__notation__spec___closed__5;
lean::inc(x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_17);
x_21 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_22);
lean::inc(x_11);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_11);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
case 1:
{
obj* x_30; 
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::box(0);
x_7 = x_30;
goto lbl_8;
}
case 2:
{
obj* x_33; 
lean::dec(x_0);
lean::dec(x_2);
x_33 = lean::box(0);
x_7 = x_33;
goto lbl_8;
}
case 3:
{
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_37; 
lean::dec(x_5);
lean::dec(x_2);
x_37 = lean::box(0);
x_3 = x_37;
goto lbl_4;
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; uint8 x_45; 
x_38 = lean::cnstr_get(x_5, 0);
lean::inc(x_38);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_40 = x_5;
}
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = l_lean_parser_command_notation__spec_precedence__term_view_to__nat___main(x_41);
x_44 = lean::mk_nat_obj(0u);
x_45 = lean::nat_dec_eq(x_43, x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; 
lean::dec(x_2);
lean::dec(x_38);
x_49 = lean::mk_nat_obj(1u);
x_50 = lean::nat_sub(x_43, x_49);
lean::dec(x_49);
lean::dec(x_43);
x_53 = l_lean_parser_number_view_of__nat(x_50);
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = l_lean_expander_mixfix__to__notation__spec___closed__6;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_56);
if (lean::is_scalar(x_40)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_40;
}
lean::cnstr_set(x_60, 0, x_59);
x_3 = x_60;
goto lbl_4;
}
else
{
obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_69; 
lean::dec(x_40);
lean::dec(x_43);
x_63 = l_lean_parser_command_notation__spec_precedence_has__view;
x_64 = lean::cnstr_get(x_63, 1);
lean::inc(x_64);
x_66 = lean::apply_1(x_64, x_38);
x_67 = l_lean_expander_mixfix__to__notation__spec___closed__7;
lean::inc(x_67);
x_69 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_66, x_67, x_2);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_1);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_73 = x_69;
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
return x_74;
}
else
{
obj* x_75; 
x_75 = lean::cnstr_get(x_69, 0);
lean::inc(x_75);
lean::dec(x_69);
x_3 = x_75;
goto lbl_4;
}
}
}
}
default:
{
obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
x_81 = lean::box(0);
lean::inc(x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_1);
lean::cnstr_set(x_83, 1, x_81);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_81);
x_85 = l_lean_expander_mixfix__to__notation__spec___closed__2;
lean::inc(x_85);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_84);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
}
lbl_4:
{
obj* x_89; obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_99; obj* x_100; 
x_89 = lean::box(0);
x_90 = l_lean_expander_mixfix__to__notation__spec___closed__1;
lean::inc(x_90);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_3);
x_93 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_1);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_89);
x_97 = l_lean_expander_mixfix__to__notation__spec___closed__2;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_96);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
return x_100;
}
lbl_8:
{
obj* x_102; obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_118; obj* x_119; 
lean::dec(x_7);
x_102 = lean::box(0);
x_103 = l_lean_expander_mixfix__to__notation__spec___closed__3;
lean::inc(x_103);
x_105 = l_option_map___rarg(x_103, x_5);
x_106 = l_lean_expander_mixfix__to__notation__spec___closed__4;
lean::inc(x_106);
x_108 = l_option_map___rarg(x_106, x_105);
x_109 = l_lean_expander_mixfix__to__notation__spec___closed__1;
lean::inc(x_109);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_109);
lean::cnstr_set(x_111, 1, x_108);
x_112 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_112, 0, x_111);
x_113 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_113, 0, x_112);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_1);
lean::cnstr_set(x_114, 1, x_113);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_102);
x_116 = l_lean_expander_mixfix__to__notation__spec___closed__2;
lean::inc(x_116);
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_115);
x_119 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_119, 0, x_118);
return x_119;
}
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = l_lean_expander_mixfix__to__notation__spec___closed__6;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* l_lean_expander_mixfix__to__notation__spec___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_string("a");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_0);
lean::cnstr_set(x_14, 4, x_0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
x_16 = lean::apply_1(x_2, x_15);
return x_16;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_string("b");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_0);
lean::cnstr_set(x_14, 4, x_0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
x_16 = lean::apply_1(x_2, x_15);
return x_16;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("notation");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(":=");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::box(0);
x_1 = l_lean_parser_ident__univs_has__view;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_string("b");
lean::inc(x_0);
x_6 = lean::name_mk_string(x_0, x_4);
x_7 = lean::mk_string(".");
lean::inc(x_6);
x_9 = l_lean_name_to__string__with__sep___main(x_7, x_6);
x_10 = l_lean_parser_substring_of__string(x_9);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_10);
lean::cnstr_set(x_14, 2, x_6);
lean::cnstr_set(x_14, 3, x_0);
lean::cnstr_set(x_14, 4, x_0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_0);
x_16 = lean::apply_1(x_2, x_15);
return x_16;
}
}
obj* _init_l_lean_expander_mixfix_transform___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("`");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_lean_expander_mixfix_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_2 = l_lean_parser_command_mixfix_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_10 = x_12;
goto lbl_11;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; 
x_15 = lean::cnstr_get(x_6, 0);
lean::inc(x_15);
lean::dec(x_6);
x_18 = lean::box(0);
x_19 = l_lean_expander_mixfix_transform___closed__6;
lean::inc(x_19);
lean::inc(x_19);
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_19);
lean::cnstr_set(x_22, 3, x_18);
x_10 = x_22;
goto lbl_11;
}
lbl_11:
{
obj* x_24; 
lean::inc(x_8);
x_24 = l_lean_expander_mixfix__to__notation__spec(x_8, x_10, x_1);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_5);
lean::dec(x_8);
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_29 = x_24;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
return x_30;
}
else
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_33 = x_24;
}
x_34 = l_lean_parser_command_notation_has__view;
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
switch (lean::obj_tag(x_8)) {
case 0:
{
obj* x_43; obj* x_44; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_8);
lean::dec(x_33);
x_43 = l_lean_parser_term_app_has__view;
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_5, 4);
lean::inc(x_46);
lean::dec(x_5);
x_49 = l_lean_expander_mixfix_transform___closed__5;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_49);
x_52 = lean::apply_1(x_44, x_51);
x_53 = l_lean_expander_mixfix_transform___closed__3;
x_54 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_54);
lean::inc(x_53);
x_57 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_53);
lean::cnstr_set(x_57, 2, x_31);
lean::cnstr_set(x_57, 3, x_54);
lean::cnstr_set(x_57, 4, x_52);
x_58 = lean::apply_1(x_35, x_57);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
return x_60;
}
case 1:
{
obj* x_62; 
lean::dec(x_8);
x_62 = lean::box(0);
x_39 = x_62;
goto lbl_40;
}
case 2:
{
obj* x_64; 
lean::dec(x_8);
x_64 = lean::box(0);
x_39 = x_64;
goto lbl_40;
}
case 3:
{
obj* x_66; 
lean::dec(x_8);
x_66 = lean::box(0);
x_39 = x_66;
goto lbl_40;
}
default:
{
obj* x_69; obj* x_70; obj* x_72; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_8);
lean::dec(x_33);
x_69 = l_lean_parser_term_app_has__view;
x_70 = lean::cnstr_get(x_69, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_5, 4);
lean::inc(x_72);
lean::dec(x_5);
x_75 = l_lean_expander_mixfix_transform___closed__1;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_72);
lean::cnstr_set(x_77, 1, x_75);
x_78 = lean::apply_1(x_70, x_77);
x_79 = l_lean_expander_mixfix_transform___closed__3;
x_80 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_80);
lean::inc(x_79);
x_83 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_83, 0, x_37);
lean::cnstr_set(x_83, 1, x_79);
lean::cnstr_set(x_83, 2, x_31);
lean::cnstr_set(x_83, 3, x_80);
lean::cnstr_set(x_83, 4, x_78);
x_84 = lean::apply_1(x_35, x_83);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
}
lbl_40:
{
obj* x_88; obj* x_89; obj* x_91; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_39);
x_88 = l_lean_parser_term_app_has__view;
x_89 = lean::cnstr_get(x_88, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_5, 4);
lean::inc(x_91);
lean::dec(x_5);
x_94 = l_lean_expander_mixfix_transform___closed__1;
lean::inc(x_94);
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_91);
lean::cnstr_set(x_96, 1, x_94);
lean::inc(x_89);
x_98 = lean::apply_1(x_89, x_96);
x_99 = l_lean_expander_mixfix_transform___closed__2;
lean::inc(x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_98);
lean::cnstr_set(x_101, 1, x_99);
x_102 = lean::apply_1(x_89, x_101);
x_103 = l_lean_expander_mixfix_transform___closed__3;
x_104 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_104);
lean::inc(x_103);
x_107 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_107, 0, x_37);
lean::cnstr_set(x_107, 1, x_103);
lean::cnstr_set(x_107, 2, x_31);
lean::cnstr_set(x_107, 3, x_104);
lean::cnstr_set(x_107, 4, x_102);
x_108 = lean::apply_1(x_35, x_107);
x_109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
if (lean::is_scalar(x_33)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_33;
}
lean::cnstr_set(x_110, 0, x_109);
return x_110;
}
}
}
}
}
obj* _init_l_lean_expander_reserve__mixfix_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reserve");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_reserve__mixfix_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
x_2 = l_lean_parser_command_reserve__mixfix_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 2);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_lean_expander_mixfix__to__notation__spec(x_6, x_8, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_14 = x_11;
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
}
x_19 = l_lean_parser_command_reserve__notation_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = l_lean_expander_reserve__mixfix_transform___closed__1;
x_23 = l_lean_expander_mixfix_transform___closed__3;
lean::inc(x_23);
lean::inc(x_22);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_16);
x_27 = lean::apply_1(x_20, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_18;
}
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("{");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("}");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xe2\xa6\x83");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xe2\xa6\x84");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("[");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_lean_expander_mk__simple__binder___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("]");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_mk__simple__binder(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
switch (x_1) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_9; obj* x_10; 
x_3 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_4 = l_lean_expander_mk__simple__binder___closed__1;
x_5 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_4);
lean::cnstr_set(x_9, 3, x_2);
lean::cnstr_set(x_9, 4, x_5);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
case 1:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_17; obj* x_18; 
x_11 = l_lean_expander_mk__simple__binder___closed__2;
x_12 = l_lean_expander_mk__simple__binder___closed__1;
x_13 = l_lean_expander_mk__simple__binder___closed__3;
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
x_17 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_0);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_2);
lean::cnstr_set(x_17, 4, x_13);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
case 2:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_25; obj* x_26; 
x_19 = l_lean_expander_mk__simple__binder___closed__4;
x_20 = l_lean_expander_mk__simple__binder___closed__1;
x_21 = l_lean_expander_mk__simple__binder___closed__5;
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
x_25 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_0);
lean::cnstr_set(x_25, 2, x_20);
lean::cnstr_set(x_25, 3, x_2);
lean::cnstr_set(x_25, 4, x_21);
x_26 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
case 3:
{
obj* x_27; obj* x_28; obj* x_29; obj* x_33; obj* x_34; 
x_27 = l_lean_expander_mk__simple__binder___closed__6;
x_28 = l_lean_expander_mk__simple__binder___closed__1;
x_29 = l_lean_expander_mk__simple__binder___closed__7;
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
x_33 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_33, 0, x_27);
lean::cnstr_set(x_33, 1, x_0);
lean::cnstr_set(x_33, 2, x_28);
lean::cnstr_set(x_33, 3, x_2);
lean::cnstr_set(x_33, 4, x_29);
x_34 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
default:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_41; obj* x_42; 
x_35 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_36 = l_lean_expander_mk__simple__binder___closed__1;
x_37 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
x_41 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_41, 0, x_35);
lean::cnstr_set(x_41, 1, x_0);
lean::cnstr_set(x_41, 2, x_36);
lean::cnstr_set(x_41, 3, x_2);
lean::cnstr_set(x_41, 4, x_37);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
}
}
obj* l_lean_expander_mk__simple__binder___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_lean_expander_mk__simple__binder(x_0, x_3, x_2);
return x_4;
}
}
obj* _init_l_lean_expander_binder__ident__to__ident___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* l_lean_expander_binder__ident__to__ident___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_5; 
lean::dec(x_0);
x_5 = l_lean_expander_binder__ident__to__ident___main___closed__1;
lean::inc(x_5);
return x_5;
}
}
}
obj* l_lean_expander_binder__ident__to__ident(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_binder__ident__to__ident___main(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_get__opt__type___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = l_lean_parser_term_hole_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
x_3 = lean::box(0);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::apply_1(x_1, x_7);
return x_8;
}
}
obj* l_lean_expander_get__opt__type___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
return x_7;
}
}
}
obj* l_lean_expander_get__opt__type(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_expander_get__opt__type___main(x_0);
return x_1;
}
}
obj* _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_expander_get__opt__type___main(x_0);
return x_1;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
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
x_8 = l_lean_expander_binder__ident__to__ident___main(x_3);
x_9 = 0;
x_10 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1;
lean::inc(x_10);
x_12 = l_lean_expander_mk__simple__binder(x_8, x_9, x_10);
x_13 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
}
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = l_lean_expander_get__opt__type___main(x_11);
x_14 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_15 = l_lean_expander_mk__simple__binder(x_14, x_0, x_13);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_0, x_1, x_8);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("opt_param");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_12 = x_3;
}
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_15 = l_lean_expander_get__opt__type___main(x_13);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
x_18 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_12;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
lean::inc(x_21);
x_23 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_21, x_20);
x_24 = l_lean_expander_binder__ident__to__ident___main(x_8);
x_25 = l_lean_expander_mk__simple__binder(x_24, x_0, x_23);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_0, x_1, x_2, x_10);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("auto_param");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
}
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_10;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
lean::inc(x_15);
x_17 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_15, x_14);
x_18 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_19 = l_lean_expander_mk__simple__binder(x_18, x_0, x_17);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_0, x_1, x_8);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
}
x_11 = l_lean_expander_binder__ident__to__ident___main(x_6);
lean::inc(x_1);
x_13 = l_lean_expander_mk__simple__binder(x_11, x_0, x_1);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_0, x_1, x_8);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = l_lean_expander_get__opt__type___main(x_10);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_14 = 0;
x_15 = l_lean_expander_mk__simple__binder(x_13, x_14, x_12);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_11 = x_2;
}
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
x_17 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
lean::inc(x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_23 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_24 = 0;
x_25 = l_lean_expander_mk__simple__binder(x_23, x_24, x_22);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_0, x_1, x_9);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
lean::inc(x_14);
x_16 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_17 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_18 = 0;
x_19 = l_lean_expander_mk__simple__binder(x_17, x_18, x_16);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_0, x_7);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_11 = 0;
lean::inc(x_0);
x_13 = l_lean_expander_mk__simple__binder(x_10, x_11, x_0);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = l_lean_expander_get__opt__type___main(x_10);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_14 = 1;
x_15 = l_lean_expander_mk__simple__binder(x_13, x_14, x_12);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_11 = x_2;
}
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
x_17 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
lean::inc(x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_23 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_24 = 1;
x_25 = l_lean_expander_mk__simple__binder(x_23, x_24, x_22);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_0, x_1, x_9);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
lean::inc(x_14);
x_16 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_17 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_18 = 1;
x_19 = l_lean_expander_mk__simple__binder(x_17, x_18, x_16);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_0, x_7);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_11 = 1;
lean::inc(x_0);
x_13 = l_lean_expander_mk__simple__binder(x_10, x_11, x_0);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = l_lean_expander_get__opt__type___main(x_10);
x_13 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_14 = 2;
x_15 = l_lean_expander_mk__simple__binder(x_13, x_14, x_12);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_11 = x_2;
}
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
x_17 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_14);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
lean::inc(x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_20, x_19);
x_23 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_24 = 2;
x_25 = l_lean_expander_mk__simple__binder(x_23, x_24, x_22);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_0, x_1, x_9);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
lean::inc(x_14);
x_16 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
x_17 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_18 = 2;
x_19 = l_lean_expander_mk__simple__binder(x_17, x_18, x_16);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_0, x_7);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; uint8 x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_11 = 2;
lean::inc(x_0);
x_13 = l_lean_expander_mk__simple__binder(x_10, x_11, x_0);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
x_12 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_10);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = l_lean_expander_get__opt__type___main(x_15);
x_17 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_18 = 3;
x_19 = l_lean_expander_mk__simple__binder(x_17, x_18, x_16);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_0);
lean::inc(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_0);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = l_lean_expander_get__opt__type___main(x_14);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_17 = 3;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_15);
x_19 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
}
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = l_lean_expander_get__opt__type___main(x_11);
x_14 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_15 = l_lean_expander_mk__simple__binder(x_14, x_0, x_13);
x_16 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_0, x_1, x_8);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_12 = x_3;
}
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_15 = l_lean_expander_get__opt__type___main(x_13);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
x_18 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_12;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1;
lean::inc(x_21);
x_23 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_21, x_20);
x_24 = l_lean_expander_binder__ident__to__ident___main(x_8);
x_25 = l_lean_expander_mk__simple__binder(x_24, x_0, x_23);
x_26 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_0, x_1, x_2, x_10);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
}
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_10;
}
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1;
lean::inc(x_15);
x_17 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_15, x_14);
x_18 = l_lean_expander_binder__ident__to__ident___main(x_6);
x_19 = l_lean_expander_mk__simple__binder(x_18, x_0, x_17);
x_20 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_0, x_1, x_8);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
}
x_11 = l_lean_expander_binder__ident__to__ident___main(x_6);
lean::inc(x_1);
x_13 = l_lean_expander_mk__simple__binder(x_11, x_0, x_1);
x_14 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_0, x_1, x_8);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected auto param after type annotation");
return x_0;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__3() {
_start:
{
obj* x_0; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_0);
x_4 = 0;
x_5 = lean::box(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = l_lean_expander_expand__bracketed__binder___main___closed__1;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_inst_");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_0);
return x_13;
}
}
obj* _init_l_lean_expander_expand__bracketed__binder___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected anonymous constructor");
return x_0;
}
}
obj* l_lean_expander_expand__bracketed__binder___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_4);
lean::dec(x_0);
x_12 = l_lean_expander_expand__bracketed__binder___main___closed__4;
lean::inc(x_12);
return x_12;
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_18; 
lean::dec(x_6);
lean::dec(x_1);
x_18 = l_lean_expander_expand__bracketed__binder___main___closed__5;
lean::inc(x_18);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_6, 0);
lean::inc(x_20);
lean::dec(x_6);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_29; obj* x_30; 
lean::dec(x_23);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_20, 0);
lean::inc(x_27);
x_29 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__6(x_20, x_27);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
obj* x_31; 
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
lean::dec(x_23);
if (lean::obj_tag(x_31) == 0)
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_1);
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_20, 0);
lean::inc(x_38);
x_40 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__7(x_20, x_35, x_38);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
else
{
obj* x_42; obj* x_44; 
x_42 = lean::cnstr_get(x_31, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_20, 1);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_31);
lean::dec(x_1);
lean::dec(x_44);
x_49 = lean::cnstr_get(x_20, 0);
lean::inc(x_49);
lean::dec(x_20);
x_52 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__8(x_42, x_49);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
return x_53;
}
else
{
obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_44);
lean::dec(x_42);
x_56 = l_lean_parser_term_binder__default_has__view;
x_57 = lean::cnstr_get(x_56, 1);
lean::inc(x_57);
x_59 = lean::apply_1(x_57, x_31);
x_60 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_60);
x_62 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_59, x_60, x_1);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_20);
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_66 = x_62;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
return x_67;
}
else
{
obj* x_68; obj* x_70; obj* x_71; obj* x_74; obj* x_75; 
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
}
x_71 = lean::cnstr_get(x_20, 0);
lean::inc(x_71);
lean::dec(x_20);
x_74 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__9(x_68, x_71);
if (lean::is_scalar(x_70)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_70;
}
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
}
}
}
}
case 1:
{
obj* x_78; 
lean::dec(x_4);
lean::dec(x_0);
x_78 = lean::cnstr_get(x_6, 2);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_78);
x_82 = lean::cnstr_get(x_6, 0);
lean::inc(x_82);
x_84 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__10(x_6, x_82);
x_85 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
return x_85;
}
else
{
obj* x_86; 
x_86 = lean::cnstr_get(x_78, 0);
lean::inc(x_86);
lean::dec(x_78);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_93; obj* x_95; obj* x_96; 
lean::dec(x_1);
x_90 = lean::cnstr_get(x_86, 0);
lean::inc(x_90);
lean::dec(x_86);
x_93 = lean::cnstr_get(x_6, 0);
lean::inc(x_93);
x_95 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__11(x_6, x_90, x_93);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
else
{
obj* x_97; obj* x_99; 
x_97 = lean::cnstr_get(x_86, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_6, 1);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_104; obj* x_107; obj* x_108; 
lean::dec(x_1);
lean::dec(x_99);
lean::dec(x_86);
x_104 = lean::cnstr_get(x_6, 0);
lean::inc(x_104);
lean::dec(x_6);
x_107 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__12(x_97, x_104);
x_108 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_108, 0, x_107);
return x_108;
}
else
{
obj* x_111; obj* x_112; obj* x_114; obj* x_115; obj* x_117; 
lean::dec(x_99);
lean::dec(x_97);
x_111 = l_lean_parser_term_binder__default_has__view;
x_112 = lean::cnstr_get(x_111, 1);
lean::inc(x_112);
x_114 = lean::apply_1(x_112, x_86);
x_115 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_115);
x_117 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_114, x_115, x_1);
if (lean::obj_tag(x_117) == 0)
{
obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_6);
x_119 = lean::cnstr_get(x_117, 0);
lean::inc(x_119);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 x_121 = x_117;
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
return x_122;
}
else
{
obj* x_123; obj* x_125; obj* x_126; obj* x_129; obj* x_130; 
x_123 = lean::cnstr_get(x_117, 0);
lean::inc(x_123);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_125 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 x_125 = x_117;
}
x_126 = lean::cnstr_get(x_6, 0);
lean::inc(x_126);
lean::dec(x_6);
x_129 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__13(x_123, x_126);
if (lean::is_scalar(x_125)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_125;
}
lean::cnstr_set(x_130, 0, x_129);
return x_130;
}
}
}
}
}
case 2:
{
obj* x_133; 
lean::dec(x_4);
lean::dec(x_0);
x_133 = lean::cnstr_get(x_6, 2);
lean::inc(x_133);
if (lean::obj_tag(x_133) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_1);
lean::dec(x_133);
x_137 = lean::cnstr_get(x_6, 0);
lean::inc(x_137);
x_139 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__14(x_6, x_137);
x_140 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_140, 0, x_139);
return x_140;
}
else
{
obj* x_141; 
x_141 = lean::cnstr_get(x_133, 0);
lean::inc(x_141);
lean::dec(x_133);
if (lean::obj_tag(x_141) == 0)
{
obj* x_145; obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_1);
x_145 = lean::cnstr_get(x_141, 0);
lean::inc(x_145);
lean::dec(x_141);
x_148 = lean::cnstr_get(x_6, 0);
lean::inc(x_148);
x_150 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__15(x_6, x_145, x_148);
x_151 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_151, 0, x_150);
return x_151;
}
else
{
obj* x_152; obj* x_154; 
x_152 = lean::cnstr_get(x_141, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_6, 1);
lean::inc(x_154);
if (lean::obj_tag(x_154) == 0)
{
obj* x_159; obj* x_162; obj* x_163; 
lean::dec(x_1);
lean::dec(x_141);
lean::dec(x_154);
x_159 = lean::cnstr_get(x_6, 0);
lean::inc(x_159);
lean::dec(x_6);
x_162 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__16(x_152, x_159);
x_163 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_163, 0, x_162);
return x_163;
}
else
{
obj* x_166; obj* x_167; obj* x_169; obj* x_170; obj* x_172; 
lean::dec(x_152);
lean::dec(x_154);
x_166 = l_lean_parser_term_binder__default_has__view;
x_167 = lean::cnstr_get(x_166, 1);
lean::inc(x_167);
x_169 = lean::apply_1(x_167, x_141);
x_170 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_170);
x_172 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_169, x_170, x_1);
if (lean::obj_tag(x_172) == 0)
{
obj* x_174; obj* x_176; obj* x_177; 
lean::dec(x_6);
x_174 = lean::cnstr_get(x_172, 0);
lean::inc(x_174);
if (lean::is_shared(x_172)) {
 lean::dec(x_172);
 x_176 = lean::box(0);
} else {
 lean::cnstr_release(x_172, 0);
 x_176 = x_172;
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_174);
return x_177;
}
else
{
obj* x_178; obj* x_180; obj* x_181; obj* x_184; obj* x_185; 
x_178 = lean::cnstr_get(x_172, 0);
lean::inc(x_178);
if (lean::is_shared(x_172)) {
 lean::dec(x_172);
 x_180 = lean::box(0);
} else {
 lean::cnstr_release(x_172, 0);
 x_180 = x_172;
}
x_181 = lean::cnstr_get(x_6, 0);
lean::inc(x_181);
lean::dec(x_6);
x_184 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__17(x_178, x_181);
if (lean::is_scalar(x_180)) {
 x_185 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_185 = x_180;
}
lean::cnstr_set(x_185, 0, x_184);
return x_185;
}
}
}
}
}
case 3:
{
lean::dec(x_1);
lean::dec(x_4);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_189; obj* x_192; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
x_189 = lean::cnstr_get(x_6, 0);
lean::inc(x_189);
lean::dec(x_6);
x_192 = lean::cnstr_get(x_189, 0);
lean::inc(x_192);
x_194 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_194, 0, x_192);
x_195 = lean::box(0);
x_196 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_195);
x_197 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__18(x_189, x_196);
x_198 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_198, 0, x_197);
return x_198;
}
else
{
obj* x_199; obj* x_202; obj* x_204; obj* x_205; 
x_199 = lean::cnstr_get(x_6, 0);
lean::inc(x_199);
lean::dec(x_6);
x_202 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_202);
x_204 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__19(x_199, x_202);
x_205 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_205, 0, x_204);
return x_205;
}
}
default:
{
obj* x_208; obj* x_209; obj* x_211; obj* x_212; obj* x_215; 
lean::dec(x_6);
lean::dec(x_0);
x_208 = l_lean_parser_term_anonymous__constructor_has__view;
x_209 = lean::cnstr_get(x_208, 1);
lean::inc(x_209);
x_211 = lean::apply_1(x_209, x_4);
x_212 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_212);
x_215 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_211, x_212, x_1);
if (lean::obj_tag(x_215) == 0)
{
obj* x_217; obj* x_219; obj* x_220; 
lean::dec(x_1);
x_217 = lean::cnstr_get(x_215, 0);
lean::inc(x_217);
if (lean::is_shared(x_215)) {
 lean::dec(x_215);
 x_219 = lean::box(0);
} else {
 lean::cnstr_release(x_215, 0);
 x_219 = x_215;
}
if (lean::is_scalar(x_219)) {
 x_220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_220 = x_219;
}
lean::cnstr_set(x_220, 0, x_217);
return x_220;
}
else
{
obj* x_221; obj* x_223; obj* x_224; obj* x_226; obj* x_229; 
x_221 = lean::cnstr_get(x_215, 0);
lean::inc(x_221);
if (lean::is_shared(x_215)) {
 lean::dec(x_215);
 x_223 = lean::box(0);
} else {
 lean::cnstr_release(x_215, 0);
 x_223 = x_215;
}
x_224 = lean::cnstr_get(x_221, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_221, 1);
lean::inc(x_226);
lean::dec(x_221);
x_229 = lean::cnstr_get(x_226, 2);
lean::inc(x_229);
if (lean::obj_tag(x_229) == 0)
{
obj* x_233; uint8 x_235; obj* x_237; obj* x_238; 
lean::dec(x_229);
lean::dec(x_1);
x_233 = lean::cnstr_get(x_226, 0);
lean::inc(x_233);
x_235 = lean::unbox(x_224);
lean::dec(x_224);
x_237 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_235, x_226, x_233);
if (lean::is_scalar(x_223)) {
 x_238 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_238 = x_223;
}
lean::cnstr_set(x_238, 0, x_237);
return x_238;
}
else
{
obj* x_239; 
x_239 = lean::cnstr_get(x_229, 0);
lean::inc(x_239);
lean::dec(x_229);
if (lean::obj_tag(x_239) == 0)
{
obj* x_243; obj* x_246; uint8 x_248; obj* x_250; obj* x_251; 
lean::dec(x_1);
x_243 = lean::cnstr_get(x_239, 0);
lean::inc(x_243);
lean::dec(x_239);
x_246 = lean::cnstr_get(x_226, 0);
lean::inc(x_246);
x_248 = lean::unbox(x_224);
lean::dec(x_224);
x_250 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_248, x_226, x_243, x_246);
if (lean::is_scalar(x_223)) {
 x_251 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_251 = x_223;
}
lean::cnstr_set(x_251, 0, x_250);
return x_251;
}
else
{
obj* x_252; obj* x_254; 
x_252 = lean::cnstr_get(x_239, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_226, 1);
lean::inc(x_254);
if (lean::obj_tag(x_254) == 0)
{
obj* x_259; uint8 x_262; obj* x_264; obj* x_265; 
lean::dec(x_239);
lean::dec(x_254);
lean::dec(x_1);
x_259 = lean::cnstr_get(x_226, 0);
lean::inc(x_259);
lean::dec(x_226);
x_262 = lean::unbox(x_224);
lean::dec(x_224);
x_264 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_262, x_252, x_259);
if (lean::is_scalar(x_223)) {
 x_265 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_265 = x_223;
}
lean::cnstr_set(x_265, 0, x_264);
return x_265;
}
else
{
obj* x_268; obj* x_269; obj* x_271; obj* x_272; obj* x_274; 
lean::dec(x_252);
lean::dec(x_254);
x_268 = l_lean_parser_term_binder__default_has__view;
x_269 = lean::cnstr_get(x_268, 1);
lean::inc(x_269);
x_271 = lean::apply_1(x_269, x_239);
x_272 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_272);
x_274 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_271, x_272, x_1);
if (lean::obj_tag(x_274) == 0)
{
obj* x_277; obj* x_280; 
lean::dec(x_226);
lean::dec(x_224);
x_277 = lean::cnstr_get(x_274, 0);
lean::inc(x_277);
lean::dec(x_274);
if (lean::is_scalar(x_223)) {
 x_280 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_280 = x_223;
 lean::cnstr_set_tag(x_223, 0);
}
lean::cnstr_set(x_280, 0, x_277);
return x_280;
}
else
{
obj* x_281; obj* x_284; uint8 x_287; obj* x_289; obj* x_290; 
x_281 = lean::cnstr_get(x_274, 0);
lean::inc(x_281);
lean::dec(x_274);
x_284 = lean::cnstr_get(x_226, 0);
lean::inc(x_284);
lean::dec(x_226);
x_287 = lean::unbox(x_224);
lean::dec(x_224);
x_289 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_287, x_281, x_284);
if (lean::is_scalar(x_223)) {
 x_290 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_290 = x_223;
}
lean::cnstr_set(x_290, 0, x_289);
return x_290;
}
}
}
}
}
}
}
}
}
case 1:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_291; obj* x_294; 
x_291 = lean::cnstr_get(x_0, 0);
lean::inc(x_291);
lean::dec(x_0);
x_294 = lean::cnstr_get(x_291, 1);
lean::inc(x_294);
lean::dec(x_291);
if (lean::obj_tag(x_294) == 0)
{
obj* x_298; 
lean::dec(x_294);
x_298 = l_lean_expander_expand__bracketed__binder___main___closed__3;
lean::inc(x_298);
x_2 = x_298;
goto lbl_3;
}
else
{
obj* x_300; uint8 x_303; obj* x_304; obj* x_305; 
x_300 = lean::cnstr_get(x_294, 0);
lean::inc(x_300);
lean::dec(x_294);
x_303 = 0;
x_304 = lean::box(x_303);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_300);
x_2 = x_305;
goto lbl_3;
}
}
case 1:
{
obj* x_306; obj* x_309; uint8 x_312; obj* x_313; obj* x_314; 
x_306 = lean::cnstr_get(x_0, 0);
lean::inc(x_306);
lean::dec(x_0);
x_309 = lean::cnstr_get(x_306, 1);
lean::inc(x_309);
lean::dec(x_306);
x_312 = 1;
x_313 = lean::box(x_312);
x_314 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_309);
x_2 = x_314;
goto lbl_3;
}
case 2:
{
obj* x_315; obj* x_318; uint8 x_321; obj* x_322; obj* x_323; 
x_315 = lean::cnstr_get(x_0, 0);
lean::inc(x_315);
lean::dec(x_0);
x_318 = lean::cnstr_get(x_315, 1);
lean::inc(x_318);
lean::dec(x_315);
x_321 = 2;
x_322 = lean::box(x_321);
x_323 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_323, 0, x_322);
lean::cnstr_set(x_323, 1, x_318);
x_2 = x_323;
goto lbl_3;
}
case 3:
{
obj* x_324; obj* x_327; 
x_324 = lean::cnstr_get(x_0, 0);
lean::inc(x_324);
lean::dec(x_0);
x_327 = lean::cnstr_get(x_324, 1);
lean::inc(x_327);
lean::dec(x_324);
if (lean::obj_tag(x_327) == 0)
{
obj* x_330; obj* x_333; obj* x_335; obj* x_336; obj* x_338; obj* x_339; obj* x_342; obj* x_344; obj* x_345; obj* x_346; uint8 x_347; obj* x_348; obj* x_349; 
x_330 = lean::cnstr_get(x_327, 0);
lean::inc(x_330);
lean::dec(x_327);
x_333 = lean::cnstr_get(x_330, 0);
lean::inc(x_333);
x_335 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_335, 0, x_333);
x_336 = lean::box(0);
lean::inc(x_336);
x_338 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_338, 0, x_335);
lean::cnstr_set(x_338, 1, x_336);
x_339 = lean::cnstr_get(x_330, 2);
lean::inc(x_339);
lean::dec(x_330);
x_342 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_342);
x_344 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_344, 0, x_342);
lean::cnstr_set(x_344, 1, x_339);
x_345 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_345, 0, x_344);
x_346 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_346, 0, x_338);
lean::cnstr_set(x_346, 1, x_345);
lean::cnstr_set(x_346, 2, x_336);
x_347 = 3;
x_348 = lean::box(x_347);
x_349 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_349, 0, x_348);
lean::cnstr_set(x_349, 1, x_346);
x_2 = x_349;
goto lbl_3;
}
else
{
obj* x_350; obj* x_353; obj* x_354; obj* x_356; obj* x_357; obj* x_358; obj* x_360; uint8 x_361; obj* x_362; obj* x_363; 
x_350 = lean::cnstr_get(x_327, 0);
lean::inc(x_350);
lean::dec(x_327);
x_353 = lean::box(0);
x_354 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_354);
x_356 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_356, 0, x_354);
lean::cnstr_set(x_356, 1, x_350);
x_357 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_357, 0, x_356);
x_358 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_358);
x_360 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_360, 0, x_358);
lean::cnstr_set(x_360, 1, x_357);
lean::cnstr_set(x_360, 2, x_353);
x_361 = 3;
x_362 = lean::box(x_361);
x_363 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_360);
x_2 = x_363;
goto lbl_3;
}
}
default:
{
obj* x_364; obj* x_367; obj* x_368; obj* x_370; obj* x_371; obj* x_374; 
x_364 = lean::cnstr_get(x_0, 0);
lean::inc(x_364);
lean::dec(x_0);
x_367 = l_lean_parser_term_anonymous__constructor_has__view;
x_368 = lean::cnstr_get(x_367, 1);
lean::inc(x_368);
x_370 = lean::apply_1(x_368, x_364);
x_371 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_371);
x_374 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_370, x_371, x_1);
if (lean::obj_tag(x_374) == 0)
{
obj* x_376; obj* x_378; obj* x_379; 
lean::dec(x_1);
x_376 = lean::cnstr_get(x_374, 0);
lean::inc(x_376);
if (lean::is_shared(x_374)) {
 lean::dec(x_374);
 x_378 = lean::box(0);
} else {
 lean::cnstr_release(x_374, 0);
 x_378 = x_374;
}
if (lean::is_scalar(x_378)) {
 x_379 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_379 = x_378;
}
lean::cnstr_set(x_379, 0, x_376);
return x_379;
}
else
{
obj* x_380; 
x_380 = lean::cnstr_get(x_374, 0);
lean::inc(x_380);
lean::dec(x_374);
x_2 = x_380;
goto lbl_3;
}
}
}
}
case 2:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_383; obj* x_386; 
x_383 = lean::cnstr_get(x_0, 0);
lean::inc(x_383);
lean::dec(x_0);
x_386 = lean::cnstr_get(x_383, 1);
lean::inc(x_386);
lean::dec(x_383);
if (lean::obj_tag(x_386) == 0)
{
obj* x_390; 
lean::dec(x_386);
x_390 = l_lean_expander_expand__bracketed__binder___main___closed__3;
lean::inc(x_390);
x_2 = x_390;
goto lbl_3;
}
else
{
obj* x_392; uint8 x_395; obj* x_396; obj* x_397; 
x_392 = lean::cnstr_get(x_386, 0);
lean::inc(x_392);
lean::dec(x_386);
x_395 = 0;
x_396 = lean::box(x_395);
x_397 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_397, 0, x_396);
lean::cnstr_set(x_397, 1, x_392);
x_2 = x_397;
goto lbl_3;
}
}
case 1:
{
obj* x_398; obj* x_401; uint8 x_404; obj* x_405; obj* x_406; 
x_398 = lean::cnstr_get(x_0, 0);
lean::inc(x_398);
lean::dec(x_0);
x_401 = lean::cnstr_get(x_398, 1);
lean::inc(x_401);
lean::dec(x_398);
x_404 = 1;
x_405 = lean::box(x_404);
x_406 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_406, 0, x_405);
lean::cnstr_set(x_406, 1, x_401);
x_2 = x_406;
goto lbl_3;
}
case 2:
{
obj* x_407; obj* x_410; uint8 x_413; obj* x_414; obj* x_415; 
x_407 = lean::cnstr_get(x_0, 0);
lean::inc(x_407);
lean::dec(x_0);
x_410 = lean::cnstr_get(x_407, 1);
lean::inc(x_410);
lean::dec(x_407);
x_413 = 2;
x_414 = lean::box(x_413);
x_415 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_415, 0, x_414);
lean::cnstr_set(x_415, 1, x_410);
x_2 = x_415;
goto lbl_3;
}
case 3:
{
obj* x_416; obj* x_419; 
x_416 = lean::cnstr_get(x_0, 0);
lean::inc(x_416);
lean::dec(x_0);
x_419 = lean::cnstr_get(x_416, 1);
lean::inc(x_419);
lean::dec(x_416);
if (lean::obj_tag(x_419) == 0)
{
obj* x_422; obj* x_425; obj* x_427; obj* x_428; obj* x_430; obj* x_431; obj* x_434; obj* x_436; obj* x_437; obj* x_438; uint8 x_439; obj* x_440; obj* x_441; 
x_422 = lean::cnstr_get(x_419, 0);
lean::inc(x_422);
lean::dec(x_419);
x_425 = lean::cnstr_get(x_422, 0);
lean::inc(x_425);
x_427 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_427, 0, x_425);
x_428 = lean::box(0);
lean::inc(x_428);
x_430 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_430, 0, x_427);
lean::cnstr_set(x_430, 1, x_428);
x_431 = lean::cnstr_get(x_422, 2);
lean::inc(x_431);
lean::dec(x_422);
x_434 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_434);
x_436 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_436, 0, x_434);
lean::cnstr_set(x_436, 1, x_431);
x_437 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_437, 0, x_436);
x_438 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_438, 0, x_430);
lean::cnstr_set(x_438, 1, x_437);
lean::cnstr_set(x_438, 2, x_428);
x_439 = 3;
x_440 = lean::box(x_439);
x_441 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_441, 0, x_440);
lean::cnstr_set(x_441, 1, x_438);
x_2 = x_441;
goto lbl_3;
}
else
{
obj* x_442; obj* x_445; obj* x_446; obj* x_448; obj* x_449; obj* x_450; obj* x_452; uint8 x_453; obj* x_454; obj* x_455; 
x_442 = lean::cnstr_get(x_419, 0);
lean::inc(x_442);
lean::dec(x_419);
x_445 = lean::box(0);
x_446 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_446);
x_448 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_448, 0, x_446);
lean::cnstr_set(x_448, 1, x_442);
x_449 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_449, 0, x_448);
x_450 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_450);
x_452 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_452, 0, x_450);
lean::cnstr_set(x_452, 1, x_449);
lean::cnstr_set(x_452, 2, x_445);
x_453 = 3;
x_454 = lean::box(x_453);
x_455 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_455, 0, x_454);
lean::cnstr_set(x_455, 1, x_452);
x_2 = x_455;
goto lbl_3;
}
}
default:
{
obj* x_456; obj* x_459; obj* x_460; obj* x_462; obj* x_463; obj* x_466; 
x_456 = lean::cnstr_get(x_0, 0);
lean::inc(x_456);
lean::dec(x_0);
x_459 = l_lean_parser_term_anonymous__constructor_has__view;
x_460 = lean::cnstr_get(x_459, 1);
lean::inc(x_460);
x_462 = lean::apply_1(x_460, x_456);
x_463 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_463);
x_466 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_462, x_463, x_1);
if (lean::obj_tag(x_466) == 0)
{
obj* x_468; obj* x_470; obj* x_471; 
lean::dec(x_1);
x_468 = lean::cnstr_get(x_466, 0);
lean::inc(x_468);
if (lean::is_shared(x_466)) {
 lean::dec(x_466);
 x_470 = lean::box(0);
} else {
 lean::cnstr_release(x_466, 0);
 x_470 = x_466;
}
if (lean::is_scalar(x_470)) {
 x_471 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_471 = x_470;
}
lean::cnstr_set(x_471, 0, x_468);
return x_471;
}
else
{
obj* x_472; 
x_472 = lean::cnstr_get(x_466, 0);
lean::inc(x_472);
lean::dec(x_466);
x_2 = x_472;
goto lbl_3;
}
}
}
}
case 3:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_475; obj* x_478; 
x_475 = lean::cnstr_get(x_0, 0);
lean::inc(x_475);
lean::dec(x_0);
x_478 = lean::cnstr_get(x_475, 1);
lean::inc(x_478);
lean::dec(x_475);
if (lean::obj_tag(x_478) == 0)
{
obj* x_482; 
lean::dec(x_478);
x_482 = l_lean_expander_expand__bracketed__binder___main___closed__3;
lean::inc(x_482);
x_2 = x_482;
goto lbl_3;
}
else
{
obj* x_484; uint8 x_487; obj* x_488; obj* x_489; 
x_484 = lean::cnstr_get(x_478, 0);
lean::inc(x_484);
lean::dec(x_478);
x_487 = 0;
x_488 = lean::box(x_487);
x_489 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_489, 0, x_488);
lean::cnstr_set(x_489, 1, x_484);
x_2 = x_489;
goto lbl_3;
}
}
case 1:
{
obj* x_490; obj* x_493; uint8 x_496; obj* x_497; obj* x_498; 
x_490 = lean::cnstr_get(x_0, 0);
lean::inc(x_490);
lean::dec(x_0);
x_493 = lean::cnstr_get(x_490, 1);
lean::inc(x_493);
lean::dec(x_490);
x_496 = 1;
x_497 = lean::box(x_496);
x_498 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_498, 0, x_497);
lean::cnstr_set(x_498, 1, x_493);
x_2 = x_498;
goto lbl_3;
}
case 2:
{
obj* x_499; obj* x_502; uint8 x_505; obj* x_506; obj* x_507; 
x_499 = lean::cnstr_get(x_0, 0);
lean::inc(x_499);
lean::dec(x_0);
x_502 = lean::cnstr_get(x_499, 1);
lean::inc(x_502);
lean::dec(x_499);
x_505 = 2;
x_506 = lean::box(x_505);
x_507 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_507, 0, x_506);
lean::cnstr_set(x_507, 1, x_502);
x_2 = x_507;
goto lbl_3;
}
case 3:
{
obj* x_508; obj* x_511; 
x_508 = lean::cnstr_get(x_0, 0);
lean::inc(x_508);
lean::dec(x_0);
x_511 = lean::cnstr_get(x_508, 1);
lean::inc(x_511);
lean::dec(x_508);
if (lean::obj_tag(x_511) == 0)
{
obj* x_514; obj* x_517; obj* x_519; obj* x_520; obj* x_522; obj* x_523; obj* x_526; obj* x_528; obj* x_529; obj* x_530; uint8 x_531; obj* x_532; obj* x_533; 
x_514 = lean::cnstr_get(x_511, 0);
lean::inc(x_514);
lean::dec(x_511);
x_517 = lean::cnstr_get(x_514, 0);
lean::inc(x_517);
x_519 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_519, 0, x_517);
x_520 = lean::box(0);
lean::inc(x_520);
x_522 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_522, 0, x_519);
lean::cnstr_set(x_522, 1, x_520);
x_523 = lean::cnstr_get(x_514, 2);
lean::inc(x_523);
lean::dec(x_514);
x_526 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_526);
x_528 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_528, 0, x_526);
lean::cnstr_set(x_528, 1, x_523);
x_529 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_529, 0, x_528);
x_530 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_530, 0, x_522);
lean::cnstr_set(x_530, 1, x_529);
lean::cnstr_set(x_530, 2, x_520);
x_531 = 3;
x_532 = lean::box(x_531);
x_533 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_533, 0, x_532);
lean::cnstr_set(x_533, 1, x_530);
x_2 = x_533;
goto lbl_3;
}
else
{
obj* x_534; obj* x_537; obj* x_538; obj* x_540; obj* x_541; obj* x_542; obj* x_544; uint8 x_545; obj* x_546; obj* x_547; 
x_534 = lean::cnstr_get(x_511, 0);
lean::inc(x_534);
lean::dec(x_511);
x_537 = lean::box(0);
x_538 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_538);
x_540 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_540, 0, x_538);
lean::cnstr_set(x_540, 1, x_534);
x_541 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_541, 0, x_540);
x_542 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_542);
x_544 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_544, 0, x_542);
lean::cnstr_set(x_544, 1, x_541);
lean::cnstr_set(x_544, 2, x_537);
x_545 = 3;
x_546 = lean::box(x_545);
x_547 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_547, 0, x_546);
lean::cnstr_set(x_547, 1, x_544);
x_2 = x_547;
goto lbl_3;
}
}
default:
{
obj* x_548; obj* x_551; obj* x_552; obj* x_554; obj* x_555; obj* x_558; 
x_548 = lean::cnstr_get(x_0, 0);
lean::inc(x_548);
lean::dec(x_0);
x_551 = l_lean_parser_term_anonymous__constructor_has__view;
x_552 = lean::cnstr_get(x_551, 1);
lean::inc(x_552);
x_554 = lean::apply_1(x_552, x_548);
x_555 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_555);
x_558 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_554, x_555, x_1);
if (lean::obj_tag(x_558) == 0)
{
obj* x_560; obj* x_562; obj* x_563; 
lean::dec(x_1);
x_560 = lean::cnstr_get(x_558, 0);
lean::inc(x_560);
if (lean::is_shared(x_558)) {
 lean::dec(x_558);
 x_562 = lean::box(0);
} else {
 lean::cnstr_release(x_558, 0);
 x_562 = x_558;
}
if (lean::is_scalar(x_562)) {
 x_563 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_563 = x_562;
}
lean::cnstr_set(x_563, 0, x_560);
return x_563;
}
else
{
obj* x_564; 
x_564 = lean::cnstr_get(x_558, 0);
lean::inc(x_564);
lean::dec(x_558);
x_2 = x_564;
goto lbl_3;
}
}
}
}
default:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_567; obj* x_570; 
x_567 = lean::cnstr_get(x_0, 0);
lean::inc(x_567);
lean::dec(x_0);
x_570 = lean::cnstr_get(x_567, 1);
lean::inc(x_570);
lean::dec(x_567);
if (lean::obj_tag(x_570) == 0)
{
obj* x_574; 
lean::dec(x_570);
x_574 = l_lean_expander_expand__bracketed__binder___main___closed__3;
lean::inc(x_574);
x_2 = x_574;
goto lbl_3;
}
else
{
obj* x_576; uint8 x_579; obj* x_580; obj* x_581; 
x_576 = lean::cnstr_get(x_570, 0);
lean::inc(x_576);
lean::dec(x_570);
x_579 = 0;
x_580 = lean::box(x_579);
x_581 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_581, 1, x_576);
x_2 = x_581;
goto lbl_3;
}
}
case 1:
{
obj* x_582; obj* x_585; uint8 x_588; obj* x_589; obj* x_590; 
x_582 = lean::cnstr_get(x_0, 0);
lean::inc(x_582);
lean::dec(x_0);
x_585 = lean::cnstr_get(x_582, 1);
lean::inc(x_585);
lean::dec(x_582);
x_588 = 1;
x_589 = lean::box(x_588);
x_590 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_590, 0, x_589);
lean::cnstr_set(x_590, 1, x_585);
x_2 = x_590;
goto lbl_3;
}
case 2:
{
obj* x_591; obj* x_594; uint8 x_597; obj* x_598; obj* x_599; 
x_591 = lean::cnstr_get(x_0, 0);
lean::inc(x_591);
lean::dec(x_0);
x_594 = lean::cnstr_get(x_591, 1);
lean::inc(x_594);
lean::dec(x_591);
x_597 = 2;
x_598 = lean::box(x_597);
x_599 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_594);
x_2 = x_599;
goto lbl_3;
}
case 3:
{
obj* x_600; obj* x_603; 
x_600 = lean::cnstr_get(x_0, 0);
lean::inc(x_600);
lean::dec(x_0);
x_603 = lean::cnstr_get(x_600, 1);
lean::inc(x_603);
lean::dec(x_600);
if (lean::obj_tag(x_603) == 0)
{
obj* x_606; obj* x_609; obj* x_611; obj* x_612; obj* x_614; obj* x_615; obj* x_618; obj* x_620; obj* x_621; obj* x_622; uint8 x_623; obj* x_624; obj* x_625; 
x_606 = lean::cnstr_get(x_603, 0);
lean::inc(x_606);
lean::dec(x_603);
x_609 = lean::cnstr_get(x_606, 0);
lean::inc(x_609);
x_611 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_611, 0, x_609);
x_612 = lean::box(0);
lean::inc(x_612);
x_614 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_614, 0, x_611);
lean::cnstr_set(x_614, 1, x_612);
x_615 = lean::cnstr_get(x_606, 2);
lean::inc(x_615);
lean::dec(x_606);
x_618 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_618);
x_620 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_620, 0, x_618);
lean::cnstr_set(x_620, 1, x_615);
x_621 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_621, 0, x_620);
x_622 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_622, 0, x_614);
lean::cnstr_set(x_622, 1, x_621);
lean::cnstr_set(x_622, 2, x_612);
x_623 = 3;
x_624 = lean::box(x_623);
x_625 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_625, 0, x_624);
lean::cnstr_set(x_625, 1, x_622);
x_2 = x_625;
goto lbl_3;
}
else
{
obj* x_626; obj* x_629; obj* x_630; obj* x_632; obj* x_633; obj* x_634; obj* x_636; uint8 x_637; obj* x_638; obj* x_639; 
x_626 = lean::cnstr_get(x_603, 0);
lean::inc(x_626);
lean::dec(x_603);
x_629 = lean::box(0);
x_630 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_630);
x_632 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_632, 0, x_630);
lean::cnstr_set(x_632, 1, x_626);
x_633 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_633, 0, x_632);
x_634 = l_lean_expander_expand__bracketed__binder___main___closed__6;
lean::inc(x_634);
x_636 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_636, 0, x_634);
lean::cnstr_set(x_636, 1, x_633);
lean::cnstr_set(x_636, 2, x_629);
x_637 = 3;
x_638 = lean::box(x_637);
x_639 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_639, 0, x_638);
lean::cnstr_set(x_639, 1, x_636);
x_2 = x_639;
goto lbl_3;
}
}
default:
{
obj* x_640; obj* x_643; obj* x_644; obj* x_646; obj* x_647; obj* x_650; 
x_640 = lean::cnstr_get(x_0, 0);
lean::inc(x_640);
lean::dec(x_0);
x_643 = l_lean_parser_term_anonymous__constructor_has__view;
x_644 = lean::cnstr_get(x_643, 1);
lean::inc(x_644);
x_646 = lean::apply_1(x_644, x_640);
x_647 = l_lean_expander_expand__bracketed__binder___main___closed__7;
lean::inc(x_1);
lean::inc(x_647);
x_650 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_646, x_647, x_1);
if (lean::obj_tag(x_650) == 0)
{
obj* x_652; obj* x_654; obj* x_655; 
lean::dec(x_1);
x_652 = lean::cnstr_get(x_650, 0);
lean::inc(x_652);
if (lean::is_shared(x_650)) {
 lean::dec(x_650);
 x_654 = lean::box(0);
} else {
 lean::cnstr_release(x_650, 0);
 x_654 = x_650;
}
if (lean::is_scalar(x_654)) {
 x_655 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_655 = x_654;
}
lean::cnstr_set(x_655, 0, x_652);
return x_655;
}
else
{
obj* x_656; 
x_656 = lean::cnstr_get(x_650, 0);
lean::inc(x_656);
lean::dec(x_650);
x_2 = x_656;
goto lbl_3;
}
}
}
}
}
lbl_3:
{
obj* x_659; obj* x_661; obj* x_664; 
x_659 = lean::cnstr_get(x_2, 0);
lean::inc(x_659);
x_661 = lean::cnstr_get(x_2, 1);
lean::inc(x_661);
lean::dec(x_2);
x_664 = lean::cnstr_get(x_661, 2);
lean::inc(x_664);
if (lean::obj_tag(x_664) == 0)
{
obj* x_668; uint8 x_670; obj* x_672; obj* x_673; 
lean::dec(x_1);
lean::dec(x_664);
x_668 = lean::cnstr_get(x_661, 0);
lean::inc(x_668);
x_670 = lean::unbox(x_659);
lean::dec(x_659);
x_672 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_670, x_661, x_668);
x_673 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_673, 0, x_672);
return x_673;
}
else
{
obj* x_674; 
x_674 = lean::cnstr_get(x_664, 0);
lean::inc(x_674);
lean::dec(x_664);
if (lean::obj_tag(x_674) == 0)
{
obj* x_678; obj* x_681; uint8 x_683; obj* x_685; obj* x_686; 
lean::dec(x_1);
x_678 = lean::cnstr_get(x_674, 0);
lean::inc(x_678);
lean::dec(x_674);
x_681 = lean::cnstr_get(x_661, 0);
lean::inc(x_681);
x_683 = lean::unbox(x_659);
lean::dec(x_659);
x_685 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_683, x_661, x_678, x_681);
x_686 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_686, 0, x_685);
return x_686;
}
else
{
obj* x_687; obj* x_689; 
x_687 = lean::cnstr_get(x_674, 0);
lean::inc(x_687);
x_689 = lean::cnstr_get(x_661, 1);
lean::inc(x_689);
if (lean::obj_tag(x_689) == 0)
{
obj* x_694; uint8 x_697; obj* x_699; obj* x_700; 
lean::dec(x_1);
lean::dec(x_674);
lean::dec(x_689);
x_694 = lean::cnstr_get(x_661, 0);
lean::inc(x_694);
lean::dec(x_661);
x_697 = lean::unbox(x_659);
lean::dec(x_659);
x_699 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_697, x_687, x_694);
x_700 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_700, 0, x_699);
return x_700;
}
else
{
obj* x_703; obj* x_704; obj* x_706; obj* x_707; obj* x_709; 
lean::dec(x_687);
lean::dec(x_689);
x_703 = l_lean_parser_term_binder__default_has__view;
x_704 = lean::cnstr_get(x_703, 1);
lean::inc(x_704);
x_706 = lean::apply_1(x_704, x_674);
x_707 = l_lean_expander_expand__bracketed__binder___main___closed__2;
lean::inc(x_707);
x_709 = l_lean_expander_error___at_lean_expander_mk__notation__transformer___spec__1___rarg(x_706, x_707, x_1);
if (lean::obj_tag(x_709) == 0)
{
obj* x_712; obj* x_714; obj* x_715; 
lean::dec(x_659);
lean::dec(x_661);
x_712 = lean::cnstr_get(x_709, 0);
lean::inc(x_712);
if (lean::is_shared(x_709)) {
 lean::dec(x_709);
 x_714 = lean::box(0);
} else {
 lean::cnstr_release(x_709, 0);
 x_714 = x_709;
}
if (lean::is_scalar(x_714)) {
 x_715 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_715 = x_714;
}
lean::cnstr_set(x_715, 0, x_712);
return x_715;
}
else
{
obj* x_716; obj* x_718; obj* x_719; uint8 x_722; obj* x_724; obj* x_725; 
x_716 = lean::cnstr_get(x_709, 0);
lean::inc(x_716);
if (lean::is_shared(x_709)) {
 lean::dec(x_709);
 x_718 = lean::box(0);
} else {
 lean::cnstr_release(x_709, 0);
 x_718 = x_709;
}
x_719 = lean::cnstr_get(x_661, 0);
lean::inc(x_719);
lean::dec(x_661);
x_722 = lean::unbox(x_659);
lean::dec(x_659);
x_724 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_722, x_716, x_719);
if (lean::is_scalar(x_718)) {
 x_725 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_725 = x_718;
}
lean::cnstr_set(x_725, 0, x_724);
return x_725;
}
}
}
}
}
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__2(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__5(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__20(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__21(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__22(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__23(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_expander_expand__bracketed__binder(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expander_expand__bracketed__binder___main(x_0, x_1);
return x_2;
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_1, x_7);
x_12 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_13 = 0;
x_14 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_14);
x_16 = l_lean_expander_mk__simple__binder(x_12, x_13, x_14);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::apply_2(x_0, x_17, x_11);
return x_18;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_0);
x_15 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_1, x_2, x_9);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_12);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::apply_2(x_0, x_19, x_15);
return x_20;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_1, x_7);
x_12 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_13 = 0;
x_14 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_14);
x_16 = l_lean_expander_mk__simple__binder(x_12, x_13, x_14);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::apply_2(x_0, x_17, x_11);
return x_18;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_0);
x_15 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_1, x_2, x_9);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_12);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::apply_2(x_0, x_19, x_15);
return x_20;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_1, x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
x_13 = lean::apply_2(x_0, x_12, x_11);
return x_13;
}
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("match ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = l_lean_parser_ident__univs_has__view;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::inc(x_0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_0);
x_17 = lean::apply_1(x_13, x_16);
lean::inc(x_0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_0);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_0);
return x_20;
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" with ");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; 
x_0 = lean::box(0);
x_1 = lean::mk_string("x");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = l_lean_parser_term_hole_has__view;
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::mk_string("_");
x_16 = l_string_trim(x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::apply_1(x_13, x_18);
x_20 = 0;
x_21 = l_lean_expander_mk__simple__binder(x_11, x_20, x_19);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
obj* l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_1);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_15; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_12 = x_2;
}
lean::inc(x_3);
lean::inc(x_0);
x_15 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_1, x_10, x_3);
if (lean::obj_tag(x_15) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_8);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_15, 0);
lean::inc(x_24);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_26 = x_15;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_8, 0);
lean::inc(x_27);
lean::dec(x_8);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_33; 
lean::dec(x_12);
x_33 = lean::box(0);
x_30 = x_33;
goto lbl_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_12);
x_35 = lean::box(0);
x_30 = x_35;
goto lbl_31;
}
case 2:
{
obj* x_37; 
lean::dec(x_12);
x_37 = lean::box(0);
x_30 = x_37;
goto lbl_31;
}
case 3:
{
obj* x_39; 
lean::dec(x_12);
x_39 = lean::box(0);
x_30 = x_39;
goto lbl_31;
}
default:
{
obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_26);
lean::dec(x_3);
x_42 = lean::cnstr_get(x_27, 0);
lean::inc(x_42);
lean::dec(x_27);
x_45 = lean::box(0);
x_46 = l_lean_parser_term_match_has__view;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_49 = l_lean_parser_term_anonymous__constructor_has__view;
x_50 = lean::cnstr_get(x_49, 1);
lean::inc(x_50);
x_52 = lean::apply_1(x_50, x_42);
lean::inc(x_45);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_45);
lean::inc(x_45);
if (lean::is_scalar(x_12)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_12;
}
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_45);
x_57 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
lean::cnstr_set(x_59, 2, x_24);
lean::inc(x_45);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_45);
lean::inc(x_45);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_45);
x_64 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_65 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2;
x_66 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
lean::inc(x_66);
lean::inc(x_45);
lean::inc(x_65);
lean::inc(x_64);
x_71 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_71, 0, x_64);
lean::cnstr_set(x_71, 1, x_65);
lean::cnstr_set(x_71, 2, x_45);
lean::cnstr_set(x_71, 3, x_66);
lean::cnstr_set(x_71, 4, x_45);
lean::cnstr_set(x_71, 5, x_63);
x_72 = lean::apply_1(x_47, x_71);
x_73 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4;
lean::inc(x_73);
x_75 = lean::apply_2(x_0, x_73, x_72);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
}
lbl_31:
{
obj* x_78; 
lean::dec(x_30);
x_78 = l_lean_expander_expand__bracketed__binder___main(x_27, x_3);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; obj* x_84; 
lean::dec(x_0);
lean::dec(x_24);
x_81 = lean::cnstr_get(x_78, 0);
lean::inc(x_81);
lean::dec(x_78);
if (lean::is_scalar(x_26)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_84, 0, x_81);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_89; 
x_85 = lean::cnstr_get(x_78, 0);
lean::inc(x_85);
lean::dec(x_78);
x_88 = l_list_foldr___main___at_lean_expander_expand__binders___spec__5(x_0, x_24, x_85);
if (lean::is_scalar(x_26)) {
 x_89 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_89 = x_26;
}
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
obj* x_92; obj* x_95; uint8 x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_12);
lean::dec(x_3);
x_92 = lean::cnstr_get(x_8, 0);
lean::inc(x_92);
lean::dec(x_8);
x_95 = l_lean_expander_binder__ident__to__ident___main(x_92);
x_96 = 0;
x_97 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_97);
x_99 = l_lean_expander_mk__simple__binder(x_95, x_96, x_97);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
x_101 = lean::apply_2(x_0, x_100, x_24);
if (lean::is_scalar(x_26)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_26;
}
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_1, x_7);
x_12 = l_lean_expander_binder__ident__to__ident___main(x_5);
x_13 = 0;
x_14 = l_lean_expander_get__opt__type___main___closed__1;
lean::inc(x_14);
x_16 = l_lean_expander_mk__simple__binder(x_12, x_13, x_14);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::apply_2(x_0, x_17, x_11);
return x_18;
}
}
}
obj* l_list_foldr___main___at_lean_expander_expand__binders___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::inc(x_0);
x_15 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_1, x_2, x_9);
x_16 = l_lean_expander_binder__ident__to__ident___main(x_7);
x_17 = 0;
x_18 = l_lean_expander_mk__simple__binder(x_16, x_17, x_12);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::apply_2(x_0, x_19, x_15);
return x_20;
}
}
}
obj* l_lean_expander_expand__binders(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_13; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_16; 
lean::dec(x_7);
x_16 = lean::box(0);
x_13 = x_16;
goto lbl_14;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_7, 0);
lean::inc(x_17);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_list_foldr___main___at_lean_expander_expand__binders___spec__2(x_0, x_2, x_20, x_10);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_28; 
lean::dec(x_17);
lean::dec(x_19);
x_28 = lean::box(0);
x_13 = x_28;
goto lbl_14;
}
}
lbl_14:
{
obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_30 = l_list_foldr___main___at_lean_expander_expand__binders___spec__1(x_0, x_2, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
else
{
obj* x_33; 
x_33 = lean::cnstr_get(x_7, 0);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_39; 
lean::dec(x_3);
x_36 = lean::cnstr_get(x_4, 0);
lean::inc(x_36);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_43; 
lean::dec(x_7);
lean::dec(x_33);
x_43 = lean::box(0);
x_39 = x_43;
goto lbl_40;
}
else
{
obj* x_44; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_44 = x_7;
}
if (lean::obj_tag(x_33) == 0)
{
obj* x_45; obj* x_48; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_33, 0);
lean::inc(x_45);
lean::dec(x_33);
x_48 = l_list_foldr___main___at_lean_expander_expand__binders___spec__4(x_0, x_2, x_45, x_36);
if (lean::is_scalar(x_44)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_44;
}
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
else
{
obj* x_53; 
lean::dec(x_44);
lean::dec(x_33);
x_53 = lean::box(0);
x_39 = x_53;
goto lbl_40;
}
}
lbl_40:
{
obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_39);
x_55 = l_list_foldr___main___at_lean_expander_expand__binders___spec__3(x_0, x_2, x_36);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
return x_57;
}
}
else
{
obj* x_58; obj* x_62; 
x_58 = lean::cnstr_get(x_33, 0);
lean::inc(x_58);
lean::inc(x_58);
lean::inc(x_0);
x_62 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6(x_0, x_2, x_58, x_3);
if (lean::obj_tag(x_62) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_33);
lean::dec(x_58);
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
return x_71;
}
else
{
obj* x_72; obj* x_74; obj* x_75; obj* x_78; 
x_72 = lean::cnstr_get(x_62, 0);
lean::inc(x_72);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_74 = x_62;
}
x_75 = lean::cnstr_get(x_4, 0);
lean::inc(x_75);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_83; 
lean::dec(x_7);
lean::dec(x_33);
lean::dec(x_58);
x_83 = lean::box(0);
x_78 = x_83;
goto lbl_79;
}
else
{
obj* x_84; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_84 = x_7;
}
if (lean::obj_tag(x_33) == 0)
{
obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_74);
lean::dec(x_33);
x_87 = l_list_foldr___main___at_lean_expander_expand__binders___spec__8(x_0, x_72, x_58, x_75);
if (lean::is_scalar(x_84)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_84;
}
lean::cnstr_set(x_88, 0, x_87);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
return x_89;
}
else
{
obj* x_93; 
lean::dec(x_84);
lean::dec(x_33);
lean::dec(x_58);
x_93 = lean::box(0);
x_78 = x_93;
goto lbl_79;
}
}
lbl_79:
{
obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_78);
x_95 = l_list_foldr___main___at_lean_expander_expand__binders___spec__7(x_0, x_72, x_75);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
if (lean::is_scalar(x_74)) {
 x_97 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_97 = x_74;
}
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
else
{
obj* x_102; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_102 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_102);
return x_102;
}
}
}
obj* l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_lean_expander_expand__bracketed__binder___main___closed__4;
lean::inc(x_4);
return x_4;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_10 = x_0;
}
lean::inc(x_1);
x_12 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_18 = x_12;
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_22 = x_12;
}
x_23 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_8, x_1);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_29; 
lean::dec(x_10);
lean::dec(x_20);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
if (lean::is_scalar(x_22)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_29, 0, x_26);
return x_29;
}
else
{
obj* x_30; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_20);
lean::cnstr_set(x_33, 1, x_30);
if (lean::is_scalar(x_22)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_22;
}
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
obj* l_lean_expander_bracketed__binders_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = l_lean_parser_term_bracketed__binders_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
}
x_9 = l_list_mmap___main___at_lean_expander_bracketed__binders_transform___spec__1(x_6, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_8);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_13 = x_9;
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_17 = x_9;
}
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
x_20 = l_list_join___main___rarg(x_15);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::apply_1(x_18, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
else
{
obj* x_27; 
lean::dec(x_5);
lean::dec(x_1);
x_27 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_27);
return x_27;
}
}
}
obj* _init_l_lean_expander_lambda_transform___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform___lambda__1), 2, 0);
return x_0;
}
}
obj* l_lean_expander_lambda_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_13; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 3);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_lean_expander_lambda_transform___closed__1;
lean::inc(x_11);
x_13 = l_lean_expander_expand__binders(x_11, x_6, x_8, x_1);
return x_13;
}
}
obj* l_lean_expander_lambda_transform___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_2 = l_lean_parser_term_lambda_has__view;
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_6 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_6);
lean::inc(x_5);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_1);
x_10 = lean::apply_1(x_3, x_9);
return x_10;
}
}
obj* l_lean_expander_pi_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_2 = l_lean_parser_term_pi_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform___lambda__1), 3, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 3);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_lean_expander_expand__binders(x_7, x_8, x_10, x_1);
return x_13;
}
}
obj* l_lean_expander_pi_transform___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_3 = l_lean_parser_term_pi_has__view;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_9);
lean::cnstr_set(x_11, 3, x_2);
x_12 = lean::apply_1(x_4, x_11);
return x_12;
}
}
obj* _init_l_lean_expander_arrow_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("a");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* _init_l_lean_expander_arrow_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("\xce\xa0");
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_lean_expander_arrow_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_3 = l_lean_parser_term_arrow_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = l_lean_parser_term_pi_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_13 = l_lean_expander_arrow_transform___closed__1;
x_14 = l_lean_expander_mk__simple__binder___closed__1;
x_15 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
x_20 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_14);
lean::cnstr_set(x_20, 3, x_10);
lean::cnstr_set(x_20, 4, x_15);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::cnstr_get(x_6, 2);
lean::inc(x_23);
lean::dec(x_6);
x_26 = l_lean_expander_arrow_transform___closed__2;
x_27 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_27);
lean::inc(x_26);
x_30 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_22);
lean::cnstr_set(x_30, 2, x_27);
lean::cnstr_set(x_30, 3, x_23);
x_31 = lean::apply_1(x_8, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
obj* l_list_map___main___at_lean_expander_paren_transform___spec__1(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
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
lean::dec(x_3);
x_11 = l_list_map___main___at_lean_expander_paren_transform___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* _init_l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("prod");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("mk");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = l_lean_expander_glob__id(x_4);
return x_5;
}
}
obj* l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
lean::dec(x_1);
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
lean::dec(x_7);
lean::dec(x_5);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_10 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_5, lean::box(0));
x_11 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1;
lean::inc(x_14);
x_16 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_14, x_13);
return x_16;
}
}
}
obj* l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_5 = l_list_map___main___at_lean_expander_paren_transform___spec__1(x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_list_foldr1___main___at_lean_expander_paren_transform___spec__3(x_6, lean::box(0));
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_lean_expander_paren_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("unit");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("star");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = l_lean_expander_glob__id(x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* _init_l_lean_expander_paren_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("typed_expr");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_lean_expander_paren_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_term_paren_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; 
lean::dec(x_7);
x_11 = l_lean_expander_paren_transform___closed__1;
lean::inc(x_11);
return x_11;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_15 = x_7;
}
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_18);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_16);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
lean::dec(x_18);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_31; obj* x_32; 
lean::dec(x_15);
x_28 = lean::cnstr_get(x_24, 0);
lean::inc(x_28);
lean::dec(x_24);
x_31 = l_list_foldr1__opt___main___at_lean_expander_paren_transform___spec__2(x_16, x_28);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_16);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_36);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l_lean_expander_paren_transform___closed__2;
lean::inc(x_42);
x_44 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_42, x_41);
if (lean::is_scalar(x_15)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_15;
}
lean::cnstr_set(x_45, 0, x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
obj* _init_l_lean_expander_assume_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("this");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_3);
lean::cnstr_set(x_10, 3, x_0);
lean::cnstr_set(x_10, 4, x_0);
return x_10;
}
}
obj* l_lean_expander_assume_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; 
lean::dec(x_1);
x_3 = l_lean_parser_term_assume_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = l_lean_parser_term_lambda_has__view;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 3);
lean::inc(x_12);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_22 = l_lean_expander_assume_transform___closed__1;
x_23 = l_lean_expander_mk__simple__binder___closed__1;
x_24 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
x_29 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_22);
lean::cnstr_set(x_29, 2, x_23);
lean::cnstr_set(x_29, 3, x_18);
lean::cnstr_set(x_29, 4, x_24);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_33 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_33);
lean::inc(x_32);
x_36 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_31);
lean::cnstr_set(x_36, 2, x_33);
lean::cnstr_set(x_36, 3, x_12);
x_37 = lean::apply_1(x_10, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_7, 0);
lean::inc(x_40);
lean::dec(x_7);
x_43 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_44 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_44);
lean::inc(x_43);
x_47 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set(x_47, 2, x_44);
lean::cnstr_set(x_47, 3, x_12);
x_48 = lean::apply_1(x_10, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
return x_50;
}
}
}
obj* _init_l_lean_expander_if_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("ite");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* _init_l_lean_expander_if_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("not");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* _init_l_lean_expander_if_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("dite");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_lean_expander_if_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_term_if_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_7);
x_10 = lean::cnstr_get(x_6, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_6, 6);
lean::inc(x_14);
lean::dec(x_6);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_10);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_expander_if_transform___closed__1;
lean::inc(x_21);
x_23 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_21, x_20);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_60; obj* x_61; obj* x_63; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_28 = x_7;
}
x_29 = lean::cnstr_get(x_6, 2);
lean::inc(x_29);
x_31 = l_lean_parser_term_lambda_has__view;
x_32 = lean::cnstr_get(x_31, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
lean::dec(x_26);
x_37 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_38 = l_lean_expander_mk__simple__binder___closed__1;
x_39 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_39);
lean::inc(x_29);
lean::inc(x_38);
lean::inc(x_34);
lean::inc(x_37);
x_45 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_45, 0, x_37);
lean::cnstr_set(x_45, 1, x_34);
lean::cnstr_set(x_45, 2, x_38);
lean::cnstr_set(x_45, 3, x_29);
lean::cnstr_set(x_45, 4, x_39);
x_46 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::cnstr_get(x_6, 4);
lean::inc(x_48);
x_50 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_51 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_51);
lean::inc(x_50);
x_54 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_47);
lean::cnstr_set(x_54, 2, x_51);
lean::cnstr_set(x_54, 3, x_48);
lean::inc(x_32);
x_56 = lean::apply_1(x_32, x_54);
x_57 = lean::box(0);
lean::inc(x_57);
lean::inc(x_29);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_29);
lean::cnstr_set(x_60, 1, x_57);
x_61 = l_lean_expander_if_transform___closed__2;
lean::inc(x_61);
x_63 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_61, x_60);
lean::inc(x_39);
lean::inc(x_38);
lean::inc(x_37);
x_67 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_67, 0, x_37);
lean::cnstr_set(x_67, 1, x_34);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_63);
lean::cnstr_set(x_67, 4, x_39);
x_68 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::cnstr_get(x_6, 6);
lean::inc(x_70);
lean::dec(x_6);
lean::inc(x_51);
lean::inc(x_50);
x_75 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_75, 0, x_50);
lean::cnstr_set(x_75, 1, x_69);
lean::cnstr_set(x_75, 2, x_51);
lean::cnstr_set(x_75, 3, x_70);
x_76 = lean::apply_1(x_32, x_75);
x_77 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_57);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_56);
lean::cnstr_set(x_78, 1, x_77);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_29);
lean::cnstr_set(x_79, 1, x_78);
x_80 = l_lean_expander_if_transform___closed__3;
lean::inc(x_80);
x_82 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_80, x_79);
if (lean::is_scalar(x_28)) {
 x_83 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_83 = x_28;
}
lean::cnstr_set(x_83, 0, x_82);
x_84 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
}
}
obj* l_list_map___main___at_lean_expander_let_transform___spec__1(obj* x_0) {
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
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_5);
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
obj* _init_l_lean_expander_let_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_lean_parser_term_hole_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::mk_string("_");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_7, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
obj* l_lean_expander_let_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_term_let_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_11 = x_7;
}
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_18 = x_9;
}
if (lean::obj_tag(x_14) == 0)
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_16);
x_20 = lean::cnstr_get(x_3, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_6, 0);
lean::inc(x_22);
x_24 = l_lean_expander_let_transform___closed__1;
lean::inc(x_24);
if (lean::is_scalar(x_18)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_18;
}
lean::cnstr_set(x_26, 0, x_12);
lean::cnstr_set(x_26, 1, x_14);
lean::cnstr_set(x_26, 2, x_24);
if (lean::is_scalar(x_11)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_11;
}
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::cnstr_get(x_6, 2);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_6, 3);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_6, 4);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_6, 5);
lean::inc(x_34);
lean::dec(x_6);
x_37 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_37, 0, x_22);
lean::cnstr_set(x_37, 1, x_27);
lean::cnstr_set(x_37, 2, x_28);
lean::cnstr_set(x_37, 3, x_30);
lean::cnstr_set(x_37, 4, x_32);
lean::cnstr_set(x_37, 5, x_34);
x_38 = lean::apply_1(x_20, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
else
{
obj* x_47; 
lean::dec(x_14);
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_6);
x_47 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_47);
return x_47;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_91; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_49 = lean::box(0);
x_50 = l_list_map___main___at_lean_expander_let_transform___spec__1(x_14);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::inc(x_49);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_49);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::cnstr_get(x_3, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_6, 0);
lean::inc(x_58);
x_60 = l_lean_parser_term_pi_has__view;
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
x_63 = l_lean_expander_get__opt__type___main(x_16);
x_64 = l_lean_expander_arrow_transform___closed__2;
x_65 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_65);
lean::inc(x_55);
lean::inc(x_64);
x_69 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_55);
lean::cnstr_set(x_69, 2, x_65);
lean::cnstr_set(x_69, 3, x_63);
x_70 = lean::apply_1(x_61, x_69);
x_71 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_71);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_70);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
if (lean::is_scalar(x_18)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_18;
}
lean::cnstr_set(x_75, 0, x_12);
lean::cnstr_set(x_75, 1, x_49);
lean::cnstr_set(x_75, 2, x_74);
if (lean::is_scalar(x_11)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_11;
}
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean::cnstr_get(x_6, 2);
lean::inc(x_77);
x_79 = l_lean_parser_term_lambda_has__view;
x_80 = lean::cnstr_get(x_79, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_6, 3);
lean::inc(x_82);
x_84 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
lean::inc(x_65);
lean::inc(x_84);
x_87 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_55);
lean::cnstr_set(x_87, 2, x_65);
lean::cnstr_set(x_87, 3, x_82);
x_88 = lean::apply_1(x_80, x_87);
x_89 = lean::cnstr_get(x_6, 4);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_6, 5);
lean::inc(x_91);
lean::dec(x_6);
x_94 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_94, 0, x_58);
lean::cnstr_set(x_94, 1, x_76);
lean::cnstr_set(x_94, 2, x_77);
lean::cnstr_set(x_94, 3, x_88);
lean::cnstr_set(x_94, 4, x_89);
lean::cnstr_set(x_94, 5, x_91);
x_95 = lean::apply_1(x_56, x_94);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_95);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
}
else
{
obj* x_98; obj* x_101; obj* x_102; obj* x_104; obj* x_105; obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_126; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_98 = lean::cnstr_get(x_7, 0);
lean::inc(x_98);
lean::dec(x_7);
x_101 = l_lean_parser_term_match_has__view;
x_102 = lean::cnstr_get(x_101, 1);
lean::inc(x_102);
x_104 = lean::box(0);
x_105 = lean::cnstr_get(x_6, 3);
lean::inc(x_105);
lean::inc(x_104);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_104);
lean::inc(x_104);
x_110 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set(x_110, 1, x_104);
lean::inc(x_104);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_98);
lean::cnstr_set(x_112, 1, x_104);
lean::inc(x_104);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_112);
lean::cnstr_set(x_114, 1, x_104);
x_115 = lean::cnstr_get(x_6, 5);
lean::inc(x_115);
lean::dec(x_6);
x_118 = l_lean_expander_mixfix_transform___closed__4;
lean::inc(x_118);
x_120 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_120, 0, x_114);
lean::cnstr_set(x_120, 1, x_118);
lean::cnstr_set(x_120, 2, x_115);
lean::inc(x_104);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_104);
lean::inc(x_104);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set(x_124, 1, x_104);
x_125 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1;
x_126 = l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3;
lean::inc(x_126);
lean::inc(x_104);
lean::inc(x_125);
x_130 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_130, 0, x_125);
lean::cnstr_set(x_130, 1, x_110);
lean::cnstr_set(x_130, 2, x_104);
lean::cnstr_set(x_130, 3, x_126);
lean::cnstr_set(x_130, 4, x_104);
lean::cnstr_set(x_130, 5, x_124);
x_131 = lean::apply_1(x_102, x_130);
x_132 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
x_133 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_133, 0, x_132);
return x_133;
}
}
}
obj* l_list_map___main___at_lean_expander_constant_transform___spec__1(obj* x_0) {
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
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_expander_constant_transform___spec__1(x_5);
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
obj* _init_l_lean_expander_constant_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_expander_constant_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
lean::dec(x_1);
x_3 = l_lean_parser_command_constant_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_13 = x_7;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::box(0);
x_18 = l_list_map___main___at_lean_expander_constant_transform___spec__1(x_14);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_6, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_6, 1);
lean::inc(x_27);
lean::dec(x_6);
x_30 = l_lean_parser_term_pi_has__view;
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_11, 1);
lean::inc(x_33);
lean::dec(x_11);
x_36 = l_lean_expander_arrow_transform___closed__2;
x_37 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_37);
lean::inc(x_36);
x_40 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_22);
lean::cnstr_set(x_40, 2, x_37);
lean::cnstr_set(x_40, 3, x_33);
x_41 = lean::apply_1(x_31, x_40);
x_42 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_41);
x_45 = l_lean_expander_constant_transform___closed__1;
lean::inc(x_45);
if (lean::is_scalar(x_13)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_13;
}
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_44);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_25);
lean::cnstr_set(x_48, 1, x_27);
lean::cnstr_set(x_48, 2, x_47);
x_49 = lean::apply_1(x_23, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
else
{
obj* x_56; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
x_56 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_56);
return x_56;
}
}
}
obj* _init_l_lean_expander_declaration_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::mk_string("@[");
x_2 = l_string_trim(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::mk_string("]");
x_7 = l_string_trim(x_6);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_0);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("class");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = lean::mk_string(".");
lean::inc(x_3);
x_6 = l_lean_name_to__string__with__sep___main(x_4, x_3);
x_7 = l_lean_parser_substring_of__string(x_6);
lean::inc(x_0);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_3);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
lean::inc(x_0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_0);
return x_14;
}
}
obj* _init_l_lean_expander_declaration_transform___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = lean::mk_string("structure");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_expander_declaration_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = l_lean_parser_command_declaration_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
switch (lean::obj_tag(x_7)) {
case 0:
{
obj* x_11; 
lean::dec(x_7);
lean::dec(x_6);
x_11 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_11);
return x_11;
}
case 1:
{
obj* x_15; 
lean::dec(x_7);
lean::dec(x_6);
x_15 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_15);
return x_15;
}
case 2:
{
obj* x_19; 
lean::dec(x_7);
lean::dec(x_6);
x_19 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_19);
return x_19;
}
case 3:
{
obj* x_23; 
lean::dec(x_7);
lean::dec(x_6);
x_23 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_23);
return x_23;
}
case 4:
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; 
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_27 = x_7;
}
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_25, 2);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_25, 3);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_25, 4);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_25, 5);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_25, 6);
lean::inc(x_40);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 lean::cnstr_release(x_25, 2);
 lean::cnstr_release(x_25, 3);
 lean::cnstr_release(x_25, 4);
 lean::cnstr_release(x_25, 5);
 lean::cnstr_release(x_25, 6);
 x_42 = x_25;
}
if (lean::obj_tag(x_28) == 0)
{
obj* x_53; 
lean::dec(x_27);
lean::dec(x_36);
lean::dec(x_38);
lean::dec(x_6);
lean::dec(x_40);
lean::dec(x_42);
lean::dec(x_28);
lean::dec(x_30);
lean::dec(x_32);
lean::dec(x_34);
x_53 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_53);
return x_53;
}
else
{
obj* x_55; obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_79; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_55 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_55 = x_28;
}
x_56 = lean::cnstr_get(x_6, 0);
lean::inc(x_56);
lean::dec(x_6);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
x_61 = lean::box(0);
x_62 = l_lean_expander_declaration_transform___closed__1;
lean::inc(x_62);
x_64 = l_option_get__or__else___main___rarg(x_59, x_62);
x_65 = lean::cnstr_get(x_3, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_56, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_64, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_64, 1);
lean::inc(x_71);
x_73 = l_lean_expander_declaration_transform___closed__2;
lean::inc(x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_71);
x_76 = lean::cnstr_get(x_64, 2);
lean::inc(x_76);
lean::dec(x_64);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_69);
lean::cnstr_set(x_79, 1, x_75);
lean::cnstr_set(x_79, 2, x_76);
if (lean::is_scalar(x_55)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_55;
}
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::cnstr_get(x_56, 2);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_56, 3);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_56, 4);
lean::inc(x_85);
lean::dec(x_56);
x_88 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_88, 0, x_67);
lean::cnstr_set(x_88, 1, x_80);
lean::cnstr_set(x_88, 2, x_81);
lean::cnstr_set(x_88, 3, x_83);
lean::cnstr_set(x_88, 4, x_85);
if (lean::is_scalar(x_42)) {
 x_89 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_89 = x_42;
}
lean::cnstr_set(x_89, 0, x_61);
lean::cnstr_set(x_89, 1, x_30);
lean::cnstr_set(x_89, 2, x_32);
lean::cnstr_set(x_89, 3, x_34);
lean::cnstr_set(x_89, 4, x_36);
lean::cnstr_set(x_89, 5, x_38);
lean::cnstr_set(x_89, 6, x_40);
if (lean::is_scalar(x_27)) {
 x_90 = lean::alloc_cnstr(4, 1, 0);
} else {
 x_90 = x_27;
}
lean::cnstr_set(x_90, 0, x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::apply_1(x_65, x_91);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
return x_94;
}
}
default:
{
obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_110; obj* x_112; obj* x_114; 
x_95 = lean::cnstr_get(x_7, 0);
lean::inc(x_95);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_97 = x_7;
}
x_98 = lean::cnstr_get(x_95, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_95, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_95, 2);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_95, 3);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_95, 4);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_95, 5);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_95, 6);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_95, 7);
lean::inc(x_112);
if (lean::is_shared(x_95)) {
 lean::dec(x_95);
 x_114 = lean::box(0);
} else {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 lean::cnstr_release(x_95, 2);
 lean::cnstr_release(x_95, 3);
 lean::cnstr_release(x_95, 4);
 lean::cnstr_release(x_95, 5);
 lean::cnstr_release(x_95, 6);
 lean::cnstr_release(x_95, 7);
 x_114 = x_95;
}
if (lean::obj_tag(x_98) == 0)
{
obj* x_126; 
lean::dec(x_6);
lean::dec(x_104);
lean::dec(x_97);
lean::dec(x_98);
lean::dec(x_102);
lean::dec(x_100);
lean::dec(x_114);
lean::dec(x_106);
lean::dec(x_110);
lean::dec(x_108);
lean::dec(x_112);
x_126 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_126);
return x_126;
}
else
{
obj* x_129; obj* x_132; obj* x_134; obj* x_136; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_147; obj* x_148; obj* x_151; obj* x_152; obj* x_153; obj* x_155; obj* x_157; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_98);
x_129 = lean::cnstr_get(x_6, 0);
lean::inc(x_129);
lean::dec(x_6);
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
x_134 = l_lean_expander_declaration_transform___closed__1;
lean::inc(x_134);
x_136 = l_option_get__or__else___main___rarg(x_132, x_134);
x_137 = lean::cnstr_get(x_3, 1);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_129, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_136, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_136, 1);
lean::inc(x_143);
x_145 = l_lean_expander_declaration_transform___closed__2;
lean::inc(x_145);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_143);
x_148 = lean::cnstr_get(x_136, 2);
lean::inc(x_148);
lean::dec(x_136);
x_151 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_151, 0, x_141);
lean::cnstr_set(x_151, 1, x_147);
lean::cnstr_set(x_151, 2, x_148);
x_152 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_152, 0, x_151);
x_153 = lean::cnstr_get(x_129, 2);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_129, 3);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_129, 4);
lean::inc(x_157);
lean::dec(x_129);
x_160 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_160, 0, x_139);
lean::cnstr_set(x_160, 1, x_152);
lean::cnstr_set(x_160, 2, x_153);
lean::cnstr_set(x_160, 3, x_155);
lean::cnstr_set(x_160, 4, x_157);
x_161 = l_lean_expander_declaration_transform___closed__3;
lean::inc(x_161);
if (lean::is_scalar(x_114)) {
 x_163 = lean::alloc_cnstr(0, 8, 0);
} else {
 x_163 = x_114;
}
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_100);
lean::cnstr_set(x_163, 2, x_102);
lean::cnstr_set(x_163, 3, x_104);
lean::cnstr_set(x_163, 4, x_106);
lean::cnstr_set(x_163, 5, x_108);
lean::cnstr_set(x_163, 6, x_110);
lean::cnstr_set(x_163, 7, x_112);
if (lean::is_scalar(x_97)) {
 x_164 = lean::alloc_cnstr(5, 1, 0);
} else {
 x_164 = x_97;
}
lean::cnstr_set(x_164, 0, x_163);
x_165 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_165, 0, x_160);
lean::cnstr_set(x_165, 1, x_164);
x_166 = lean::apply_1(x_137, x_165);
x_167 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_167, 0, x_166);
x_168 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_168, 0, x_167);
return x_168;
}
}
}
}
}
obj* l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(obj* x_0) {
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
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_5);
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
obj* l_lean_expander_intro__rule_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; 
lean::dec(x_1);
x_3 = l_lean_parser_command_intro__rule_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_13 = x_7;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_21; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
x_21 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_21);
return x_21;
}
else
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_23 = lean::cnstr_get(x_11, 0);
lean::inc(x_23);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_25 = x_11;
}
x_26 = lean::box(0);
x_27 = l_list_map___main___at_lean_expander_intro__rule_transform___spec__1(x_14);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_25)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_25;
}
lean::cnstr_set(x_29, 0, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::cnstr_get(x_3, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_6, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_6, 1);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_6, 2);
lean::inc(x_38);
lean::dec(x_6);
x_41 = l_lean_parser_term_pi_has__view;
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_23, 1);
lean::inc(x_44);
lean::dec(x_23);
x_47 = l_lean_expander_arrow_transform___closed__2;
x_48 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_48);
lean::inc(x_47);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set(x_51, 1, x_31);
lean::cnstr_set(x_51, 2, x_48);
lean::cnstr_set(x_51, 3, x_44);
x_52 = lean::apply_1(x_42, x_51);
x_53 = l_lean_expander_mk__simple__binder___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_52);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = l_lean_expander_constant_transform___closed__1;
lean::inc(x_57);
if (lean::is_scalar(x_13)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_13;
}
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_56);
x_60 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_60, 0, x_34);
lean::cnstr_set(x_60, 1, x_36);
lean::cnstr_set(x_60, 2, x_38);
lean::cnstr_set(x_60, 3, x_59);
x_61 = lean::apply_1(x_32, x_60);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
}
else
{
obj* x_68; 
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_9);
x_68 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_68);
return x_68;
}
}
}
obj* _init_l_lean_expander_variable_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("variables");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_expander_variable_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
lean::dec(x_1);
x_3 = l_lean_parser_command_variable_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = l_lean_parser_command_variables_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_13 = lean::box(0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_13);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = l_lean_expander_variable_transform___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_18);
x_22 = lean::apply_1(x_8, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_25 = lean::cnstr_get(x_10, 0);
lean::inc(x_25);
lean::dec(x_10);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_29 = l_lean_expander_coe__binder__bracketed__binder___closed__1;
x_30 = l_lean_expander_coe__binder__bracketed__binder___closed__2;
lean::inc(x_30);
lean::inc(x_29);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set(x_33, 1, x_28);
lean::cnstr_set(x_33, 2, x_30);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_13);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = l_lean_expander_variable_transform___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_36);
x_40 = lean::apply_1(x_8, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
}
obj* _init_l_lean_expander_binding__annotation__update() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("expander");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("binding_annotation_update");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_expander_binding__annotation__update_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_expander_binding__annotation__update_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_1);
x_3 = l_option_map___rarg(x_1, x_0);
x_4 = lean::box(3);
x_5 = l_option_get__or__else___main___rarg(x_3, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_expander_binding__annotation__update;
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mk__node(x_8, x_7);
return x_10;
}
}
obj* _init_l_lean_expander_binding__annotation__update_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_expander_binding__annotation__update_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_binding__annotation__update_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_20; 
x_0 = lean::mk_string("dummy");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__view___spec__1), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_parser_term__parser__m_monad;
x_9 = l_lean_parser_term__parser__m_monad__except;
x_10 = l_lean_parser_term__parser__m_lean_parser_monad__parsec;
x_11 = l_lean_parser_term__parser__m_alternative;
x_12 = l_lean_expander_binding__annotation__update;
x_13 = l_lean_expander_binding__annotation__update_has__view;
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
x_20 = l_lean_parser_combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
return x_20;
}
}
obj* _init_l_lean_expander_binding__annotation__update_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("dummy");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_command_notation__spec_precedence__term_parser_lean_parser_has__view___spec__1), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_lean_expander_binding__annotation__update_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = l_lean_expander_binding__annotation__update;
x_6 = l_lean_expander_binding__annotation__update_parser___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_combinators_node___at_lean_parser_command_notation__spec_precedence__lit_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_9;
}
}
obj* _init_l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string(" : ");
x_2 = l_string_trim(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = l_lean_expander_binding__annotation__update_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::mk_string("dummy");
x_10 = l_string_trim(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_7, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
obj* l_list_mmap___main___at_lean_expander_variables_transform___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_lean_expander_expand__bracketed__binder___main___closed__4;
lean::inc(x_4);
return x_4;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_10 = x_0;
}
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_13, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 2);
lean::inc(x_19);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 lean::cnstr_release(x_13, 2);
 x_21 = x_13;
}
if (lean::obj_tag(x_17) == 0)
{
obj* x_27; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_17);
lean::dec(x_21);
lean::inc(x_1);
x_27 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_27;
goto lbl_12;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; 
x_28 = lean::cnstr_get(x_17, 0);
lean::inc(x_28);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_30 = x_17;
}
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_28, 2);
lean::inc(x_35);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 lean::cnstr_release(x_28, 2);
 x_37 = x_28;
}
if (lean::obj_tag(x_33) == 0)
{
lean::dec(x_33);
if (lean::obj_tag(x_35) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_6);
x_40 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1;
lean::inc(x_40);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_31);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 2, x_35);
if (lean::is_scalar(x_30)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_30;
}
lean::cnstr_set(x_43, 0, x_42);
if (lean::is_scalar(x_21)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_21;
}
lean::cnstr_set(x_44, 0, x_15);
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set(x_44, 2, x_19);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::inc(x_1);
x_47 = l_lean_expander_expand__bracketed__binder___main(x_45, x_1);
x_11 = x_47;
goto lbl_12;
}
else
{
obj* x_56; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_37);
lean::dec(x_21);
lean::dec(x_30);
lean::dec(x_31);
lean::dec(x_35);
lean::inc(x_1);
x_56 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_56;
goto lbl_12;
}
}
else
{
obj* x_66; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_37);
lean::dec(x_21);
lean::dec(x_30);
lean::dec(x_31);
lean::dec(x_33);
lean::dec(x_35);
lean::inc(x_1);
x_66 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_66;
goto lbl_12;
}
}
}
case 1:
{
obj* x_68; 
lean::inc(x_1);
x_68 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_68;
goto lbl_12;
}
case 2:
{
obj* x_70; 
lean::inc(x_1);
x_70 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_70;
goto lbl_12;
}
case 3:
{
obj* x_72; 
lean::inc(x_1);
x_72 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_72;
goto lbl_12;
}
default:
{
obj* x_74; 
lean::inc(x_1);
x_74 = l_lean_expander_expand__bracketed__binder___main(x_6, x_1);
x_11 = x_74;
goto lbl_12;
}
}
lbl_12:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_10);
x_78 = lean::cnstr_get(x_11, 0);
lean::inc(x_78);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_80 = x_11;
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_11, 0);
lean::inc(x_82);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_84 = x_11;
}
x_85 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_8, x_1);
if (lean::obj_tag(x_85) == 0)
{
obj* x_88; obj* x_91; 
lean::dec(x_10);
lean::dec(x_82);
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
if (lean::is_scalar(x_84)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_91, 0, x_88);
return x_91;
}
else
{
obj* x_92; obj* x_95; obj* x_96; 
x_92 = lean::cnstr_get(x_85, 0);
lean::inc(x_92);
lean::dec(x_85);
if (lean::is_scalar(x_10)) {
 x_95 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_95 = x_10;
}
lean::cnstr_set(x_95, 0, x_82);
lean::cnstr_set(x_95, 1, x_92);
if (lean::is_scalar(x_84)) {
 x_96 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_96 = x_84;
}
lean::cnstr_set(x_96, 0, x_95);
return x_96;
}
}
}
}
}
}
obj* l_lean_expander_variables_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_lean_parser_command_variables_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::apply_1(x_3, x_0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
}
x_12 = l_list_mmap___main___at_lean_expander_variables_transform___spec__1(x_9, x_1);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_11);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_16 = x_12;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
}
x_21 = lean::cnstr_get(x_2, 1);
lean::inc(x_21);
x_23 = l_list_join___main___rarg(x_18);
if (lean::is_scalar(x_11)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_11;
 lean::cnstr_set_tag(x_11, 1);
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = l_lean_expander_variable_transform___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_24);
x_28 = lean::apply_1(x_21, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_20)) {
 x_30 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_30 = x_20;
}
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
else
{
obj* x_33; 
lean::dec(x_6);
lean::dec(x_1);
x_33 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_33);
return x_33;
}
}
}
obj* l_lean_expander_level_leading_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; 
lean::dec(x_1);
x_3 = l_lean_parser_level_leading_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_8; 
lean::dec(x_6);
x_8 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_8);
return x_8;
}
case 1:
{
obj* x_11; 
lean::dec(x_6);
x_11 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_11);
return x_11;
}
case 2:
{
obj* x_14; 
lean::dec(x_6);
x_14 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_14);
return x_14;
}
case 3:
{
obj* x_16; obj* x_19; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_6, 0);
lean::inc(x_16);
lean::dec(x_6);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
case 4:
{
obj* x_25; 
lean::dec(x_6);
x_25 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_25);
return x_25;
}
default:
{
obj* x_28; 
lean::dec(x_6);
x_28 = l_lean_expander_no__expansion___closed__1;
lean::inc(x_28);
return x_28;
}
}
}
}
obj* _init_l_lean_expander_subtype_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = lean::mk_string("subtype");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = l_lean_expander_glob__id(x_2);
return x_3;
}
}
obj* l_lean_expander_subtype_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_3 = l_lean_parser_term_subtype_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = l_lean_parser_term_lambda_has__view;
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 2);
lean::inc(x_12);
x_14 = l_lean_expander_get__opt__type___main(x_12);
x_15 = 0;
x_16 = l_lean_expander_mk__simple__binder(x_10, x_15, x_14);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
x_18 = lean::cnstr_get(x_6, 4);
lean::inc(x_18);
lean::dec(x_6);
x_21 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2;
x_22 = l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3;
lean::inc(x_22);
lean::inc(x_21);
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set(x_25, 1, x_17);
lean::cnstr_set(x_25, 2, x_22);
lean::cnstr_set(x_25, 3, x_18);
x_26 = lean::apply_1(x_8, x_25);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_lean_expander_subtype_transform___closed__1;
lean::inc(x_29);
x_31 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
obj* _init_l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("universe");
x_2 = l_string_trim(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_list_map___main___at_lean_expander_universes_transform___spec__1(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
x_8 = l_lean_parser_command_universe_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
x_11 = l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_3);
x_14 = lean::apply_1(x_9, x_13);
x_15 = l_list_map___main___at_lean_expander_universes_transform___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
obj* l_lean_expander_universes_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_3 = l_lean_parser_command_universes_has__view;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_4, x_0);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = l_list_map___main___at_lean_expander_universes_transform___spec__1(x_7);
x_11 = l_lean_parser_no__kind;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
obj* _init_l_lean_expander_sorry_transform___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_0 = lean::box(0);
x_1 = lean::mk_string("sorry_ax");
lean::inc(x_0);
x_3 = lean::name_mk_string(x_0, x_1);
x_4 = l_lean_expander_glob__id(x_3);
x_5 = l_lean_parser_term_hole_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::mk_string("_");
x_9 = l_string_trim(x_8);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = lean::apply_1(x_6, x_12);
x_14 = lean::mk_string("bool");
lean::inc(x_0);
x_16 = lean::name_mk_string(x_0, x_14);
x_17 = lean::mk_string("ff");
x_18 = lean::name_mk_string(x_16, x_17);
x_19 = l_lean_expander_glob__id(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_list_foldl___main___at_lean_parser_term_mk__app___spec__1(x_4, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
obj* l_lean_expander_sorry_transform(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_lean_expander_sorry_transform___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; uint8 x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
uint8 x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
uint8 x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_expander_builtin__transformers___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_expander_builtin__transformers___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_rbnode_insert___at_lean_expander_builtin__transformers___spec__3(x_0, x_8, x_10);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
}
}
obj* _init_l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_0 = l_lean_parser_command_mixfix;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_mixfix_transform), 2, 0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_lean_parser_command_reserve__mixfix;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_reserve__mixfix_transform), 2, 0);
lean::inc(x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_lean_parser_term_bracketed__binders;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_bracketed__binders_transform), 2, 0);
lean::inc(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_term_lambda;
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_lambda_transform), 2, 0);
lean::inc(x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_lean_parser_term_pi;
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_pi_transform), 2, 0);
lean::inc(x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
x_20 = l_lean_parser_term_arrow;
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_arrow_transform), 2, 0);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
x_24 = l_lean_parser_term_paren;
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_paren_transform), 2, 0);
lean::inc(x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_lean_parser_term_assume;
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_assume_transform), 2, 0);
lean::inc(x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
x_32 = l_lean_parser_term_if;
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_if_transform), 2, 0);
lean::inc(x_32);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_lean_parser_term_let;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_let_transform), 2, 0);
lean::inc(x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
x_40 = l_lean_parser_command_constant;
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_constant_transform), 2, 0);
lean::inc(x_40);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_lean_parser_command_declaration;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_declaration_transform), 2, 0);
lean::inc(x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
x_48 = l_lean_parser_command_intro__rule;
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_intro__rule_transform), 2, 0);
lean::inc(x_48);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
x_52 = l_lean_parser_command_variable;
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variable_transform), 2, 0);
lean::inc(x_52);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
x_56 = l_lean_parser_command_variables;
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_variables_transform), 2, 0);
lean::inc(x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
x_60 = l_lean_parser_level_leading;
x_61 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_level_leading_transform), 2, 0);
lean::inc(x_60);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
x_64 = l_lean_parser_term_subtype;
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_subtype_transform), 2, 0);
lean::inc(x_64);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set(x_67, 1, x_65);
x_68 = l_lean_parser_command_universes;
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_universes_transform), 2, 0);
lean::inc(x_68);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_69);
x_72 = l_lean_parser_term_sorry;
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_sorry_transform), 2, 0);
lean::inc(x_72);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
x_76 = lean::box(0);
lean::inc(x_76);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_71);
lean::cnstr_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_67);
lean::cnstr_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_63);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_59);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_55);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_51);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_47);
lean::cnstr_set(x_85, 1, x_84);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_43);
lean::cnstr_set(x_86, 1, x_85);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_39);
lean::cnstr_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_35);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_31);
lean::cnstr_set(x_89, 1, x_88);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_27);
lean::cnstr_set(x_90, 1, x_89);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_23);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_19);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_15);
lean::cnstr_set(x_93, 1, x_92);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_11);
lean::cnstr_set(x_94, 1, x_93);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_7);
lean::cnstr_set(x_95, 1, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_3);
lean::cnstr_set(x_96, 1, x_95);
x_97 = l_list_foldl___main___at_lean_expander_builtin__transformers___spec__5(x_76, x_96);
return x_97;
}
}
obj* _init_l_lean_expander_builtin__transformers() {
_start:
{
obj* x_0; 
x_0 = l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_expander_expander__config_has__lift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_expander_expander__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_expander_expander__state_new() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(0u);
return x_0;
}
}
obj* l_lean_expander_mk__scope(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_0, x_3);
lean::dec(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_4);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* l_lean_expander_error___at___private_1776961947__expand__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_lean_parser_syntax_get__pos(x_0);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_option_get__or__else___main___rarg(x_13, x_14);
x_16 = l_lean_file__map_to__position(x_10, x_15);
x_17 = lean::box(0);
x_18 = 2;
x_19 = l_string_join___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_16);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_19);
lean::cnstr_set(x_21, 4, x_1);
lean::cnstr_set_scalar(x_21, sizeof(void*)*5, x_18);
x_22 = x_21;
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
obj* l_lean_expander_error___at___private_1776961947__expand__core___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_error___at___private_1776961947__expand__core___main___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at___private_1776961947__expand__core___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_mmap___main___at___private_1776961947__expand__core___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
lean::inc(x_3);
lean::inc(x_0);
x_17 = l___private_1776961947__expand__core___main(x_0, x_10, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_24 = x_17;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
return x_25;
}
else
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
x_26 = lean::cnstr_get(x_17, 0);
lean::inc(x_26);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_28 = x_17;
}
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_33 = x_26;
}
x_34 = l_list_mmap___main___at___private_1776961947__expand__core___main___spec__3(x_0, x_12, x_31, x_3);
if (lean::obj_tag(x_34) == 0)
{
obj* x_38; obj* x_41; 
lean::dec(x_14);
lean::dec(x_29);
lean::dec(x_33);
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
if (lean::is_scalar(x_28)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_28;
 lean::cnstr_set_tag(x_28, 0);
}
lean::cnstr_set(x_41, 0, x_38);
return x_41;
}
else
{
obj* x_42; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; 
x_42 = lean::cnstr_get(x_34, 0);
lean::inc(x_42);
lean::dec(x_34);
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
lean::dec(x_42);
if (lean::is_scalar(x_14)) {
 x_50 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_50 = x_14;
}
lean::cnstr_set(x_50, 0, x_29);
lean::cnstr_set(x_50, 1, x_45);
if (lean::is_scalar(x_33)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_33;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
if (lean::is_scalar(x_28)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_28;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
obj* l_list_map___main___at___private_1776961947__expand__core___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::box(0);
lean::inc(x_0);
if (lean::is_scalar(x_9)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_9;
}
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_lean_parser_syntax_flip__scopes___main(x_12, x_5);
x_14 = l_list_map___main___at___private_1776961947__expand__core___main___spec__4(x_0, x_7);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
obj* l_list_mmap___main___at___private_1776961947__expand__core___main___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_14 = x_1;
}
lean::inc(x_3);
lean::inc(x_0);
x_17 = l___private_1776961947__expand__core___main(x_0, x_10, x_2, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_24 = x_17;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
return x_25;
}
else
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_34; 
x_26 = lean::cnstr_get(x_17, 0);
lean::inc(x_26);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_28 = x_17;
}
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_33 = x_26;
}
x_34 = l_list_mmap___main___at___private_1776961947__expand__core___main___spec__5(x_0, x_12, x_31, x_3);
if (lean::obj_tag(x_34) == 0)
{
obj* x_38; obj* x_41; 
lean::dec(x_14);
lean::dec(x_29);
lean::dec(x_33);
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
if (lean::is_scalar(x_28)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_28;
 lean::cnstr_set_tag(x_28, 0);
}
lean::cnstr_set(x_41, 0, x_38);
return x_41;
}
else
{
obj* x_42; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; 
x_42 = lean::cnstr_get(x_34, 0);
lean::inc(x_42);
lean::dec(x_34);
x_45 = lean::cnstr_get(x_42, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
lean::dec(x_42);
if (lean::is_scalar(x_14)) {
 x_50 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_50 = x_14;
}
lean::cnstr_set(x_50, 0, x_29);
lean::cnstr_set(x_50, 1, x_45);
if (lean::is_scalar(x_33)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_33;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
if (lean::is_scalar(x_28)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_28;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
obj* _init_l___private_1776961947__expand__core___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("macro expansion limit exceeded");
return x_0;
}
}
obj* l___private_1776961947__expand__core___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::inc(x_1);
x_8 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_2);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_24; obj* x_27; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_sub(x_0, x_18);
lean::dec(x_18);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 0);
lean::inc(x_24);
lean::inc(x_24);
x_27 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_22, x_24);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_32; 
lean::dec(x_27);
x_29 = lean::cnstr_get(x_15, 1);
lean::inc(x_29);
lean::dec(x_15);
x_32 = l_list_mmap___main___at___private_1776961947__expand__core___main___spec__3(x_19, x_29, x_2, x_3);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_24);
x_34 = lean::cnstr_get(x_32, 0);
lean::inc(x_34);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 x_36 = x_32;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_32, 0);
lean::inc(x_38);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 x_40 = x_32;
}
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
if (lean::is_shared(x_38)) {
 lean::dec(x_38);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_45 = x_38;
}
x_46 = l_lean_parser_syntax_mk__node(x_24, x_41);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_40)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_40;
}
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
}
else
{
obj* x_49; obj* x_53; 
x_49 = lean::cnstr_get(x_27, 0);
lean::inc(x_49);
lean::dec(x_27);
lean::inc(x_3);
x_53 = l_lean_expander_mk__scope(x_2, x_3);
if (lean::obj_tag(x_53) == 0)
{
obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_24);
lean::dec(x_49);
x_59 = lean::cnstr_get(x_53, 0);
lean::inc(x_59);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_61 = x_53;
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_76; obj* x_78; obj* x_79; obj* x_81; 
x_63 = lean::cnstr_get(x_53, 0);
lean::inc(x_63);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_65 = x_53;
}
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_63, 1);
lean::inc(x_68);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_70 = x_63;
}
x_71 = lean::cnstr_get(x_15, 1);
lean::inc(x_71);
lean::dec(x_15);
lean::inc(x_71);
lean::inc(x_66);
x_76 = l_list_map___main___at___private_1776961947__expand__core___main___spec__4(x_66, x_71);
lean::inc(x_24);
x_78 = l_lean_parser_syntax_mk__node(x_24, x_76);
x_79 = lean::cnstr_get(x_3, 0);
lean::inc(x_79);
x_81 = lean::apply_2(x_49, x_78, x_79);
if (lean::obj_tag(x_81) == 0)
{
obj* x_89; obj* x_92; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_24);
lean::dec(x_68);
lean::dec(x_66);
lean::dec(x_70);
lean::dec(x_71);
x_89 = lean::cnstr_get(x_81, 0);
lean::inc(x_89);
lean::dec(x_81);
if (lean::is_scalar(x_65)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_92, 0, x_89);
return x_92;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_81, 0);
lean::inc(x_93);
lean::dec(x_81);
if (lean::obj_tag(x_93) == 0)
{
obj* x_98; 
lean::dec(x_66);
lean::dec(x_93);
x_98 = l_list_mmap___main___at___private_1776961947__expand__core___main___spec__5(x_19, x_71, x_68, x_3);
if (lean::obj_tag(x_98) == 0)
{
obj* x_101; obj* x_104; 
lean::dec(x_24);
lean::dec(x_70);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
lean::dec(x_98);
if (lean::is_scalar(x_65)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_104, 0, x_101);
return x_104;
}
else
{
obj* x_105; obj* x_108; obj* x_110; obj* x_113; obj* x_114; obj* x_115; 
x_105 = lean::cnstr_get(x_98, 0);
lean::inc(x_105);
lean::dec(x_98);
x_108 = lean::cnstr_get(x_105, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_105, 1);
lean::inc(x_110);
lean::dec(x_105);
x_113 = l_lean_parser_syntax_mk__node(x_24, x_108);
if (lean::is_scalar(x_70)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_70;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_110);
if (lean::is_scalar(x_65)) {
 x_115 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_115 = x_65;
}
lean::cnstr_set(x_115, 0, x_114);
return x_115;
}
}
else
{
obj* x_120; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_24);
lean::dec(x_65);
lean::dec(x_70);
lean::dec(x_71);
x_120 = lean::cnstr_get(x_93, 0);
lean::inc(x_120);
lean::dec(x_93);
x_123 = lean::box(0);
x_124 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_124, 0, x_66);
lean::cnstr_set(x_124, 1, x_123);
x_125 = l_lean_parser_syntax_flip__scopes___main(x_124, x_120);
x_0 = x_19;
x_1 = x_125;
x_2 = x_68;
goto _start;
}
}
}
}
}
}
else
{
obj* x_128; obj* x_130; 
lean::dec(x_0);
x_128 = l___private_1776961947__expand__core___main___closed__1;
lean::inc(x_128);
x_130 = l_lean_expander_error___at___private_1776961947__expand__core___main___spec__1___rarg(x_1, x_128, x_2, x_3);
return x_130;
}
}
}
obj* l___private_1776961947__expand__core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_1776961947__expand__core___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_expander_expand(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::mk_nat_obj(1000u);
x_3 = l_lean_expander_expander__state_new;
lean::inc(x_3);
x_5 = l___private_1776961947__expand__core___main(x_2, x_0, x_3, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_8 = x_5;
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_13);
return x_16;
}
}
}
void initialize_init_lean_parser_module();
void initialize_init_lean_expr();
static bool _G_initialized = false;
void initialize_init_lean_expander() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_module();
 initialize_init_lean_expr();
 l_lean_expander_transform__m_monad__except = _init_l_lean_expander_transform__m_monad__except();
 l_lean_expander_transform__m_monad__reader = _init_l_lean_expander_transform__m_monad__reader();
 l_lean_expander_transform__m_monad = _init_l_lean_expander_transform__m_monad();
 l_lean_expander_transform__m = _init_l_lean_expander_transform__m();
 l_lean_expander_transformer = _init_l_lean_expander_transformer();
 l_lean_expander_no__expansion___closed__1 = _init_l_lean_expander_no__expansion___closed__1();
 l_lean_expander_coe__binder__bracketed__binder___closed__1 = _init_l_lean_expander_coe__binder__bracketed__binder___closed__1();
 l_lean_expander_coe__binder__bracketed__binder___closed__2 = _init_l_lean_expander_coe__binder__bracketed__binder___closed__2();
 l___private_4083062675__pop__stx__arg___closed__1 = _init_l___private_4083062675__pop__stx__arg___closed__1();
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__1();
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__2();
 l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3 = _init_l_list_mmap_x_27___main___at_lean_expander_mk__notation__transformer___spec__4___closed__3();
 l_lean_expander_mixfix__to__notation__spec___closed__1 = _init_l_lean_expander_mixfix__to__notation__spec___closed__1();
 l_lean_expander_mixfix__to__notation__spec___closed__2 = _init_l_lean_expander_mixfix__to__notation__spec___closed__2();
 l_lean_expander_mixfix__to__notation__spec___closed__3 = _init_l_lean_expander_mixfix__to__notation__spec___closed__3();
 l_lean_expander_mixfix__to__notation__spec___closed__4 = _init_l_lean_expander_mixfix__to__notation__spec___closed__4();
 l_lean_expander_mixfix__to__notation__spec___closed__5 = _init_l_lean_expander_mixfix__to__notation__spec___closed__5();
 l_lean_expander_mixfix__to__notation__spec___closed__6 = _init_l_lean_expander_mixfix__to__notation__spec___closed__6();
 l_lean_expander_mixfix__to__notation__spec___closed__7 = _init_l_lean_expander_mixfix__to__notation__spec___closed__7();
 l_lean_expander_mixfix_transform___closed__1 = _init_l_lean_expander_mixfix_transform___closed__1();
 l_lean_expander_mixfix_transform___closed__2 = _init_l_lean_expander_mixfix_transform___closed__2();
 l_lean_expander_mixfix_transform___closed__3 = _init_l_lean_expander_mixfix_transform___closed__3();
 l_lean_expander_mixfix_transform___closed__4 = _init_l_lean_expander_mixfix_transform___closed__4();
 l_lean_expander_mixfix_transform___closed__5 = _init_l_lean_expander_mixfix_transform___closed__5();
 l_lean_expander_mixfix_transform___closed__6 = _init_l_lean_expander_mixfix_transform___closed__6();
 l_lean_expander_reserve__mixfix_transform___closed__1 = _init_l_lean_expander_reserve__mixfix_transform___closed__1();
 l_lean_expander_mk__simple__binder___closed__1 = _init_l_lean_expander_mk__simple__binder___closed__1();
 l_lean_expander_mk__simple__binder___closed__2 = _init_l_lean_expander_mk__simple__binder___closed__2();
 l_lean_expander_mk__simple__binder___closed__3 = _init_l_lean_expander_mk__simple__binder___closed__3();
 l_lean_expander_mk__simple__binder___closed__4 = _init_l_lean_expander_mk__simple__binder___closed__4();
 l_lean_expander_mk__simple__binder___closed__5 = _init_l_lean_expander_mk__simple__binder___closed__5();
 l_lean_expander_mk__simple__binder___closed__6 = _init_l_lean_expander_mk__simple__binder___closed__6();
 l_lean_expander_mk__simple__binder___closed__7 = _init_l_lean_expander_mk__simple__binder___closed__7();
 l_lean_expander_binder__ident__to__ident___main___closed__1 = _init_l_lean_expander_binder__ident__to__ident___main___closed__1();
 l_lean_expander_get__opt__type___main___closed__1 = _init_l_lean_expander_get__opt__type___main___closed__1();
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__1___closed__1();
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__3___closed__1();
 l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1 = _init_l_list_map___main___at_lean_expander_expand__bracketed__binder___main___spec__4___closed__1();
 l_lean_expander_expand__bracketed__binder___main___closed__1 = _init_l_lean_expander_expand__bracketed__binder___main___closed__1();
 l_lean_expander_expand__bracketed__binder___main___closed__2 = _init_l_lean_expander_expand__bracketed__binder___main___closed__2();
 l_lean_expander_expand__bracketed__binder___main___closed__3 = _init_l_lean_expander_expand__bracketed__binder___main___closed__3();
 l_lean_expander_expand__bracketed__binder___main___closed__4 = _init_l_lean_expander_expand__bracketed__binder___main___closed__4();
 l_lean_expander_expand__bracketed__binder___main___closed__5 = _init_l_lean_expander_expand__bracketed__binder___main___closed__5();
 l_lean_expander_expand__bracketed__binder___main___closed__6 = _init_l_lean_expander_expand__bracketed__binder___main___closed__6();
 l_lean_expander_expand__bracketed__binder___main___closed__7 = _init_l_lean_expander_expand__bracketed__binder___main___closed__7();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__1();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__2();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__3();
 l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4 = _init_l_list_mfoldr___main___at_lean_expander_expand__binders___spec__6___closed__4();
 l_lean_expander_lambda_transform___closed__1 = _init_l_lean_expander_lambda_transform___closed__1();
 l_lean_expander_arrow_transform___closed__1 = _init_l_lean_expander_arrow_transform___closed__1();
 l_lean_expander_arrow_transform___closed__2 = _init_l_lean_expander_arrow_transform___closed__2();
 l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1 = _init_l_list_foldr1___main___at_lean_expander_paren_transform___spec__3___closed__1();
 l_lean_expander_paren_transform___closed__1 = _init_l_lean_expander_paren_transform___closed__1();
 l_lean_expander_paren_transform___closed__2 = _init_l_lean_expander_paren_transform___closed__2();
 l_lean_expander_assume_transform___closed__1 = _init_l_lean_expander_assume_transform___closed__1();
 l_lean_expander_if_transform___closed__1 = _init_l_lean_expander_if_transform___closed__1();
 l_lean_expander_if_transform___closed__2 = _init_l_lean_expander_if_transform___closed__2();
 l_lean_expander_if_transform___closed__3 = _init_l_lean_expander_if_transform___closed__3();
 l_lean_expander_let_transform___closed__1 = _init_l_lean_expander_let_transform___closed__1();
 l_lean_expander_constant_transform___closed__1 = _init_l_lean_expander_constant_transform___closed__1();
 l_lean_expander_declaration_transform___closed__1 = _init_l_lean_expander_declaration_transform___closed__1();
 l_lean_expander_declaration_transform___closed__2 = _init_l_lean_expander_declaration_transform___closed__2();
 l_lean_expander_declaration_transform___closed__3 = _init_l_lean_expander_declaration_transform___closed__3();
 l_lean_expander_variable_transform___closed__1 = _init_l_lean_expander_variable_transform___closed__1();
 l_lean_expander_binding__annotation__update = _init_l_lean_expander_binding__annotation__update();
 l_lean_expander_binding__annotation__update_has__view_x_27 = _init_l_lean_expander_binding__annotation__update_has__view_x_27();
 l_lean_expander_binding__annotation__update_has__view = _init_l_lean_expander_binding__annotation__update_has__view();
 l_lean_expander_binding__annotation__update_parser_lean_parser_has__view = _init_l_lean_expander_binding__annotation__update_parser_lean_parser_has__view();
 l_lean_expander_binding__annotation__update_parser___closed__1 = _init_l_lean_expander_binding__annotation__update_parser___closed__1();
 l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1 = _init_l_list_mmap___main___at_lean_expander_variables_transform___spec__1___closed__1();
 l_lean_expander_subtype_transform___closed__1 = _init_l_lean_expander_subtype_transform___closed__1();
 l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1 = _init_l_list_map___main___at_lean_expander_universes_transform___spec__1___closed__1();
 l_lean_expander_sorry_transform___closed__1 = _init_l_lean_expander_sorry_transform___closed__1();
 l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1 = _init_l_rbmap_from__list___at_lean_expander_builtin__transformers___spec__1();
 l_lean_expander_builtin__transformers = _init_l_lean_expander_builtin__transformers();
 l_lean_expander_expander__m = _init_l_lean_expander_expander__m();
 l_lean_expander_expander__state_new = _init_l_lean_expander_expander__state_new();
 l___private_1776961947__expand__core___main___closed__1 = _init_l___private_1776961947__expand__core___main___closed__1();
}
